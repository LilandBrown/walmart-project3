#!/usr/bin/env python3
"""
Walmart Checkout Demo — observe (and optionally replay) the checkout API calls.

A walkthrough tool, laid out like the cart tool. It attaches a Frida agent to the Walmart
Canada app in BlueStacks and documents the two GraphQL operations that make up checkout as
you drive it by hand:

  CreatePurchaseContract — prices and locks the cart, returns a contractId
  PlaceOrder             — the operation that commits the order

For each call it captures the exact details: the request (operation, URL with the
persisted-query hash, Apollo headers, and the full body) AND — for a call that reaches the
network — the RESPONSE the gateway sends back, read non-destructively at the okhttp layer
so the app still gets it (the contractId for checkout; the order result for place order).

Interception is governed entirely by the Mode, applied the SAME to both ops — there is no
special PlaceOrder guard:
  Watch     — both reach Walmart and are documented (a Place Order the app makes goes
              through and the order is placed).
  Intercept — both are blocked on-device; nothing reaches Walmart.
  Idle      — both pass through, nothing logged.

Beyond observing, it can REPLAY a captured call through the app's own OkHttpClient (so
its interceptors mint the PerimeterX token) and show the response. Each pane dispatches
its own way:

  Checkout calls — "Generate & Send xN (mint)" builds N CreatePurchaseContract calls for
                   each account that has a checkout call of its own in the box, from THAT
                   account's capture, and sends them. That is the pane's only dispatch:
                   the account list can only be read off the box if generating and
                   sending are one action.
  Place order    — "Generate PlaceOrder" builds a row from a contractId; the pane's
                   "Send (LIVE)" sends the row(s) you select. Sending one COMMITS an
                   order, so it stays a deliberate, selected step.

Sending is host-driven and explicit — the agent never sends on its own.

Requires a rooted BlueStacks instance with frida-server running and the Walmart app
logged in — same setup as the cart tool (see ../cart_tool/README.md).
"""
import os, sys, json, time, threading, queue, subprocess, re, shutil, socket
import tkinter as tk
import sendlog
from session import (Instance, discover, find_adb,
                     load_json, mode_column, save_json, run,
                     BASE, CONFIG_PATH, DEFAULT_CONFIG)
from tkinter import ttk, messagebox


# Captured calls kept as templates, so they can be generated later without navigating the
# app. Separate from config.json so Settings stays clean.
TEMPLATE_PATH = os.path.join(BASE, "placeorder_template.json")           # PlaceOrder
CHECKOUT_TEMPLATE_PATH = os.path.join(BASE, "checkout_template.json")    # CreatePurchaseContract

# The field a generated PlaceOrder rewrites. Named rather than inlined because the
# builder and the "is this template usable at all?" guard have to agree on it, and they
# sit in different methods now that a conversion runs over every id in the list.
TEMPLATE_CONTRACT_RE = r'"contractId"\s*:\s*"[^"]*"'
























def pretty_body(raw):
    """Pretty-print a captured GraphQL body, and split out the persisted-query hash."""
    if not raw:
        return "(no body)", None
    try:
        obj = json.loads(raw)
    except Exception:
        return raw, None
    h = None
    try:
        h = obj["extensions"]["persistedQuery"]["sha256Hash"]
    except Exception:
        pass
    return json.dumps(obj, indent=2, ensure_ascii=False), h


def extract_contract_id(raw):
    """Best-effort pull of a contractId out of a CreatePurchaseContract response body.
    The response field name varies by build, so try, in order: any key that looks like a
    contract id (contractId / purchaseContractId), then an id/contractId sitting inside an
    object whose key mentions 'contract' (createPurchaseContract{ id }, purchaseContract{…}),
    then raw-text regexes (covers multipart/wrapped bodies). A convenience label for the
    log/list — the full body is always kept."""
    if not raw:
        return None

    def by_key(o):
        if isinstance(o, dict):
            for k, v in o.items():
                if isinstance(k, str) and k.lower() in ("contractid", "purchasecontractid") \
                        and isinstance(v, str) and v:
                    return v
                r = by_key(v)
                if r:
                    return r
        elif isinstance(o, list):
            for v in o:
                r = by_key(v)
                if r:
                    return r
        return None

    def by_contract_parent(o):
        if isinstance(o, dict):
            for k, v in o.items():
                if isinstance(k, str) and "contract" in k.lower() and isinstance(v, dict):
                    cand = v.get("contractId") or v.get("id")
                    if isinstance(cand, str) and cand:
                        return cand
                r = by_contract_parent(v)
                if r:
                    return r
        elif isinstance(o, list):
            for v in o:
                r = by_contract_parent(v)
                if r:
                    return r
        return None

    try:
        obj = json.loads(raw)
    except Exception:
        obj = None
    if obj is not None:
        return by_key(obj) or by_contract_parent(obj)

    for pat in (r'"(?:purchaseC|c)ontractId"\s*:\s*"([^"]+)"',
                r'"(?:create)?[Pp]urchaseContract"\s*:\s*\{[^{}]*?"id"\s*:\s*"([^"]+)"'):
        m = re.search(pat, raw)
        if m:
            return m.group(1)
    return None


# The one field that says an order really happened. Walmart sets it when the order is
# handed to its order-management system; anything else — `CREATED` above all — is an
# order record that exists and was never placed.
ORDER_PLACED_STATUS = "SEND_TO_OMS"


def checkout_result(raw):
    """What Walmart actually DID, read out of a checkout / place-order response body.

    Returns {"errors": [(code, message)], "status": str|None, "order_id": str|None}.

    This function exists because the transport cannot see a refusal. Walmart refuses a
    checkout with **HTTP 200 and no GraphQL `errors` array** — which is every signal the
    agent has, so it scores the send `accepted` (agent_toolkit.js) and the row goes out
    green. The refusal is in the body instead: `checkoutError`, a populated array beside
    an order whose status never leaves `CREATED`:

        {"code": "item_policy_violation", "operationalErrorCode": "POLICY_VIOLATION",
         "message": "Limit of  items per customer.", ...}

    Three runs reported 22 sends ACCEPTED when 10 of them placed no order. The only
    place that difference ever appeared was in here.

    Read shape-agnostically on purpose: prep answers under `data.createPurchaseContract`
    and commit under `data.placeOrder`, and both carry the same `checkoutError`/`order`
    pair, so whichever single object sits under `data` is the one read.

    Both refusal shapes are read — `checkoutError` under the op, and the top-level
    GraphQL `errors` array beside a null op (`graphql_errors`), which is where a payment
    decline lands. Either one is a refusal and neither is visible from the wire.
    """
    empty = {"errors": [], "status": None, "order_id": None}
    if not raw:
        return empty
    try:
        obj = json.loads(raw)
    except Exception:
        # Not walkable JSON. The row falls back to reporting the HTTP code, which is
        # what it did before this existed — worse, but never wrong about what it knows.
        return empty
    if not isinstance(obj, dict):
        return empty
    errors, status, order_id = [], None, None
    data = obj.get("data")
    op = (next((v for v in data.values() if isinstance(v, dict)), None)
          if isinstance(data, dict) else None)
    if op is not None:
        for e in (op.get("checkoutError") or []):
            if not isinstance(e, dict):
                continue
            # `code` is the specific one (item_policy_violation); operationalErrorCode is
            # its family (POLICY_VIOLATION). The specific one is what names the row.
            code = e.get("code") or e.get("operationalErrorCode") or "checkout_error"
            errors.append((str(code), str(e.get("message") or "").strip()))
        order = op.get("order") if isinstance(op.get("order"), dict) else {}
        status, order_id = order.get("status"), order.get("id")
    # After the op's own, never instead of it: when a call gets far enough to name a
    # checkout refusal, that is the more specific answer and it names the row.
    errors += graphql_errors(obj)
    return {"errors": errors, "status": status, "order_id": order_id}


def graphql_errors(obj):
    """Walmart's OTHER refusal: a top-level `errors` array beside a null op.

    `checkoutError` is what a checkout that RAN produces. A declined payment never gets
    that far — the resolver returns nothing and the reason arrives one level up, next to
    a `data` that parses fine and holds nothing:

        {"data": {"placeOrder": null},
         "errors": [{"message": "Your payment couldn't be authorized. ...",
                     "extensions": {"code": "payment_service_authorization_decline",
                                    "upstreamErrorCode": "400.PAYMENT.Z499",
                                    "statusCode": 400}}]}

    Unread, that row said `sent HTTP 200` — the same slot, in the same amber, as a body
    we simply could not parse — while its six siblings in the same box read
    `sent ✓ order …`. The run's only two failures were the only two rows claiming
    nothing was wrong. Read here they name themselves and go red like any other refusal.

    `extensions.code` is the specific one; `upstreamErrorCode` (400.PAYMENT.Z499) is the
    service's own and stands in when there is no code, because a row naming the upstream
    code is still a row that says refused.
    """
    out = []
    if not isinstance(obj, dict):
        return out
    for e in (obj.get("errors") or []):
        if not isinstance(e, dict):
            continue
        ext = e.get("extensions") if isinstance(e.get("extensions"), dict) else {}
        code = ext.get("code") or ext.get("upstreamErrorCode") or "graphql_error"
        out.append((str(code), str(e.get("message") or "").strip()))
    return out


def refusal_label(errors):
    """`⛔ ITEM_POLICY_VIOLATION` — the first refusal, as the row's whole verdict.

    Upper-cased because it replaces `sent HTTP 200` in the same slot and has to read as
    a verdict rather than as a field out of a body. Only the first is shown; the rest
    are in the detail the row expands to.
    """
    if not errors:
        return ""
    more = f" (+{len(errors) - 1})" if len(errors) > 1 else ""
    return "⛔ " + errors[0][0].upper() + more






class CheckoutPanel:
    # Mode: what the agent does with a checkout call the app makes. Set PER OP — Checkout
    # (CreatePurchaseContract) and Place order (PlaceOrder) each carry their own mode.
    # Descriptions below are per-op-generic.
    MODES = {
        "watch": ("Watch — observe & document",
                  "reaches Walmart & is documented, response read (→ ● observed). "
                  "the app's own call goes through."),
        "intercept": ("Intercept — block & document",
                      "blocked on-device — nothing reaches Walmart (→ ⛔ BLOCKED)."),
        "idle":  ("Idle — attached, log nothing",
                  "passes through, nothing logged."),
    }
    MODE_CHOICES = ("watch", "intercept", "idle")
    # dot colour: green = observing (calls reach Walmart), red = blocking what the app
    # sends, grey = quiet/pass-through.
    MODE_COLOUR = {"watch": "#0a7d00", "intercept": "#b30000", "idle": "#6b6b6b"}

    # Chain mode: what THIS TOOL does after it sees a checkout call, as opposed to what
    # the agent does with the app's call (that is MODES, above). The two are
    # independent and both matter: a chain needs the checkout op set to Watch or
    # Intercept to see anything at all, but seeing it and acting on it are separate
    # decisions and are separate switches.
    #
    # Unlike every other mode in this panel, this one is NOT pushed to the agent —
    # there is no `setcheckoutmode` broadcast for it, nothing on-device changes, and
    # an instance connecting later inherits nothing from it. It is a host-side
    # reaction to a call that has already been captured, which is exactly why it can
    # be flipped mid-run without touching the emulators.
    #
    # Both settings exist to be shown side by side: Manual is the tool as it was, and
    # is what a walkthrough should start on, so the four clicks are visible as four
    # separate acts before Auto-arm collapses three of them.
    CHAIN_MODES = {
        "manual": ("Manual — every step by hand",
                   "a captured checkout does nothing on its own. Mint, → PlaceOrder "
                   "calls and ▶ Send (LIVE) stay four separate clicks."),
        "armed":  ("Auto-arm — mint, convert, select",
                   "a captured checkout mints ×N on the accounts that have one, turns "
                   "the new ids into PlaceOrder rows and selects them. It stops there "
                   "— ▶ Send (LIVE) is still a click you make."),
    }
    CHAIN_CHOICES = ("manual", "armed")
    # Amber, not green: armed means loaded and waiting on you, which is not the same
    # kind of state as "observing" and should not borrow its colour.
    CHAIN_COLOUR = {"manual": "#6b6b6b", "armed": "#b26a00"}

    def __init__(self, root, session):
        # `root` is the collapsible section this panel builds into; `session`
        # is the one connection both panels share (see session.py).
        self.session = session
        session.register(self)
        self.root = root
        # There is no standalone mode and no broker any more: a panel is always a
        # section of the one window, on the one session.
        for k, v in DEFAULT_CONFIG.items():
            self.cfg.setdefault(k, v)
        # The instance a connect/switch is working towards, as (Instance, verb), or None.
        # A switch tears down the old session on a worker, so for a second or two the
        # OLD instance is still connected while the picker already shows the new one —
        # without this the header would name the account you just moved off. The header
        # reads this first, so it reports the transition instead of a stale truth.
        # Serialises switches: clicking through instances quickly must not leave two
        # workers tearing down and attaching over each other.
        self._switch_lock = threading.Lock()
        # Two panes (prep = CreatePurchaseContract, commit = PlaceOrder). Newest first.
        #
        # ONE list per operation, holding both dispositions. They used to be four —
        # <stage>_watch and <stage>_int — which meant a walkthrough's calls arrived in
        # two different boxes depending on which mode was in force at the time, and
        # reading the sequence back meant looking in both. The disposition is a property
        # of the row now (tagged and coloured), not of which box it landed in.
        self.prep_calls = []
        self.commit_calls = []
        self.box_data = {}         # listbox widget -> attribute name of its list
        # listbox widget -> [index into that box's list per line]. A row can occupy
        # more than one line, so a line number is not a row number.
        self.box_rows = {}
        # Per-op mode (plain strs: worker threads must not touch tk vars). 'prep' =
        # CreatePurchaseContract, 'commit' = PlaceOrder — set independently.
        self.mode_state = {"prep": "watch", "commit": "watch"}
        # Templates to generate calls from without navigating the app, kept PER
        # INSTANCE: {instance key: {url, headers, body}}.
        #
        # They were one template each, newest capture wins. That was right while one
        # emulator could be attached and is wrong the moment six can: a
        # CreatePurchaseContract body carries the cartId of the cart that made it, so a
        # template captured on account 3 mints contracts on account 3's cart no matter
        # which account you thought you were generating for. Newest-wins made that
        # silent — the last account you touched would quietly become the target of
        # everything. Keyed by instance, a generated call belongs to a cart by
        # construction, and an account with no capture of its own is told so rather
        # than borrowing someone else's.
        self.placeorder_templates = self._load_templates(TEMPLATE_PATH)
        self.checkout_templates = self._load_templates(CHECKOUT_TEMPLATE_PATH)
        self.latest_contract_id = ""
        # Every contractId Walmart returned from CreatePurchaseContract this session:
        # [{id, ts, source ('observed'|'sent'), inst}], newest first.
        self.contract_ids = []
        self.delay_entry = {}      # stage -> Entry: ms to wait between consecutive live sends
        # Host-side only — see CHAIN_MODES. Starts manual: the tool does not begin
        # reacting to captured checkouts because it was launched.
        self.chain_mode = "manual"
        # The chain run in flight, or None. Carries the contract ids that existed
        # BEFORE the mint, so the ids the mint actually returned can be told from the
        # ones already in the list — the box is not cleared between runs, and
        # converting the lot would build orders for contracts from an earlier run.
        self._chain = None
        # A trigger that arrived while a batch dispatched BY HAND was in flight, held
        # until that batch lands. Without it a capture during a manual mint would
        # start a chain on top of it, and the manual batch's `sendbatchdone` would
        # then finish the chain early — converting whatever had been minted so far.
        self._chain_pending = None
        # Whether any batch is on the wire. _set_send_enabled already knows; the chain
        # needs to ask, and asking a Button's state for it would tie this to the UI.
        self._batch_busy = False
        self.q = queue.Queue()

        self._build_ui()
        # The panel still drains its OWN queue (see the cart panel). Only detect()
        # moved: the Session owns the instance list.
        self.root.after(300, self._pump)

    # ---------- ui ----------
    def _build_ui(self):


        # The two per-op mode rows are NOT built here. Every mode in the tool now lives
        # in one Mode panel, in the Cart section — see build_modes(), which app.py calls
        # with that panel as the parent once both halves exist. Having the switch that
        # decides whether a PlaceOrder reaches Walmart sitting in a section you might
        # have collapsed was the thing worth fixing.
        self.mode_combo, self.mode_badge, self.mode_desc = {}, {}, {}


        # mid — two panes: checkout (prep) calls | place order (commit) calls. Each pane
        # has ONE box carrying both dispositions, told apart by tag and colour.
        # Clicking any row prints its full request into the log.
        mid = ttk.Frame(self.root, padding=6); mid.pack(fill="both", expand=True)

        left = ttk.LabelFrame(
            mid, text="Checkout calls — CreatePurchaseContract (prices & locks the cart)",
            padding=6)
        left.pack(side="left", fill="both", expand=True, padx=(0, 4))
        self.prep_list = self._pane_box(
            left, "● observed = reached Walmart    ⛔ BLOCKED = stopped on-device    "
                  "(a mint's own calls are counted beside the button, not listed here)",
            "prep_calls")
        # Mint contract IDs without pressing Continue to checkout: generate N checkout
        # calls AND send them, spaced by the mint delay, on the accounts that have
        # actually captured a checkout call in this list.
        #
        # There is ONE button here now. "Generate checkout call" (build the rows,
        # send them later with the pane's own ▶ Send (LIVE)) and that Send button are
        # both gone: two steps for one action, where step one silently built rows for
        # accounts that had never captured a checkout call of their own. Generating
        # and sending together is the only way the account list can be decided from
        # what is actually in the box at the moment you click.
        cgen = ttk.Frame(left); cgen.pack(fill="x", pady=(2, 0))
        self.mint_btn = ttk.Button(cgen, text="Generate & Send ×N (mint)",
                                   command=self.generate_and_send_checkout)
        self.mint_btn.pack(side="left")
        ttk.Label(cgen, text="×").pack(side="left", padx=(6, 1))
        self.checkout_count = ttk.Entry(cgen, width=4)
        self.checkout_count.insert(0, "6")
        self.checkout_count.pack(side="left")
        ttk.Label(cgen, text="delay ms:").pack(side="left", padx=(6, 2))
        self.delay_entry["mint"] = ttk.Entry(cgen, width=6)
        self.delay_entry["mint"].insert(0, self.DEFAULT_DELAY_MS)
        self.delay_entry["mint"].pack(side="left")
        # Which accounts the next mint would run on, kept up to date as calls land in
        # the box. The count is the whole point of the change: a mint acts on the
        # accounts that captured a checkout call, not on everything attached.
        self.mint_targets_lbl = ttk.Label(cgen, text="", foreground="#555")
        self.mint_targets_lbl.pack(side="left", padx=(8, 0))
        pbtn = ttk.Frame(left); pbtn.pack(fill="x", pady=(4, 0))
        ttk.Button(pbtn, text="Export", command=lambda: self._export("prep")).pack(side="left")
        ttk.Button(pbtn, text="Clear", command=lambda: self._clear_calls("prep")).pack(side="left", padx=4)

        right = ttk.LabelFrame(
            mid, text="Place order calls — PlaceOrder (places the order)",
            padding=6)
        right.pack(side="left", fill="both", expand=True, padx=(4, 0))
        self.commit_list = self._pane_box(
            right, "● observed = ORDER PLACED    ⛔ BLOCKED = stopped on-device    "
                   "✎ generated = built here, not sent", "commit_calls")
        # Generate a PlaceOrder from the saved template + a contractId, without navigating
        # to the app's place-order screen. The new row lands in the box above, tagged generated.
        gen = ttk.Frame(right); gen.pack(fill="x", pady=(2, 0))
        ttk.Label(gen, text="contractId:").pack(side="left")
        self.contract_entry = ttk.Entry(gen, width=30)
        self.contract_entry.pack(side="left", padx=4)
        ttk.Button(gen, text="Generate PlaceOrder",
                   command=self.generate_placeorder).pack(side="left")
        cbtn = ttk.Frame(right); cbtn.pack(fill="x", pady=(4, 0))
        ttk.Button(cbtn, text="Export", command=lambda: self._export("commit")).pack(side="left")
        ttk.Button(cbtn, text="Clear", command=lambda: self._clear_calls("commit")).pack(side="left", padx=4)
        # Live send: replay EVERY PlaceOrder row in this pane through the app's own client.
        self.send_btn_commit = ttk.Button(cbtn, text="▶ Send all (LIVE)",
                                          command=lambda: self.send_pane("commit"))
        self.send_btn_commit.pack(side="right")
        self.delay_entry["commit"] = self._delay_field(cbtn)
        # What the chain left behind: N orders built and selected, none of them sent.
        # It reads "NOT sent" out loud because the pane looks the same either way — a
        # selection of generated rows is what you have before sending and what you
        # have after a chain, and the difference is the whole point.
        self.chain_lbl = ttk.Label(cbtn, text="", foreground="#555")
        self.chain_lbl.pack(side="left", padx=(8, 0))

        # Contract IDs — every contractId Walmart returned from CreatePurchaseContract.
        # Click one to load it into the Generate contractId field.
        cidbar = ttk.LabelFrame(self.root,
                                text="Contract IDs — received from CreatePurchaseContract "
                                     "(click one to use it for Generate PlaceOrder)", padding=6)
        cidbar.pack(fill="x", padx=6, pady=(0, 4))
        self.cid_list = tk.Listbox(cidbar, height=4, font=("Consolas", 9), selectmode="extended")
        self.cid_list.pack(side="left", fill="both", expand=True)
        self.cid_list.bind("<<ListboxSelect>>", lambda e: self._use_selected_contract())
        cidbtns = ttk.Frame(cidbar); cidbtns.pack(side="left", fill="y", padx=(6, 0))
        ttk.Button(cidbtns, text="→ PlaceOrder calls",
                   command=self.convert_contracts_to_placeorders).pack(fill="x")
        ttk.Button(cidbtns, text="Use for PlaceOrder", command=self._use_selected_contract).pack(fill="x", pady=2)
        ttk.Button(cidbtns, text="Copy", command=self._copy_selected_contract).pack(fill="x")
        ttk.Button(cidbtns, text="Clear", command=self._clear_contracts).pack(fill="x", pady=(2, 0))


        self._refresh_instances()

    def _pane_box(self, parent, title, attr):
        """A labelled listbox inside a pane; registers it against its data list.
        Multi-select (extended) so a Send can dispatch several rows at once."""
        ttk.Label(parent, text=title, foreground="gray").pack(anchor="w")
        lst = tk.Listbox(parent, height=5, font=("Consolas", 9), selectmode="extended")
        lst.pack(fill="both", expand=True, pady=(0, 4))
        lst.bind("<<ListboxSelect>>", lambda e, w=lst: self._show_detail(w))
        self.box_data[lst] = attr
        return lst

    DEFAULT_DELAY_MS = "1000"  # default gap between consecutive live sends / mints

    def _delay_field(self, parent):
        """A small 'delay ms:' entry packed to the left of a right-packed Send button."""
        e = ttk.Entry(parent, width=6)
        e.insert(0, self.DEFAULT_DELAY_MS)
        e.pack(side="right", padx=(0, 4))
        ttk.Label(parent, text="delay ms:").pack(side="right")
        return e

    def _ui(self, fn):
        """Run `fn` on the UI thread, from anywhere.

        Tk must only be touched from the thread that owns it — the same rule
        `_send_batch_worker` follows. Calling `root.after` from a worker does not merely
        risk a race: with no mainloop servicing it, Tcl parks the calling thread inside
        createcommand, and a worker holding a lock while parked there wedges every other
        worker behind it. So off-thread work goes through the queue `_pump` already
        drains on the main thread; only a call that is already on the UI thread runs
        inline.
        """
        if threading.current_thread() is threading.main_thread():
            try:
                fn()
            except Exception:
                pass
            return
        self.q.put({"type": "uicall", "fn": fn})





    # ---------- mode ----------
    def build_modes(self, parent):
        """Build this half's two mode selectors as columns of the shared Mode panel.

        Called by app.py with the Cart section's Mode column strip, so all three modes
        (Add to cart, Checkout, Place order) sit side by side as the peers they are.
        Kept as a method rather than done in _build_ui because the parent belongs to
        the other panel and does not exist until both have been constructed.

        No group heading: with the columns side by side, each one's own title already
        says which operation it governs, and a banner over two of the three implied a
        grouping that isn't there — all three are independent.
        """
        self._build_mode_row(parent, "prep", "Checkout")
        self._build_mode_row(parent, "commit", "Place order")
        # Fourth column, and the only one that governs the tool rather than the agent.
        # It sits with the others because it answers the same question they do — "what
        # happens when a checkout call goes past?" — and because the demo it exists for
        # is flipping it while the other three stay put.
        self._build_chain_row(parent)

    def _build_chain_row(self, parent):
        """The chain selector, as the last column of the shared Mode panel.

        Deliberately not folded into _build_mode_row: that one writes into
        mode_combo/mode_badge/mode_desc keyed by stage and its combo handler
        broadcasts to the agent. This one broadcasts nothing, so sharing the widget
        code would mean sharing a handler that has to ask which kind it is — and the
        thing worth being able to see at a glance here is that no path from this
        column reaches an emulator.
        """
        m = self.chain_mode
        row = mode_column(parent, "Checkout chain", pad=(0, 14))
        combo = ttk.Combobox(row, state="readonly", width=28,
                             values=[self.CHAIN_MODES[k][0] for k in self.CHAIN_CHOICES])
        combo.set(self.CHAIN_MODES[m][0])
        combo.pack(side="left")
        combo.bind("<<ComboboxSelected>>", lambda e: self._apply_chain_mode())
        badge = ttk.Label(row, text="●", foreground=self.CHAIN_COLOUR[m])
        badge.pack(side="left", padx=(6, 0))
        # Where the op name sits in the other columns. This column has no single op —
        # it spans both — so it says what it does to them instead.
        ttk.Label(row.master, text="this tool, after capture — not the agent",
                  foreground="#6b6b6b", font=("Consolas", 8)).pack(anchor="w")
        desc = ttk.Label(row.master, text=self.CHAIN_MODES[m][1], foreground="gray",
                         wraplength=280, justify="left")
        desc.pack(fill="x", anchor="w")
        self.chain_combo, self.chain_badge, self.chain_desc = combo, badge, desc

    def _apply_chain_mode(self):
        """Switch the chain on or off. Nothing is sent, and no emulator is touched."""
        mode = next((k for k in self.CHAIN_CHOICES
                     if self.CHAIN_MODES[k][0] == self.chain_combo.get()), "manual")
        self.chain_mode = mode
        title, desc = self.CHAIN_MODES[mode]
        self.chain_desc.config(text=desc)
        self.chain_badge.config(foreground=self.CHAIN_COLOUR[mode])
        if mode == "armed":
            n = self._chain_count()
            self.log(f"⛓ Checkout chain: {title}. The next checkout call captured on an "
                     f"account that has one will mint ×{n} on every qualifying account, "
                     f"convert the new ids and select the orders. Nothing is sent by it "
                     f"— ▶ Send (LIVE) is still yours.")
            if self.mode_state["prep"] == "idle":
                self.log("   ⚠ Checkout is on Idle, so no checkout call is captured and "
                         "the chain will never fire. Set it to Watch or Intercept.")
        else:
            # A chain mid-flight is left to finish: its mint is already on the wire and
            # pretending otherwise would leave contract ids minted and unconverted.
            self.log(f"⛓ Checkout chain: {title}."
                     + (" The run already in flight finishes; no new one starts."
                        if self._chain is not None else ""))

    # Which GraphQL operation each column governs. The column title is the short name;
    # the operation goes underneath, because that is the thing being pointed at during
    # a walkthrough and it should not be hidden in a tooltip.
    OP_NAME = {"prep": "CreatePurchaseContract", "commit": "PlaceOrder"}

    def _build_mode_row(self, parent, stage, label):
        """One per-op mode selector, as a column of the shared Mode panel."""
        m = self.mode_state[stage]
        row = mode_column(parent, label, pad=(0, 14))
        combo = ttk.Combobox(row, state="readonly", width=28,
                             values=[self.MODES[k][0] for k in self.MODE_CHOICES])
        combo.set(self.MODES[m][0])
        combo.pack(side="left")
        combo.bind("<<ComboboxSelected>>", lambda e, s=stage: self._apply_mode(s))
        badge = ttk.Label(row, text="●", foreground=self.MODE_COLOUR[m])
        badge.pack(side="left", padx=(6, 0))
        ttk.Label(row.master, text=self.OP_NAME[stage], foreground="#6b6b6b",
                  font=("Consolas", 8)).pack(anchor="w")
        desc = ttk.Label(row.master, text=self.MODES[m][1], foreground="gray",
                         wraplength=280, justify="left")
        desc.pack(fill="x", anchor="w")
        self.mode_combo[stage] = combo
        self.mode_badge[stage] = badge
        self.mode_desc[stage] = desc

    def _apply_mode(self, stage):
        mode = next((k for k in self.MODE_CHOICES
                     if self.MODES[k][0] == self.mode_combo[stage].get()), "watch")
        self.mode_state[stage] = mode
        title, desc = self.MODES[mode]
        self.mode_desc[stage].config(text=desc)
        self.mode_badge[stage].config(foreground=self.MODE_COLOUR[mode])
        which = "Checkout" if stage == "prep" else "Place order"
        hit = self.broadcast("setcheckoutmode", stage, mode)
        if not hit:
            self.log(f"{which} mode set to {title} — 0 instances connected, applies on Connect.")
        else:
            self.log(f"{which} mode: {title} on {len(hit)} instance(s).")

    def _apply_state(self, inst):
        """Push both per-op modes + the response-capture setting onto one instance's agent."""
        try:
            inst.script.exports_sync.setcheckoutmode("prep", self.mode_state["prep"])
            inst.script.exports_sync.setcheckoutmode("commit", self.mode_state["commit"])
            inst.script.exports_sync.setcaptureresponses(True)
        except Exception as e:
            self._ui(lambda e=e, inst=inst: self.log(f"[{inst.name}] couldn't apply mode: {e}"))

    # ---------- fan-out helpers ----------
    def active(self):
        return [i for i in self.instances if i.connected and i.enabled]

    def broadcast(self, method, *args):
        hit = []
        for inst in self.active():
            try:
                getattr(inst.script.exports_sync, method)(*args)
                hit.append(inst)
            except Exception as e:
                self.log(f"[{inst.name}] {method} failed: {e}")
        return hit






    # ---------- checkout calls ----------
    # Each pane (prep/commit) has one box, <stage>_calls, holding both dispositions.
    # box_data maps each listbox widget to its list attribute name.
    def _find_call_by_cid(self, cid):
        """The captured call carrying this correlation id, across all four boxes."""
        if cid is None:
            return None
        for attr in ("prep_calls", "commit_calls"):
            for c in getattr(self, attr):
                if c.get("cid") == cid:
                    return c
        return None

    # Observed and intercepted share a box now, so the disposition has to be legible
    # from the row itself — at a glance, from across a room. Three things carry it:
    # the symbol, the word, and the colour.
    #   ● observed   green   it reached Walmart (a PlaceOrder here PLACED THE ORDER)
    #   ⛔ BLOCKED   red     stopped on-device; nothing reached Walmart
    #   ✎ generated  amber   built from a template here, never sent
    DISPOSITION = {
        "observed":  ("● observed",  "#0a7d00"),
        "blocked":   ("⛔ BLOCKED",   "#b30000"),
        "generated": ("✎ generated", "#9a6b00"),
    }
    # A send Walmart refused. Same red as BLOCKED, deliberately: both mean "this call
    # did nothing", and the row already says which kind of nothing it was.
    REFUSED_COLOUR = "#b30000"

    @staticmethod
    def _disposition(c):
        if c.get("generated"):
            return "generated"
        return "blocked" if c.get("intercepted") else "observed"

    @staticmethod
    def _sent_tag(call, sn):
        """What the row says about a live send — Walmart's answer, not the wire's.

        This slot used to read `sent HTTP 200` and nothing else, which was true and
        useless: a refused checkout and a placed order are both HTTP 200, and across
        three runs the box showed 22 green rows for 12 orders. The HTTP code only ever
        earns the slot when there is nothing better to put in it.

            ⛔ ITEM_POLICY_VIOLATION      Walmart refused it; no order, no contract
            ⛔ PAYMENT_SERVICE_AUTHORIZATION_DECLINE
                                          the card was declined — same slot, because a
                                          decline is a refusal and not an HTTP result
            sent ✓ order 600000108897103  status SEND_TO_OMS — this one is real
            sent ⚠ CREATED (no order)     no refusal named, and still not handed to OMS
            sent HTTP 200                 a checkout call, or a body we could not read

        `sent HTTP 200` is now the row of last resort it was always meant to be: it says
        we could not read the body, and nothing else claims that slot.
        """
        if sn.get("errors"):
            return refusal_label(sn["errors"])
        if sn.get("placed"):
            return f"sent ✓ order {sn.get('order_id')}"
        if call.get("stage") == "commit" and sn.get("order_status"):
            return f"sent ⚠ {sn['order_status']} (no order)"
        return f"sent HTTP {sn.get('code')}"

    # A generated CreatePurchaseContract is not shown. A mint of 5 on 6 accounts is 30
    # rows the tool built itself, arriving at once and pushing the calls the APP made —
    # the ones that are actually evidence, and the ones that decide who a mint runs on —
    # off the top of the box. They are still kept (a send result has to land back on its
    # row), just not listed: the mint reports itself through the pending count beside its
    # button, the log, and the Contract IDs it produces, which is its actual output.
    #
    # Generated PLACE ORDER rows are different and stay listed: you select one and press
    # Send (LIVE), so it has to be there to select.
    def _hidden_row(self, attr, c):
        return attr == "prep_calls" and bool(c.get("generated"))

    def _refresh_calls(self):
        """Redraw both call boxes — one flat newest-first column each, every row
        naming its own emulator right of the time.

        The rows used to be grouped into a block per emulator under a `[name]` rule.
        That answered "which account" with a heading rather than with the row, so the
        newest call in the box was not the top line — it was the top line of whichever
        block its emulator sat in, and the sequence you were watching restarted once
        per account. Flat and time-ordered, the box reads as the run it is, and the
        [instance] tag right of the time says whose each call was.

        A list line is still not a call: `self.box_rows[lst]` maps line -> index into
        that box's data list. Selection is restored by identity rather than by line
        number, because a row arriving mid-list shifts every line under it.
        """
        for lst, attr in self.box_data.items():
            data = getattr(self, attr)
            picked = {id(c) for c in self._calls_in_box(lst)}
            lst.delete(0, "end")
            rows = []
            for n, c in enumerate(data):
                if self._hidden_row(attr, c):
                    continue        # kept in `data`, never given a line — see above
                t = time.strftime("%H:%M:%S", time.localtime(c["ts"] / 1000.0))
                label, colour = self.DISPOSITION[self._disposition(c)]
                tag = label
                r = c.get("response")
                if r:
                    tag += f"  ⇠ resp HTTP {r.get('code')}"
                sn = c.get("sent")
                if sn:
                    tag += "  ▶ " + self._sent_tag(c, sn)
                    # A refusal owns the row's colour too. `✎ generated` amber said
                    # "built here, never sent", which stops being true the moment it is
                    # sent — and green on a call that placed no order is the exact
                    # failure this whole path exists to stop reporting.
                    # `order_status` is required on the second arm: a body we could
                    # not parse tells us nothing, and unknown is not the same as refused.
                    if sn.get("errors") or (c.get("stage") == "commit"
                                            and sn.get("order_status")
                                            and not sn.get("placed")):
                        colour = self.REFUSED_COLOUR
                lst.insert("end", f"  {t}  [{c['inst'][:12]}]  {tag}")
                # Per-row colour: the one cue that survives not reading the text.
                lst.itemconfig(lst.size() - 1, foreground=colour)
                rows.append(n)
            self.box_rows[lst] = rows
            for line, n in enumerate(rows):
                if n is not None and id(data[n]) in picked:
                    lst.selection_set(line)
        # The mint reads this same box for who it would run on, so the note beside its
        # button is redrawn with the box rather than on a timer.
        self._refresh_mint_targets()

    def _calls_in_box(self, lst):
        """The calls currently selected in one box, by row rather than by line."""
        data = getattr(self, self.box_data.get(lst, ""), [])
        rows = self.box_rows.get(lst) or []
        out = []
        for line in lst.curselection():
            if line < len(rows) and rows[line] is not None and rows[line] < len(data):
                out.append(data[rows[line]])
        return out

    def _show_detail(self, lst):
        picked = self._calls_in_box(lst)
        if not picked:
            return
        c = picked[0]
        pretty, h = pretty_body(c.get("body"))
        if c.get("generated"):
            disp = "generated from template — not sent yet (Send to place it)"
        elif c.get("intercepted"):
            disp = "BLOCKED on-device — nothing reached Walmart"
        else:
            disp = "observed — reached Walmart"
        lines = [
            "─" * 64,
            f"{c['op']}  [{c['inst']}]",
            f"disposition: {disp}",
            f"mode      : {c.get('mode', '?')}",
            f"time      : {time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(c['ts']/1000.0))}",
            f"url       : {c.get('url') or '(none)'}",
            f"pq sha256 : {h or '(none)'}",
            "headers:",
        ]
        for k, v in (c.get("headers") or []):
            lines.append(f"  {k}: {v}")
        lines += ["body:", pretty]

        # response — present for a call that reached Walmart and came back (any op in Watch
        # mode). Blocked calls never have one.
        r = c.get("response")
        if r:
            rpretty, _ = pretty_body(r.get("body"))
            contract = extract_contract_id(r.get("body"))
            lines += ["", "response:",
                      f"  http status: {r.get('code')}",
                      f"  time       : {time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(r['ts']/1000.0))}"]
            if contract:
                lines.append(f"  contractId : {contract}")
            lines += ["  body:", rpretty]
        elif c.get("generated"):
            lines += ["", "response: (none yet — generated call, not sent. A PlaceOrder "
                          "goes out with ▶ Send (LIVE); a checkout call is generated and "
                          "sent together by Generate & Send ×N.)"]
        elif c.get("intercepted"):
            lines += ["", "response: (none — blocked on-device in Intercept mode, nothing reached Walmart)"]
        else:
            lines += ["", "response: (not captured — still in flight, or response capture off/unavailable)"]

        # sent — the result of a LIVE dispatch of THIS captured call via the app's client.
        s = c.get("sent")
        if s:
            spretty, _ = pretty_body(s.get("body"))
            errs = s.get("errors") or []
            if errs:
                verdict = "REFUSED BY WALMART"
            elif s.get("accepted"):
                verdict = "ACCEPTED"
            else:
                verdict = "graphql errors" if s.get("gqlErrors") else "rejected"
            contract = extract_contract_id(s.get("body"))
            lines += ["", "sent (LIVE dispatch — replayed through the app):",
                      f"  http status: {s.get('code')}  [{verdict}]",
                      f"  url        : {s.get('url')}",
                      f"  rtt        : {s.get('rtt')} ms",
                      f"  time       : {time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(s['ts']/1000.0))}"]
            if errs:
                # The point of the whole block. The HTTP status above it says nothing —
                # these lines are Walmart's actual answer, in Walmart's own words.
                lines.append("  refused    : HTTP 200 above means nothing here — "
                             "Walmart refused this in the body:")
                for code, msg in errs:
                    lines.append(f"    ⛔ {code}" + (f" — {msg}" if msg else ""))
            if c.get("stage") == "commit":
                if s.get("placed"):
                    lines.append(f"  ORDER      : PLACED — id {s.get('order_id')} "
                                 f"(status {s.get('order_status')})")
                elif s.get("order_status"):
                    # An order id comes back on a refusal too. Saying so here is the
                    # difference between reading this pane and misreading it.
                    lines.append(f"  ORDER      : NOT PLACED — status "
                                 f"{s.get('order_status')}, not {ORDER_PLACED_STATUS}. "
                                 f"Order id {s.get('order_id')} is a record, not an order.")
            if contract:
                lines.append(f"  contractId : {contract}")
            lines += ["  body:", spretty]

        lines.append("─" * 64)
        for ln in lines:
            self.log(ln)

    # ---------- live send ----------
    def _selected_calls_in_pane(self, kind):
        """Every call selected in this pane's box (one box now, both dispositions)."""
        lst = self.prep_list if kind == "prep" else self.commit_list
        return self._calls_in_box(lst)

    def _all_calls_in_pane(self, kind):
        """Every call in this pane's box, selected or not — newest first, as shown."""
        attr = "prep_calls" if kind == "prep" else "commit_calls"
        return list(getattr(self, attr, []))

    def _delay_ms(self, kind):
        """This pane's ROW delay: the gap between consecutive calls of ONE account."""
        try:
            return max(0, int(float(self.delay_entry[kind].get().strip() or 0)))
        except Exception:
            return 0

    def _emu_delay_ms(self):
        """The gap between one emulator's first call and the next emulator's.

        One setting for the whole tool (Settings -> emulator_delay_ms, and the box
        beside the row delay in the Cart section), because it describes the fan-out
        rather than a send path — the cart half staggers its instances by the same
        number, so a walkthrough has one dial for "how far apart are the accounts"
        instead of one per box.
        """
        try:
            return max(0, int(float(self.cfg.get("emulator_delay_ms", 0) or 0)))
        except Exception:
            return 0

    # Captured calls kept PER EMULATOR. A flat cap shared between six accounts lets
    # the busiest evict the quietest, and the quiet account is usually the one whose
    # call you are looking for.
    CALLS_PER_INSTANCE = 100

    def _trim_calls(self, attr):
        """Cap the box per emulator — and, within an emulator, cap what the APP made
        apart from what this tool generated.

        One quota for both would let a mint evict the very capture that qualifies its
        account: 100 generated rows push the account's one real CreatePurchaseContract
        out of the list, `_captured_keys` stops seeing it, and the next mint skips the
        account for having nothing of its own. Two quotas, so a mint can never cost an
        account its evidence.
        """
        kept, seen = [], {}
        for c in getattr(self, attr):
            k = (c.get("inst_key") or c.get("inst") or "?", bool(c.get("generated")))
            seen[k] = seen.get(k, 0) + 1
            if seen[k] <= self.CALLS_PER_INSTANCE:
                kept.append(c)
        setattr(self, attr, kept)

    def _set_send_enabled(self, on):
        """Grey the buttons that dispatch while a batch is in flight.

        The checkout pane has no Send button any more — its one dispatch is
        Generate & Send, which is disabled the same way.
        """
        self._batch_busy = not on
        st = "normal" if on else "disabled"
        for b in (getattr(self, "mint_btn", None), getattr(self, "send_btn_commit", None)):
            if b is not None:
                b.config(state=st)

    def send_pane(self, kind):
        """Replay every call in this pane's box through the app's own OkHttpClient, with
        the pane's delay(ms) between consecutive sends. No extra confirmation, by request —
        every PlaceOrder in the box goes out, one order committed per row."""
        calls = [c for c in self._all_calls_in_pane(kind) if c.get("body")]
        if not calls:
            which = "checkout (CreatePurchaseContract)" if kind == "prep" \
                else "place order (PlaceOrder)"
            messagebox.showinfo("No calls to send",
                                f"There are no {which} calls in this pane. "
                                f"Generate one first, then Send.")
            return
        if next(iter(self.active()), None) is None:
            messagebox.showerror("Not connected",
                                 "No connected instance to send through — Connect first.")
            return
        delay = self._delay_ms(kind)
        emu = self._emu_delay_ms()
        n = len(calls)
        accounts = len({c.get("inst_key") for c in calls})
        if kind == "commit":
            # These are the armed orders (or a selection the user made instead) going
            # out now, so the "armed, NOT sent" note has stopped being true.
            self._chain_status("")
        self._set_send_enabled(False)
        sendlog.note_once(self.log)
        self.log(f"▶ live-sending {n} {'call' if n == 1 else 'calls'} across "
                 f"{accounts} account(s)"
                 + (f", {delay} ms between one account's calls" if delay else "")
                 + (f", accounts {emu} ms apart" if emu else "") + " …")
        threading.Thread(target=self._send_batch_worker, args=(calls, delay), daemon=True).start()

    def _send_batch_worker(self, calls, delay):
        """Dispatch a batch, one worker per account, on the two independent delays.

        It used to be a single loop over every selected call, sleeping `delay` before
        each one. With six accounts attached that loop is wrong twice over: it
        serialises accounts that have no reason to wait for each other (six mints of
        five calls at 1 s each took 30 s, not 5), and the one delay had to stand for
        both "space this account's calls" and "stagger the accounts", which are
        different numbers with different jobs.

        So the batch is split by account and each gets its own thread:

        * `delay` — the pane's **row delay** — is slept before each of ONE account's
          calls, exactly as before, and now genuinely only affects that account;
        * the **emulator delay** is slept once, up front, scaled by the account's
          position in the picker: account n starts n x emulator delay after the first.

        Runs on worker threads: they do the blocking RPC only, and hand results back
        through self.q, which _pump drains on the main thread — tkinter is not
        thread-safe, so no widget call is made from here.
        """
        order = [i.key for i in self.instances]

        def rank(key):
            try:
                return order.index(key)
            except ValueError:
                return len(order)

        groups = {}
        for c in calls:
            groups.setdefault(c.get("inst_key"), []).append(c)
        # Picker order, so the stagger follows the checkboxes on screen. Positions are
        # taken over the accounts ACTUALLY in this batch, so a batch of accounts 4 and
        # 6 starts them one emulator delay apart, not two.
        keys = sorted(groups, key=lambda k: (rank(k), str(k)))
        emu = self._emu_delay_ms()

        def one(key, n):
            if emu and n:
                time.sleep(n * emu / 1000.0)
            for row_n, c in enumerate(groups[key]):
                if delay:                        # before EVERY call of this account
                    time.sleep(delay / 1000.0)
                # This send's own share of the two delays, banked at the moment they
                # are actually applied rather than re-read from the boxes when the
                # reply lands — by then the run may have been retuned. Row n of this
                # account waited (n+1) x delay: the sleep is before EVERY call,
                # including the first, so the first row is one delay behind too.
                c["_delays"] = sendlog.delays(
                    emulator_instance_ms=n * emu, row_ms=(row_n + 1) * delay,
                    path="checkout pane — manual dispatch (unscheduled: no nudge, no lead)",
                    settings={"row_delay_ms": delay, "emulator_delay_ms": emu,
                              "account_position": n, "row_position": row_n})
                inst = next((x for x in self.instances
                             if x.key == key and x.connected), None)
                if inst is None:
                    # A captured call goes out on the account that made it and on no
                    # other — with six attached, redirecting one would run this
                    # account's checkout (or place its order) against another
                    # account's cart. A row whose account is not connected, and a row
                    # that names none at all (intercepted before rows were tagged),
                    # are both reported unsent rather than sent somewhere else.
                    self.q.put({"type": "sendlog",
                                "msg": (f"✗ {c.get('op')} not sent — it names no "
                                        f"account, and a captured call is only ever "
                                        f"sent on the one that made it."
                                        if key is None else
                                        f"✗ {c.get('op')} not sent — "
                                        f"{c.get('inst')} is not connected.")})
                    continue
                tmpl = {"url": c.get("url"), "headers": c.get("headers") or [],
                        "body": c.get("body")}
                # Both instants are taken HERE, around the blocking RPC, not when the
                # result is drained on the UI thread: _pump runs on a 300 ms timer, so
                # a receipt time read there would be quantised by the poll and a burst
                # of replies would all read as one instant.
                c["_sent_ms"] = time.time() * 1000.0
                try:
                    res = inst.script.exports_sync.sendcall(tmpl)
                except Exception as e:
                    res = {"ok": False, "error": str(e)}
                c["_recv_ms"] = time.time() * 1000.0
                self.q.put({"type": "sendresult", "call": c, "res": res})

        threads = [threading.Thread(target=one, args=(k, n), daemon=True)
                   for n, k in enumerate(keys)]
        for t in threads:
            t.start()
        for t in threads:
            t.join()
        self.q.put({"type": "sendbatchdone"})

    def _send_done(self, c, res):
        """Record and report ONE live send, on Walmart's verdict rather than the wire's.

        The agent can only answer "did this request come back 2xx with no GraphQL
        `errors` array", and for a refused checkout the answer is yes — Walmart refuses
        inside the body. So the reply is re-read here (`checkout_result`) and the
        transport's verdict is downgraded when either refusal shape is populated:
        `checkoutError` under the op, or a top-level `errors` array (a card decline). The
        second answers 2xx-with-errors, which the agent scores rejected but cannot name.
        The wire's
        own answer is kept as `http_accepted`, because "HTTP 200 but refused" is a
        different thing from "HTTP 500" and the detail view has to be able to say which.
        """
        if not res.get("ok"):
            # Written even though nothing came back: the file is a list of what this
            # run PUT ON THE WIRE, and a request that failed in transport is part of
            # that list — leaving it out would make the log read as if fewer went out.
            self._write_send_record(c, res)
            self.log(f"✗ live send failed ({c.get('op')}): {res.get('error')}")
            return
        out = checkout_result(res.get("detail"))
        errors = out["errors"]
        # An order is placed only when Walmart says SEND_TO_OMS. A CreatePurchaseContract
        # has no order to place, and its `order.status` sits at CREATED by design, so
        # `placed` is asked of the commit stage only — never of a checkout call.
        placed = (c.get("stage") == "commit" and not errors
                  and out["status"] == ORDER_PLACED_STATUS)
        c["sent"] = {"code": res.get("code"), "body": res.get("detail"),
                     "accepted": bool(res.get("accepted")) and not errors,
                     "http_accepted": bool(res.get("accepted")),
                     "gqlErrors": bool(res.get("gqlErrors")),
                     "errors": errors, "order_status": out["status"],
                     "order_id": out["order_id"], "placed": placed,
                     "url": res.get("url"), "rtt": res.get("rtt"),
                     "ts": int(time.time() * 1000)}
        # On receipt, before anything is reported to the screen: the box trims itself
        # and the log pane scrolls, so the file is the only record that outlives the
        # run. Written here rather than at dispatch because the reply is half of it.
        self._write_send_record(c, res, errors=errors, out=out, placed=placed)
        self._refresh_calls()
        if errors:
            verdict = errors[0][0].upper()
        elif res.get("accepted"):
            verdict = "ACCEPTED"
        else:
            verdict = "graphql errors" if res.get("gqlErrors") else "rejected"
        self.log(f"◀ live send {c.get('op')} → HTTP {res.get('code')} [{verdict}] "
                 f"({len(res.get('detail') or '')}B, {res.get('rtt')}ms)")
        for code, msg in errors:
            # Walmart's own words. "Limit of  items per customer." is what a per-customer
            # purchase cap looks like from here, and it is the whole reason a run of ten
            # places six — so it goes in the log verbatim, not summarised.
            self.log(f"   ⛔ {code}" + (f" — {msg}" if msg else ""))
        if c.get("stage") == "commit":
            if placed:
                self.log(f"   ✓ ORDER PLACED — id {out['order_id']} (status {out['status']}).")
            else:
                # An order id comes back either way, so the id is not the evidence —
                # the status is. Say so on the row's own line rather than leaving a
                # reader to infer it from an id that looks exactly like a real one.
                self.log(f"   ⚠ NO ORDER — status {out['status']}, not "
                         f"{ORDER_PLACED_STATUS}. The order id ({out['order_id']}) is a "
                         f"record, not a placed order.")
        cid_ = extract_contract_id(res.get("detail"))
        if cid_:
            self.log(f"   contractId: {cid_}")
            if c.get("stage") == "prep":
                self._record_contract_id(cid_, "sent", c.get("inst"),
                                         c.get("inst_key"))
        elif c.get("stage") == "prep":
            # A checkout send with no id: either it was refused, or it was rejected, or
            # the response names the contract id in a field we don't recognize yet. Say
            # which, and point to the body.
            if errors:
                self.log("   ⚠ no contractId — the checkout was REFUSED by Walmart "
                         "(see above). Nothing was locked.")
            elif not res.get("accepted"):
                self.log("   ⚠ no contractId — the checkout send was NOT accepted "
                         "(rejected/errors). Click the row to see why.")
            else:
                self.log("   ⚠ accepted, but no contractId field recognized in the response. "
                         "Click the row and paste the response body so the field can be added.")
        self.log("   (click the row to see the full sent response)")

    def _write_send_record(self, c, res, errors=(), out=None, placed=False):
        """Append one dispatched checkout/place-order call to the sent-request log.

        Everything the detail view can show goes in, plus the two things it cannot:
        the delay breakdown this send actually went out on (banked per call in
        _send_batch_worker) and the instants either side of the RPC. The reply is kept
        verbatim under `response.raw` as well as parsed, because a body summarised at
        write time cannot be re-read for a field nobody thought to pull out yet.

        Never raises: a send is not worth failing over its own bookkeeping.
        """
        try:
            out = out or {}
            inst = next((x for x in self.instances if x.key == c.get("inst_key")), None)
            sendlog.record(
                tool="checkout", op=c.get("op"), stage=c.get("stage"),
                instance=inst if inst is not None else (c.get("inst") or "?"),
                item=c.get("contract_id"), quantity=None,
                sent_at_ms=c.get("_sent_ms"), received_at_ms=c.get("_recv_ms"),
                # Host-clock instants around the blocking RPC — this pane has no
                # device-measured wire time, so the record says so rather than
                # implying the precision the timed cart path has.
                sent_measured=False,
                delay=c.get("_delays") or sendlog.delays(path="checkout pane"),
                request={"url": c.get("url"), "body": c.get("body"),
                         "headers": c.get("headers") or [],
                         "contract_id": c.get("contract_id"),
                         "generated": bool(c.get("generated")),
                         "captured_ts": c.get("ts"),
                         "captured_on": c.get("inst"),
                         "borrowed": bool(c.get("borrowed"))},
                response={"reached": bool(res.get("ok")),
                          "http_code": res.get("code"),
                          "http_accepted": bool(res.get("accepted")),
                          "accepted": bool(res.get("accepted")) and not errors,
                          "graphql_errors": bool(res.get("gqlErrors")),
                          "errors": [list(e) for e in errors],
                          "order_status": out.get("status"),
                          "order_id": out.get("order_id"),
                          "placed": bool(placed),
                          "contract_id": extract_contract_id(res.get("detail")),
                          "rtt_ms": res.get("rtt"),
                          "url": res.get("url"),
                          "body": res.get("detail"),
                          "error": res.get("error"),
                          "raw": res},
                log=self.log)
        except Exception as e:
            self.log(f"⚠ sent-request log skipped for this call — {e}")

    # ---------- contract IDs ----------
    def _record_contract_id(self, cid, source, inst, inst_key=None):
        """Add a contractId received from CreatePurchaseContract to the Contract IDs list.

        The owning instance is kept as well as its name. A contractId is minted by ONE
        account's cart and is worthless to any other, so with six attached the id alone
        is not enough to build a PlaceOrder from — the row has to remember whose it is,
        or a generated order would be aimed at whichever emulator happened to be first
        in the list.
        """
        if not cid:
            return
        self.contract_ids = [e for e in self.contract_ids if e["id"] != cid]  # dedup, newest wins
        self.contract_ids.insert(0, {"id": cid, "ts": int(time.time() * 1000),
                                     "source": source, "inst": inst or "?",
                                     "inst_key": inst_key})
        self.contract_ids = self.contract_ids[:400]
        self._refresh_contracts()
        self._set_latest_contract(cid)   # also auto-fill the Generate field

    def _refresh_contracts(self):
        """One flat newest-first column, every id tagged with the emulator that minted
        it — right of the time, the same shape the call boxes use.

        An id is only usable on the cart that minted it, so whose it is has to travel
        WITH the id: these get read off the screen and pasted into the Generate field,
        and a name in a heading two lines up does not come along with the row.
        """
        picked = {e["id"] for e in self._selected_contracts()}
        self.cid_list.delete(0, "end")
        self._cid_rows = []
        for n, e in enumerate(self.contract_ids):
            t = time.strftime("%H:%M:%S", time.localtime(e["ts"] / 1000.0))
            # Padded outside the brackets so the tag is the same `[Pie64]` token the
            # call boxes write, while the ids under it still line up in a column.
            tag = f"[{(e.get('inst') or '?')[:12]}]"
            self.cid_list.insert("end", f"  {t}  {tag:<15}{e['id']}   ({e['source']})")
            self._cid_rows.append(n)
        for line, n in enumerate(self._cid_rows):
            if n is not None and self.contract_ids[n]["id"] in picked:
                self.cid_list.selection_set(line)

    def _selected_contracts(self):
        """Every contract-id entry selected in the box, by row rather than by line."""
        rows = getattr(self, "_cid_rows", [])
        out = []
        for line in self.cid_list.curselection():
            if line < len(rows) and rows[line] is not None                     and rows[line] < len(self.contract_ids):
                out.append(self.contract_ids[rows[line]])
        return out

    def _selected_contract(self):
        sel = self._selected_contracts()
        return sel[0]["id"] if sel else None

    def _use_selected_contract(self):
        cid = self._selected_contract()
        if not cid:
            return
        self.contract_entry.delete(0, "end")
        self.contract_entry.insert(0, cid)
        self.log(f"Loaded contractId {cid} into the Generate field.")

    def _copy_selected_contract(self):
        cid = self._selected_contract()
        if not cid:
            messagebox.showinfo("No contractId selected", "Select a contractId in the list first.")
            return
        self.root.clipboard_clear()
        self.root.clipboard_append(cid)
        self.root.update()
        self.log(f"Copied contractId {cid}.")

    def _clear_contracts(self):
        self.contract_ids = []
        self._refresh_contracts()

    def _clear_all_captures(self):
        """Drop every captured call and contract id — both panes and both boxes.

        Run when the demo switches accounts. What's on screen belongs to the instance
        it was captured on: a `contractId` is only valid for the cart that minted it,
        and a captured call carries that instance's cart/session state. Carrying any of
        it across would leave rows that look sendable but belong to the previous
        account — so the switch starts each account from an empty board.
        """
        for attr in ("prep_calls", "commit_calls"):
            setattr(self, attr, [])
        self.contract_ids = []
        self._refresh_calls()
        self._refresh_contracts()
        # the Generate field auto-fills from the newest contractId — that id is gone too
        try:
            self.contract_entry.delete(0, "end")
        except Exception:
            pass

    # ---------- generate calls from saved templates (without navigating the app) ----------
    # A template is per instance, and ONLY per instance. A captured checkout call
    # carries the cartId of the cart that made it, so it is that account's call and
    # nobody else's: generating from it on the other five would send one intercepted
    # call to six emulators, which is the one thing an intercepted call must not do.
    #
    # `ANY_KEY` is what an ownerless template lands under — the pre-upgrade single
    # template file, and any capture that named no instance. It is kept so a file
    # written by an older build still loads and can be seen, and it is never usable:
    # nothing knows whose cart it was, so there is no account it can honestly run on.
    ANY_KEY = "*"

    @staticmethod
    def _load_templates(path):
        """{instance key: template} from disk. A pre-upgrade single template loads
        under ANY_KEY, which no instance can send on — see the note above."""
        if not os.path.exists(path):
            return {}
        data = load_json(path, None)
        if not isinstance(data, dict):
            return {}
        if "body" in data or "url" in data:          # the old single-template file
            return {CheckoutPanel.ANY_KEY: data}
        return {k: v for k, v in data.items() if isinstance(v, dict)}

    def _tmpl_store(self, stage):
        return self.placeorder_templates if stage == "commit" else self.checkout_templates

    def _tmpl_path(self, stage):
        return TEMPLATE_PATH if stage == "commit" else CHECKOUT_TEMPLATE_PATH

    def template_for(self, stage, inst):
        """This instance's own template for `stage`, or (None, False).

        Nothing is borrowed. A CreatePurchaseContract body carries the cartId of the
        cart that made it, so another account's template does not mint a contract for
        THIS account — it mints one for that account, from this account's client. That
        is an intercepted call being replayed somewhere it never came from, so an
        account without its own capture generates nothing and is told why.

        The second element is kept (always True when there is a template) because
        callers read it as "this account has one of its own".
        """
        store = self._tmpl_store(stage)
        key = getattr(inst, "key", None)
        if key and store.get(key):
            return store[key], True
        return None, False

    def _save_template(self, stage, call):
        store = self._tmpl_store(stage)
        key = call.get("inst_key") or self.ANY_KEY
        store[key] = {"url": call.get("url"),
                      "headers": call.get("headers") or [],
                      "body": call.get("body")}
        try:
            save_json(self._tmpl_path(stage), store)
        except Exception as e:
            self.log(f"(couldn't save {call.get('op')} template: {e})")
            return
        self.log(f"[{call.get('inst')}] saved this {call.get('op')} as THIS instance's "
                 f"template — Generate now builds against its cart. "
                 f"({len([k for k in store if k != self.ANY_KEY])} instance(s) have one.)")

    def _save_placeorder_template(self, call):
        self._save_template("commit", call)

    def _save_checkout_template(self, call):
        self._save_template("prep", call)

    def _make_generated_checkout(self, inst):
        """One generated CreatePurchaseContract row for ONE instance, from THAT
        instance's template, inserted at the top of the checkout box.

        The row is tagged with the emulator it belongs to rather than the old
        "(generated)" — it goes out through that emulator's client against that
        emulator's cart, so that is what it is, and that tag is what the row shows
        right of its time. `generated` is already carried as its own flag, which is
        what colours it amber and marks it "not sent".
        """
        tmpl, own = self.template_for("prep", inst)
        call = {"op": "CreatePurchaseContract", "stage": "prep", "mode": "generated",
                "intercepted": True, "ts": int(time.time() * 1000),
                "body": tmpl.get("body"), "url": tmpl.get("url"),
                "headers": tmpl.get("headers") or [],
                "inst": getattr(inst, "name", "?"), "inst_key": getattr(inst, "key", None),
                "borrowed": not own,
                "cid": None, "response": None, "generated": True}
        self.prep_calls.insert(0, call)
        self._trim_calls("prep_calls")
        return call

    NO_MINT_TARGET = (
        "A mint runs on the accounts that have a checkout call in the list above, and "
        "no connected account has one.\n\n"
        "Capture one on each account you want to mint on: set Checkout to Watch (or "
        "Intercept, which captures it without anything reaching Walmart) and tap "
        "Continue to checkout in the app. A ✎ generated row does not count — it is one "
        "this tool built, not one the account made.\n\n"
        "It has to be per account: the call carries the cartId of the cart that made "
        "it, so one account's checkout would mint contracts on THAT account's cart, "
        "not on the others'."
    )

    def _captured_keys(self, stage):
        """Instance keys with a REAL captured call for `stage` in this session's box.

        "Real" is one the APP made and the agent documented — ● observed or ⛔ BLOCKED.
        A ✎ generated row is one this tool built, so it proves nothing about the
        account: counting them would let one mint qualify the account for the next.

        Blocked counts as much as observed. Working in Intercept is the normal way to
        walk checkout without anything reaching Walmart, and the request the agent
        documented is exactly as good a template either way — the difference is only
        whether Walmart also saw it.
        """
        attr = "commit_calls" if stage == "commit" else "prep_calls"
        return {c.get("inst_key") for c in getattr(self, attr)
                if not c.get("generated") and c.get("inst_key") and c.get("body")}

    def _gen_targets(self, stage):
        """Instances a mint should run on, having reported the ones it skips.

        Two things are required of an account, and both are about THAT account:

          1. a checkout call of its own in the list — the box on screen, this session;
          2. its own saved template, which is that captured call.

        (1) is the rule this exists for. It used to be (2) alone, and a template
        outlives the list — it is written to disk and reloaded next run — so an account
        that had captured nothing this session could still be minted on from a capture
        made hours ago, on a cart that has since changed. Worse, before templates went
        per instance, ONE account's captured checkout qualified every attached
        emulator: one intercepted call, six emulators, six carts none of it belonged
        to. A mint now runs on exactly the accounts you can see a checkout call for.
        """
        seen = self._captured_keys(stage)
        op = "PlaceOrder" if stage == "commit" else "CreatePurchaseContract"
        targets = []
        for inst in self.active():
            if inst.key not in seen:
                self.log(f"[{inst.name}] ✗ skipped — no {op} captured on this account "
                         f"in this list. Another account's capture is NOT used for it: "
                         f"that call belongs to that account's cart.")
                continue
            tmpl, _ = self.template_for(stage, inst)
            if not tmpl or not tmpl.get("body"):
                self.log(f"[{inst.name}] ✗ skipped — its {op} was captured with no body "
                         f"to build from.")
                continue
            targets.append(inst)
        return targets

    def _refresh_mint_targets(self):
        """Keep the note beside Generate & Send honest about who it would run on.

        Reads the same box the mint does, so it changes as calls land — and says zero
        out loud rather than leaving the button looking armed on a list of accounts
        that have nothing of their own in it.
        """
        lbl = getattr(self, "mint_targets_lbl", None)
        if lbl is None:
            return
        seen = self._captured_keys("prep")
        ready = [i for i in self.active() if i.key in seen]
        # A mint's own calls are not listed, so this is the only place in flight is
        # visible: generated and no result back yet.
        pending = sum(1 for c in self.prep_calls
                      if c.get("generated") and not c.get("sent"))
        tail = f"  ·  {pending} pending" if pending else ""
        if not ready:
            lbl.config(text="no account has a checkout call in this list yet" + tail)
            return
        names = ", ".join(i.name for i in ready[:3]) + (", …" if len(ready) > 3 else "")
        lbl.config(text=f"→ {len(ready)} account(s): {names}" + tail)

    def generate_and_send_checkout(self):
        """Mint N contract IDs on each account that has a checkout call in this list.

        The one dispatch in the checkout pane. It builds N CreatePurchaseContract rows
        for each qualifying account, from THAT account's own captured call, and sends
        them — accounts with no checkout call of their own take no part and are named
        in the log.

        Checkout calls are free: they price and lock the cart and return a contractId.
        No order is placed here.

        The mint delay is the ROW delay: it separates one account's own N calls. The
        accounts are separated by the emulator delay, in _send_batch_worker.
        """
        targets = self._gen_targets("prep")
        if not targets:
            messagebox.showinfo("No checkout call captured", self.NO_MINT_TARGET)
            return
        try:
            n = max(1, int(float(self.checkout_count.get().strip() or 1)))
        except Exception:
            n = 1
        calls = [self._make_generated_checkout(i) for i in targets for _ in range(n)]
        self._refresh_calls()
        delay = self._delay_ms("mint")
        self._set_send_enabled(False)
        sendlog.note_once(self.log)
        self.log(f"▶ minting {n} contractId(s) on each of {len(targets)} account(s) that "
                 f"has a checkout call of its own — {len(calls)} checkout call(s)"
                 + (f", {delay} ms between one account's own calls" if delay else "")
                 + (f", accounts {self._emu_delay_ms()} ms apart"
                    if self._emu_delay_ms() else "") + " …")
        threading.Thread(target=self._send_batch_worker, args=(calls, delay),
                         daemon=True).start()

    # ---------- the chain ----------
    #
    # Three of the four manual steps, run off a captured checkout: mint ×N, convert the
    # ids the mint returned, select the resulting orders. The fourth — ▶ Send (LIVE) —
    # is not here and is not called from here. That is the whole shape of it: the chain
    # ends holding N orders that have not been placed, and placing them stays an act
    # someone performs, on a pane where every row names its account and its contract.
    #
    # It re-enters through generate_and_send_checkout and _placeorders_for_ids rather
    # than reimplementing either, so the per-account rules those enforce (a mint only
    # on accounts with a real captured checkout of their own; a contractId only ever
    # sent through the account that minted it) hold identically whether a run was
    # started by hand or by a captured call — and so every send still funnels through
    # _send_done, and therefore through sendlog.

    def _chain_count(self):
        """N for a chain run: the same box the manual mint reads, same fallback."""
        try:
            return max(1, int(float(self.checkout_count.get().strip() or 1)))
        except Exception:
            return 1

    def _chain_start(self, call):
        """A real checkout call landed and the chain is armed — mint on it.

        Every captured call re-triggers, but two mints must not share one batch latch:
        the run in flight would collect the second run's ids as its own and the second
        would find none of its own left. So a call arriving mid-run is counted and
        re-run when the current one finishes, which is the same behaviour one step
        later rather than a dropped trigger.
        """
        if self._chain is not None:
            self._chain["requeued"] += 1
            self.log(f"⛓ [{call.get('inst')}] checkout captured while a chain run is in "
                     f"flight — queued, it re-runs when this one lands.")
            return
        if self._batch_busy:
            # A mint or a send started from a button is on the wire. Starting a chain
            # now would put two batches on one latch, and the first to finish would
            # end the chain — so it waits for the wire to clear instead.
            self._chain_pending = call.get("inst", "?")
            self.log(f"⛓ [{call.get('inst')}] checkout captured while a batch started "
                     f"by hand is in flight — the chain waits for it to land.")
            return
        if not self._gen_targets("prep"):
            # _gen_targets has already named each account it skipped and why.
            self.log("⛓ chain armed, but no connected account has a checkout call of "
                     "its own in the list — nothing minted.")
            return
        n = self._chain_count()
        self._chain = {"known": {e["id"] for e in self.contract_ids}, "requeued": 0,
                       "trigger": call.get("inst", "?"), "n": n}
        self.log(f"⛓ chain: [{call.get('inst')}] checked out → minting ×{n} …")
        self.generate_and_send_checkout()

    def _chain_batch_done(self):
        """The mint's replies are all in — convert what it returned and arm the pane.

        Ids are diffed against the ones that existed when the run started rather than
        converting the whole Contract IDs list: that list is not cleared between runs,
        and a chain that converted it wholesale would rebuild orders for contracts from
        earlier runs — some already placed, some expired — every time it fired.
        """
        if self._chain is None:
            # No chain run of ours — a manual batch just landed. If a capture arrived
            # during it, it was held rather than stacked; the wire is clear now.
            if self._chain_pending and self.chain_mode == "armed":
                trigger, self._chain_pending = self._chain_pending, None
                self.log(f"⛓ the batch has landed — running the chain held for "
                         f"[{trigger}].")
                self._chain_start({"inst": trigger})
            else:
                self._chain_pending = None
            return
        run, self._chain = self._chain, None
        fresh = [e["id"] for e in self.contract_ids if e["id"] not in run["known"]]
        if not fresh:
            # The mint went out and came back with nothing to place. Usually a refusal
            # (the per-customer cap, an expired cart) — _send_done has already printed
            # Walmart's own words for each one.
            self.log("⛓ chain stopped — the mint returned no new contractId. See the "
                     "refusals above; nothing was converted and nothing is armed.")
        else:
            made = self._placeorders_for_ids(fresh)
            self._refresh_calls()
            if made:
                self._chain_arm(made)
            else:
                self.log(f"⛓ chain stopped — {len(fresh)} new contractId(s) produced no "
                         f"PlaceOrder (see above). Nothing is armed.")
        if run["requeued"]:
            self.log(f"⛓ {run['requeued']} checkout call(s) arrived during that run — "
                     f"re-running the chain for the most recent.")
            self._chain_start({"inst": run["trigger"]})

    def _chain_arm(self, made):
        """Select the orders the chain built and say so — the last thing it does.

        Selecting them is the point: ▶ Send (LIVE) sends the selection, so the chain
        leaves the pane in the state a person would have had to click it into, and the
        one remaining act is the one that places the orders.
        """
        want = {id(c) for c in made}
        lst, data = self.commit_list, self.commit_calls
        rows = self.box_rows.get(lst) or []
        lst.selection_clear(0, "end")
        for line, n in enumerate(rows):
            if n is not None and n < len(data) and id(data[n]) in want:
                lst.selection_set(line)
        lst.see(0)
        accounts = len({c["inst"] for c in made})
        self._chain_status(f"⛓ {len(made)} order(s) armed across {accounts} account(s) "
                           f"— selected, NOT sent")
        self.log(f"⛓ chain done — {len(made)} PlaceOrder row(s) built across "
                 f"{accounts} account(s) and selected in the Place order box. "
                 f"NOTHING HAS BEEN SENT: press ▶ Send (LIVE) to place them, or change "
                 f"the selection first. One order per selected row.")

    def _chain_status(self, text):
        """The armed note beside ▶ Send (LIVE), amber while orders are waiting."""
        lbl = getattr(self, "chain_lbl", None)
        if lbl is not None:
            lbl.config(text=text, foreground="#b26a00" if text else "#555")

    def _set_latest_contract(self, cid):
        self.latest_contract_id = cid
        # Auto-fill the entry if the user hasn't typed one.
        if getattr(self, "contract_entry", None) is not None and not self.contract_entry.get().strip():
            self.contract_entry.delete(0, "end")
            self.contract_entry.insert(0, cid)

    def _make_generated_placeorder(self, cid, inst):
        """One generated PlaceOrder row for ONE instance, from THAT instance's template
        with `cid` swapped in, at the top of the Place order box.

        Both halves have to belong to the same account: the contractId was minted by
        one cart and the template body carries that cart's session state. Building
        every generated order from "whichever instance is first in the list" was
        harmless with one attached and is an order placed on the wrong account with
        six, so the owner is passed in rather than looked up.
        """
        tmpl, own = self.template_for("commit", inst)
        body = re.sub(TEMPLATE_CONTRACT_RE, '"contractId":"%s"' % cid, tmpl["body"])
        call = {"op": "PlaceOrder", "stage": "commit", "mode": "generated",
                "intercepted": True, "ts": int(time.time() * 1000),
                "body": body, "url": tmpl.get("url"), "headers": tmpl.get("headers") or [],
                "inst": getattr(inst, "name", "?"), "inst_key": getattr(inst, "key", None),
                "borrowed": not own, "contract_id": cid,
                "cid": None, "response": None, "generated": True}
        self.commit_calls.insert(0, call)
        self._trim_calls("commit_calls")
        return call

    def generate_placeorder(self):
        """One generated PlaceOrder for the contractId in the box, on the account that
        minted it — not on whichever emulator happens to be first in the picker."""
        cid = self.contract_entry.get().strip() or self.latest_contract_id
        if not cid:
            messagebox.showinfo(
                "No contractId",
                "Enter a contractId, or run CreatePurchaseContract first (Watch or Send it) "
                "so the latest one is auto-filled.")
            return
        made = self._placeorders_for_ids([cid])
        if not made:
            return
        self._refresh_calls()
        self.log(f"Generated a PlaceOrder for contractId {cid} on "
                 f"{made[0]['inst']} (✎ generated). Select it and ▶ Send (LIVE) "
                 f"to place it.")

    def _owner_for_contract(self, cid):
        """The connected instance that minted `cid`, or None.

        A contractId belongs to exactly one cart. With six accounts attached, sending
        a PlaceOrder for account 2's contract through account 5's client is not a
        near-miss — it is an order attempted against the wrong cart — so an id whose
        owner is not attached is skipped and named, never reassigned.
        """
        entry = next((e for e in self.contract_ids if e["id"] == cid), None)
        key = (entry or {}).get("inst_key")
        if key:
            hit = next((i for i in self.active() if i.key == key), None)
            if hit is not None:
                return hit
        if entry is None:
            # A hand-typed id: nothing knows whose it is, so the first connected
            # account is the only available reading of "this one".
            return next(iter(self.active()), None)
        return None

    def _placeorders_for_ids(self, ids):
        """Build one generated PlaceOrder per id, each on the account that minted it.

        Returns the calls built. Everything skipped is named in the log — a quiet
        shortfall here is the difference between six orders and four.
        """
        made, skipped = [], 0
        for cid in reversed(list(ids)):   # reversed: each insert goes on top
            inst = self._owner_for_contract(cid)
            if inst is None:
                skipped += 1
                entry = next((e for e in self.contract_ids if e["id"] == cid), None)
                self.log(f"✗ {cid} skipped — the account that minted it "
                         f"({(entry or {}).get('inst', '?')}) is not connected. "
                         f"Tick it and Connect, then convert again.")
                continue
            tmpl, _ = self.template_for("commit", inst)
            if not tmpl or not tmpl.get("body"):
                skipped += 1
                self.log(f"[{inst.name}] ✗ {cid} skipped — no PlaceOrder captured on "
                         f"this account, so there is no template to build from.")
                continue
            if not re.search(TEMPLATE_CONTRACT_RE, tmpl["body"]) and not messagebox.askyesno(
                    "contractId not found in template",
                    f"{inst.name}'s PlaceOrder template has no \"contractId\" field to "
                    f"swap, so it would be sent as-is (it may target a different or "
                    f"expired contract). Build it anyway?"):
                skipped += 1
                continue
            made.append(self._make_generated_placeorder(cid, inst))
        if skipped:
            self.log(f"⚠ {skipped} contractId(s) produced no PlaceOrder — see above.")
        return made

    def convert_contracts_to_placeorders(self):
        """Put a PlaceOrder in the box for EVERY contract id — one per id, nothing sent.

        It used to convert the selected ids, falling back to all of them when nothing
        was selected. Two behaviours behind one button, told apart by a selection that
        is invisible from a metre away, in the one box where the difference is how many
        orders get placed. With six accounts' ids in the list that is not a nuance
        worth keeping: the button converts the lot, and which ones you actually send is
        decided in the Place order box, where every row names its account and each one
        is a visible, selectable thing.
        """
        if not self.contract_ids:
            messagebox.showinfo("No contract IDs", "No contract IDs to convert.")
            return
        ids = [e["id"] for e in self.contract_ids]
        made = self._placeorders_for_ids(ids)
        self._refresh_calls()
        if not made:
            return
        accounts = len({c["inst"] for c in made})
        self.log(f"Converted {len(made)} of {len(ids)} contractId(s) into PlaceOrder "
                 f"call(s) across {accounts} account(s), each on the account that minted "
                 f"it (✎ generated, each tagged with its emulator). Select and Send (LIVE) — "
                 f"one order each.")

    def _pane_lists(self, kind):
        """The (attr, list) pairs for one pane."""
        names = ("prep_calls",) if kind == "prep" else ("commit_calls",)
        return [(n, getattr(self, n)) for n in names]

    def _clear_calls(self, kind):
        for name, _ in self._pane_lists(kind):
            setattr(self, name, [])
        if kind == "commit":
            self._chain_status("")   # the rows it counted are gone
        self._refresh_calls()

    def _export(self, kind):
        data = [c for _, lst in self._pane_lists(kind) for c in lst]
        label = "checkout" if kind == "prep" else "placeorder"
        if not data:
            messagebox.showinfo("Nothing to export", "No calls captured in this pane yet.")
            return
        path = os.path.join(BASE, time.strftime(f"{label}_calls_%Y%m%d_%H%M%S.json"))
        save_json(path, data)
        self.log(f"Exported {len(data)} {label} call(s) to {path}")
        messagebox.showinfo("Exported", f"Wrote {len(data)} call(s) to:\n{path}")








    # ---------- connect ----------
    # This app holds ONE connection at a time: the selected instance. Demoing several
    # accounts means switching selection, which disconnects the old one first.
    # ---------- session broker ----------
    # Both tools' agents hook DefaultHttpRequestComposer.compose. Two frida scripts
    # assigning .implementation on one method fight — the second wins, and unloading
    # either can restore the wrong original — so only one tab may hold a session.
    TOOL_LABEL = "Checkout"














    # ---------- messages ----------
    def _on_message(self, inst, msg, data):
        if msg.get("type") == "send":
            payload = dict(msg["payload"])
            payload["_key"], payload["_inst"] = inst.key, inst.name
            self.q.put(payload)
        elif msg.get("type") == "error":
            self.q.put({"_key": inst.key, "_inst": inst.name, "type": "error",
                        "msg": msg.get("stack") or msg.get("description")})

    def _pump(self):
        while not self.q.empty():
            p = self.q.get()
            t = p.get("type")
            who = p.get("_inst", "?")
            if t == "uicall":
                # UI work handed over by a worker thread — see _ui().
                try:
                    p["fn"]()
                except Exception:
                    pass
                continue
            if t == "checkout":
                call = {"op": p.get("op"), "stage": p.get("stage"),
                        "mode": p.get("mode"), "intercepted": bool(p.get("intercepted")),
                        "ts": p.get("ts") or int(time.time() * 1000),
                        "body": p.get("body"), "url": p.get("url"),
                        "headers": p.get("headers") or [], "inst": who,
                        "inst_key": p.get("_key"),   # which instance to live-send it through
                        # cid ties this request to the response the agent reads later;
                        # response stays None until (and unless) a checkout_response lands.
                        # sent stays absent until a live dispatch of this call returns.
                        "cid": p.get("cid"), "response": None}
                # Route by stage only — which operation it is. Whether it was observed
                # or blocked rides on the row (call["intercepted"]) and shows as its
                # tag and colour, instead of deciding which box it lands in.
                stage = "commit" if call["stage"] == "commit" else "prep"
                attr = f"{stage}_calls"
                lst = getattr(self, attr)
                lst.insert(0, call)
                setattr(self, attr, lst)
                self._trim_calls(attr)      # per emulator, not a flat cap over all six
                self._refresh_calls()
                disp = "BLOCKED" if call["intercepted"] else "observed"
                self.log(f"[{who}] ⇢ checkout [{stage.upper()}] {p.get('op')} "
                         f"{disp} ({len(p.get('body') or '')}B)")
                # Keep the newest PlaceOrder as a template so one can be generated later
                # without navigating to the app's place-order screen.
                if stage == "commit" and call.get("body"):
                    self._save_placeorder_template(call)
                elif stage == "prep" and call.get("body"):
                    self._save_checkout_template(call)
                # Armed chain: a captured checkout starts a run. Only the agent's own
                # captures reach this branch — a mint's generated rows are built
                # locally and inserted straight into prep_calls, so a run cannot
                # trigger itself.
                if stage == "prep" and call.get("body") and self.chain_mode == "armed":
                    self._chain_start(call)
            elif t == "checkout_response":
                # The reply to a non-blocked checkout call (CreatePurchaseContract in
                # Watch mode). Stitch it onto the request with the matching cid.
                call = self._find_call_by_cid(p.get("cid"))
                if call is not None:
                    call["response"] = {"code": p.get("code"), "body": p.get("body"),
                                        "ts": p.get("ts") or int(time.time() * 1000)}
                    self._refresh_calls()
                    cid_ = extract_contract_id(p.get("body"))
                    if cid_ and call.get("stage") == "prep":
                        self._record_contract_id(cid_, "observed", who,
                                                 p.get("_key"))
                    self.log(f"[{who}] ⇠ response {call.get('op')} HTTP {p.get('code')} "
                             f"({len(p.get('body') or '')}B)"
                             + (f" · contractId {cid_}" if cid_ else ""))
                else:
                    self.log(f"[{who}] ⇠ response arrived (cid {p.get('cid')}) with no "
                             f"matching request row — cleared or from before connect.")
            elif t == "resp-armed":
                if p.get("ok"):
                    extra = "peekBody" if p.get("peekBody") else \
                            ("okio-peek" if p.get("fallback") else "no body reader")
                    self.log(f"[{who}] response capture armed — {p.get('hooked')} chain "
                             f"hook(s), read via {extra}.")
                else:
                    self.log(f"[{who}] response capture NOT armed: "
                             f"{p.get('error') or 'no chain hook found'}. Requests are still "
                             f"captured; responses won't be on this build.")
            elif t == "blocked":
                self.log(f"[{who}] ⛔ BLOCKED {p.get('op')} ({p.get('stage', '?')}) "
                         f"— nothing reached Walmart.")
            elif t == "ready":
                self.log(f"[{who}] Agent ready — checkout: {self.MODES[self.mode_state['prep']][0]}"
                         f", place order: {self.MODES[self.mode_state['commit']][0]}.")
                inst = next((i for i in self.instances if i.key == p.get("_key")), None)
                if inst and inst.script:
                    self._apply_state(inst)
            elif t == "error":
                self.log(f"[{who}] agent error: {p.get('msg')}")
            # results of live sends, handed back from the worker thread (main-thread only)
            elif t == "sendresult":
                self._send_done(p["call"], p["res"])
            elif t == "sendbatchdone":
                self._set_send_enabled(True)
                # After the buttons come back, and on the UI thread: the chain builds
                # rows and moves a selection. Every reply of the batch has been through
                # _send_done by now, so every contractId the mint returned is recorded.
                self._chain_batch_done()
            elif t == "sendlog":
                self.log(p["msg"])
        self.root.after(300, self._pump)

    # ---------- everything below is the shared Session, not this panel ----------
    # The panel keeps calling self.cfg / self.log(...) / self.instances exactly as it
    # did when it owned them; only the implementations moved. That is what let the
    # ~250 feature call sites through this file stay untouched by the merge.

    LABEL = 'Checkout'

    # Write-through, not read-only: a panel assigning self.instances = [...] should
    # set the session's list, because that IS the panel's list now. (The ported suites
    # do exactly this to stand up a fake picker.)
    @property
    def cfg(self):
        return self.session.cfg

    @cfg.setter
    def cfg(self, v):
        self.session.cfg = v

    @property
    def pending(self):
        return self.session.pending

    @pending.setter
    def pending(self, v):
        self.session.pending = v

    def _select_default(self):
        self.session._select_default()

    def _select_instance(self, inst):
        self.session._select_instance(inst)

    @property
    def instances(self):
        return self.session.instances

    @instances.setter
    def instances(self, v):
        self.session.instances = v

    @property
    def dm(self):
        return self.session.dm

    def log(self, msg):
        self.session.log(msg)

    def adb(self, inst, *a, **kw):
        return self.session.adb(inst, *a, **kw)

    def detect(self, quiet=False):
        return self.session.detect(quiet=quiet)

    def selected(self):
        return self.session.selected()

    def connect(self):
        self.session.connect()

    def disconnect(self):
        self.session.disconnect()

    def _teardown(self, inst):
        self.session._teardown(inst)

    def _refresh_instances(self):
        self.session._refresh_instances()
        # Ticking, connecting or dropping an emulator changes who a mint would run on.
        self._refresh_mint_targets()

    def _settings(self):
        self.session._settings()

    def apply_state(self, inst):
        """Session hook: push this panel's state onto the freshly-attached agent."""
        self._apply_state(inst)
        # One more account is live: it counts toward the mint only once it has a
        # checkout call of its own, and the note beside the button has to say so.
        self._refresh_mint_targets()

    def on_message(self, inst, payload):
        """Session hook: one agent, so every message is offered to both panels.

        Tagging with the instance here (rather than in the pump) keeps the existing
        per-type handling in _pump untouched — it already expects _key/_inst.
        """
        p = dict(payload)
        p["_key"], p["_inst"] = inst.key, inst.name
        self.q.put(p)

    def on_session_dropped(self):
        """Session hook: the connection is going away (disconnect, or a switch to
        another account). Anything this panel had in flight belonged to it."""
        for flag in ("cancel", "sched_cancel"):
            ev = getattr(self, flag, None)
            if ev is not None:
                ev.set()

    def on_config_saved(self):
        """Session hook: Settings was saved. cfg is read through the Session, so there
        is nothing to reload — but a panel showing a config-derived value redraws."""
        fn = getattr(self, "_refresh_sched_readout", None)
        if fn is not None:
            try:
                fn()
            except Exception:
                pass

    def script_for(self, inst):
        """The one merged agent, on the one connected instance."""
        return getattr(inst, "script", None)

    def instance_note(self, inst):
        """Which of this account's two templates exist — so the picker says, per row,
        what Generate can build for it.

        Worth a row note only since templates went per instance: with six attached,
        "Generate checkout call" builds for every account that has one and skips the
        rest, and without this the skip is only visible in the log after the fact.
        Only this account's own templates count; nothing is borrowed from another.
        """
        have = [name for name, stage in (("checkout", "prep"), ("order", "commit"))
                if self.template_for(stage, inst)[1]]
        return ("tmpl: " + "+".join(have)) if have else None

    def on_instance_dropped(self, inst):
        """Session hook: ONE emulator was unticked. Every other one stays attached.

        This replaces on_account_switch, and the difference is the whole release: a
        switch meant the board belonged to the account you had just left, so it was
        cleared wholesale. Now only one account leaves, and clearing everything would
        throw away five accounts' captures because a sixth was detached.

        So exactly that account's rows go — a contractId is only valid for the cart
        that minted it, and a captured call carries its own account's session state,
        so its rows would look sendable while belonging to something no longer
        attached. The templates are kept, as they always were: they are what Generate
        builds from, and they are keyed per instance so nothing borrows across.
        """
        key, name = getattr(inst, "key", None), getattr(inst, "name", "?")

        def theirs(r):
            """Rows belonging to this emulator. Matched on the key when the row has
            one and on the name otherwise, because a hand-typed contract id and a
            generated row from an older session carry only the name."""
            return (r.get("inst_key") or r.get("inst")) in (key, name)

        had = 0
        for a in ("prep_calls", "commit_calls", "contract_ids"):
            rows = getattr(self, a)
            keep = [r for r in rows if not theirs(r)]
            had += len(rows) - len(keep)
            setattr(self, a, keep)
        self._refresh_calls()
        self._refresh_contracts()
        if had:
            self.log(f"[{name}] detached — cleared its {had} captured item(s) "
                     f"(checkout calls, place order calls, contract IDs). Every other "
                     f"account's rows are untouched.")

    def on_account_switch(self, inst):
        """Kept as an alias: the picker no longer switches, it ticks and unticks."""
        self.on_instance_dropped(inst)
