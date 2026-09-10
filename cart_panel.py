#!/usr/bin/env python3
"""
Walmart Cart Tool — intercept add-to-cart requests, edit them, re-send with one click,
and save items as one-tap presets (e.g. "Bananas").

How it works (see ../DOCUMENTATION.md): a Frida agent hooks the app's GraphQL request
composer and documents add-to-cart mutations. "Send requests" then sends DIRECTLY — the
agent rebuilds a captured request and dispatches it through the app's OWN OkHttpClient,
whose interceptor chain mints a fresh PerimeterX token and the x-o-* envelope for it.
Nothing of the app's is replaced, nothing is armed, and nobody taps Add-to-cart.

A send needs one intercepted add-to-cart from THAT instance as a template, for the
server-assigned cartId and the persisted-query hash — neither can be derived, and the
cartId belongs to that instance's cart, so templates are per instance.

Requires rooted emulators with frida-server running and the Walmart app logged in.

Three modes pick what the agent does with the app's own add-to-carts:
  View — document nothing, intercept nothing.
  Grab — document them; the add still reaches Walmart untouched.
  Hold — document them, then block them on-device.
Only Hold affects the app, and none of the three touch your own sends: those are built
at the okhttp layer and never pass through the hook the modes act on. Sending from Hold
is the normal way to work — capture with nothing reaching Walmart, then send only what
you meant to.

Multi-instance: every booted BlueStacks instance is detected and attached to at once.
An INTERCEPTED row goes back only to the cart it was intercepted on — never to the other
five (one cart per instance/account). A saved item ("Selected item") is not tied to any
cart, so sending one still fans out to every ticked instance.
"""
import os, sys, json, time, threading, queue, subprocess, re, shutil, socket, struct, statistics, math
import tkinter as tk
import sendlog
from session import (Instance, discover, find_adb, load_json, mode_column, save_json,
                     run, BASE, CONFIG_PATH, DEFAULT_CONFIG)
from tkinter import ttk, messagebox, simpledialog


PRESETS_PATH = os.path.join(BASE, "presets.json")





























def parse_item(body):
    """Pull {name, offerId, usItemId, quantity} out of a captured mutation body."""
    def g(pat):
        m = re.search(pat, body)
        return m.group(1) if m else ""
    return {
        "name": g(r'"name":"([^"]*)"'),
        "offerId": g(r'"offerId":"([^"]*)"'),
        "usItemId": g(r'"usItemId":"([^"]*)"'),
        "quantity": g(r'"quantity":([0-9.]+)') or "1",
    }


# ---------- SCHEDULING ----------
# Getting a request to ARRIVE at a given instant, across every instance at once.
#
# The round-trip is the wrong number to aim with: most of it happens after the
# request has already landed. What sits before arrival is
#
#     preflight (our interceptor chain, PX token minting)  ~4 ms
#   + one way on the wire                                  ~14 ms
#
# so a send is dispatched `lead` = preflight + one-way ahead of the deadline. The
# host->agent RPC hop (~8 ms, and the jitteriest piece) is NOT in there, because
# the agent is armed seconds early and does the final wait itself against the
# device clock (agent.js `schedulesend`). Three clocks are therefore in play:
#
#   true time  --(NTP offset)-->  host clock  --(device offset)-->  device clock
#
# Both offsets are measured, not assumed: this host was 610 ms off true time and
# the device is a further ~405 ms off the host, either of which dwarfs the lead.
# See DOCUMENTATION.md §9.

NTP_EPOCH = 2208988800   # 1900 -> 1970

# Mirrors SCHED_MAX_WAIT in agent.js. The agent refuses a longer hold because the
# wait blocks its single-threaded runtime — and with it any app thread that hits
# one of our hooks — so the host must never arm further out than this.
AGENT_MAX_HOLD_MS = 30000

# Item ids that resolve to no offer, mirroring WARM_OFFER/WARM_ITEM in agent.js.
# A send carrying them travels the entire path — PX minting, TLS, the gateway —
# and comes back rejected inside a 200, so it measures the timing exactly like a
# real send while being incapable of changing the cart. This is what makes a
# full-dress rehearsal possible.
SENTINEL_ITEM = {"offerId": "0" * 32, "usItemId": "0" * 10, "quantity": 1}


def sntp_offset(host, samples=6, timeout=4, budget=None):
    """(rtt_ms, offset_ms) against an NTP server, or (None, None).

    Positive offset = the local clock is BEHIND true time, i.e. everything you
    schedule by wall clock fires that late. Deliberately does not go through
    w32time, which reports a slewed sub-second error as a successful sync.
    Keeps the sample with the smallest round-trip — the least contaminated by
    path asymmetry, which is what bounds the error.

    `budget` caps the TOTAL wall time in seconds, and is not optional in the
    scheduled path: this runs 20 s before a deadline, and six samples against a
    black-holed server is 6 x timeout = 24 s, which would sail straight past the
    instant the whole feature exists to hit. With a budget the call returns
    whatever it has (possibly nothing) and the caller schedules uncorrected
    rather than late.
    """
    got = []
    t_start = time.monotonic()

    def left():
        return None if budget is None else budget - (time.monotonic() - t_start)

    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        for _ in range(samples):
            lf = left()
            if lf is not None and lf <= 0:
                break
            s.settimeout(timeout if lf is None else max(0.25, min(timeout, lf)))
            try:
                t1 = time.time()
                s.sendto(b"\x1b" + 47 * b"\0", (host, 123))
                data, _ = s.recvfrom(1024)
                t4 = time.time()
            except Exception:
                continue
            if len(data) < 48:
                continue
            u = struct.unpack("!12I", data[:48])
            t2 = u[8] + float(u[9]) / 2 ** 32 - NTP_EPOCH      # server received
            t3 = u[10] + float(u[11]) / 2 ** 32 - NTP_EPOCH    # server transmitted
            got.append(((((t4 - t1) - (t3 - t2)) * 1000), ((t2 - t1) + (t3 - t4)) / 2 * 1000))
            lf = left()
            if lf is not None and lf <= 0.15:
                break
            time.sleep(0.12)
    finally:
        s.close()
    got.sort()
    return got[0] if got else (None, None)


def fmt_clock(t, with_day=True):
    """An epoch instant as the wall clock, to the millisecond.

    with_day=False drops the weekday, for the next-arrival readout: it is always
    within the next interval, so naming the day is noise.
    """
    return (time.strftime("%a %H:%M:%S" if with_day else "%H:%M:%S", time.localtime(t))
            + f".{int(round((t - int(t)) * 1000)):03d}")


def next_occurrence(peg, interval, now, min_lead=0.0):
    """The next `peg + k*interval` at least `min_lead` ahead of `now`.

    Pegged, not chained: every target is computed from the original peg, so a
    cycle that overruns cannot drag the rest of the series late behind it, and
    01:00:00 every 60 s stays on 01:01:00, 01:02:00, … rather than drifting to
    01:01:00.4, 01:02:01.1. `interval` <= 0 means a single shot.
    """
    if interval <= 0:
        return peg if peg > now + min_lead else None
    # floor+1, not ceil: landing exactly ON a grid point means that one is gone,
    # so the answer is the following one. ceil() would return the instant itself
    # and a cycle finishing precisely on time would re-target its own deadline.
    #
    # k is NOT clamped to >= 0: the peg is a fixed anchor (12:00:00), not a start
    # time, so the grid runs in both directions from it. At 09:00 with a noon peg
    # the answer is 09:01:00 — the next point on the grid — not noon.
    k = math.floor((now + min_lead - peg) / interval) + 1
    return peg + k * interval


def fmt_countdown(secs):
    """Seconds left, as h:mm:ss.t — tenths, because the last second matters."""
    if secs < 0:
        return "0:00:00.0"
    h, rem = divmod(secs, 3600)
    m, s = divmod(rem, 60)
    return f"{int(h)}:{int(m):02d}:{s:04.1f}"


def fmt_countdown_fine(secs):
    """Like fmt_countdown but to the millisecond - for the live time-left readout,
    where the fractional second is the whole point of watching it."""
    if secs < 0:
        return "0:00:00.000"
    h, rem = divmod(secs, 3600)
    m, s = divmod(rem, 60)
    return f"{int(h)}:{int(m):02d}:{s:06.3f}"


class CartPanel:
    # Cap on the log pane. A repeating schedule writes ~6 lines per cycle per
    # instance, so an unbounded pane grows all day and never releases it.
    LOG_MAX_LINES = 1500

    def __init__(self, root, session):
        # `root` is the collapsible section this panel builds into; `session`
        # is the one connection both panels share (see session.py).
        self.session = session
        session.register(self)
        self.root = root
        # There is no standalone mode and no broker any more: a panel is always a
        # section of the one window, on the one session.
        # the delay used to be stored in seconds — carry an existing setting over
        # rather than silently resetting someone's throttle to 0
        if "delay_sec" in self.cfg:
            try:
                self.cfg.setdefault("delay_ms", str(int(float(self.cfg["delay_sec"]) * 1000)))
            except Exception:
                pass
            self.cfg.pop("delay_sec", None)
        for k, v in DEFAULT_CONFIG.items():
            self.cfg.setdefault(k, v)
        self.presets = load_json(PRESETS_PATH, [])
        self.captures = []          # newest first, max 6
        self._cap_seq = 0           # hands each capture its own `cid` — see _pump
        # Every request WE sent, with Walmart's verdict on it — newest first. This is
        # the only place a per-request outcome is kept: before this box the verdict
        # existed once, as a line in the shared log, and scrolled away behind whatever
        # ran next. The intercepted list cannot carry it, because those rows are the
        # app's own adds documented on the REQUEST side (the composer hook never reads
        # a reply), and an accepted send deletes its row anyway.
        self.sent = []
        self._sent_rows = []        # listbox line -> index in self.sent (_refresh_sent)
        self._cap_rows = []         # listbox line -> index in self.captures
        # The ARMED list is its OWN snapshot, taken when you Arm - not a live view of
        # the intercepted list. It stays put after a send, and changes only on a fresh
        # arm (possible only while disarmed) or when a row is dropped with the Remove
        # button beside it. armed_rows are the very dicts the worker fires, and
        # armed_per_key regroups those SAME dicts by cart, so removing one in place is
        # seen by an in-flight run too.
        self.armed_rows = []        # snapshot of what is armed; the box's data
        self.armed_per_key = None   # {instance key: [rows]} routing, or None = fan-out
        self._armed_lines = []      # listbox line -> index in self.armed_rows
        # The instance a connect/switch is working towards, as (Instance, verb), or None.
        # A switch tears the old session down on a worker, so for a moment the OLD
        # instance is still connected while the picker already shows the new one; the
        # header reads this first so it reports the transition, not a stale truth.
        self.mode_state = "grab"    # plain mirrors of the tk vars — worker threads must
        self.holdco_state = False   # not touch tkinter variables
        self.editing_idx = None     # preset index currently being edited in the editor
        # Newest captured request per instance, kept as that instance's send template.
        # Held separately from self.captures so clearing the visible list after a send
        # does not throw away the cartId/hash later sends need — and keyed by instance
        # because the cartId is server-assigned to THAT instance's cart, so a template
        # is not portable between instances.  {instance key: {url, headers, body, ts}}
        self.templates = {}
        self.sending = False              # a send run is in flight
        self.cancel = threading.Event()   # set to stop the run after the current request
        # --- scheduled send ---
        self.armed = False                # a deadline is set and being counted down to
        self.sched_target = None          # host-clock epoch seconds to ARRIVE at
        self.sched_label = ""             # what the user typed, resolved
        self.sched_cancel = threading.Event()
        # The nudge the running series was armed with, in ms — see _schedule_worker.
        # None until a series arms, which is also what tells the sent-request log that
        # a send took the untimed path and had no nudge at all (as opposed to 0).
        self.armed_nudge_ms = None
        # Host clock minus true time, ms, from NTP. Positive = host is BEHIND, so a
        # send scheduled by wall clock lands that late unless it is corrected out.
        self.ntp_off_ms = None
        self.ntp_at = 0                   # when it was measured (it drifts ~1.2 ms/min)
        self.q = queue.Queue()      # frida->GUI messages
        self._build_ui()
        # The panel still drains its OWN queue: _pump is per-message feature logic,
        # not connection plumbing. What it no longer does is detect() — the Session
        # owns the instance list and finds the emulators once for both panels.
        self.root.after(300, self._pump)
        self.root.after(1000, self._tick_ages)

    def _ui(self, fn):
        """Run `fn` on the tkinter thread, from anywhere.

        Tk must only be touched from the thread that owns it. Calling `root.after` from
        a worker is not merely racy: with no mainloop servicing it, Tcl parks the caller
        inside createcommand, and a worker parked there while holding a lock wedges every
        other worker behind it. So off-thread work goes through the queue `_pump` already
        drains on the main thread; a call already on the UI thread runs inline.
        """
        if threading.current_thread() is threading.main_thread():
            try:
                fn()
            except Exception:
                pass
            return
        self.q.put({"type": "uicall", "fn": fn})







    # ---------- session broker ----------
    # Both tools' agents hook DefaultHttpRequestComposer.compose. Two frida scripts
    # assigning .implementation on one method fight — the second wins, and unloading
    # either can restore the wrong original — so only one tab may hold a session.
    TOOL_LABEL = "Cart Tool"














    # ---------- fan-out helpers ----------
    def active(self):
        """Instances a send/toggle should reach: connected and ticked."""
        return [i for i in self.instances if i.connected and i.enabled]

    def broadcast(self, method, *args):
        """Call an agent rpc export on every active instance. Returns those it reached."""
        hit = []
        for inst in self.active():
            try:
                getattr(inst.script.exports_sync, method)(*args)
                hit.append(inst)
            except Exception as e:
                self.log(f"[{inst.name}] {method} failed: {e}")
        return hit

    def _require_active(self):
        if self.active():
            return True
        messagebox.showwarning("Not connected",
                               "Select an instance and click 'Connect' first.")
        return False

    def _refresh_sub_choices(self):
        nicks = [self._nick(p) for p in self.presets]
        idx = self.sub_combo.current()
        self.sub_combo["values"] = nicks
        if 0 <= idx < len(nicks):
            self.sub_combo.current(idx)
        elif nicks:
            self.sub_combo.current(0)
        else:
            self.sub_combo.set("")

    def _apply_sub(self):
        """Overwrite every intercepted row with the selected item.

        This edits the *list*, not the agent: the rows keep their slots and count,
        only the item they carry changes. 'Send requests' then fires the list as it
        stands and neither knows nor cares that anything was overwritten.
        """
        idx = self.sub_combo.current()
        if idx < 0 or idx >= len(self.presets):
            messagebox.showinfo("Pick one", "Choose a saved item from the dropdown first."); return
        if not self.captures:
            messagebox.showinfo("Nothing intercepted",
                "There are no intercepted add-to-carts to overwrite.\n\n"
                "Add items in the app (Grab or Hold mode) first."); return
        if self.sending:
            messagebox.showinfo("Send in flight",
                "Requests are still being sent — let them land before overwriting the list."); return
        p = self.presets[idx]; name = self._nick(p)
        try:
            q = int(float(self.sub_qty.get()))
        except Exception:
            q = 1
        for c in self.captures:
            c["name"] = p.get("name") or name
            c["nick"] = name
            c["offerId"] = p["offerId"]
            c["usItemId"] = p["usItemId"]
            c["quantity"] = str(q)
            c["overwritten"] = True
        n = len(self.captures)
        self._refresh_captures()
        self.sub_status.config(text=f"{n} row(s) → {name} ×{q}", foreground="#0a7d00")
        self.log(f"Overwrote {n} intercepted request(s) with {name} ×{q}. "
                 f"Click 'Send requests' to send them.")

    def _delay_ms(self):
        """The configured throttle, in ms. Never raises — junk reads as 0."""
        try:
            return max(0, int(float(self.cfg.get("delay_ms", 0) or 0)))
        except Exception:
            return 0

    def _emu_delay_ms(self):
        """The gap between one emulator's FIRST request and the next emulator's, in ms.

        The other axis of a fan-out, and deliberately a separate number from the row
        delay. The row delay separates rows *inside* one emulator — that is what a
        burst spaces, and it stays entirely within one device's dispatch. This one
        separates the *emulators*: instance 1 fires at the deadline, instance 2 at
        deadline + emulator delay, instance 3 at + 2x, and each then runs its own rows
        at the row delay from there.

        They were one number before, which could not express either intent: raising it
        to stagger the accounts also spread every account's own rows, and lowering it
        to tighten a burst also collapsed the accounts onto each other.
        """
        try:
            return max(0, int(float(self.cfg.get("emulator_delay_ms", 0) or 0)))
        except Exception:
            return 0

    def _emu_offset_ms(self, inst, targets):
        """This instance's share of the emulator delay: its index x the delay.

        Index is the position in `targets`, which is picker order, so the stagger is
        the order of the checkboxes on screen rather than whichever thread won a race.
        """
        try:
            n = list(targets).index(inst)
        except ValueError:
            n = 0
        return n * self._emu_delay_ms()

    def _emu_delay_boxes(self):
        """Both entries showing the emulator delay: the bulk bar's and the timed one's."""
        return [e for e in (getattr(self, "emu_delay_entry", None),
                            getattr(self, "sched_emu_entry", None)) if e is not None]

    def _show_emu_delay(self, ms):
        """Put one value in every box that shows it.

        There is ONE emulator delay — it describes the fan-out, not a send path — so
        it appears beside the row delay in both panels and the two must never disagree.
        A box showing a stale number here would be read as the setting not applying to
        that path.
        """
        for e in self._emu_delay_boxes():
            e.delete(0, "end")
            e.insert(0, str(ms))

    def _apply_emu_delay(self, src=None):
        src = src or self.emu_delay_entry
        raw = src.get().strip()
        try:
            ms = max(0, int(float(raw or 0)))
        except Exception:                       # typo: put the old value back
            self._show_emu_delay(self._emu_delay_ms())
            self.log(f"⚠ '{raw}' isn't a number of milliseconds — emulator delay left "
                     f"at {self._emu_delay_ms()} ms.")
            return
        if ms == self._emu_delay_ms() and raw == str(ms):
            return                              # FocusOut with nothing changed
        self.cfg["emulator_delay_ms"] = str(ms)
        save_json(CONFIG_PATH, self.cfg)
        self._show_emu_delay(ms)
        self.log(f"Emulator delay set to {ms} ms — instance 2 starts {ms} ms after "
                 f"instance 1, instance 3 {2 * ms} ms after it, and so on. Rows within "
                 f"one instance are still spaced by the row delay."
                 if ms else "Emulator delay off — every instance starts together.")

    def _sync_emu_delay(self):
        """The timed panel's copy of the emulator delay was edited."""
        self._apply_emu_delay(self.sched_emu_entry)

    def _apply_delay(self):
        raw = self.delay_entry.get().strip()
        try:
            ms = max(0, int(float(raw or 0)))
        except Exception:                       # typo: put the old value back
            self.delay_entry.delete(0, "end")
            self.delay_entry.insert(0, str(self._delay_ms()))
            self.log(f"⚠ '{raw}' isn't a number of milliseconds — delay left at "
                     f"{self._delay_ms()} ms.")
            return
        if ms == self._delay_ms() and raw == str(ms):
            return                              # FocusOut with nothing changed
        self.cfg["delay_ms"] = str(ms)
        save_json(CONFIG_PATH, self.cfg)
        self.delay_entry.delete(0, "end")
        self.delay_entry.insert(0, str(ms))     # normalise "1000.0" -> "1000"
        self.broadcast("setdelay", ms)
        self.log(f"Delay between sent requests set to {ms} ms (per instance)."
                 if ms else "Delay between sent requests off (no throttle).")

    # key -> (dropdown label, what it does). Two axes: does the tool *document*
    # the app's add-to-cart, and does it *intercept* it. Only Hold touches the app.
    MODES = {
        "view": ("View — ignore everything",
                 "attached but inert: nothing documented, nothing intercepted"),
        "grab": ("Grab — document only",
                 "adds reach your cart untouched and are listed under Intercepted"),
        "hold": ("Hold — intercept & document",
                 "adds are listed, then blocked on-device — nothing reaches Walmart"),
    }
    # View is selectable: it parks the agent inert while staying attached, which is
    # not what Disconnect does — that tears down the frida session and needs a
    # reconnect. No mode has to be parked for a send any more: a send is built at
    # the okhttp layer and never reaches the hook these three gate.
    MODE_CHOICES = ("view", "grab", "hold")
    # dot colour: grey = inert, green = app untouched, red = the tool is altering it
    MODE_COLOUR = {"view": "#6b6b6b", "grab": "#0a7d00", "hold": "#b30000"}

    def _mode_from_label(self, label):
        return next((k for k in self.MODE_CHOICES if self.MODES[k][0] == label), "grab")

    def _apply_mode(self):
        mode = self._mode_from_label(self.mode_combo.get())
        self.mode_state = mode        # plain str: worker threads must not touch tk vars
        title, desc = self.MODES[mode]
        self.mode_desc.config(text=desc)
        self.mode_badge.config(foreground=self.MODE_COLOUR[mode])
        hit = self.broadcast("setmode", mode)
        if not hit:
            self.log(f"Mode set to {title} — but 0 instances are connected, so nothing is "
                     f"applied yet. It will be pushed on Connect.")
            return
        self.log(f"Mode: {title} on {len(hit)} instance(s) — {desc}.")


    def _apply_state(self, inst):
        """Push hold / checkout-guard / delay onto one instance's agent."""
        try:
            inst.script.exports_sync.setmode(self.mode_state)
            inst.script.exports_sync.setdelay(self._delay_ms())
        except Exception as e:
            self._ui(lambda e=e, inst=inst: self.log(f"[{inst.name}] couldn't apply hold/delay: {e}"))

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
            if t == "capture":
                item = parse_item(p["body"])
                item["ts"] = p["ts"] / 1000.0
                item["op"] = p["op"]
                item["inst"] = who
                item["key"] = p.get("_key")     # which instance's cart this belongs to
                # Kept verbatim so a send can rebuild this exact request: the body
                # carries the server-assigned cartId, the url carries the
                # persisted-query hash, the headers are Apollo's X-APOLLO-* set.
                item["body"] = p["body"]
                item["url"] = p.get("url")
                item["headers"] = p.get("headers") or []
                # This row's own identity, and the only thing that distinguishes it
                # from another capture of the SAME item. Adding one product three
                # times gives three rows with identical (offerId, usItemId), so an
                # id-pair match cannot tell them apart — see _mark_capture_sent.
                self._cap_seq += 1
                item["cid"] = self._cap_seq
                if item["url"] and item["key"]:
                    # Newest capture from this instance becomes its send template.
                    self.templates[item["key"]] = {
                        "url": item["url"], "headers": item["headers"],
                        "body": item["body"], "ts": item["ts"]}
                self.captures.insert(0, item)
                self._trim_captures()
                self._refresh_captures()
                self._refresh_instances()       # template state per row may have changed
                self.log(f"[{who}] Captured: {item['name'][:36]}  (qty {item['quantity']})"
                         + ("  — send template for this instance updated." if item["url"] else ""))
            elif t == "held":
                if p.get("scope") == "checkout":
                    self.log(f"[{who}] ⛔ BLOCKED {p.get('op')} — no order was placed.")
                else:
                    # Only the app's own adds reach here: ours are built at the okhttp
                    # layer and never pass through the hook Hold acts on.
                    self.log(f"[{who}] ⊘ Held — documented, request aborted "
                             f"(nothing sent to Walmart).")
            elif t == "checkout":
                stage = "COMMIT" if p.get("commit") else "prep"
                self.log(f"[{who}] ⇢ checkout [{stage}] {p.get('op')} "
                         f"({len(p.get('body') or '')}B)")
            elif t == "ready":
                self.log(f"[{who}] Agent ready.")
                inst = next((i for i in self.instances if i.key == p.get("_key")), None)
                if inst and inst.script:      # backstop; _connect_one already pushed state
                    self._apply_state(inst)
            elif t == "error":
                self.log(f"[{who}] agent error: {p.get('msg')}")
        self.root.after(300, self._pump)

    # ---------- send ----------
    # One path only: the agent builds each request and dispatches it through the
    # app's own OkHttpClient. Nothing is armed, no add-to-cart is triggered, and the
    # app's own requests are never touched. See DOCUMENTATION.md §7.

    def _template_for(self, inst):
        """That instance's send template, or None.

        A send is not synthesised out of thin air: it reuses a real captured
        request's url (which carries the persisted-query hash) and body (which
        carries the server-assigned cartId), swapping only the item fields. The
        cartId belongs to THAT instance's cart, so a template captured on one
        instance is not usable on another — hence per-instance, not a single
        newest-wins template.
        """
        return self.templates.get(inst.key)

    def _templated(self):
        """Active instances that can send right now, and those that can't."""
        ready = [i for i in self.active() if self._template_for(i)]
        missing = [i for i in self.active() if not self._template_for(i)]
        return ready, missing

    NO_TEMPLATE = ("A send rebuilds a real captured request — it needs the "
                   "server-assigned cartId and the persisted-query hash, and neither "
                   "can be derived.\n\nThe cartId belongs to one instance's cart, so "
                   "EACH instance needs its own capture: add one item in the app on "
                   "each, in Grab or Hold mode (Hold captures it without anything "
                   "reaching Walmart). After that, sends never touch the app again.")

    def _start_send(self, rows, per_key=None):
        """Start a send run. Returns True if one started.

        `rows` is the whole list. `per_key` — {instance key: [rows]} — narrows what
        each instance gets: an intercepted row is sent ONLY on the cart it was
        intercepted on. `per_key` None is the fan-out — every instance sends every row
        — and is now reached only from "Selected item", whose row is a saved item
        rather than anyone's capture.

        The intercepted list is a mix of six carts' adds once six accounts are
        attached, and putting all six carts' adds into all six carts is not what
        intercepting them meant: an add belongs to the account that made it. So the
        list is regrouped by the [instance] tag each row already carries and handed
        back, rather than broadcast.
        """
        if self.sending:
            messagebox.showinfo("Send in flight",
                "A send is still running — let it finish, or click Cancel."); return False
        if self.armed:
            # Sending now would consume the throttle's clock and, worse, leave an
            # ambiguous cart at the deadline. Make it an explicit choice.
            messagebox.showinfo("Armed",
                f"A timed send is counting down to {self.sched_label}. Disarm it first "
                f"if you want to send now."); return False
        ready, missing = self._templated()
        for inst in missing:
            self.log(f"[{inst.name}] ✗ skipped — no capture from this instance yet, so there "
                     f"is no cartId to build from.")
        if not ready:
            messagebox.showwarning("No template", self.NO_TEMPLATE)
            return False
        if per_key is not None:
            # An instance with nothing of its own in the list has nothing to send —
            # it is not an error, and it must not be handed someone else's rows.
            ready = [i for i in ready if per_key.get(i.key)]
            if not ready:
                messagebox.showinfo(
                    "Nothing to send",
                    "No connected account has any unsent rows of its own in "
                    "the list.\n\nEvery intercepted row is sent on the cart it "
                    "was intercepted on, so a row whose account is not "
                    "connected (or not ticked) has nothing to go out on — "
                    "tick it and Connect.")
                self.sending = False
                return False
        self.sending = True
        self.cancel.clear()
        sendlog.note_once(self.log)
        emu = self._emu_delay_ms()
        total = sum(len(per_key[i.key]) for i in ready) if per_key else len(rows) * len(ready)
        self._set_send_status(
            (f"sending {total} request(s) over {len(ready)} instance(s), each its own rows"
             if per_key else
             f"sending {len(rows)} request(s) × {len(ready)} instance(s)")
            + (f", {emu} ms apart per emulator" if emu else "") + "…")
        threading.Thread(target=self._send_worker, args=(rows, ready, per_key),
                         daemon=True).start()
        return True

    def _send_worker(self, rows, targets, per_key=None):
        """Fan out: one thread per instance, each walking the rows in order.

        Per-instance threads because every directsend blocks on real network I/O
        inside that app — serialising them would make a fan-out take N times longer
        for no reason. The agent's delay throttle is per instance too, so the
        instances never wait on each other.

        The two delays act on different axes and both are honoured here:

        * the **row delay** (Settings -> delay_ms, the box beside Selected item) is
          slept inside the agent before each request, so it only ever separates rows
          of the SAME instance;
        * the **emulator delay** staggers the threads themselves — instance n does not
          start its first row until n x emulator delay after instance 1 did.
        """
        self._ui(lambda: self.log(
            (f"Sending each of {len(targets)} instance(s) its own row(s) — "
             f"{sum(len(per_key.get(i.key, [])) for i in targets)} request(s) in total"
             if per_key is not None else
             f"Sending {len(rows)} request(s) to {len(targets)} instance(s)")
            + " — built by the agent and dispatched through the app's own client. "
              "Nothing is armed."))
        tally, lock = {"ok": 0, "fail": 0}, threading.Lock()
        rtts = []            # per-request round-trip, as measured inside the agent

        # The device clock offset used to be measured only in the timed path's warm-up,
        # so on THIS path it was never known — and without it a device instant cannot
        # be put on the host clock, leaving the intercepted row's time column stamped
        # when the host recorded the verdict. Every row of a run then read as the same
        # instant. Measured here, once per instance, off the UI thread: a handful of
        # RPCs before a run that is about to do real network I/O anyway.
        for inst in targets:
            if getattr(inst, "clock_off_ms", None) is None:
                try:
                    self._measure_device_offset(inst, n=5)
                except Exception:
                    pass        # the column falls back to the record time; a send is
                                # not worth failing over a clock probe

        def one(inst):
            # This instance's place in the stagger. Slept on the worker rather than
            # asked of the agent, because it is a property of the fan-out and not of
            # any one device — the agent knows nothing about the other five.
            off = self._emu_offset_ms(inst, targets)
            if off:
                self._ui(lambda i=inst, o=off: self.log(
                    f"[{i.name}] waiting {o} ms (emulator delay) before its first row."))
                if self.cancel.wait(off / 1000.0):
                    return
            tmpl = self._template_for(inst)
            # An intercepted run hands this instance the rows IT intercepted; a
            # 'Selected item' run has no owner to route by and sends the lot — see
            # _start_send.
            mine = per_key.get(inst.key, []) if per_key is not None else rows
            for n, row in enumerate(mine, 1):
                if self.cancel.is_set():
                    self._ui(lambda i=inst, n=n, m=len(mine): self.log(
                        f"[{i.name}] ⊘ cancelled with {m - n + 1} request(s) left."))
                    return
                item = {"offerId": row["offerId"], "usItemId": row["usItemId"],
                        "quantity": row["quantity"]}
                try:
                    res = inst.script.exports_sync.directsend(tmpl, item)
                except Exception as e:
                    res = {"ok": False, "error": str(e)}
                # `accepted` is the agent's verdict: 2xx AND no GraphQL "errors"
                # array. Status alone would score a rejected add as a success.
                good = bool(res.get("ok") and res.get("accepted"))
                rtt = (res.get("timing") or {}).get("rtt")
                with lock:
                    tally["ok" if good else "fail"] += 1
                    if rtt is not None:
                        rtts.append(rtt)
                # Same verdict the log line below reports, kept as a row in the
                # "Sent requests" box so it survives whatever scrolls past next, and
                # appended to the sent-request log with what actually spaced it. The
                # row delay is the agent's MEASURED sleep (timing.wait) rather than
                # the setting: the throttle only sleeps the remainder of the gap that
                # the previous round-trip did not already cover, so on this path the
                # setting is a ceiling and the measurement is what happened.
                d = sendlog.delays(
                    emulator_instance_ms=off,
                    row_ms=(res.get("timing") or {}).get("wait"),
                    path="cart pane — bulk send (unscheduled: no nudge, no lead)",
                    settings={"row_delay_ms": self._delay_ms(),
                              "emulator_delay_ms": self._emu_delay_ms(),
                              "row_position": n})
                self._ui(lambda i=inst, r=row, res=res, g=good, d=d:
                         self._record_sent(i, r, res, g, delays=d))
                if good:
                    self._ui(lambda i=inst, n=n, r=row, res=res, rtt=rtt,
                                    m=len(mine): self.log(
                        f"[{i.name}] ✓ [{n}/{m}] {r['label']} ×{r['quantity']} "
                        f"— HTTP {res.get('code')}"
                        + (f" in {rtt} ms" if rtt is not None else "")
                        + f" via {res.get('interceptors')} interceptors."))
                elif res.get("ok"):
                    # The gateway's own error text says far more than the status
                    # line — a bad persisted-query path, a stale cartId and a
                    # relisted offerId look identical without it.
                    self._ui(lambda i=inst, n=n, r=row, res=res, m=len(mine): self.log(
                        f"[{i.name}] ✗ [{n}/{m}] {r['label']} — HTTP {res.get('code')}"
                        + (f"\n    {res['detail']}" if res.get("detail") else "")
                        + (f"\n    url: {res['url']}" if res.get("url") else "")))
                else:
                    self._ui(lambda i=inst, n=n, r=row, res=res, m=len(mine): self.log(
                        f"[{i.name}] ✗ [{n}/{m}] {r['label']} — {res.get('error')}"))

        threads = [threading.Thread(target=one, args=(i,), daemon=True) for i in targets]
        for t in threads:
            t.start()
        for t in threads:
            t.join()
        total = (sum(len(per_key.get(i.key, [])) for i in targets) if per_key is not None
                 else len(rows) * len(targets))
        self._ui(lambda: self._send_done(tally["ok"], tally["fail"], total, rtts))

    def _send_done(self, ok, fail, total, rtts=()):
        self.sending = False
        cancelled = self.cancel.is_set()
        self.cancel.clear()
        self._set_send_status("")
        self.log(f"Send finished: {ok}/{total} accepted"
                 + (f", {fail} failed" if fail else "")
                 + (" (cancelled part-way)." if cancelled else "."))
        if rtts:
            # Round-trip as the agent measures it: the okhttp call itself, so it
            # includes minting the PX token and the gateway's own work. The delay
            # throttle is not in here — it is slept BEFORE dispatch, so it overlaps
            # the round-trip rather than adding to it (DOCUMENTATION.md §9).
            s = sorted(rtts)
            self.log(f"    round-trip: median {s[len(s) // 2]} ms, "
                     f"min {s[0]}, max {s[-1]} ms over {len(s)} request(s)"
                     + (f" — throttle {self._delay_ms()} ms sets the floor on cadence."
                        if self._delay_ms() > s[len(s) // 2] else "."))
        if ok and not fail and not cancelled:
            self.sub_status.config(text="—", foreground="gray")
            # The rows are NOT wiped here any more. Each one is marked with its verdict
            # and its sent time, and holds for add_to_cart_information_time so it can be
            # read and documented; _expire_sent_captures drops it after that. Nothing
            # further goes out meanwhile: a sent row is skipped by every send path.
            hold = self._cfg_int("add_to_cart_information_time", 5000)
            self._refresh_captures()
            self.log(f"Sent rows stay listed for {hold} ms with their verdict and sent "
                     f"time, then clear themselves (Settings → "
                     f"add_to_cart_information_time). A sent row is never sent again; "
                     f"saved items still send, the template is kept per instance.")
        elif fail:
            self.log("⚠ Intercepted list kept so you can see what was left and retry.")

    def cancel_send(self):
        """Stop a run after the request currently in flight on each instance."""
        if not self.sending:
            self.log("Nothing to cancel — no send is running.")
            return
        self.cancel.set()
        self._set_send_status("cancelling — finishing the requests already in flight…")
        self.log("Cancelling — each instance stops after its current request.")

    def _set_send_status(self, text):
        self.send_lbl.config(text=(f"◉ {text}" if text else ""))

    def send_item(self, offerId, usItemId, quantity, label=""):
        """One saved item -> one request on every ready instance."""
        if not self._require_active():
            return
        if not offerId or not usItemId:
            messagebox.showwarning("Missing", "offerId and usItemId are required.")
            return
        try:
            q = int(float(quantity))
        except Exception:
            q = 1
        self._start_send([{"offerId": offerId, "usItemId": usItemId,
                           "quantity": max(1, q), "label": label or usItemId}])

    def probe_direct(self):
        """Ask each agent whether it can build and dispatch a request on this build.

        Reports what okhttp discovery resolved (§7) without sending a byte — the
        first thing to look at if sends start failing after an app update.
        """
        if not self._require_active():
            return
        for inst in self.active():
            try:
                r = inst.script.exports_sync.probedirect()
            except Exception as e:
                self.log(f"[{inst.name}] probe failed: {e}")
                continue
            if r.get("ok"):
                tmpl = self._template_for(inst)
                self.log(f"[{inst.name}] ✓ ready — okhttp={r.get('pkg')}, "
                         f"client={r.get('client')}.{r.get('newCall')}, "
                         f"body={'field ' + str(r.get('respBodyField')) if r.get('respBodyField') else 'unreadable'}"
                         + (f", template {self._age(int(time.time() - tmpl['ts']))}."
                            if tmpl else ", but NO template captured on it yet."))
                # Parallel dispatch is optional — a build that hides okhttp's async
                # half still sends, one row at a time. Say which one this is here,
                # rather than at the deadline.
                self.log(f"    parallel dispatch: "
                         + (f"yes — {r.get('newCall')} → {r.get('enqueue')}(), so a timed "
                            f"send's rows go out together, spaced only by the row delay."
                            if r.get("async") else
                            f"NO ({r.get('asyncError')}) — a multi-row timed send falls back "
                            f"to one row at a time, so the round-trip sets their spacing."))
            else:
                self.log(f"[{inst.name}] ✗ cannot send — {r.get('error')}")

    # ---------- scheduled send ----------
    def _cfg_int(self, key, default):
        try:
            return int(float(self.cfg.get(key, default)))
        except Exception:
            return int(default)

    def _peg(self):
        """The fixed anchor the repeat grid hangs off, as an epoch instant today.

        Resolved against today's date every time it is asked for. That is safe
        while the interval divides a day (60 s does): today's noon and tomorrow's
        noon sit on the same grid, so the answer does not jump at midnight.
        """
        lt = time.localtime()
        raw = str(self.cfg.get("schedule_peg", "12:00:00"))
        try:
            parts = [int(x) for x in raw.split(":")] + [0, 0]
            h, m, s = parts[0], parts[1], parts[2]
            if not (0 <= h < 24 and 0 <= m < 60 and 0 <= s < 60):
                raise ValueError
        except (ValueError, IndexError):
            h, m, s = 12, 0, 0
        return time.mktime((lt.tm_year, lt.tm_mon, lt.tm_mday, h, m, s, 0, 0, -1))

    def _repeat_sec(self):
        try:
            return max(0.0, float(self.repeat_entry.get().strip() or 0))
        except ValueError:
            return -1.0          # unparseable; callers report it

    def _sched_delay_ms(self):
        """Throttle for a timed run's follow-up rows, in ms. -1 = unparseable."""
        raw = (self.sched_delay_entry.get().strip()
               if hasattr(self, "sched_delay_entry") else self.cfg.get("schedule_delay_ms", "0"))
        try:
            return max(0, int(float(raw or 0)))
        except ValueError:
            return -1

    def _persist_sched_field(self, key, entry):
        """Write a timed-send field back to config.json, so it survives a restart.

        Deliberately quiet and forgiving: junk is left in the box for the reader that
        already validates it (arming reports a bad value), and only a clean number is
        stored. Nothing here changes what a send does — the entry is still what is
        read at arm time — it only stops the value evaporating on the next launch.
        """
        raw = entry.get().strip()
        try:
            val = str(int(float(raw or 0)))
        except (TypeError, ValueError):
            return
        if self.cfg.get(key) == val:
            return
        self.cfg[key] = val
        save_json(CONFIG_PATH, self.cfg)

    def _nudge_sec(self):
        """Deliberate arrival offset in SECONDS: -ve earlier, +ve later.

        Read from the entry, falling back to config. NaN signals unparseable.
        """
        raw = self.nudge_entry.get().strip() if hasattr(self, "nudge_entry") else None
        if raw is None:
            raw = self.cfg.get("schedule_nudge_ms", "0")
        try:
            return float(raw or 0) / 1000.0
        except ValueError:
            return float("nan")

    def _grid_target(self, peg, repeat, nudge_s, now=None):
        """The next arrival instant: a grid point, moved by the nudge.

        The nudge is applied AFTER the grid point is chosen, never folded into
        the peg, so it cannot compound — every cycle re-derives from the same
        grid. Nudging earlier has to be reserved up front, otherwise a -200 ms
        nudge could pull a target inside the arming window it only just cleared.
        """
        now = time.time() if now is None else now
        floor = self._arm_ms() / 1000.0 + 0.5
        t = next_occurrence(peg, repeat, now, floor + max(0.0, -nudge_s))
        return None if t is None else t + nudge_s

    def _next_arrival(self, repeat=None, nudge_s=None):
        """When the next send would land, or None if there is nothing scheduled."""
        if repeat is None:
            repeat = self._repeat_sec()
        if nudge_s is None:
            nudge_s = self._nudge_sec()
        if repeat < 0 or nudge_s != nudge_s:      # NaN
            return None
        return self._grid_target(self._peg(), repeat, nudge_s)

    def _refresh_next(self):
        """Keep the next-arrival and lead readouts live, armed or not."""
        if self.armed and self.sched_target:
            self.next_lbl.config(text=fmt_clock(self.sched_target, with_day=False),
                                 foreground="#0a7d00")
        else:
            t = self._next_arrival()
            if t is None:
                bad = "bad nudge" if self._nudge_sec() != self._nudge_sec() else (
                      "bad interval" if self._repeat_sec() < 0 else "peg has passed")
                self.next_lbl.config(text=f"—  ({bad})", foreground="#b30000")
            else:
                self.next_lbl.config(text=fmt_clock(t, with_day=False), foreground="gray")
        self.lead_lbl.config(text=self._lead_text())

    def _lead_text(self):
        """How far BEFORE the arrival instant the dispatch goes, and where it comes from.

        Called "calculated delay" in the UI: it is how many ms early the request
        leaves so that it *lands* on the instant, not how long anything waits.

        Shown rather than buried: it is the number that decides whether the send
        lands on the deadline, and every term in it is measured.
        """
        cfg = self._cfg_int("schedule_oneway_ms", 14)
        act = self.active()
        nudge_s = self._nudge_sec()
        tail = ""
        if nudge_s != nudge_s:
            tail = "  ·  nudge: not a number"
        elif nudge_s:
            tail = (f"  ·  nudge {nudge_s * 1000:+.0f} ms "
                    f"({'later' if nudge_s > 0 else 'earlier'})")
        if not act:
            # Show the numbers it WOULD use rather than a bare dash — otherwise the
            # calculated lead looks missing whenever nothing happens to be attached.
            return (f"calculated delay: {4 + cfg:.2f} ms EARLIER = 4.00 preflight "
                    f"+ {cfg:.2f} one way (defaults — connect and send to measure){tail}")
        if len(act) == 1:
            i = act[0]
            pre = i.warm_preflight if i.warm_preflight is not None else 4
            one = i.oneway_ms if i.oneway_ms is not None else cfg
            how = ("measured" if i.oneway_ms is not None and i.warm_preflight is not None
                   else "defaults until the first send measures them")
            return (f"calculated delay: {pre + one:.2f} ms EARLIER = {pre:.2f} preflight "
                    f"+ {one:.2f} one way ({how}){tail}")
        leads = [self._lead_for(i, cfg) for i in act]
        return (f"calculated delay: {min(leads):.2f}–{max(leads):.2f} ms EARLIER across "
                f"{len(act)} instances (preflight + one way, per instance){tail}")

    def _arm_ms(self):
        """How early each agent is handed the deadline, clamped to what it will hold.

        Kept well under AGENT_MAX_HOLD_MS: the value is measured from when the host
        starts the fan-out, and a slow RPC on the last instance must not push it
        over the agent's limit and have the send refused outright.
        """
        return max(200, min(self._cfg_int("schedule_arm_ms", 2000), AGENT_MAX_HOLD_MS - 5000))

    def _measure_device_offset(self, inst, n=9):
        """device clock - host clock, in ms, as the median of n RPC probes.

        Each probe brackets the agent's Date.now() between two host readings and
        takes the midpoint, so a symmetric RPC cancels out. The spread is the
        RPC's own jitter and is reported: it bounds how well this can be known.
        """
        ds = []
        for _ in range(n):
            try:
                t0 = time.time()
                dev = inst.script.exports_sync.nowdev()
                t1 = time.time()
            except Exception:
                continue
            ds.append(dev - (t0 + t1) / 2 * 1000)
        if not ds:
            return None, None
        inst.clock_off_ms = statistics.median(ds)
        return inst.clock_off_ms, max(ds) - min(ds)

    def _measure_ntp(self, force=False, budget=None):
        """Host clock vs true time. Cached for 10 min — it drifts ~1.2 ms/min.

        The scheduled path always forces a fresh reading: at up to 1.2 ms/min a
        10-minute-old value is worth 12 ms of error, which is most of the 18 ms
        lead and the whole ±10 ms jitter budget. It is only worth caching for the
        status line.
        """
        if not force and self.ntp_off_ms is not None and time.time() - self.ntp_at < 600:
            return self.ntp_off_ms
        host = self.cfg.get("ntp_server") or "time.cloudflare.com"
        rtt, off = sntp_offset(host, budget=budget)
        if off is None:
            self._ui(lambda: self.log(f"⚠ clock: {host} unreachable — scheduling uncorrected, "
                                      f"so any error in this PC's clock lands in full."))
            return None
        self.ntp_off_ms, self.ntp_at = off, time.time()
        self._ui(lambda: self.log(
            f"Clock: host is {abs(off):.0f} ms {'BEHIND' if off > 0 else 'AHEAD OF'} true time "
            f"({host}, rtt {rtt:.0f} ms) — corrected out of the deadline."
            + ("\n    ⚠ over 100 ms out. w32time slews sub-second errors instead of stepping "
               "them; DOCUMENTATION.md §9 has the registry fix." if abs(off) > 100 else "")))
        return off

    def _refresh_sched_status(self):
        if self.ntp_off_ms is None:
            txt, col = "clock: measured on every send", "gray"
        else:
            txt = f"clock: host {self.ntp_off_ms:+.0f} ms vs true time"
            col = "#0a7d00" if abs(self.ntp_off_ms) <= 50 else "#b30000"
        devs = [i for i in self.active() if i.clock_off_ms is not None]
        if devs:
            txt += f" · {len(devs)} device clock(s)"
        self.clock_lbl.config(text=txt, foreground=col)
        # The lead has its own readout now — keep it in step with the measurements.
        self.lead_lbl.config(text=self._lead_text())

    def arm_selected_item(self):
        """Schedule the item chosen in 'Selected item' — the usual case."""
        i = self.sub_combo.current()
        if i < 0 or i >= len(self.presets):
            messagebox.showinfo("No item", "Pick a saved item in 'Selected item' first.")
            return
        p = self.presets[i]
        try:
            q = max(1, int(float(self.sub_qty.get())))
        except Exception:
            q = 1
        self._arm([{"offerId": p.get("offerId", ""), "usItemId": p.get("usItemId", ""),
                    "quantity": q, "label": self._nick(p)}])

    def arm_intercepted(self):
        """Schedule the intercepted list as it stands — same rows, and the same
        routing, 'Send requests' would use: every row fires on the cart it was
        intercepted on, not on all six."""
        rows = [{"offerId": c["offerId"], "usItemId": c["usItemId"],
                 "quantity": max(1, int(float(c.get("quantity", 1) or 1))),
                 "cid": c.get("cid"),
                 # which cart this row was intercepted on — what the run is routed by
                 "key": c.get("key"),
                 "inst": c.get("inst"),   # the [tag] the armed-list box shows
                 "label": c.get("nick") or c.get("name") or c["usItemId"]}
                for c in self.captures
                if c.get("offerId") and c.get("usItemId") and not c.get("sent_n")]
        if not rows:
            messagebox.showinfo("Nothing to schedule",
                "No intercepted row has both an offerId and a usItemId.")
            return
        self._warn_untagged(rows)
        per_key = self._per_instance_rows(rows)
        if not per_key:
            messagebox.showinfo("Nothing to schedule",
                "No intercepted row names the account it was intercepted on, and a "
                "row is only ever sent on that account.")
            return
        self._arm(rows, per_key=per_key)

    def _lead_for(self, inst, cfg_oneway):
        """Dispatch lead for one instance: our own work, plus one way on the wire.

        Every term prefers a measurement over a default. preflight comes from the
        warm-up send, one way from Calibrate; either falling back only if that
        instance has never been measured.
        """
        pre = inst.warm_preflight if inst.warm_preflight is not None else 4
        one = inst.oneway_ms if inst.oneway_ms is not None else cfg_oneway
        return pre + one

    def _measure_all(self, targets, warm_ms, arm_ms, cycle):
        """Re-measure everything the aim depends on, before every single send.

        There is no separate calibrate step any more: the host clock, each device
        clock, each instance's preflight and each instance's one way are all taken
        here, every cycle, in the window before the deadline.

        **A failed measurement keeps the previous cycle's value** rather than
        reverting to a config default — that is the point of measuring on a
        repeating schedule. Cycle 1 uses the defaults, cycle 2 uses cycle 1's
        numbers, and a transient failure costs freshness, not aim.
        """
        self._measure_ntp(force=True,
                          budget=max(1.0, min(5.0, (warm_ms - arm_ms) / 1000.0 * 0.3)))
        self._ui(lambda n=len(targets), c=cycle: self.log(
            f"#{c} measuring {n} instance(s): one throwaway send each (item ids that "
            f"resolve to no offer, so nothing can enter a cart) plus a TCP handshake."))
        nping = max(2, self._cfg_int("oneway_samples", 4))

        def probe(inst):
            tmpl = self._template_for(inst)
            # preflight — our own chain plus PX minting, from a real but unacceptable send
            try:
                r = inst.script.exports_sync.warmup(tmpl)
            except Exception as e:
                r = {"ok": False, "error": str(e)}
            t = r.get("timing") or {}
            if r.get("ok"):
                if t.get("preflight") is not None:
                    inst.warm_preflight = t["preflight"]
                if r.get("landed"):
                    self._ui(lambda i=inst: self.log(
                        f"[{i.name}] ⚠ the throwaway send was ACCEPTED — the sentinel resolved "
                        f"to a real offer and IS in that cart. Remove it."))
            else:
                self._ui(lambda i=inst, r=r: self.log(
                    f"[{i.name}] ⚠ probe send failed: {r.get('error')} — keeping the previous "
                    f"preflight."))
            # one way — a bare TCP handshake carries no server work, so it is the
            # network RTT outright. Timed on the DEVICE: the emulator sits behind a
            # BlueStacks NAT hop the host never traverses. First sample pays DNS.
            host = re.sub(r"^https?://([^/]+).*$", r"\1", (tmpl or {}).get("url", ""))
            try:
                p = (inst.script.exports_sync.pingtcp(host, 443, nping + 1) if host
                     else {"ok": False, "error": "no host in the template url"})
            except Exception as e:
                p = {"ok": False, "error": str(e)}
            hs = [x for x in (p.get("rtts") or [])[1:] if x is not None] if p.get("ok") else []
            if hs:
                inst.oneway_ms = statistics.median(hs) / 2.0
            else:
                self._ui(lambda i=inst, p=p: self.log(
                    f"[{i.name}] ⚠ no TCP handshake completed "
                    f"({p.get('error') or 'all attempts failed'}) — keeping the previous "
                    f"one way."))
            wire = (t.get("wireIn") - t.get("wireOut")
                    if t.get("wireIn") is not None and t.get("wireOut") is not None else None)
            self._ui(lambda i=inst, hs=hs, w=wire: self.log(
                f"[{i.name}] preflight {i.warm_preflight if i.warm_preflight is not None else '—'} ms"
                + (f", handshake {statistics.median(hs):.0f} ms" if hs else ", handshake —")
                + (f" -> one way {i.oneway_ms:.0f} ms" if i.oneway_ms is not None else "")
                + (f", wire {w:.0f} ms" if w is not None else "")
                + (f" (of which ~{w - statistics.median(hs):.0f} ms is Walmart's own work, "
                   f"after arrival)" if hs and w is not None else "")))

        ps = [threading.Thread(target=probe, args=(i,), daemon=True) for i in targets]
        for th in ps:
            th.start()
        for th in ps:
            th.join()
        # Clocks last: they drift, so take them as close to the deadline as possible.
        for inst in targets:
            self._measure_device_offset(inst)
        self._ui(self._refresh_sched_status)

    def rehearse(self):
        """Run the whole timed path at the target, with an item that cannot land.

        Same warm-up, same clock measurement, same in-agent hold, same dispatch —
        but carrying SENTINEL_ITEM, so Walmart rejects it and the cart is
        untouched. The arrival error it reports is the real one, which is the only
        way to check aim before it counts.
        """
        self._arm([dict(SENTINEL_ITEM, label="rehearsal")], rehearse=True)

    def _arm(self, rows, rehearse=False, per_key=None):
        if self.armed:
            messagebox.showinfo("Already armed",
                "A send is already counting down — Disarm it first."); return
        if self.sending:
            messagebox.showinfo("Send in flight", "A send is still running."); return
        if not self._require_active():
            return
        peg = self._peg()
        repeat = self._repeat_sec()
        if repeat < 0:
            messagebox.showwarning("Bad interval",
                "'every' must be a number of seconds (0 = fire once)."); return
        sched_delay = self._sched_delay_ms()
        if sched_delay < 0:
            messagebox.showwarning("Bad delay",
                "The Timed send 'row delay' must be a whole number of milliseconds "
                "(0 = no throttle)."); return
        nudge_s = self._nudge_sec()
        if nudge_s != nudge_s:      # NaN
            messagebox.showwarning("Bad nudge",
                "'nudge' must be a number of milliseconds — negative to arrive earlier, "
                "positive to arrive later."); return
        arm_ms = self._arm_ms()
        floor = arm_ms / 1000.0 + 0.5
        if 0 < repeat <= floor:
            messagebox.showwarning("Interval too short",
                f"A {repeat:g}s interval leaves no room to prepare: each send needs "
                f"{floor:.1f}s just to hand the agents the deadline."); return
        target = self._next_arrival(repeat, nudge_s)
        if target is None:
            messagebox.showwarning("Nothing to fire",
                f"The peg ({fmt_clock(peg)}) has passed and 'every' is 0, so there is no "
                f"next arrival. Set an interval, or move schedule_peg in Settings."); return
        human = fmt_clock(target)
        left = target - time.time()
        ready, missing = self._templated()
        for inst in missing:
            self.log(f"[{inst.name}] ✗ will be skipped — no capture from this instance yet.")
        if per_key is not None:
            # An intercepted run is routed by the row's own cart, so an account with
            # nothing of its own in the list takes no part in it — it must not be
            # armed with someone else's adds.
            ready = [i for i in ready if per_key.get(i.key)]
        if not ready:
            if per_key is not None:
                messagebox.showwarning(
                    "Nothing to arm",
                    "No connected account has any unsent rows of its own in the "
                    "list. Every intercepted row is sent on the cart it was "
                    "intercepted on — tick that account and Connect.")
                return
            messagebox.showwarning("No template", self.NO_TEMPLATE); return

        self.armed = True
        self.sched_target, self.sched_label = target, human
        self.sched_cancel.clear()
        sendlog.note_once(self.log)
        every = (f", then every {repeat:g}s pegged to {fmt_clock(peg)[4:]}"
                 if repeat > 0 else " (once)")
        if rehearse:
            self.log(f"Armed a REHEARSAL on {len(ready)} instance(s) for {human}{every} "
                     f"(in {fmt_countdown(left)}). It runs the full timed path with an item "
                     f"Walmart will reject, so nothing can enter a cart.")
        elif per_key is not None:
            total = sum(len(per_key.get(i.key, [])) for i in ready)
            self.log(f"Armed: {total} request(s) over {len(ready)} instance(s) — each "
                     f"account its own intercepted row(s) — to ARRIVE at {human}{every} "
                     f"(in {fmt_countdown(left)}).")
            self.log(f"    Each account's row 1 is its timed one.")
        else:
            self.log(f"Armed: {len(rows)} request(s) × {len(ready)} instance(s) to ARRIVE at "
                     f"{human}{every} (in {fmt_countdown(left)}).")
            self.log(f"    Row 1 is the timed one.")
            if len(rows) > 1:
                # Cumulative offsets off the SAME deadline: row N is aimed at
                # target + (N-1) gaps. The rows are dispatched in parallel — none of
                # them waits on another's reply — so the row delay is the whole of
                # the spacing, and the round-trip is no longer a floor under it.
                offs = ", ".join(f"+{sched_delay * n} ms" for n in range(1, min(len(rows), 4)))
                self.log(f"    Rows 2–{len(rows)} follow cumulatively at {offs}"
                         + (", …" if len(rows) > 4 else "")
                         + f" (row delay {sched_delay} ms)."
                         + ("\n    All rows go out in parallel — the row delay is the only "
                            "thing between them."
                            if sched_delay > 0 else
                            "\n    Row delay is 0, so all rows go out together, in parallel."))
        self.log(f"    Every cycle re-measures both clocks, preflight and one way "
                 f"{self._cfg_int('schedule_warm_ms', 20000) / 1000:.0f}s before its deadline, "
                 f"arms the agents {arm_ms / 1000.0:.1f}s before, then each holds on its own "
                 f"device clock."
                 + (" A failed measurement keeps the previous cycle's value."
                    if repeat > 0 else ""))
        # The armed-list box shows this snapshot and the worker fires the SAME dicts;
        # a rehearsal is a throwaway probe and must not disturb the standing armed list.
        if not rehearse:
            self._set_armed(rows, per_key)
        # Captured now, not read live: a worker thread must not touch tk widgets,
        # and an armed schedule should not silently change under an edit.
        threading.Thread(target=self._schedule_worker,
                         args=(rows, peg, repeat, nudge_s, sched_delay, rehearse,
                               per_key),
                         daemon=True).start()
        self._tick_schedule()

    def disarm(self):
        if not self.armed:
            self.log("Nothing armed."); return
        self.sched_cancel.set()
        self.log("Disarming — the countdown is stopped.")

    def _wait_until(self, t):
        """Sleep to a host-clock instant, waking often enough to notice a disarm.

        Coarse on purpose: the precise wait is the agent's, on the device clock.
        Returns False if the schedule was cancelled.
        """
        while True:
            left = t - time.time()
            if left <= 0:
                return True
            if self.sched_cancel.wait(min(left, 0.2)):
                return False

    def _schedule_worker(self, rows, peg, repeat, nudge_s=0.0, sched_delay=0,
                         rehearse=False, per_key=None):
        """Fire at `peg`, then every `repeat` seconds pegged to it, until disarmed.

        Each target is recomputed from the original peg rather than chained off
        the last one, so a cycle that runs long cannot drag the series late:
        01:00:00 every 60 s stays on 01:01:00, 01:02:00, … `repeat` <= 0 fires
        once and stops.
        """
        cycle = 0
        # The nudge is folded into every target instant before _run_cycle sees it, so
        # the value that moved this run is not otherwise recoverable downstream. Banked
        # here, at arm time, because the entry can be retyped while a series is running
        # and the record has to say what the run was ARMED with, not what the box says
        # when a reply happens to land.
        self.armed_nudge_ms = nudge_s * 1000.0
        try:
            while not self.sched_cancel.is_set():
                target = self._grid_target(peg, repeat, nudge_s)
                if target is None:
                    break
                cycle += 1
                self.sched_target, self.sched_label = target, fmt_clock(target)
                if not self._run_cycle(rows, target, rehearse, cycle, sched_delay,
                                       per_key):
                    break
                if repeat <= 0:
                    break
        finally:
            self.sending = False
            self._ui(self._sched_done)

    def _run_cycle(self, all_rows, target, rehearse, cycle, sched_delay=0,
                   per_key=None):
        """One measure -> arm -> fire -> report pass. Returns False to end the series.

        `per_key` routes an intercepted run: each instance fires the rows IT
        intercepted and nothing else. Without it (a 'Selected item' or a rehearsal)
        every instance fires the same `all_rows`, which is what a timed drop of one
        saved item is.

        The host does all the long waiting; each agent is only handed the deadline
        `schedule_arm_ms` before it, and does the final hold itself. That is what
        keeps the RPC hop out of the critical path — and it also keeps the agents'
        single-threaded runtimes (and so the app) from stalling for more than a
        couple of seconds.
        """
        warm_ms = self._cfg_int("schedule_warm_ms", 20000)
        arm_ms = self._arm_ms()
        oneway = self._cfg_int("schedule_oneway_ms", 14)
        # --- measure: also pays the cold okhttp-discovery and TLS cost now
        if not self._wait_until(target - warm_ms / 1000.0):
            return False
        targets = [i for i in self.active() if self._template_for(i)
                   and (per_key is None or per_key.get(i.key))]
        if not targets:
            self._ui(lambda: self.log("✗ Nothing left to send on — every instance lost its "
                                      "template, lost its own rows, or disconnected. "
                                      "Disarmed."))
            return False
        self._measure_all(targets, warm_ms, arm_ms, cycle)
        if self.sched_cancel.is_set():
            return False

        # --- arm each agent, then let it hold on its own clock
        # Warm-up and clock probes are supposed to finish inside the window. If
        # they didn't, the agents get a deadline that is already close (or past)
        # and the send lands late — say so rather than letting it look clean.
        late = time.time() - (target - arm_ms / 1000.0)
        if late > 0:
            self._ui(lambda l=late: self.log(
                f"⚠ preparation overran the arming point by {l * 1000:.0f} ms — "
                f"agents are being armed late, so this send may not make its deadline."))
        if not self._wait_until(target - arm_ms / 1000.0):
            return self._ui(self._sched_done)
        self.sending = True
        ntp = self.ntp_off_ms or 0.0
        host_deadline = target - ntp / 1000.0   # host-clock instant of true `target`
        results, lock = [], threading.Lock()

        def fire(inst):
            # An intercepted run fires this instance's OWN rows; anything else fires
            # the list it was armed with — see _run_cycle.
            rows = per_key.get(inst.key, []) if per_key is not None else all_rows
            if not rows:
                return
            tmpl = self._template_for(inst)
            if inst.clock_off_ms is None:
                self._ui(lambda i=inst: self.log(
                    f"[{i.name}] ✗ skipped — device clock never measured, so the deadline "
                    f"cannot be converted to its clock."))
                return
            lead = self._lead_for(inst, oneway)
            # The emulator delay moves THIS instance's deadline, and nothing else.
            # Doing it here rather than by sleeping the thread keeps the whole point
            # of the timed path intact: every instance is still handed an absolute
            # instant it holds for on its own clock, so the stagger is as accurate as
            # the deadline itself instead of inheriting the host scheduler's jitter.
            # The row delay is untouched by it — the burst still spaces this
            # instance's own rows from this instance's own deadline.
            emu_off = self._emu_offset_ms(inst, targets)
            dev_deadline = host_deadline * 1000.0 + inst.clock_off_ms + emu_off
            if emu_off:
                self._ui(lambda i=inst, o=emu_off: self.log(
                    f"[{i.name}] aimed {o} ms after the deadline (emulator delay)."))
            # Last possible moment to call it off. Once schedulesend is issued the
            # agent is holding on its own clock and WILL fire — there is no way to
            # recall it, so Disarm has to be checked here rather than after.
            if self.sched_cancel.is_set():
                self._ui(lambda i=inst: self.log(
                    f"[{i.name}] ⊘ disarmed just before dispatch — nothing sent."))
                return
            # More than one row goes out as a BURST: every row in flight at once,
            # spaced only by the row delay. A rehearsal is one sentinel row and has
            # nothing to parallelise, so it keeps the single-send path — as does a
            # build where the agent could not resolve okhttp's async half, which
            # falls back rather than not sending.
            if not rehearse and len(rows) > 1:
                if self._fire_burst(inst, tmpl, rows, dev_deadline, lead,
                                    sched_delay, oneway, results, lock, emu_off):
                    return
            try:
                res = inst.script.exports_sync.schedulesend(
                    tmpl, {"offerId": rows[0]["offerId"], "usItemId": rows[0]["usItemId"],
                           "quantity": rows[0]["quantity"]},
                    int(round(dev_deadline)), round(lead, 2))
                res["oneway_used"] = (inst.oneway_ms if inst.oneway_ms is not None
                                      else oneway)
            except Exception as e:
                res = {"ok": False, "error": str(e)}
            with lock:
                results.append((inst, res, lead))
            self._ui(lambda i=inst, r=res, l=lead:
                     self._log_scheduled(i, r, l, oneway, rehearse))
            # A timed send is a send: it lands in the same box, with the same verdict.
            # A rehearsal is listed too but marked, and its verdict is inverted — the
            # sentinel is meant to be rejected (see _tally).
            # Row 1 of a timed send is aimed AT the deadline, so it carries no row
            # delay of its own — the lead, the nudge and this instance's share of the
            # emulator stagger are the whole of what moved it.
            d1 = self._sched_delays(lead, emu_off, row_ms=0, sched_delay=sched_delay,
                                    what="row 1, aimed at the deadline")
            self._ui(lambda i=inst, r=res, rw=rows[0], d=d1:
                     self._record_sent(
                         i, dict(rw, label=("rehearsal" if rehearse else rw["label"])), r,
                         (not r.get("accepted")) if rehearse else r.get("accepted"),
                         kind="rehearsal" if rehearse else "send", delays=d))
            if rehearse:
                return          # a rehearsal is the one probe, nothing follows it
            # FALLBACK ONLY — reached when the burst could not dispatch. These are
            # ordinary blocking sends, so each row waits on the previous row's reply
            # and the round-trip, not the row delay, sets their spacing.
            if len(rows) > 1:
                # Said here, at the moment it happens, and not only in the one warning
                # further up that a busy log scrolls away: on this path a row delay
                # under the round-trip has NO effect on the spacing, which is the
                # symptom that looks like the row delay being ignored.
                self._ui(lambda i=inst, d=sched_delay: self.log(
                    f"[{i.name}] ⚠ these rows go one after another, so their spacing is "
                    f"max(row delay, round-trip) — a row delay of {d} ms below the "
                    f"~200 ms round-trip will not be what separates them. Only a burst "
                    f"makes the row delay the whole of the gap."))
            for n, row in enumerate(rows[1:], 2):
                if self.cancel.is_set() or self.sched_cancel.is_set():
                    return
                try:
                    # Its OWN throttle, not the bulk one from Selected item.
                    r2 = inst.script.exports_sync.directsend(
                        tmpl, {"offerId": row["offerId"], "usItemId": row["usItemId"],
                               "quantity": row["quantity"]}, sched_delay)
                except Exception as e:
                    r2 = {"ok": False, "error": str(e)}
                ok2 = bool(r2.get("ok") and r2.get("accepted"))
                # Fallback rows are ordinary blocking sends: their real spacing is
                # what the agent's throttle actually slept, which on this path is
                # usually nothing because the previous round-trip already covered the
                # gap. The measurement is recorded, not the setting — the warning
                # logged just above is exactly about the two not being the same.
                d2 = self._sched_delays(
                    lead, emu_off, row_ms=(r2.get("timing") or {}).get("wait"),
                    sched_delay=sched_delay,
                    what=f"row {n}, sequential fallback (burst could not dispatch)")
                self._ui(lambda i=inst, r=row, res=r2, o=ok2, d=d2:
                         self._record_sent(i, r, res, o, delays=d))
                self._ui(lambda i=inst, n=n, r=row, res=r2, o=ok2: self.log(
                    f"[{i.name}] {'✓' if o else '✗'} [{n}/{len(rows)}] {r['label']} "
                    f"— HTTP {res.get('code')}"
                    + (f"\n    {res['detail']}" if not o and res.get("detail") else "")))

        fs = [threading.Thread(target=fire, args=(i,), daemon=True) for i in targets]
        for t_ in fs:
            t_.start()
        for t_ in fs:
            t_.join()
        self.sending = False
        self._ui(lambda c=cycle: self._sched_report(results, oneway, rehearse, c))
        return True

    # How long to keep collecting a burst's replies before giving up on the stragglers.
    # Generous on purpose: every row is already on the wire, and a row still pending
    # here has to be reported as pending rather than quietly dropped.
    BURST_COLLECT_S = 25.0

    def _fire_burst(self, inst, tmpl, rows, dev_deadline, lead, sched_delay,
                    oneway, results, lock, emu_off=0):
        """Every row of one timed send away together, spaced only by the row delay.

        The agent dispatches these through okhttp's async path, so no row waits on the
        one before it: row 1 lands on the deadline and row n is aimed at
        deadline + (n-1) x row delay, whatever the round-trip is doing. Returns False
        if it could not dispatch at all, so the caller can fall back to the old
        one-after-another path rather than send nothing.
        """
        items = [{"offerId": r["offerId"], "usItemId": r["usItemId"],
                  "quantity": r["quantity"]} for r in rows]
        try:
            b = inst.script.exports_sync.burstsend(
                tmpl, items, int(round(dev_deadline)), round(lead, 2), sched_delay)
        except Exception as e:
            b = {"ok": False, "error": str(e)}
        if not b.get("ok"):
            self._ui(lambda i=inst, e=b.get("error"): self.log(
                f"[{i.name}] ⚠ parallel dispatch unavailable ({e}) — falling back to "
                f"sending the rows one after another, so the round-trip sets their "
                f"spacing."))
            return False

        n = int(b.get("n") or len(rows))
        if b.get("perHostRaised"):
            self._ui(lambda i=inst, bb=b: self.log(
                f"[{i.name}] okhttp's per-host limit raised {bb.get('perHostWas')} → "
                f"{bb.get('perHost')} for this burst, so no row had to queue behind "
                f"another."))
        elif b.get("perHost") is not None and b["perHost"] < n:
            self._ui(lambda i=inst, bb=b, n=n: self.log(
                f"[{i.name}] ⚠ okhttp allows only {bb['perHost']} concurrent calls to this "
                f"host and the burst has {n} rows — the extras will leave as earlier ones "
                f"finish, not on their own offsets."))
        if b.get("dispatched", n) < n:
            self._ui(lambda i=inst, bb=b, n=n: self.log(
                f"[{i.name}] ⚠ only {bb.get('dispatched')}/{n} rows were dispatched — "
                f"{bb.get('error')}"))
        t = b.get("timing") or {}
        # The row delay is named on EVERY burst, including 0. It used to be mentioned
        # only when non-zero, so the one case worth diagnosing — a delay you set that
        # arrived as 0 — read exactly like a burst you meant to send together.
        gap = int(b.get("gap") or 0)
        self._ui(lambda i=inst, t=t, n=n, g=gap: self.log(
            f"[{i.name}] burst away: {n} row(s) in flight, row delay {g} ms"
            + (f" (so a span of {g * (n - 1)} ms is expected)" if g
               else " — every row on the wire together")
            + f", dispatched over {t.get('span')} ms, sent {lead:.2f} ms early."))

        # PROOF, measured on the device, that the rows went out together rather than
        # one after another: each row's own dispatch instant as an offset from row 1.
        # With a row delay of 0 these sit within a millisecond or two of each other,
        # because enqueue() returns as soon as the call is handed to okhttp. The old
        # sequential path could not look like this — each row there waited on the
        # previous row's reply, so the ~220 ms round-trip stood between them.
        # Verdict spacing is NOT this number: replies are polled every 50 ms below.
        sa = [s for s in (b.get("sentAt") or []) if s is not None]
        if len(sa) > 1:
            base = sa[0]
            self._ui(lambda i=inst, offs=[float(s) - base for s in sa]: self.log(
                f"[{i.name}]    dispatched at (from row 1): "
                + ", ".join(f"{v:+.0f}" for v in offs) + " ms"))

        # Nothing can come back while the agent is dispatching — that call holds its
        # single JS thread — so the replies are collected here, once it has returned.
        seen, deadline = set(), time.time() + self.BURST_COLLECT_S
        flight = {}      # row -> (dispatch instant, rtt), for the overlap proof below
        while len(seen) < n and time.time() < deadline:
            try:
                got = inst.script.exports_sync.burstresults(b["id"])
            except Exception as e:
                self._ui(lambda i=inst, e=e: self.log(
                    f"[{i.name}] ✗ lost the burst's replies — {e}"))
                break
            if not got.get("ok"):
                break
            for r in got.get("rows") or []:
                if not r.get("done") or r["i"] in seen:
                    continue
                seen.add(r["i"])
                self._collect_burst_row(inst, rows, r, lead, oneway, results, lock, n,
                                        emu_off, gap)
                rt = ((r.get("result") or {}).get("timing") or {}).get("rtt")
                out = ((r.get("result") or {}).get("timing") or {}).get("wireOut")
                if out is None:
                    out = r.get("sentAt")
                if out is not None and rt is not None:
                    flight[r["i"]] = (float(out), float(rt))
            if len(seen) < n:
                time.sleep(0.05)

        for line in self._overlap_report(flight, gap):
            self._ui(lambda i=inst, ln=line: self.log(f"[{i.name}] {ln}"))

        if len(seen) < n:
            self._ui(lambda i=inst, m=n - len(seen): self.log(
                f"[{i.name}] ⚠ {m} row(s) never answered within "
                f"{self.BURST_COLLECT_S:.0f}s — they went out, but their verdict is "
                f"unknown."))
        try:
            inst.script.exports_sync.burstclear(b["id"])
        except Exception:
            pass
        return True

    @staticmethod
    def _overlap_report(flight, gap):
        """Did each row leave BEFORE the row before it was answered? Lines for the log.

        This is the one claim about a burst that the time column cannot make. Rows
        spaced by the row delay look, in a list of times, exactly like rows sent one
        after another — the reader cannot see whether row 2 waited on row 1's reply.
        Here that is measured rather than asserted: row n's dispatch instant against
        row n-1's dispatch instant PLUS its round-trip, both from the device.

        A row that does not overlap is not a fault — a row delay longer than the
        round-trip means you ASKED for them not to overlap — so that case names the
        two numbers instead of warning, because the fix is a setting.
        """
        idx = sorted(flight)
        if len(idx) < 2:
            return []
        over, under, seq_cost = [], [], 0.0
        for a, b in zip(idx, idx[1:]):
            out_a, rtt_a = flight[a]
            out_b, _ = flight[b]
            margin = (out_a + rtt_a) - out_b     # >0 = b left while a was still open
            (over if margin > 0 else under).append((b + 1, abs(margin)))
        for i in idx:
            seq_cost += flight[i][1]
        span = max(flight[i][0] + flight[i][1] for i in idx) - min(flight[i][0] for i in idx)
        rtts = [flight[i][1] for i in idx]

        out = []
        if over:
            out.append("in flight together: "
                       + ", ".join(f"row {r} left {m:.0f} ms before row {r - 1} was answered"
                                   for r, m in over)
                       + f". One after another would have cost {seq_cost:.0f} ms; "
                         f"this run took {span:.0f} ms.")
        if under:
            med = sorted(rtts)[len(rtts) // 2]
            out.append("↔ these rows did NOT overlap — "
                       + ", ".join(f"row {r} left {m:.0f} ms after row {r - 1} was answered"
                                   for r, m in under)
                       + f". That is the row delay ({gap} ms) being longer than the "
                         f"round-trip (~{med:.0f} ms), not the dispatch path: set the "
                         f"row delay below {med:.0f} ms to put them on the wire together.")
        return out

    def _sched_delays(self, lead, emu_off, row_ms, sched_delay, what=""):
        """The four-part delay breakdown for one send on the TIMED path.

        All four axes are live here, which is what makes this path's record different
        from a bulk send's: the calculated lead fires it early so it ARRIVES on the
        deadline, the nudge has already moved the deadline itself, the emulator delay
        moved THIS instance's deadline, and the row delay spaces this instance's own
        rows from there. `armed_nudge_ms` is the value the series armed with, not
        whatever the box currently reads (see _schedule_worker).
        """
        return sendlog.delays(
            calculated_ms=lead, nudge_ms=self.armed_nudge_ms,
            emulator_instance_ms=emu_off, row_ms=row_ms,
            path="cart pane — timed send" + (f" ({what})" if what else ""),
            settings={"row_delay_ms": sched_delay,
                      "emulator_delay_ms": self._emu_delay_ms(),
                      "peg": str(self.cfg.get("schedule_peg", "")),
                      "target_epoch_s": self.sched_target,
                      "target_label": self.sched_label})

    def _collect_burst_row(self, inst, rows, r, lead, oneway, results, lock, n,
                           emu_off=0, gap=0):
        """One row of a burst, reported exactly as the send it is.

        Row 1 is the timed one and reads as it always did. Every later row is timed
        too now — it was aimed at its own offset off the same deadline — so it gets
        the same arrival line rather than a bare status.
        """
        idx = r["i"]
        row = rows[idx] if idx < len(rows) else {"label": f"row {idx + 1}", "quantity": 1}
        res = r.get("result") or {"ok": False, "error": "no result"}
        res["oneway_used"] = (inst.oneway_ms if inst.oneway_ms is not None else oneway)
        # The agent stamped this row's own dispatch instant; carry it so the row's time
        # column is the moment IT went out, not the moment its reply was collected.
        if r.get("sentAt") is not None:
            res.setdefault("sentAt", r["sentAt"])
        ok = bool(res.get("ok") and res.get("accepted"))
        with lock:
            results.append((inst, res, lead))
        # A burst row's row delay is the offset it was AIMED at off this instance's
        # deadline — (i x gap), reported by the agent as timing.offset. That is the
        # real thing on this path: nothing was slept, every row went out together and
        # each held for its own instant, so a measured sleep would read as zero and
        # say nothing about how the rows were spaced.
        t_ = res.get("timing") or {}
        row_ms = t_.get("offset")
        if row_ms is None:
            row_ms = idx * gap
        d = self._sched_delays(lead, emu_off, row_ms=row_ms, sched_delay=gap,
                               what=f"burst row {idx + 1} of {n}")
        self._ui(lambda i=inst, rw=row, rs=res, o=ok, dd=d:
                 self._record_sent(i, rw, rs, o, delays=dd))
        if not res.get("ok"):
            self._ui(lambda i=inst, k=idx, rw=row, rs=res: self.log(
                f"[{i.name}] ✗ [{k + 1}/{n}] {rw['label']} — {rs.get('error')}"))
            return
        t = res.get("timing") or {}
        err = self._arrival_error(t, res["oneway_used"])
        self._ui(lambda i=inst, k=idx, rw=row, rs=res, t=t, e=err, o=ok: self.log(
            f"[{i.name}] {'✓' if o else '✗'} [{k + 1}/{n}] {rw['label']} "
            f"— HTTP {rs.get('code')}"
            + (f", +{t['offset']} ms off the deadline by design" if t.get("offset") else "")
            + (f", arrived {e:+.2f} ms vs that." if e is not None
               else ", arrival not measurable.")
            + (f"\n    {rs['detail']}" if not o and rs.get("detail") else "")))

    def _log_scheduled(self, inst, res, lead, oneway, rehearse=False):
        if not res.get("ok"):
            self.log(f"[{inst.name}] ✗ {'rehearsal' if rehearse else 'scheduled send'} "
                     f"failed — {res.get('error')}")
            return
        t = res.get("timing") or {}
        err = self._arrival_error(t, res.get("oneway_used", oneway))
        skew = t.get("skew")
        # In a rehearsal the verdict is inverted: the sentinel item is SUPPOSED to
        # be rejected, and an accepted one means it reached a real offer and is now
        # in that cart. The timing is equally valid either way.
        good = (not res.get("accepted")) if rehearse else res.get("accepted")
        self.log(f"[{inst.name}] {'✓' if good else '⚠'} "
                 f"{'rehearsal' if rehearse else 'timed send'} — HTTP {res.get('code')}, "
                 f"sent {lead:.2f} ms early"
                 + (f", woke {skew:+.2f} ms off" if skew is not None else "")
                 + (f", arrived {err:+.2f} ms vs the deadline." if err is not None
                    else ", arrival not measurable.")
                 + ("\n    ⚠ the rehearsal was ACCEPTED — the sentinel resolved to a real "
                    "offer and IS in that cart. Remove it." if rehearse and not good else "")
                 + (f"\n    {res.get('detail')}"
                    if not rehearse and not good and res.get("detail") else ""))

    @staticmethod
    def _arrival_error(t, oneway):
        """How far the request actually LANDED from the deadline, in ms.

        okhttp stamps sentRequestAtMillis when the bytes go on the wire, so
        arrival is that plus one way. Both are device-clock ms, and so is the
        deadline the agent was given — the offsets cancel.
        """
        if t.get("wireOut") is None or t.get("deadline") is None:
            return None
        return (t["wireOut"] + oneway) - t["deadline"]

    def _sched_report(self, results, oneway, rehearse=False, cycle=None):
        errs = [e for e in (self._arrival_error(r.get("timing") or {},
                                                r.get("oneway_used", oneway))
                            for _, r, _ in results if r.get("ok")) if e is not None]
        if rehearse:
            landed = sum(1 for _, r, _ in results if r.get("ok") and r.get("accepted"))
            self.log(f"Rehearsal finished at {self.sched_label}: {len(errs)}/{len(results)} "
                     f"request(s) measured"
                     + (f" — ⚠ {landed} ACCEPTED and are in a cart." if landed
                        else ", nothing entered any cart."))
        else:
            ok = sum(1 for _, r, _ in results if r.get("ok") and r.get("accepted"))
            self.log(f"{'#' + str(cycle) + ' ' if cycle else ''}timed send: {ok}/{len(results)} accepted at {self.sched_label}.")
        if errs:
            s = sorted(errs)
            # Each request is scored against ITS OWN deadline — row 1 against the
            # target, row n against target + (n-1) x row delay — so a burst's rows
            # belong in the same spread as a fan-out's instances.
            self.log(f"    arrival vs deadline: median {s[len(s) // 2]:+.2f} ms, "
                     f"min {s[0]:+.2f}, max {s[-1]:+.2f} ms"
                     + (f" — spread {s[-1] - s[0]:.2f} ms across requests."
                        if len(s) > 1 else ".")
                     + "\n    Residual is one-way network jitter (±10 ms) plus whatever this "
                       "PC's clock is still off by; see DOCUMENTATION.md §9.")

    def _sched_done(self):
        self.armed = False
        self.sched_target = None
        self.sched_cancel.clear()
        self.sched_lbl.config(text="")
        self._refresh_next()

    def _tick_schedule(self):
        """Live countdown while armed. Stops itself when the run is over."""
        if not self.armed or self.sched_target is None:
            self.sched_lbl.config(text="")
            return
        left = self.sched_target - time.time()
        self.sched_lbl.config(
            # Countdown only. The instant itself is already on the left of the
            # panel under "next arrival", so repeating it (with a weekday) here
            # was duplication.
            text=f"◉ {fmt_countdown_fine(left)}" if left > 0 else "◉ firing…",
            foreground=("#b30000" if left <= 10 else "#0a7d00"))
        # The sub-second digits only matter near the end, so redraw fast there and
        # slowly far out - a target hours away must not burn thousands of tkinter
        # callbacks an hour to move a digit nobody is watching.
        self.root.after(30 if left <= 10 else 100 if left <= 60 else 1000,
                        self._tick_schedule)

    # ---------- presets ----------
    @staticmethod
    def _nick(p):
        return p.get("nick") or p.get("name") or "item"

    def _save_or_update(self):
        offer = self.e_offer.get().strip(); us = self.e_usitem.get().strip()
        if not offer or not us:
            messagebox.showwarning("Missing", "offerId and usItemId required to save.")
            return
        name = self.e_name.get().strip() or "item"
        p = {"name": name,
             "nick": self.e_nick.get().strip() or name,
             "offerId": offer, "usItemId": us,
             "quantity": self.e_qty.get().strip() or "1"}
        if self.editing_idx is not None and 0 <= self.editing_idx < len(self.presets):
            self.presets[self.editing_idx] = p
            self.log(f"Updated saved item: {p['nick']}")
            self._exit_edit_mode()
        else:
            self.presets.append(p)
            self.log(f"Saved item: {p['nick']}")
        save_json(PRESETS_PATH, self.presets)
        self._refresh_presets()

    def _edit_preset(self, i):
        self.editing_idx = i
        self._fill_editor(self.presets[i])
        self.save_btn.config(text="Update item")
        self.log(f"Editing '{self._nick(self.presets[i])}' — change the Nickname (or any field), then click 'Update item'.")

    def _exit_edit_mode(self):
        self.editing_idx = None
        try:
            self.save_btn.config(text="Save as item")
        except Exception:
            pass

    def del_preset(self, idx):
        if self.editing_idx == idx:
            self._exit_edit_mode(); self._clear_editor()
        del self.presets[idx]
        save_json(PRESETS_PATH, self.presets)
        self._refresh_presets()

    # ---------- UI ----------
    def _build_ui(self):

        # Mode — every mode in the tool, three columns side by side: what happens to an
        # add-to-cart, and what happens to each of the two checkout ops. Side by side
        # rather than stacked because they are peers: you read across to see the whole
        # posture of the tool in one line, instead of down a list.
        modebar = ttk.LabelFrame(self.root, text="Mode", padding=6)
        modebar.pack(fill="x", padx=6, pady=(0, 4))
        self.mode_cols = ttk.Frame(modebar)
        self.mode_cols.pack(fill="x")
        col = mode_column(self.mode_cols, "Add to cart", pad=(0, 14))

        self.mode_combo = ttk.Combobox(
            col, state="readonly", width=28,
            values=[self.MODES[k][0] for k in self.MODE_CHOICES])
        self.mode_combo.set(self.MODES[self.mode_state][0])
        self.mode_combo.pack(side="left")
        self.mode_combo.bind("<<ComboboxSelected>>", lambda e: self._apply_mode())
        # a small colour dot, so the mode in force reads at a glance without
        # having to parse the dropdown text
        self.mode_badge = ttk.Label(col, text="●",
                                    foreground=self.MODE_COLOUR[self.mode_state])
        self.mode_badge.pack(side="left", padx=(6, 0))
        # The operation this column governs, in the same slot the checkout columns use
        # for theirs — so the three descriptions line up instead of one starting high.
        # A substring match: it covers UpdateQuantityLiteMutation (product page, per-item
        # add) and UpdateQuantityMutation (cart quantity change, add-all).
        ttk.Label(col.master, text="UpdateQuantity*", foreground="#6b6b6b",
                  font=("Consolas", 8)).pack(anchor="w")
        self.mode_desc = ttk.Label(col.master, text=self.MODES[self.mode_state][1],
                                   foreground="gray", wraplength=280, justify="left")
        self.mode_desc.pack(fill="x", anchor="w")
        # Held so app.py can hand mode_cols to the checkout half, which adds its two
        # columns beside this one.
        self.modebar = modebar


        # send status — a run is fired and forgotten; this is where it reports in
        sendbar = ttk.Frame(self.root); sendbar.pack(fill="x", padx=12, pady=(0, 2))
        self.send_lbl = ttk.Label(sendbar, text="", foreground="#b30000",
                                  font=("Segoe UI", 9, "bold"))
        self.send_lbl.pack(side="left")
        ttk.Button(sendbar, text="Cancel", command=self.cancel_send).pack(side="right")
        ttk.Button(sendbar, text="Check sending",
                   command=self.probe_direct).pack(side="right", padx=4)

        # Selected item: Apply overwrites the rows already in the intercepted list
        subbar = ttk.LabelFrame(self.root, text="Selected item — Apply overwrites every intercepted add-to-cart with this", padding=6)
        subbar.pack(fill="x", padx=6, pady=(0, 4))
        self.sub_combo = ttk.Combobox(subbar, state="readonly", width=32, values=[]); self.sub_combo.pack(side="left")
        ttk.Label(subbar, text="qty").pack(side="left", padx=(6, 0))
        self.sub_qty = ttk.Spinbox(subbar, from_=1, to=99, width=3); self.sub_qty.set("1"); self.sub_qty.pack(side="left", padx=(2, 6))
        ttk.Button(subbar, text="Apply", command=self._apply_sub).pack(side="left")
        # Add / Edit / ✕ for the selected saved item. These were per-row buttons in the
        # "Saved items" box; with the box gone they act on whichever item this dropdown
        # is showing, which is the same item Apply already acts on.
        ttk.Button(subbar, text="Add", width=5, command=self._add_sub).pack(side="left", padx=(6, 0))
        ttk.Button(subbar, text="Edit", width=5, command=self._edit_sub).pack(side="left", padx=2)
        ttk.Button(subbar, text="✕", width=2, command=self._del_sub).pack(side="left")
        self.sub_status = ttk.Label(subbar, text="—", foreground="gray"); self.sub_status.pack(side="left", padx=8)
        # Named "row delay" rather than "delay" now that there are two of them, and
        # named the same as its counterpart in the timed panel: it is the same axis
        # (rows within ONE emulator) on a different send path, and calling it "delay"
        # in one place and "row delay" in another made them read as unrelated.
        ttk.Label(subbar, text="row delay (ms)").pack(side="left", padx=(12, 0))
        # plain entry, not a spinbox: the useful values are hundreds of ms apart,
        # so step arrows are noise — type the number.
        self.delay_entry = ttk.Entry(subbar, width=7)
        self.delay_entry.insert(0, str(self._delay_ms()))
        self.delay_entry.pack(side="left", padx=2)
        self.delay_entry.bind("<Return>", lambda e: self._apply_delay())
        self.delay_entry.bind("<FocusOut>", lambda e: self._apply_delay())
        # The other axis: the gap between one emulator's first request and the next
        # emulator's. Sitting beside the row delay on purpose — the pair is only
        # understandable as a pair, and it is the same pair in the timed panel below.
        ttk.Label(subbar, text="emulator delay (ms)").pack(side="left", padx=(12, 0))
        self.emu_delay_entry = ttk.Entry(subbar, width=7)
        self.emu_delay_entry.insert(0, str(self._emu_delay_ms()))
        self.emu_delay_entry.pack(side="left", padx=2)
        self.emu_delay_entry.bind("<Return>", lambda e: self._apply_emu_delay())
        self.emu_delay_entry.bind("<FocusOut>", lambda e: self._apply_emu_delay())

        # Timed send: arrive at an instant, on every instance at once. The long wait
        # is the host's; each agent is handed the deadline seconds out and does the
        # final hold on the device's own clock (see SCHEDULING).
        sched = ttk.LabelFrame(
            self.root, text="Timed send — fires so the request ARRIVES at the instant you set",
            padding=6)
        sched.pack(fill="x", padx=6, pady=(0, 4))
        # Three columns side by side so the intercepted-list mirror can span the FULL
        # height of the box, between the schedule controls and the delay fields:
        #   lcol  — schedule controls, three stacked rows (left)
        #   armbox + Remove — the mirror of what "Arm list" fires, full height (middle)
        #   rcol  — nudge / row delay / emulator delay, one per row, lined up with lcol
        # lcol takes the left; rcol pins to the right edge and Remove sits just left of
        # it, so the box ends at the LEFT of the delay fields and stretches to fill
        # everything between. exportselection=False so a pick here does not steal the
        # selection _picked_capture reads off cap_list.
        lcol = ttk.Frame(sched); lcol.pack(side="left", fill="y")
        rcol = ttk.Frame(sched); rcol.pack(side="right", fill="y")
        ttk.Button(sched, text="Remove", command=self._remove_armed_row).pack(side="right", padx=(2, 8))
        armbox = ttk.Frame(sched); armbox.pack(side="left", fill="both", expand=True, padx=(10, 2))
        # No scrollbar (unwanted) - but the box still scrolls: the mouse wheel is bound
        # here, and the arrow keys move through it once it has focus.
        self.armed_list = tk.Listbox(armbox, height=4, font=("Consolas", 8),
                                     exportselection=False, activestyle="dotbox")
        self.armed_list.pack(side="left", fill="both", expand=True)
        self.armed_list.bind("<MouseWheel>", lambda e: (
            self.armed_list.yview_scroll(int(-e.delta / 120), "units"), "break")[1])

        # --- lcol row 1: the target readout, the interval, and the arm/disarm buttons.
        srow = ttk.Frame(lcol); srow.pack(fill="x")
        # The target is not typed any more: the grid is anchored to schedule_peg
        # (12:00:00) and this shows where the next point on it falls.
        ttk.Label(srow, text="next arrival").pack(side="left")
        self.next_lbl = ttk.Label(srow, text="—", width=18, foreground="gray",
                                  font=("Segoe UI", 9, "bold"))
        self.next_lbl.pack(side="left", padx=4)
        ttk.Label(srow, text="every").pack(side="left", padx=(10, 0))
        self.repeat_entry = ttk.Entry(srow, width=5)
        self.repeat_entry.insert(0, str(self._cfg_int("schedule_repeat_sec", 60)))
        self.repeat_entry.pack(side="left", padx=2)
        for ev in ("<KeyRelease>", "<FocusOut>", "<Return>"):
            self.repeat_entry.bind(ev, lambda e: self._refresh_next())
        ttk.Label(srow, text="s (0 = once)", foreground="gray").pack(side="left")
        ttk.Button(srow, text="Arm selected item", command=self.arm_selected_item).pack(side="left", padx=(10, 2))
        ttk.Button(srow, text="Arm list", command=self.arm_intercepted).pack(side="left", padx=2)
        ttk.Button(srow, text="Rehearse", command=self.rehearse).pack(side="left", padx=2)
        ttk.Button(srow, text="Disarm", command=self.disarm).pack(side="left", padx=2)

        # --- lcol row 2: the clock readout.
        crow = ttk.Frame(lcol); crow.pack(fill="x", pady=(3, 0))
        # No Calibrate / Check clocks buttons: both measurements now run inside
        # every cycle, so this is a readout of what the last one found.
        self.clock_lbl = ttk.Label(crow, text="clock: measured on every send", foreground="gray")
        self.clock_lbl.pack(side="left")
        # The live time-left countdown rides the same line as the clock readout now,
        # just to its right, at millisecond precision.
        self.sched_lbl = ttk.Label(crow, text="", font=("Segoe UI", 9, "bold"))
        self.sched_lbl.pack(side="left", padx=10)

        # --- lcol row 3: the calculated-delay readout.
        lrow = ttk.Frame(lcol); lrow.pack(fill="x", pady=(3, 0))
        self.lead_lbl = ttk.Label(lrow, text="calculated delay: —", foreground="gray")
        self.lead_lbl.pack(side="left")

        # --- rcol: the three delay fields, one per row so they line up with lcol.
        # Nudge: move the arrival off the grid point on purpose. Negative lands
        # earlier, positive later. Independent of the lead, which aims AT the point.
        nrow = ttk.Frame(rcol); nrow.pack(fill="x")
        ttk.Label(nrow, text="ms").pack(side="right")
        self.nudge_entry = ttk.Entry(nrow, width=6)
        self.nudge_entry.insert(0, str(self._cfg_int("schedule_nudge_ms", 0)))
        self.nudge_entry.pack(side="right", padx=2)
        ttk.Label(nrow, text="nudge (− earlier / + later)").pack(side="right")
        for ev in ("<KeyRelease>", "<FocusOut>", "<Return>"):
            self.nudge_entry.bind(ev, lambda e: self._refresh_next())
        # ...and REMEMBER it. Both timed-send fields used to be seeded from config at
        # startup and never written back, so a value you typed was silently lost on
        # the next launch and the box came back at 0 — indistinguishable from the
        # setting not working. The bulk delay beside Selected item always persisted;
        # these two now do the same.
        for ev in ("<FocusOut>", "<Return>"):
            self.nudge_entry.bind(ev, lambda e: self._persist_sched_field(
                "schedule_nudge_ms", self.nudge_entry), add="+")

        # This panel's own throttle. Separate from the bulk 'delay (ms)' next to
        # Selected item, and it never touches the timed row — only what follows it.
        drow = ttk.Frame(rcol); drow.pack(fill="x", pady=(3, 0))
        ttk.Label(drow, text="ms").pack(side="right")
        self.sched_delay_entry = ttk.Entry(drow, width=6)
        self.sched_delay_entry.insert(0, str(self._cfg_int("schedule_delay_ms", 0)))
        self.sched_delay_entry.pack(side="right", padx=2)
        ttk.Label(drow, text="row delay (rows 2+ of one emulator)").pack(side="right")
        for ev in ("<FocusOut>", "<Return>"):
            self.sched_delay_entry.bind(ev, lambda e: self._persist_sched_field(
                "schedule_delay_ms", self.sched_delay_entry), add="+")

        # The second axis. This one is shared with the bulk send path — there is one
        # emulator delay in the tool, because it describes the fan-out and not a
        # particular send path.
        erow = ttk.Frame(rcol); erow.pack(fill="x", pady=(3, 0))
        ttk.Label(erow, text="ms").pack(side="right")
        self.sched_emu_entry = ttk.Entry(erow, width=6)
        self.sched_emu_entry.insert(0, str(self._emu_delay_ms()))
        self.sched_emu_entry.pack(side="right", padx=2)
        ttk.Label(erow, text="emulator delay (instance 2+)").pack(side="right")
        for ev in ("<FocusOut>", "<Return>"):
            self.sched_emu_entry.bind(ev, lambda e: self._sync_emu_delay())

        mid = ttk.Frame(self.root, padding=6); mid.pack(fill="both", expand=True)

        # This row is three boxes: intercepted | sent | editor. The editor is built and
        # packed FIRST even though it sits on the right, because pack allocates in
        # packing order and it is the one box that must not be squeezed — its entries
        # are fixed-width and clip rather than reflow, so at a narrow window width it
        # would lose the right-hand end of every field. Packed first with side="right"
        # it takes its natural width off the top and the two lists share what is left;
        # they shrink gracefully, and a clipped row is one double-click from the log.
        #
        # The editor is here at all because the "Saved items" box that used to hold this
        # column was a second view of the same list the "Selected item" dropdown already
        # shows. What that box carried and the dropdown did not — Add, Edit and delete
        # for one saved item — moved onto that bar rather than being dropped. Sitting
        # beside the intercepted list is also where the editor wants to be: you click a
        # captured row on the left and it fills in over here.
        ed = ttk.LabelFrame(mid, text="Item — edit / save", padding=8)
        ed.pack(side="right", fill="y", padx=(4, 0))
        self.e_nick = self._field(ed, "Nickname (shown in Selected item)", 0, width=32)
        self.e_name = self._field(ed, "Name (real product)", 1, width=32)
        self.e_offer = self._field(ed, "offerId (seller)", 2, width=32)
        self.e_usitem = self._field(ed, "usItemId (product)", 3, width=32)
        self.e_qty = self._field(ed, "Quantity", 4, width=8)
        btns = ttk.Frame(ed); btns.grid(row=5, column=0, columnspan=2, pady=6, sticky="w")
        self.save_btn = ttk.Button(btns, text="Save as item", command=self._save_or_update)
        self.save_btn.pack(side="left")
        ttk.Button(btns, text="Clear", command=self._clear_editor).pack(side="left", padx=6)

        # left: captures. The title carries the send tally rather than the old
        # "(last 6, all instances)" note — the cap and the fan-out it described are
        # both gone (one connection, and the 6 is visible by counting the rows),
        # whereas how many sends landed was previously only in the log.
        self.cap_frame = ttk.LabelFrame(mid, text=self._cap_title(), padding=6)
        left = self.cap_frame
        left.pack(side="left", fill="both", expand=True, padx=(0, 4))
        # Monospaced on purpose: the row carries a right-hand status column and
        # the default proportional font would not line it up.
        self.cap_list = tk.Listbox(left, height=10, font=("Consolas", 9))
        self.cap_list.pack(fill="both", expand=True)
        self.cap_list.bind("<<ListboxSelect>>", self._on_pick_capture)
        capbtns = ttk.Frame(left); capbtns.pack(fill="x", pady=(4, 0))
        ttk.Button(capbtns, text="Send requests", command=self._send_requests).pack(side="left")
        ttk.Button(capbtns, text="Clear all", command=self._clear_captures).pack(side="left", padx=4)
        ttk.Button(capbtns, text="Remove", command=self._remove_selected_capture).pack(side="left")
        # Says what "Send requests" does, because it is no longer a choice: every row
        # goes back to the cart it was intercepted on. This was a tickbox that
        # defaulted to broadcasting the whole list to all six accounts, which is not
        # what intercepting six carts' adds meant.
        ttk.Label(capbtns, text="each row → its own account",
                  foreground="#555").pack(side="left", padx=(10, 0))

        # middle: what came back. One row per request we sent, ✓/✗ on Walmart's own
        # verdict (2xx AND no GraphQL "errors" array — a rejected add comes back as a
        # 200, so the status line alone would score it as a success).
        res = ttk.LabelFrame(mid, text="Sent requests — Walmart's verdict", padding=6)
        res.pack(side="left", fill="both", expand=True, padx=4)
        # Monospaced like the intercepted list: the [instance] tag and the row
        # columns only line up in a fixed-width font.
        self.sent_list = tk.Listbox(res, height=10, font=("Consolas", 9))
        self.sent_list.pack(fill="both", expand=True)
        # The list is one line per request so a run reads as a run. The full reply —
        # url and the whole body — goes to the log on a double-click, which is where
        # the room for it is.
        self.sent_list.bind("<Double-Button-1>", self._explain_sent)
        sentbtns = ttk.Frame(res); sentbtns.pack(fill="x", pady=(4, 0))
        ttk.Button(sentbtns, text="Clear", command=self._clear_sent).pack(side="left")
        ttk.Label(sentbtns, text="double-click a row for the full reply",
                  foreground="gray").pack(side="left", padx=6)

        self._refresh_presets()
        self._refresh_instances()

    def _field(self, parent, label, row, width=60):
        ttk.Label(parent, text=label).grid(row=row, column=0, sticky="e", padx=4, pady=2)
        e = ttk.Entry(parent, width=width); e.grid(row=row, column=1, sticky="w", padx=4, pady=2)
        return e






    # Intercepted rows kept PER EMULATOR, not across all of them. The cap used to be a
    # flat six, which was right when one instance could be attached and wrong the
    # moment six can: six accounts adding two items each would evict four accounts'
    # rows before you ever looked at the list, and the ones evicted would be the
    # earliest instances — exactly the accounts already set up and waiting.
    CAP_PER_INSTANCE = 6

    def _trim_captures(self):
        """Keep the newest CAP_PER_INSTANCE rows of EACH instance, order preserved."""
        kept, seen = [], {}
        for c in self.captures:
            k = c.get("key") or c.get("inst") or "?"
            seen[k] = seen.get(k, 0) + 1
            if seen[k] <= self.CAP_PER_INSTANCE:
                kept.append(c)
        self.captures = kept

    def _refresh_captures(self):
        """Redraw the intercepted list — one flat newest-first column, every row
        naming its own emulator.

        The rows used to be grouped into a block per emulator under a `[name]` rule.
        That put the name above the rows instead of on them, so a row copied into the
        log or read on its own had nothing saying whose cart it was, and the newest
        add in the box was not the top line — it was the top line of whichever block
        its emulator happened to sit in. The instance tag now rides the row, right of
        the age, the way the sent-request rows already carry theirs.

        A list line is still not a capture — a row can take more than one line — so
        `_cap_rows` maps line -> index in self.captures.
        """
        self.cap_list.delete(0, "end")
        self._cap_rows = []
        for n, c in enumerate(self.captures):
            age = int(time.time() - c["ts"])
            mark = "→" if c.get("overwritten") else " "   # row was replaced by Apply
            status, colour = self._cap_status(c)
            # The nickname REPLACES the name once one is applied: it is what you typed
            # to identify this row, so it is what the row should say.
            label = (c.get("nick") or c.get("name") or "")[:30]
            # Sent time sits right of the quantity, and carries milliseconds: a burst
            # is documented by these, and whole seconds would hide the whole point.
            # Padded OUTSIDE the brackets, not inside: `[Pie64]` is the same token the
            # call boxes and the log write, and `[Pie64    ]` reads as a different one.
            # The padding is still there — the columns right of it have to line up.
            tag = f"[{(c.get('inst') or '?')[:10]}]"
            self.cap_list.insert("end",
                f"  {self._age_short(age):>4} {mark} {tag:<13}"
                f"{label:<30} q{c['quantity']:<3} {c.get('sent_at', ''):<13}{status}")
            if colour:
                self.cap_list.itemconfig(self.cap_list.size() - 1, foreground=colour)
            self._cap_rows.append(n)

    def _picked_capture(self):
        """The capture the selected line belongs to, as (index, capture) — or None.

        A line is not a row — `_cap_rows` says which capture the clicked line belongs
        to, rather than trusting the offset.
        """
        sel = self.cap_list.curselection()
        if not sel or sel[0] >= len(self._cap_rows):
            return None
        n = self._cap_rows[sel[0]]
        if n is None or n >= len(self.captures):
            return None
        return n, self.captures[n]

    def _cap_status(self, c):
        """The right-hand column: what happened to this row when it was sent.

        Blank until the row has actually been sent, so the column is empty on a
        freshly intercepted list and fills in as the verdicts land. The verdict is
        Walmart's own (2xx AND no GraphQL "errors" array), which is why a rejected
        add can carry a 200 — see _record_sent.
        """
        if not c.get("sent_n"):
            return "", ""
        if not c.get("sent_reached"):
            return "✗ NOT SENT", "red"        # never left the device
        code = c.get("sent_code") or ""
        many = f" ×{c['sent_n']}" if c["sent_n"] > 1 else ""
        if c.get("sent_good"):
            return f"✓ SENT {code}{many}".rstrip(), "#0a7a0a"
        return f"✗ REJECTED {code}{many}".rstrip(), "red"

    @staticmethod
    def _stamp(t):
        """A send instant as a clock time, to the millisecond.

        One formatter for both boxes: the intercepted row's time column and the Sent
        requests row are the same instant seen twice, so they have to render the same
        or they look like two different events.
        """
        return time.strftime("%H:%M:%S", time.localtime(t)) + f".{int((t % 1) * 1000):03d}"

    @staticmethod
    def _sent_instant(inst, res):
        """Host-clock epoch ms this request actually went out, or None.

        The intercepted row's time column used to be stamped when the HOST recorded
        the verdict. For a burst that is when the reply was COLLECTED — quantised by
        the 50 ms poll — so every row read as the same instant and neither the row
        delay nor the nudge could move it, however well either was working.

        The device measures the real thing: okhttp's sentRequestAtMillis (wireOut),
        stamped as the bytes go on the wire, or failing that the dispatch instant.
        Both are DEVICE-clock ms, so they are shifted onto the host clock with the
        offset already measured for this instance. With no offset measured a device
        instant is not comparable to host time at all, so it is refused rather than
        shown wrong.
        """
        t = res.get("timing") or {}
        dev = t.get("wireOut")
        if dev is None:
            dev = res.get("sentAt")
        off = getattr(inst, "clock_off_ms", None)
        if dev is None or off is None:
            return None
        try:
            return float(dev) - float(off)
        except (TypeError, ValueError):
            return None

    def _matching_captures(self, row):
        """The intercepted row(s) one send belongs to. ONE of them, wherever possible.

        It used to match on (offerId, usItemId) and mark EVERY row that carried the
        pair. That pair is not an identity: adding one product three times gives three
        intercepted rows that are identical under it, which is what a demo list
        normally looks like. One send then ticked all three at once, and since the
        stamp is written once and never rewritten they all kept the FIRST row's
        instant — so the list showed one time for the whole run, ticked in lockstep,
        while Sent requests showed the same run correctly spaced. The row delay was
        working; only this could not show it.

        A row built from a capture carries that capture's `cid`, so it marks exactly
        the row it came from. Rows that carry no cid — a saved item sent from
        'Selected item' — still fall back to the pair, but take the first UNSENT
        match rather than all of them, so nothing ticks in lockstep either way.
        """
        cid = (row or {}).get("cid")
        if cid is not None:
            return [c for c in self.captures if c.get("cid") == cid]
        oid, uid = (row or {}).get("offerId"), (row or {}).get("usItemId")
        if not oid or not uid:
            return []
        same = [c for c in self.captures
                if c.get("offerId") == oid and c.get("usItemId") == uid]
        unsent = [c for c in same if not c.get("sent_n")]
        return (unsent or same)[:1]

    def _mark_capture_sent(self, row, res, good, sent_ms=None):
        """Tag the intercepted row a send was built from with its verdict.

        A row sent on several instances marks the same capture once per instance, so
        the count is kept and shown — one row, N sends. One failure among them makes
        the row read as failed, because a row that did not land everywhere did not
        land. Which row that is, is _matching_captures' problem.
        """
        hit = False
        for c in self._matching_captures(row):
            c["sent_n"] = c.get("sent_n", 0) + 1
            c["sent_good"] = bool(good) and c.get("sent_good", True)
            c["sent_reached"] = bool(res.get("ok")) and c.get("sent_reached", True)
            c["sent_code"] = res.get("code")
            # STAMPED ONCE, by the first send of this row — never rewritten.
            # A row can be marked again (a second instance, a repeat cycle, a
            # re-send), and rewriting the stamp each time would make the column
            # tick under you and, worse, restart the display window every time,
            # so a row being re-sent would never age out. The time you documented
            # has to be the time it says an hour later.
            if not c.get("sent_ts"):
                # The device's instant when we have one; the host clock only as a
                # last resort, and then it is the record time, not the send time.
                now = (sent_ms / 1000.0) if sent_ms else time.time()
                c["sent_ts"] = now      # also starts this row's display window
                c["sent_at"] = self._stamp(now)
            hit = True
        if hit:
            self._refresh_captures()

    # ---------- sent requests: the per-request verdict ----------
    # `accepted` comes from the agent and means 2xx AND no GraphQL "errors" array
    # (DOCUMENTATION.md §"A rejected add returns HTTP 200"). Everything here just
    # keeps and renders that verdict; none of it decides anything.

    # Kept PER EMULATOR, like the intercepted list. A flat cap shared between six
    # instances lets the busiest one evict the rows of the quietest, and the quiet one
    # is usually the account whose verdict you are looking for.
    SENT_MAX = 200      # plenty for a session; keeps a long repeat run bounded

    def _tally(self):
        """(total, successful, unsuccessful) over real sends.

        Rehearsals are excluded on purpose: a rehearsal carries sentinel ids that
        resolve to no offer, so it is SUPPOSED to be rejected and counting it either
        way would misreport whether adds are landing. They are still listed, marked.
        """
        real = [r for r in self.sent if r["kind"] == "send"]
        good = sum(1 for r in real if r["good"])
        return len(real), good, len(real) - good

    def _cap_title(self):
        total, good, bad = self._tally()
        if not total:
            return "Intercepted add-to-cart — nothing sent yet"
        return (f"Intercepted add-to-cart — {total} sent: "
                f"{good} successful, {bad} unsuccessful")

    def _record_sent(self, inst, row, res, good, kind="send", delays=None):
        """Keep one send's outcome. UI thread only — callers marshal via _ui.

        The row's time is the SEND instant (_sent_instant), the same one the
        intercepted row is stamped with — not the moment this verdict was recorded.
        For a burst the record instant is when the reply was COLLECTED, quantised by
        the 50 ms burstresults poll, so every row of a run read as one instant here
        and neither the row delay nor the nudge could move it. The host clock is the
        fallback only, for a send whose device instant is unmeasurable; `measured`
        carries which one it is so the box can mark it rather than imply a precision
        it does not have.
        """
        t = res.get("timing") or {}
        sent_ms = self._sent_instant(inst, res)
        ts = (sent_ms / 1000.0) if sent_ms else time.time()
        self.sent.insert(self._sent_slot(ts), {
            "ts": ts, "measured": sent_ms is not None,
            "inst": getattr(inst, "name", "?"), "kind": kind,
            "label": (row or {}).get("label") or "—",
            "qty": (row or {}).get("quantity", ""),
            # `good` is the mark: for a send it IS accepted, for a rehearsal it is the
            # inverse (a sentinel that lands is a problem). `accepted` is kept
            # separately because the row's right-hand column reports what Walmart
            # actually said, which for a well-behaved rehearsal is a rejection.
            "good": bool(good), "accepted": bool(res.get("accepted")),
            # ok=False is ours (frida/transport threw); ok=True with accepted=False is
            # Walmart's. The box distinguishes them, because they need different fixes.
            "reached": bool(res.get("ok")),
            "code": res.get("code"), "rtt": t.get("rtt", res.get("rtt")),
            "detail": res.get("detail"), "url": res.get("url"),
            "error": res.get("error"),
        })
        self._trim_sent()
        self._refresh_sent()
        # …and to disk, on receipt. The box above holds SENT_MAX rows per instance and
        # dies with the app; this run has to be readable afterwards, so the same
        # verdict — with the delay breakdown and the whole reply — is appended to the
        # sent-request log as well. _trim_sent has just discarded rows from the box;
        # the file keeps them.
        self._write_send_record(inst, row, res, good, kind, delays, sent_ms)
        # The same verdict, shown again on the intercepted row it came from, so the
        # list you are watching says what happened to each row. A rehearsal is skipped:
        # it carries the row's ids but a sentinel item was sent, not this row.
        if kind != "rehearsal":
            self._mark_capture_sent(row, res, good, sent_ms)

    def _write_send_record(self, inst, row, res, good, kind, delays, sent_ms):
        """Append one dispatched add-to-cart to the sent-request log.

        The send instant is the device's own (`_sent_instant`) wherever it could be
        measured — for a burst that is the only instant that distinguishes the rows,
        since they are COLLECTED in a 50 ms poll and would otherwise all record as one
        moment. The receipt instant is derived as send + round-trip for the same
        reason, and falls back to now only when one of the two is unknown; which of
        the two it is rides in the record rather than being left to be assumed.

        Never raises: a send is not worth failing over its own bookkeeping.
        """
        try:
            t = res.get("timing") or {}
            rtt = t.get("rtt", res.get("rtt"))
            recv_ms = None
            if sent_ms is not None and rtt is not None:
                try:
                    recv_ms = float(sent_ms) + float(rtt)
                except (TypeError, ValueError):
                    recv_ms = None
            sendlog.record(
                tool="cart", op=res.get("op") or "add-to-cart", stage=kind,
                kind=kind, instance=inst,
                item=(row or {}).get("label"), quantity=(row or {}).get("quantity"),
                sent_at_ms=sent_ms, received_at_ms=recv_ms,
                sent_measured=sent_ms is not None,
                delay=delays if delays is not None else sendlog.delays(
                    path="cart pane — send with no recorded delay context"),
                request={"url": res.get("url"),
                         "offerId": (row or {}).get("offerId"),
                         "usItemId": (row or {}).get("usItemId"),
                         "quantity": (row or {}).get("quantity"),
                         "label": (row or {}).get("label"),
                         "sent_item": res.get("sentItem"),
                         "interceptors": res.get("interceptors")},
                response={"reached": bool(res.get("ok")),
                          "http_code": res.get("code"),
                          "http_accepted": bool(res.get("accepted")),
                          "accepted": bool(res.get("accepted")),
                          "graphql_errors": bool(res.get("gqlErrors")),
                          # `good` is the mark the box shows, which for a rehearsal is
                          # the INVERSE of accepted — a sentinel that lands is a
                          # problem. Kept under its own name so the file never reads
                          # as if Walmart had accepted a rehearsal it rejected.
                          "marked_good": bool(good),
                          "rtt_ms": rtt,
                          "received_time_derived": recv_ms is not None,
                          "url": res.get("url"),
                          "body": res.get("detail"),
                          "error": res.get("error"),
                          "timing": t,
                          "raw": res},
                log=self.log)
        except Exception as e:
            self.log(f"⚠ sent-request log skipped for this row — {e}")

    def _trim_sent(self):
        """Keep the newest SENT_MAX rows of each instance, order preserved."""
        kept, seen = [], {}
        for r in self.sent:
            k = r.get("inst") or "?"
            seen[k] = seen.get(k, 0) + 1
            if seen[k] <= self.SENT_MAX:
                kept.append(r)
        self.sent = kept

    def _sent_slot(self, ts):
        """Where a row with send instant `ts` belongs — the list is newest-sent first.

        Rows are RECORDED in the order their replies came back, which for a burst is
        whatever order Walmart answered in, not the order they went out. Ordering the
        box by the send instant instead puts a run in the order it was actually sent,
        so the time column reads monotonically down the box. A tie keeps the newer
        record first, which is what plain insert(0) did on the sequential paths.
        """
        for i, r in enumerate(self.sent):
            if r["ts"] <= ts:
                return i
        return len(self.sent)

    def _refresh_sent(self):
        """Redraw the box. A failed request takes a second, indented line for its
        reason, the way the log writes one — the reason is the whole point of the row
        and this column is not wide enough to hold it on the end. So a list line is
        not a request: `self._sent_rows` maps line -> index in self.sent, which is
        what the double-click reads.
        """
        self.sent_list.delete(0, "end")
        self._sent_rows = []
        # One flat column in send order — newest sent first — so a burst's spacing
        # reads straight down the time column instead of restarting once per emulator.
        # Whose send it was rides the row, in the [instance] tag right of the time.
        for i, r in enumerate(self.sent):
            if r["kind"] == "rehearsal":
                mark, colour = "⊙", "gray"
            elif r["good"]:
                mark, colour = "✓", "#1a7f37"
            else:
                mark, colour = "✗", "#b3261e"
            # To the millisecond, and only because of what this column is for: a row
            # delay is 100–300 ms and a nudge can be tens, so at second resolution a
            # burst's rows read as one instant even when the instants are right. A
            # time we could not measure is marked `~` rather than shown to a
            # precision it does not have — it is the record instant, not the send.
            when = self._stamp(r["ts"]) + ("" if r.get("measured") else "~")
            qty = f" ×{r['qty']}" if r["qty"] else ""
            head = (f"  {mark} {when} [{r['inst'][:10]}] {r['label'][:22]}{qty}"
                    + (f"  {r['code']}" if r["code"] is not None else "")
                    + (f" · {r['rtt']} ms" if r["accepted"] and r["rtt"] else ""))
            lines = [head]
            if not r["reached"]:
                # Never got to Walmart, so there is no verdict — ours failed, and the
                # exception says where. Different problem, different fix.
                lines.append(f"        not sent — {(r['error'] or 'error')[:60]}")
            elif not r["accepted"]:
                # Walmart's own words. The status line is 200 on a rejection, so this
                # text is the only thing that says what was actually wrong.
                lines.append(f"        {self._first_error(r['detail'])}")
            for ln in lines:
                self.sent_list.insert("end", ln)
                self.sent_list.itemconfig(self.sent_list.size() - 1, foreground=colour)
                self._sent_rows.append(i)
        self.cap_frame.config(text=self._cap_title())

    @staticmethod
    def _first_error(detail):
        """Walmart's own first error message, for the one-line row."""
        if not detail:
            return "rejected"
        m = re.search(r'"message"\s*:\s*"([^"]{1,80})', detail)
        return m.group(1) if m else "graphql errors"

    def _explain_sent(self, _evt=None):
        """Double-click: put the whole reply in the log, where there is room for it."""
        sel = self.sent_list.curselection()
        if not sel or sel[0] >= len(self._sent_rows):
            return
        n = self._sent_rows[sel[0]]     # a line is not a request — see above
        if n is None:
            return
        r = self.sent[n]
        head = ("✓ accepted" if r["good"] else
                ("✗ rejected by Walmart" if r["reached"] else "✗ never sent"))
        self.log(f"— sent request: [{r['inst']}] {r['label']} "
                 f"{self._stamp(r['ts'])}"
                 + ("" if r.get("measured") else " (recorded, not measured)")
                 + f" — {head}"
                 + (f", HTTP {r['code']}" if r["code"] is not None else "")
                 + (f", {r['rtt']} ms" if r["rtt"] else "")
                 + (f"\n    url: {r['url']}" if r.get("url") else "")
                 + (f"\n    {r['error']}" if r.get("error") else "")
                 + (f"\n    {r['detail']}" if r.get("detail") else ""))

    def _clear_sent(self):
        self.sent = []
        self._refresh_sent()

    def _tick_ages(self):
        if self.captures:
            self._expire_sent_captures()
            self._refresh_captures()
        self._refresh_next()
        self.root.after(1000, self._tick_ages)

    def _expire_sent_captures(self):
        """Drop rows whose post-send display window has run out.

        A sent row stays listed on purpose — its verdict and its sent time are what
        you read off the screen, and they used to be wiped the instant a clean run
        landed. It must not stay for good either: an intercepted list still holding
        sent rows is one click from adding them a second time. So the row is held for
        Settings -> add_to_cart_information_time (ms) and then drops off. 0 holds it
        indefinitely; a sent row is excluded from any further run either way.
        """
        hold = self._cfg_int("add_to_cart_information_time", 5000) / 1000.0
        if hold <= 0:
            return False
        now = time.time()
        keep = [c for c in self.captures
                if not c.get("sent_ts") or (now - c["sent_ts"]) < hold]
        if len(keep) == len(self.captures):
            return False
        self.captures = keep
        return True

    @staticmethod
    def _age_short(s):
        """Age with no "ago" — the column is narrow and every row is an age."""
        if s < 60: return f"{s}s"
        if s < 3600: return f"{s//60}m"
        return f"{s//3600}h"

    @staticmethod
    def _age(s):
        if s < 60: return f"{s}s ago"
        if s < 3600: return f"{s//60}m ago"
        return f"{s//3600}h ago"

    def _send_requests(self):
        """Send every intercepted add-to-cart, one request per row.

        Deliberately dumb: it sends the list as it stands. Whether a row is what the
        app originally added or was overwritten by 'Selected item → Apply' makes no
        difference here — a row is a request.

        A row carries only the ITEM. Which captured request it is built from is
        decided per instance at send time (_template_for), because the cartId in a
        template belongs to one instance's cart.
        """
        if not self._require_active():
            return
        if not self.captures:
            # The list is emptied once a clean run lands, so this is also the guard
            # that stops a second run going out before anything new is intercepted.
            messagebox.showinfo("Nothing intercepted",
                "No intercepted add-to-carts to send.\n\n"
                "Add items in the app (Grab or Hold mode) to intercept some first."); return
        # Snapshot now: captures can change under us while the run is in flight.
        rows, skipped = [], 0
        for c in self.captures:
            if c.get("sent_n"):
                # Still listed only so its verdict can be read; sending it again would
                # add it to the cart twice. This is the guard the instant wipe used to be.
                continue
            if not c.get("offerId") or not c.get("usItemId"):
                skipped += 1        # a row we couldn't parse IDs out of is unsendable
                continue
            try:
                q = int(float(c.get("quantity", 1)))
            except Exception:
                q = 1
            rows.append({"offerId": c["offerId"], "usItemId": c["usItemId"],
                         "quantity": max(1, q), "cid": c.get("cid"),
                         # which cart this row was intercepted on — what 'own rows
                         # only' regroups by, and meaningless before six could attach
                         "key": c.get("key"),
                         "label": c.get("nick") or c.get("name") or c["usItemId"]})
        if skipped:
            self.log(f"⚠ Skipping {skipped} intercepted row(s) with no offerId/usItemId.")
        if not rows:
            messagebox.showwarning("Nothing sendable",
                "None of the intercepted rows have both an offerId and a usItemId."); return
        self._warn_untagged(rows)
        self._start_send(rows, self._per_instance_rows(rows))

    def _per_instance_rows(self, rows):
        """{instance key: its own rows} — how every intercepted run is routed.

        A row carries the key of the cart it was intercepted on, so this is a regroup
        of the same list the box is already showing: each row sent back to the account
        whose [instance] tag it carries, and to no other.

        A row with no key names no cart. That only happens to a row intercepted before
        rows were tagged, and there is no honest guess to make about which of six carts
        it belongs to, so it is left out (and named by _warn_untagged) rather than
        broadcast.
        """
        out = {}
        for r in rows:
            if r.get("key"):
                out.setdefault(r["key"], []).append(r)
        return out

    def _warn_untagged(self, rows):
        """Name the rows _per_instance_rows has to drop, so a shortfall is never quiet."""
        lost = [r for r in rows if not r.get("key")]
        if lost:
            self.log(f"⚠ {len(lost)} intercepted row(s) name no account (intercepted "
                     f"before rows carried one) — skipped. Every row goes out on the "
                     f"cart it was intercepted on, and these name none.")
        return lost

    def _clear_captures(self):
        self.captures = []
        self._refresh_captures()
        self.log("Cleared intercepted list.")


    def _remove_selected_capture(self):
        picked = self._picked_capture()
        if picked is None:
            return
        del self.captures[picked[0]]
        self._refresh_captures()

    def _refresh_armed(self):
        """Redraw the armed-list box from self.armed_rows - its OWN snapshot, not the
        intercepted list. One line per armed send; _armed_lines maps line -> index."""
        if not hasattr(self, "armed_list"):
            return
        self.armed_list.delete(0, "end")
        self._armed_lines = []
        for n, r in enumerate(self.armed_rows):
            who = r.get("inst") or ("all" if r.get("key") is None else "?")
            tag = f"[{who[:10]}]"
            label = str(r.get("label") or r.get("usItemId") or "")[:22]
            self.armed_list.insert("end", f"{tag:<12}{label:<22} q{r.get('quantity', 1)}")
            self._armed_lines.append(n)

    def _set_armed(self, rows, per_key):
        """Take the snapshot the box shows and the worker fires. The SAME row dicts are
        shared with per_key, so a later Remove edits both - and an in-flight run too."""
        self.armed_rows = rows
        self.armed_per_key = per_key
        self._refresh_armed()

    def _remove_armed_row(self):
        """Drop the selected armed send. Works armed or disarmed - the one edit the
        armed list allows besides a fresh arm. The row object is pulled from both the
        flat list and its per-cart bucket in place, so a running series stops sending
        it too."""
        sel = self.armed_list.curselection()
        if not sel or sel[0] >= len(self._armed_lines):
            return
        n = self._armed_lines[sel[0]]
        if n >= len(self.armed_rows):
            return
        r = self.armed_rows[n]
        del self.armed_rows[n]
        if self.armed_per_key is not None:
            bucket = self.armed_per_key.get(r.get("key"))
            if bucket is not None:
                try:
                    bucket.remove(r)
                except ValueError:
                    pass
                if not bucket:
                    self.armed_per_key.pop(r.get("key"), None)
        self._refresh_armed()
        self.log(f"Removed {r.get('label') or r.get('usItemId') or 'a row'} from the "
                 f"armed list.")

    def _on_pick_capture(self, _evt):
        picked = self._picked_capture()
        if picked is None:
            return
        self._exit_edit_mode()   # a capture is a new item, not an edit of a saved one
        self._fill_editor(picked[1])

    def _fill_editor(self, c):
        for e, k in ((self.e_nick, "nick"), (self.e_name, "name"), (self.e_offer, "offerId"),
                     (self.e_usitem, "usItemId"), (self.e_qty, "quantity")):
            e.delete(0, "end"); e.insert(0, str(c.get(k, "")))

    def _clear_editor(self):
        for e in (self.e_nick, self.e_name, self.e_offer, self.e_usitem, self.e_qty): e.delete(0, "end")
        self._exit_edit_mode()

    def _refresh_presets(self):
        """Saved items changed — repopulate the one place they are shown.

        This used to rebuild a box of per-item buttons as well. The box is gone (the
        dropdown was already showing the same list), so the whole job is the dropdown.
        The name is kept because every place that edits the list calls it.
        """
        self._refresh_sub_choices()

    # ---------- the selected saved item ----------
    def _sub_preset(self):
        """The saved item the 'Selected item' dropdown is showing, or None."""
        i = self.sub_combo.current()
        return self.presets[i] if 0 <= i < len(self.presets) else None

    def _sub_or_warn(self):
        p = self._sub_preset()
        if p is None:
            messagebox.showinfo("No item", "Pick a saved item in 'Selected item' first.")
        return p

    def _add_sub(self):
        """Send the selected item once, at the quantity on the bar."""
        p = self._sub_or_warn()
        if p is not None:
            self.send_item(p["offerId"], p["usItemId"], self.sub_qty.get(),
                           label=self._nick(p))

    def _edit_sub(self):
        """Load the selected item into the editor beside the intercepted list."""
        i = self.sub_combo.current()
        if self._sub_or_warn() is not None:
            self._edit_preset(i)

    def _del_sub(self):
        i = self.sub_combo.current()
        p = self._sub_or_warn()
        if p is None:
            return
        # The per-row ✕ deleted without asking, which was survivable when the row you
        # were pointing at was the thing that vanished. Off a dropdown it is one
        # mis-click from losing an item whose offerId can only be re-captured, so ask.
        if messagebox.askyesno("Delete item",
                               f"Delete the saved item “{self._nick(p)}”?\n\n"
                               f"Its offerId/usItemId can only be recovered by "
                               f"capturing the item again."):
            self.del_preset(i)

    # ---------- everything below is the shared Session, not this panel ----------
    # The panel keeps calling self.cfg / self.log(...) / self.instances exactly as it
    # did when it owned them; only the implementations moved. That is what let the
    # ~250 feature call sites through this file stay untouched by the merge.

    LABEL = 'Cart'

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

    def _settings(self):
        self.session._settings()

    def apply_state(self, inst):
        """Session hook: push this panel's state onto the freshly-attached agent."""
        self._apply_state(inst)

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
        # Both delays are editable from Settings as well as from their boxes, and a box
        # left showing the old number reads as the setting not having taken.
        try:
            self._show_emu_delay(self._emu_delay_ms())
            self.delay_entry.delete(0, "end")
            self.delay_entry.insert(0, str(self._delay_ms()))
        except Exception:
            pass

    def on_instance_dropped(self, inst):
        """Session hook: one emulator was unticked; the others stay attached.

        Its rows are deliberately KEPT. They are the documentation of what that account
        did — the whole reason every row is tagged with its emulator — and a row is
        already marked with its verdict, so nothing left behind can be sent again by
        accident.
        The send template is kept too: it holds that cart's cartId, which is still that
        cart's cartId when the instance is ticked back on.
        """
        self.log(f"[{inst.name}] detached — its rows stay listed, tagged with its name.")
        self._refresh_captures()
        self._refresh_sent()

    def script_for(self, inst):
        """The one merged agent, on the one connected instance."""
        return getattr(inst, "script", None)

    def instance_note(self, inst):
        """Whether this instance can send: its own capture is the template, and the
        cartId in it is not portable from another instance."""
        return "template ✓" if inst.key in self.templates else "no template"
