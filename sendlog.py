#!/usr/bin/env python3
"""
Sent-request log — every live send written to disk the moment its reply lands.

The tool already shows a send's verdict in the Sent requests box and in the log pane,
but both are in-memory: the box trims itself per instance, the log pane scrolls, and
neither survives the app closing. A record you have to keep — "what did this run
actually send, when, and what came back" — cannot live only there.

So each send is appended here as its own line, WHEN THE REPLY IS RECEIVED rather than
when it is dispatched, because the verdict is half of what is being recorded. A send
whose reply never comes back is still written (with the transport's error and no
response), so the file is a list of what went out, not only of what succeeded.

Two files, written side by side into BASE — the folder the exe runs from, i.e. dist/
next to config.json and the exported call dumps:

  sent_requests_YYYYMMDD.jsonl   one JSON object per line, EVERYTHING about the send
                                 and the reply, for documentation.
  sent_requests_YYYYMMDD.csv     one row per send, the summary columns, for handing
                                 to someone who wants the list rather than the bodies.

Append-per-record, so a crash loses at most the send in flight; one file per DAY, so a
day's runs are one list. Each record carries `run_id`, which is unique per launch, so
a single run can still be filtered back out of a day that holds several.

Nothing here is allowed to break a send: every write is guarded, and a failure is
reported once through the panel's own log and then suppressed.
"""
import csv
import json
import os
import threading
import time

from session import BASE

# Unique per launch of the app. Lets a day's file be split back into its runs without
# needing a separate file per run — a manager asking for "the list" wants one file.
RUN_ID = time.strftime("%Y%m%d-%H%M%S")

# The CSV's columns, in order. Kept as one list because the header and every row are
# written from it — they cannot drift apart.
CSV_COLUMNS = [
    "sent_local", "received_local", "run_id", "seq", "tool", "op", "stage",
    "instance", "item", "quantity",
    "total_delay_ms", "calculated_delay_ms", "nudge_ms", "emulator_instance_delay_ms",
    "row_delay_ms", "delay_path",
    "rtt_ms", "http_code", "verdict", "order_status", "order_id",
    "response_bytes", "error", "url",
]

_lock = threading.Lock()
_seq = 0
_broken = False          # a write failed; report once, then stay quiet


def _paths():
    """Today's pair of files. Resolved per record so a run over midnight rolls."""
    day = time.strftime("%Y%m%d")
    return (os.path.join(BASE, f"sent_requests_{day}.jsonl"),
            os.path.join(BASE, f"sent_requests_{day}.csv"))


def _clock(epoch_ms):
    """One instant, three ways: the raw ms, local time to the millisecond, and UTC.

    Local because that is what the run was watched in and what a peg time is set in;
    UTC because a record read months later, or on another machine, needs an instant
    that does not depend on the reader's timezone. The millisecond matters: a row
    delay is 100-300 ms and a nudge is tens, so at second resolution a burst's sends
    all read as one instant.
    """
    if epoch_ms is None:
        return None
    t = epoch_ms / 1000.0
    return {
        "epoch_ms": round(epoch_ms, 3),
        "local": (time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(t))
                  + f".{int(round(epoch_ms)) % 1000:03d}"),
        "utc": (time.strftime("%Y-%m-%dT%H:%M:%S", time.gmtime(t))
                + f".{int(round(epoch_ms)) % 1000:03d}Z"),
    }


def delays(calculated_ms=None, nudge_ms=None, emulator_instance_ms=None,
           row_ms=None, path="", settings=None):
    """The delay breakdown for one send, and the single number that combines them.

    The four knobs are independent axes and each moves a send a different way, so the
    record keeps them apart AND states what they add up to:

      calculated delay  the lead the timed path dispatches with — preflight + one way
                        on the wire. It fires the request EARLIER so it ARRIVES on the
                        deadline, so it enters the total as a NEGATIVE offset.
      nudge             moves the target instant itself; negative = earlier.
      emulator instance the stagger between accounts: account n is n x this delay
                        behind the first.
      row               how far this row sits behind its own account's first row.

    The two stagger components are THIS send's share, already multiplied out by the
    caller — not the settings they came from. That is what makes the total mean "how
    far this request went out from the batch's start" rather than "the numbers in the
    boxes"; the settings themselves ride along under `settings` so the record still
    says what was configured.

    A component that does not apply on the path a send took is recorded as null rather
    than 0, and left out of the total: a manual send has no nudge and no calculated
    lead, and writing them as 0 would claim they were applied and came to nothing.
    `formula` spells out the arithmetic in the record itself so the total never has to
    be taken on trust.
    """
    parts, terms = {}, []
    for name, sign, val in (("calculated_delay_ms", -1, calculated_ms),
                            ("nudge_ms", 1, nudge_ms),
                            ("emulator_instance_delay_ms", 1, emulator_instance_ms),
                            ("row_delay_ms", 1, row_ms)):
        if val is None:
            parts[name] = None
            continue
        try:
            v = round(float(val), 3)
        except (TypeError, ValueError):
            parts[name] = None
            continue
        parts[name] = v
        terms.append((name, sign, v))
    total = sum(sign * v for _, sign, v in terms)
    parts["total_ms"] = round(total, 3)
    parts["formula"] = (" + ".join(f"{'-' if s < 0 else ''}{n}({v})"
                                   for n, s, v in terms) + f" = {round(total, 3)}"
                        if terms else "no delay applied on this path")
    parts["path"] = path
    # What the boxes said when this went out, as opposed to this send's own share of
    # them. Recorded because a run's settings can be edited mid-run, and a record that
    # only kept the share could not show that they were.
    parts["settings"] = settings or {}
    return parts


# Codes that name no cause. When Walmart answers with one of these the message is the
# only thing that says what happened, so the verdict carries the message instead. Kept
# as a visible set rather than a guess at the string, so adding one is a one-line edit.
_GENERIC_CODES = {"", "unexpected_error", "internal_error", "unknown_error"}


def _refusal(response):
    """The refusal a 2xx body carries, as (code, message), or (None, None).

    A 200 from Walmart is not a success, and a refusal arrives one of two ways, so
    the verdict has to look in both places:

      errors[]                     a GraphQL error array, beside `data` or instead of
                                   it — item_unavailable, out_of_stock.
      data.<root>.checkoutError[]  a well-formed 200 whose payload carries the refusal
                                   — item_policy_violation, the per-customer purchase
                                   cap. These have no `errors` array at all and set no
                                   graphql_errors flag, which is why they used to score
                                   "rejected", the same word as a 429.

    The body is parsed here rather than at send time because the record keeps it whole
    and this is the only place that needs it broken apart. A body that will not parse
    is not an error: it means this response said nothing about a refusal.
    """
    body = response.get("body")
    if not isinstance(body, str) or not body.strip():
        return (None, None)
    try:
        doc = json.loads(body)
    except (ValueError, TypeError):
        return (None, None)
    if not isinstance(doc, dict):
        return (None, None)

    for err in (doc.get("errors") or []):
        if isinstance(err, dict):
            ext = err.get("extensions")
            code = ext.get("code") if isinstance(ext, dict) else None
            return (code, err.get("message"))

    data = doc.get("data")
    if isinstance(data, dict):
        for node in data.values():
            if not isinstance(node, dict):
                continue
            for err in (node.get("checkoutError") or []):
                if isinstance(err, dict):
                    return (err.get("code"), err.get("message"))
    return (None, None)


def _refusal_name(code, message):
    """Walmart's own word for a refusal — its code, or its message when the code
    names nothing. Trimmed to stay a column value rather than a paragraph."""
    code = (code or "").strip()
    if code and code not in _GENERIC_CODES:
        return code
    msg = " ".join((message or "").split())
    if msg:
        if len(msg) > 60:
            # Cut back to a word boundary: a verdict ending mid-word reads like the
            # file is damaged rather than like a message that was too long.
            msg = msg[:60].rsplit(" ", 1)[0] + "…"
        return msg.strip().rstrip(".") or code or "refused"
    return code or "refused"


def _verdict(response):
    """The one word for the CSV's verdict column, from the same facts the UI reads.

    Most specific first, because several of these are true of the same response: a
    rate-limited send is also not accepted, and a policy refusal is also a 200 whose
    transport did everything right. Reading them in the wrong order is what collapsed
    a purchase-cap refusal and a throttle into the same word.
    """
    if not response.get("reached", True):
        return "not sent"
    # The checkout panel hands these over already broken into [code, message] pairs,
    # so they get the same treatment as a code dug out of a body: the code names the
    # refusal unless the code names nothing.
    errs = response.get("errors") or []
    if errs:
        first = errs[0]
        if isinstance(first, (list, tuple)) and first:
            return _refusal_name(first[0], first[1] if len(first) > 1 else "")
        return str(first)
    if response.get("http_code") == 429:
        return "rate limited"
    if response.get("placed"):
        return "ORDER PLACED"
    code, message = _refusal(response)
    if code or message:
        return _refusal_name(code, message)
    if response.get("accepted"):
        return "accepted"
    if response.get("graphql_errors"):
        return "graphql errors"
    return "rejected"


def record(tool, op, instance, response, request=None, delay=None,
           sent_at_ms=None, received_at_ms=None, sent_measured=None,
           stage=None, kind="send", item=None, quantity=None, log=None):
    """Append one completed send. Returns the record written, or None if it could not be.

    `response` is the whole reply as it came back, verbatim under `raw` plus the
    fields already parsed out of it by the caller — the raw body is the point of the
    file, and a summary that dropped it would not be documentation.

    `log` is the panel's own log callable; a write failure is reported through it
    once and then suppressed, because a broken log must not turn into one message per
    send in the middle of a run.
    """
    global _seq, _broken
    now_ms = time.time() * 1000.0
    inst_name = getattr(instance, "name", instance if isinstance(instance, str) else "?")
    rec = {
        "run_id": RUN_ID,
        "tool": tool,
        "op": op,
        "stage": stage,
        "kind": kind,
        "instance": {
            "name": inst_name,
            "key": getattr(instance, "key", None),
            "serial": getattr(instance, "serial", None),
            # Device minus host clock, in ms. Recorded because every device-measured
            # instant in here was shifted onto the host clock with it — without it a
            # reader cannot check the send time or reproduce it.
            "clock_offset_ms": getattr(instance, "clock_off_ms", None),
            "oneway_ms": getattr(instance, "oneway_ms", None),
        },
        "item": item,
        "quantity": quantity,
        "sent_at": _clock(sent_at_ms if sent_at_ms is not None else now_ms),
        # False = the send instant is the host's record of dispatch, not the device's
        # measurement of the bytes leaving. Marked rather than implied, so the column
        # is never read to a precision it does not have.
        "sent_measured": bool(sent_measured) if sent_measured is not None else None,
        "received_at": _clock(received_at_ms if received_at_ms is not None else now_ms),
        "delay": delay if delay is not None else delays(),
        "request": request or {},
        "response": response,
    }
    line = json.dumps(rec, default=str)
    jsonl_path, csv_path = _paths()
    with _lock:
        _seq += 1
        rec["seq"] = _seq
        if _broken:
            return rec
        try:
            with open(jsonl_path, "a", encoding="utf-8") as f:
                # Re-dumped rather than reusing `line`, so `seq` — assigned under the
                # lock, because it counts the file's records — is in it.
                f.write(json.dumps(rec, default=str) + "\n")
            fresh = not os.path.exists(csv_path) or os.path.getsize(csv_path) == 0
            with open(csv_path, "a", encoding="utf-8", newline="") as f:
                w = csv.DictWriter(f, fieldnames=CSV_COLUMNS, extrasaction="ignore")
                if fresh:
                    w.writeheader()
                w.writerow(_csv_row(rec))
        except Exception as e:
            _broken = True
            if log:
                log(f"⚠ could not write the sent-request log ({jsonl_path}) — {e}. "
                    f"Sending continues; nothing further will be recorded this run.")
            return None
    return rec


def _csv_row(rec):
    """The summary row: the columns someone reads as a list, not as documentation."""
    d = rec.get("delay") or {}
    resp = rec.get("response") or {}
    body = resp.get("body")
    return {
        "sent_local": (rec.get("sent_at") or {}).get("local"),
        "received_local": (rec.get("received_at") or {}).get("local"),
        "run_id": rec.get("run_id"),
        "seq": rec.get("seq"),
        "tool": rec.get("tool"),
        "op": rec.get("op"),
        "stage": rec.get("stage") or rec.get("kind"),
        "instance": (rec.get("instance") or {}).get("name"),
        "item": rec.get("item"),
        "quantity": rec.get("quantity"),
        "total_delay_ms": d.get("total_ms"),
        "calculated_delay_ms": d.get("calculated_delay_ms"),
        "nudge_ms": d.get("nudge_ms"),
        "emulator_instance_delay_ms": d.get("emulator_instance_delay_ms"),
        "row_delay_ms": d.get("row_delay_ms"),
        "delay_path": d.get("path"),
        "rtt_ms": resp.get("rtt_ms"),
        "http_code": resp.get("http_code"),
        "verdict": _verdict(resp),
        "order_status": resp.get("order_status"),
        "order_id": resp.get("order_id"),
        "response_bytes": len(body) if isinstance(body, str) else None,
        "error": resp.get("error"),
        "url": resp.get("url"),
    }


def paths_note():
    """Where the log is going, for a panel to say before its first send."""
    jsonl_path, csv_path = _paths()
    return (f"Sent requests are recorded on receipt to {jsonl_path} "
            f"(full request + response) and {csv_path} (summary). Run id {RUN_ID}.")


_noted = False


def note_once(log):
    """Say where the log lives, once per run, whichever pane sends first.

    Both panes write to the same pair of files, so this belongs to the run and not to
    either of them — said once, at the first send, rather than at startup where it
    would scroll away before anything had been recorded.
    """
    global _noted
    if _noted or not log:
        return
    _noted = True
    try:
        log(paths_note())
    except Exception:
        pass
