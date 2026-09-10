#!/usr/bin/env python3
"""The one connection both halves of the toolkit share.

Before the merge each tool owned all of this — its own adb discovery, its own frida
session, its own instance list, its own log pane and its own Settings dialog — and the
two could not be attached at the same time, because their agents fought over the same
Apollo hook. There is now ONE agent (agent_toolkit.js), so there is one session, and
this is what owns it.

    Session          the connection: cfg, instances, the frida script, the message
                     pump, the log, Settings, and the top bar + instance picker widgets
    panels           the two feature halves (cart_panel.CartPanel,
                     checkout_panel.CheckoutPanel). Each registers itself, contributes
                     an instance-row note, gets its state pushed on connect, and is
                     handed every agent message.

A panel never connects, never tears down and never logs on its own — it calls into the
Session. That is the whole point: one instance, one session, both tools live on it.

The adb/discovery/frida code below is lifted verbatim from the cart tool by
_build_session.py, because it was identical in both and is the part that cannot be
tested without an emulator.
"""
import json
import os
import queue
import re
import shutil
import socket
import subprocess
import sys
import threading
import time
import tkinter as tk
from tkinter import ttk, messagebox

try:
    import frida
except ImportError:
    print("Missing dependency: pip install frida==16.7.19")
    raise

BASE = os.path.dirname(sys.executable) if getattr(sys, "frozen", False) \
    else os.path.dirname(os.path.abspath(__file__))
CONFIG_PATH = os.path.join(BASE, "config.json")
AGENT_PATH = os.path.join(BASE, "agent_toolkit.js")

# The union of what the two tools used to configure separately. Their shared keys always
# had identical defaults; the schedule_* block is the cart half's, and nothing in the
# checkout half conflicts with it.
DEFAULT_CONFIG = {
    "adb_path": r"C:\Program Files\BlueStacks_nxt\HD-Adb.exe",
    "frida_port_base": "27042",
    "app_name": "Walmart Canada",
    "pkg": "ca.walmart.ecommerceapp",
    "delay_ms": "0",
    "frida_server": "/data/local/tmp/frida-server",
    "auto_start_frida": "true",
    "schedule_oneway_ms": "14",
    "schedule_arm_ms": "2000",
    "schedule_warm_ms": "20000",
    "ntp_server": "time.cloudflare.com",
    "schedule_repeat_sec": "60",
    "schedule_delay_ms": "0",
    "schedule_nudge_ms": "0",
    "schedule_peg": "12:00:00",
    "oneway_samples": "4",
    # How long a sent add-to-cart row stays on the intercepted list, carrying its
    # verdict and its sent time, before it clears itself. 0 holds it indefinitely.
    "add_to_cart_information_time": "5000",
    # The gap between the FIRST request of one emulator and the first request of the
    # next, in ms. Its counterpart is the row delay (schedule_delay_ms / delay_ms),
    # which only ever separates rows WITHIN one emulator — the two are independent
    # axes of one fan-out and neither is allowed to stand in for the other.
    "emulator_delay_ms": "0",
    # How many emulators may be attached at once. Six is what a walkthrough needs and
    # what the picker is sized for; the cap exists so a stray Detect on a machine full
    # of instances cannot try to attach to all of them at once.
    "max_instances": "6",
}

# Dropped on load. device/frida_host pinned a single instance; send_mode/auto_place/
# launchpad_url configured the removed armed path; calibrate_samples belonged to a
# Calibrate button whose work now runs inside every scheduled send.
LEGACY_KEYS = ("device", "frida_host", "send_mode", "auto_place", "launchpad_url",
               "calibrate_samples")

# --------------------------------------------------------------------------
# Lifted verbatim from cart_app.py by _build_session.py
# --------------------------------------------------------------------------

NO_WINDOW = 0x08000000 if os.name == "nt" else 0

ADB_CANDIDATES = [
    r"C:\Program Files\BlueStacks_nxt\HD-Adb.exe",
    r"C:\Program Files\BlueStacks_nxt_cn\HD-Adb.exe",
    r"C:\Program Files (x86)\BlueStacks_nxt\HD-Adb.exe",
    r"C:\Program Files\BlueStacks_X\HD-Adb.exe",
    r"C:\Program Files\BlueStacks\HD-Adb.exe",
    r"C:\Program Files (x86)\BlueStacks\HD-Adb.exe",
]

CONF_CANDIDATES = [
    r"C:\ProgramData\BlueStacks_nxt\bluestacks.conf",
    r"C:\ProgramData\BlueStacks_nxt_cn\bluestacks.conf",
    r"C:\ProgramData\BlueStacks\bluestacks.conf",
]

SU_CANDIDATES = ("/system/xbin/su", "su", "/system/bin/su", "/sbin/su")

SU_PROBE_TIMEOUT = 8      # seconds per candidate — a gated su never returns at all

# Host-side copy of the device binary, kept next to the tool. `/data/local/tmp` is
# per-instance — every BlueStacks instance is its own VM with its own filesystem — so a
# frida-server pushed to instance 1 does not exist on instance 4, and an instance that
# never got one cannot be attached to at all. This is where the tool keeps a copy so it
# can put one on an instance itself, instead of telling you to go and run adb.
FRIDA_CACHE = os.path.join(BASE, "frida-server")

# A frida-server is ~110 MB, and adb push/pull is not fast. Generous, because the
# alternative to waiting is the instance simply not working.
FRIDA_XFER_TIMEOUT = 600


def run(cmd, timeout=30):
    """Run a command; return (returncode, stdout, stderr) — never raises."""
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout,
                           creationflags=NO_WINDOW)
        return p.returncode, (p.stdout or "").strip(), (p.stderr or "").strip()
    except Exception as e:
        return -1, "", str(e)


def find_adb(configured=""):
    """First adb that actually exists: the configured one, a BlueStacks one, or PATH."""
    for c in [configured, *ADB_CANDIDATES]:
        if c and os.path.exists(c):
            return c
    return shutil.which("adb") or ""


def port_open(port, host="127.0.0.1", timeout=0.35):
    s = socket.socket()
    s.settimeout(timeout)
    try:
        return s.connect_ex((host, int(port))) == 0
    finally:
        s.close()


def bluestacks_instances():
    """Every instance BlueStacks knows about: [{key, name, port}] from bluestacks.conf.

    `key` is the config name (e.g. Rvc64_1), `name` the display name you set in the
    Multi-instance Manager, `port` the adb port BlueStacks assigned to it.
    """
    ports, names = {}, {}
    for conf in CONF_CANDIDATES:
        try:
            with open(conf, "r", encoding="utf-8", errors="ignore") as f:
                text = f.read()
        except Exception:
            continue
        # status.adb_port is the live one; plain adb_port is the configured fallback
        for m in re.finditer(r'bst\.instance\.([^.]+)\.adb_port\s*=\s*"?(\d+)"?', text):
            ports.setdefault(m.group(1), int(m.group(2)))
        for m in re.finditer(r'bst\.instance\.([^.]+)\.status\.adb_port\s*=\s*"?(\d+)"?', text):
            ports[m.group(1)] = int(m.group(2))
        for m in re.finditer(r'bst\.instance\.([^.]+)\.display_name\s*=\s*"([^"]*)"', text):
            if m.group(2).strip():
                names[m.group(1)] = m.group(2).strip()
    out = [{"key": k, "name": names.get(k, k), "port": p} for k, p in ports.items()]
    out.sort(key=lambda i: i["port"])
    if not out:
        # no conf found — 5555 is the classic default
        out = [{"key": "default", "name": "BlueStacks", "port": 5555}]
    return out


def list_devices(adb):
    """[(serial, state)] from `adb devices`."""
    rc, out, _ = run([adb, "devices"], timeout=15)
    if rc != 0:
        return []
    devs = []
    for line in out.splitlines()[1:]:
        parts = line.split()
        if len(parts) >= 2:
            devs.append((parts[0], parts[1]))
    return devs


def serials_for_port(port):
    """A BlueStacks instance on adb port N shows up either as 127.0.0.1:N (adb connect)
    or as emulator-(N-1) (adb's own emulator scan). Both name the same device."""
    return [f"127.0.0.1:{port}", f"emulator-{int(port) - 1}"]


def port_for_serial(serial):
    """The adb port behind either serial form, or None if the serial is neither.

    The inverse of serials_for_port: `127.0.0.1:5585` is port 5585, and adb's own
    `emulator-5584` is port 5585 — adb names an emulator by its console port, which
    is one below the adb one.
    """
    m = re.fullmatch(r"127\.0\.0\.1:(\d+)", serial or "")
    if m:
        return int(m.group(1))
    m = re.fullmatch(r"emulator-(\d+)", serial or "")
    if m:
        return int(m.group(1)) + 1
    return None


def discover(adb_path):
    """Every emulator we can attach to right now: [(key, name, port, serial)].

    Booted BlueStacks instances from bluestacks.conf, plus anything else already
    attached to adb (another emulator, a real device) so nothing is silently ignored.
    """
    attached = [s for s, st in list_devices(adb_path) if st == "device"]
    found, claimed = [], set()
    for meta in bluestacks_instances():
        if not port_open(meta["port"]):
            continue
        names = serials_for_port(meta["port"])
        hit = next((n for n in names if n in attached), None)
        if not hit:
            run([adb_path, "connect", f"127.0.0.1:{meta['port']}"], timeout=15)
            attached = [s for s, st in list_devices(adb_path) if st == "device"]
            hit = next((n for n in names if n in attached), None)
        if hit:
            found.append((meta["key"], meta["name"], meta["port"], hit))
            claimed.update(names)   # both naming forms are the same device
    for s in attached:
        if s in claimed:
            continue
        found.append((s, s, 0, s))
        # An instance the loop above skipped is on adb under one of its two serial
        # forms — but adb can be showing BOTH, and then the same device is listed
        # twice: once as emulator-5584 and once as 127.0.0.1:5585. Claim the twin the
        # way the named branch does. Without this the pair also renames to one conf
        # key at connect, and detect() matches instances by key.
        port = port_for_serial(s)
        if port:
            claimed.update(serials_for_port(port))
    return found


class Instance:
    """One emulator we attach to.

    Each gets its own adb serial and its own *host-side* frida port: the host end of an
    adb forward is global, so instances can't all forward 27042 -> 27042.
    """

    def __init__(self, key, name, port, serial, frida_port):
        self.key = key
        self.name = name
        self.port = port
        self.serial = serial
        self.frida_port = frida_port
        # "Ticked". Several instances are attached at once now (up to
        # Session.max_instances), so this is a checkbox rather than a radio: it means
        # "this emulator takes part" — Connect attaches every ticked one, a send fans
        # out to every ticked one that is connected, and unticking a live instance
        # detaches just that one. A freshly detected instance starts ticked so a
        # Detect → Connect reaches everything that is running.
        self.enabled = True
        # True only while WE are tearing this instance down: frida fires 'detached' for
        # a deliberate detach exactly as it does for a crash, and without this the
        # teardown's own signal reports the app as having restarted.
        self.disconnecting = False
        self.session = None
        self.script = None
        self.status = "not connected"
        # The short label in the picker is `status`; this is the whole reason, kept
        # because the useful half of a connect failure never fits in a picker row.
        # It used to be truncated to 60 characters and thrown away — which turned "no
        # frida-server on this instance, push one" into "failed: error receiving data:
        # An existing connection was forcibly close", six rows deep in a parallel
        # connect. The row shows the short form; this goes to the log in full.
        self.fail_reason = ""
        # The su on THIS instance that actually returns root, found by probing once and
        # kept for the session. Instances differ: a rooted master may answer plain `su`
        # while its clones only answer the stock setuid one. None = not probed yet.
        self.su_cmd = None
        # device clock minus host clock, in ms. Measured per instance (each emulator
        # keeps its own clock, ~405 ms off the host here), and the only way to turn
        # a host deadline into one the agent can wait on. None = not measured yet.
        self.clock_off_ms = None
        # preflight measured by the warm-up send: our interceptor chain plus PX
        # token minting, i.e. the part of the lead time that is ours rather than
        # the network's. None = never warmed, so the lead falls back to a default.
        self.warm_preflight = None
        # One way to Walmart from THIS device, ms, as measured by Calibrate.
        # Overrides the schedule_oneway_ms default for this instance while set,
        # which is the difference between an aimed send and an assumed one.
        self.oneway_ms = None

    @property
    def connected(self):
        return self.script is not None

    @property
    def addr(self):
        return f"127.0.0.1:{self.frida_port}"

    @property
    def label(self):
        return f"{self.name} ({self.serial})"


def load_json(path, default):
    try:
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return json.loads(json.dumps(default))


def save_json(path, data):
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2)




# ---------------------------------------------------------------------------
# Which emulator a row came from
#
# With six instances attached, every list in the tool is a mix: adds from six carts,
# sends to six accounts, checkout calls from six sessions. Each list was grouped into
# a block per emulator under a `──── [name] ────` rule, and the helpers that drew
# those rules lived here.
#
# They are gone. A heading answers "whose is this" for a row only while the row is
# still sitting under it — a contractId read off the screen, a row copied into the
# log by a double-click, the top line of a box glanced at from a metre away all lost
# the name. And grouping reordered the boxes: the newest row was not the top line, it
# was the top line of whichever block its emulator sat in, so a run being watched
# restarted once per account.
#
# Every row now carries its own `[instance]` tag, right of the time, and the lists
# are flat and time-ordered again. The tag is the label; nothing above the row is
# needed to read it.
# ---------------------------------------------------------------------------


def mode_column(parent, title, pad=(0, 14)):
    """One column of the shared Mode panel: a title above a row for the control.

    Both halves put their mode selectors in one panel, side by side, so the column
    shape lives here rather than being written twice. Returns the row to pack the
    combo and badge into; the column itself is `row.master`, which is where a
    description goes so it sits under the control instead of beside it.
    """
    col = ttk.Frame(parent)
    col.pack(side="left", fill="both", expand=True, padx=pad)
    ttk.Label(col, text=title, font=("Segoe UI", 9, "bold")).pack(anchor="w")
    row = ttk.Frame(col)
    row.pack(fill="x")
    return row


class Session:
    """The shared connection. One instance, one frida script, both panels on it."""

    LOG_MAX_LINES = 3000        # one pane for both halves now, so twice the traffic

    def __init__(self, root, agent_js=""):
        self.root = root
        self.agent_js = agent_js
        self.cfg = load_json(CONFIG_PATH, DEFAULT_CONFIG)
        for k in LEGACY_KEYS:
            self.cfg.pop(k, None)
        if "delay_sec" in self.cfg:      # carried over rather than silently reset to 0
            try:
                self.cfg.setdefault("delay_ms", str(int(float(self.cfg["delay_sec"]) * 1000)))
            except Exception:
                pass
            self.cfg.pop("delay_sec", None)
        for k, v in DEFAULT_CONFIG.items():
            self.cfg.setdefault(k, v)

        self.instances = []
        self.pending = None
        self._switch_lock = threading.Lock()
        self.dm = frida.get_device_manager()
        # One device manager, six workers attaching at once. add_remote_device and
        # remove_remote_device mutate its shared device list, and nothing in frida
        # promises that is safe from several threads — a connect used to be the only
        # thing running, so this could not come up. Held for the registration call
        # only, never across attach() or across the network.
        self._dm_lock = threading.Lock()
        # Provisioning moves ~110 MB per instance through one adb server. Three of
        # those at once is slower than three in a row and unreadable in the log.
        self._provision_lock = threading.Lock()
        self.q = queue.Queue()
        self.panels = []
        self._log_scroll_pending = False
        self.logbox = None
        self.status = None
        self.inst_rows = None
        # Which instance the radio group has selected. Tk vars must be created after a
        # root exists, which it does by the time a Session is built.
        self._pick_var = tk.StringVar(master=root, value="")

    # ---------- panels ----------
    def register(self, panel):
        """A feature half joins the session. Order fixes instance-row note order."""
        self.panels.append(panel)

    def _panel_note(self, inst):
        """Per-instance notes the panels contribute (e.g. the cart's 'template ✓')."""
        notes = []
        for p in self.panels:
            try:
                n = p.instance_note(inst)
            except Exception:
                n = None
            if n:
                notes.append(n)
        return "  ".join(notes)

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

    def adb(self, inst, *args, timeout=30):
        adb_path = self.cfg.get("adb_path") or ""
        if not adb_path or not inst or not inst.serial:
            self.log("adb: no device — click Detect.")
            return ""
        rc, out, err = run([adb_path, "-s", inst.serial, *args], timeout=timeout)
        if rc != 0:
            self.log(f"[{inst.name}] adb error ({' '.join(args)[:50]}): {err or out or f'exit {rc}'}")
        return out

    def resolve_su(self, inst):
        """The su on this instance that really gives root, probed once and cached.

        Each candidate gets a bounded timeout: a root manager's grant prompt is shown
        inside Android where nothing can answer it, so a gated su does not fail — it
        blocks. Bounding the probe is what keeps that from freezing the connect, and
        trying every candidate is what lets an instance whose manager never granted
        shell still work through the stock setuid su.
        """
        if inst.su_cmd:
            return inst.su_cmd
        adb_path = find_adb(self.cfg.get("adb_path", ""))
        if not adb_path:
            return None
        for cand in SU_CANDIDATES:
            rc, out, _ = run([adb_path, "-s", inst.serial, "shell", f"{cand} -c id"],
                             timeout=SU_PROBE_TIMEOUT)
            if rc == 0 and "uid=0" in out:
                inst.su_cmd = cand
                self.log(f"[{inst.name}] root via '{cand}'.")
                return cand
        self.log(f"[{inst.name}] no working su — every candidate was denied or timed out "
                 f"({', '.join(SU_CANDIDATES)}). If this instance uses a root manager "
                 f"(Magisk/Kyubi), open it inside Android and grant root to shell/ADB.")
        return None

    def _frida_running(self, inst):
        out = self.adb(inst, "shell", "ps -A 2>/dev/null || ps", timeout=20)
        return "frida-server" in out

    def _has_frida_binary(self, inst, path):
        """Does this instance already carry the frida-server binary at `path`?

        Asked with `ls` rather than by trying to run it: an instance with no binary and
        an instance whose binary will not start need different answers, and only the
        first one can be fixed by putting a file there.
        """
        rc, out, _ = run([self.cfg.get("adb_path", ""), "-s", inst.serial,
                          "shell", f"ls {path}"], timeout=20)
        return rc == 0 and path in out and "No such file" not in out

    def _frida_donor(self, path, exclude=None):
        """An instance that already has the binary, to copy from. None if there is none."""
        for other in self.instances:
            if other is exclude or not other.serial:
                continue
            if self._has_frida_binary(other, path):
                return other
        return None

    def _cache_frida_binary(self, path, exclude=None):
        """A host-side copy of frida-server, pulled off a peer instance if need be.

        Returns the local path, or None with the reason logged. The copy is kept so the
        pull happens once per machine rather than once per instance, and so an instance
        added later can be provisioned with no donor running at all.

        Copying from a peer rather than downloading is deliberate: the binary has to
        match the frida Python package driving it, and the one already working on
        another instance provably does.
        """
        if os.path.exists(FRIDA_CACHE) and os.path.getsize(FRIDA_CACHE) > 1_000_000:
            return FRIDA_CACHE
        donor = self._frida_donor(path, exclude=exclude)
        if donor is None:
            return None
        self.log(f"Copying frida-server off {donor.name} to keep locally "
                 f"({os.path.basename(FRIDA_CACHE)}) — this takes a moment, and only "
                 f"happens once.")
        rc, out, err = run([self.cfg.get("adb_path", ""), "-s", donor.serial,
                            "pull", path, FRIDA_CACHE], timeout=FRIDA_XFER_TIMEOUT)
        if rc != 0 or not os.path.exists(FRIDA_CACHE):
            self.log(f"✗ couldn't copy frida-server off {donor.name}: {err or out or f'exit {rc}'}")
            return None
        self.log(f"Kept a local copy of frida-server "
                 f"({os.path.getsize(FRIDA_CACHE) // (1024 * 1024)} MB) — any instance "
                 f"missing one is set up from this, without a donor.")
        return FRIDA_CACHE

    def provision_frida_server(self, inst, path):
        """Put the frida-server binary on an instance that has none. True if it landed.

        This is the whole reason instances 4, 5 and 6 of a six-instance set typically do
        not work: `/data/local/tmp` belongs to one instance, so the binary you pushed
        when you set the first ones up simply is not there on the ones you added later.
        The tool used to detect that and print the adb command for you to run by hand,
        once per instance, which is not something to be doing while presenting.

        Serialised across instances: three ~110 MB transfers through one adb server at
        once are slower than three in a row, and unreadable in the log.
        """
        with self._provision_lock:
            if self._has_frida_binary(inst, path):
                return True            # another worker got there first
            local = self._cache_frida_binary(path, exclude=inst)
            if not local:
                self.log(f"[{inst.name}] ✗ no frida-server on this instance, and no other "
                         f"instance has one to copy from. Push it once by hand and every "
                         f"later instance can be set up from it:\n"
                         f"    adb -s {inst.serial} push frida-server {path}")
                return False
            mb = os.path.getsize(local) // (1024 * 1024)
            self.log(f"[{inst.name}] setting up frida-server ({mb} MB) — this instance "
                     f"has none of its own. One-off; it stays there.")
            rc, out, err = run([self.cfg.get("adb_path", ""), "-s", inst.serial,
                                "push", local, path], timeout=FRIDA_XFER_TIMEOUT)
            if rc != 0:
                self.log(f"[{inst.name}] ✗ push failed: {err or out or f'exit {rc}'}")
                return False
            if not self._has_frida_binary(inst, path):
                self.log(f"[{inst.name}] ✗ push reported success but {path} is not there.")
                return False
            # chmod as shell first: the file is shell-owned straight after a push, so
            # this works even before root is resolved, and a failure here is not fatal.
            self.adb(inst, "shell", f"chmod 755 {path}", timeout=20)
            self.log(f"[{inst.name}] frida-server installed.")
            return True

    def ensure_frida_server(self, inst):
        """Start frida-server on the instance if it isn't already listening."""
        if self._frida_running(inst):
            return True
        if str(self.cfg.get("auto_start_frida", "true")).lower() not in ("1", "true", "yes"):
            return False
        path = self.cfg.get("frida_server", "/data/local/tmp/frida-server")
        if not self._has_frida_binary(inst, path):
            # Not an error to report and give up on any more — put one there.
            if not self.provision_frida_server(inst, path):
                inst.fail_reason = (
                    f"no frida-server at {path} on this instance, and it could not be "
                    f"set up automatically. /data/local/tmp belongs to one instance, so "
                    f"every instance needs its own copy.")
                return False
        su = self.resolve_su(inst)
        if not su:
            inst.fail_reason = ("no working su — this instance is not rooted, or its root "
                                "manager has not granted shell/ADB. frida-server cannot "
                                "be started without root.")
            return False
        self.log(f"[{inst.name}] starting frida-server…")
        self.adb(inst, "shell", f"{su} -c 'chmod 755 {path}'", timeout=20)
        try:
            subprocess.Popen([self.cfg["adb_path"], "-s", inst.serial, "shell",
                              f"{su} -c '{path} -D'"],
                             stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                             creationflags=NO_WINDOW)
        except Exception as e:
            self.log(f"[{inst.name}] couldn't launch frida-server: {e}")
            return False
        for _ in range(12):
            time.sleep(0.5)
            if self._frida_running(inst):
                self.log(f"[{inst.name}] frida-server is up.")
                return True
        inst.fail_reason = ("frida-server is installed and root works, but it did not stay "
                            "running. Usually a binary that does not match this machine's "
                            "frida package — delete it on the device and let the tool "
                            "copy one off a working instance.")
        self.log(f"[{inst.name}] frida-server didn't come up — {inst.fail_reason}")
        return False

    def detect(self, quiet=False):
        """Find every booted instance and keep the Instance list in sync.

        BlueStacks assigns a different adb port per instance, and adb registers an
        emulator it auto-detected as `emulator-<port-1>` rather than `127.0.0.1:<port>` —
        so both naming forms are accepted. Already-connected instances are preserved.
        """
        adb_path = find_adb(self.cfg.get("adb_path", ""))
        if not adb_path:
            if not quiet:
                messagebox.showerror("adb not found",
                    "Couldn't find HD-Adb.exe (or adb on PATH).\n"
                    "Set the full path in Settings → adb_path.")
            self._refresh_instances()
            return []
        self.cfg["adb_path"] = adb_path

        try:
            base = int(self.cfg.get("frida_port_base", 27042))
        except Exception:
            base = 27042

        old = {i.key: i for i in self.instances}
        found = discover(adb_path)
        fresh = []
        for n, (key, name, port, serial) in enumerate(found):
            inst = old.pop(key, None)
            if inst:                       # keep the live session, refresh what may have moved
                inst.name, inst.port, inst.serial = name, port, serial
                if not inst.connected:
                    inst.frida_port = base + n
            else:
                inst = Instance(key, name, port, serial, base + n)
            fresh.append(inst)
        for gone in old.values():          # instance shut down since last detect
            self._teardown(gone)
        self.instances = fresh
        # A fresh instance arrives ticked, so a machine running more emulators than the
        # cap would present a picker asking for more than can be attached. Untick the
        # overflow here rather than letting Connect quietly drop it: the picker has to
        # show what will actually happen.
        cap = self.max_instances()
        over = [i for i in self.instances if i.enabled][cap:]
        for i in over:
            if not i.connected:
                i.enabled = False
        save_json(CONFIG_PATH, self.cfg)
        self._refresh_instances()

        if not self.instances:
            if not quiet:
                messagebox.showerror("No emulator found",
                    "No running emulator is reachable over adb.\n\n"
                    f"adb: {adb_path}\n"
                    f"BlueStacks instances in config: "
                    f"{[i['port'] for i in bluestacks_instances()] or 'none'}\n"
                    f"adb devices: {[s for s, _ in list_devices(adb_path)] or 'none'}\n\n"
                    "• Is BlueStacks actually running (an instance window open)?\n"
                    "• In BlueStacks Settings → Advanced, enable Android Debug Bridge.")
            return []
        self.log(f"Detected {len(self.instances)} instance(s): "
                 + ", ".join(i.label for i in self.instances))
        return self.instances

    def _detect_clicked(self):
        for inst in self.detect():
            model = self.adb(inst, "shell", "getprop", "ro.product.model").strip()
            self.log(f"[{inst.name}] {inst.serial} ready{f' ({model})' if model else ''}.")

    def connect(self):
        """Attach to every ticked instance, in parallel.

        The tool used to hold exactly one session and tear the previous one down on
        the way in. That was never a protocol limit — one frida script per process on
        each device is fine, and each device has its own adb serial and its own
        forwarded host port — it was a UI decision from when the picker was a radio
        group. A walkthrough across six accounts done one at a time is six
        connect/teardown cycles of ~10 s each, which is the whole reason this changed.

        Instances attach on their own workers rather than one after another: a connect
        is dominated by waiting on adb and on frida-server, so six done together cost
        about what one does. Each reports its own outcome; one failing does not stop
        the rest.
        """
        if not self.instances and not self.detect():
            return
        targets = [i for i in self.wanted() if not i.connected]
        if not targets:
            if self.wanted():
                self.log("Every ticked instance is already connected.")
            else:
                self.log("No instance ticked — tick at least one in Emulator instance.")
            return
        cap = self.max_instances()
        live = len([i for i in self.instances if i.connected])
        room = max(0, cap - live)
        if len(targets) > room:
            self.log(f"⚠ {len(targets)} instance(s) ticked but only {room} slot(s) left "
                     f"of the {cap}-instance cap — attaching the first {room}. "
                     f"Raise Settings → max_instances to go higher.")
            targets = targets[:room]
        if not targets:
            self.log(f"Already at the {cap}-instance cap — untick one first.")
            return
        self.pending = (targets[0], "connecting to")
        self._refresh_instances()
        threading.Thread(target=self._connect_worker, args=(targets,), daemon=True).start()

    def _connect_worker(self, targets):
        """Attach `targets` together, one thread each, and report once at the end."""
        done, lock = [], threading.Lock()

        def one(inst):
            # _switch_lock is NOT held across the attach any more. It used to
            # serialise the whole thing because a connect tore down whoever else was
            # attached, so two of them overlapping could tear down each other's fresh
            # session. Nothing is torn down here, so the only thing left to protect is
            # the per-instance work — and that is already per-instance.
            ok = self._connect_one(inst)
            with lock:
                done.append((inst, ok))
            self._ui(lambda: self.log(
                f"[{inst.name}] connected." if ok
                else f"[{inst.name}] could not connect."))

        threads = [threading.Thread(target=one, args=(i,), daemon=True) for i in targets]
        for t in threads:
            t.start()
        for t in threads:
            t.join()
        good = [i for i, ok in done if ok]
        self.pending = None
        self._ui(self._refresh_instances)
        self._ui(lambda: self.log(
            (f"Connected to {len(good)} instance(s): {', '.join(i.name for i in good)}. "
             f"Add items in the app — captures are tagged and grouped by instance.")
            if good else "Nothing connected."))

    # How long to wait for an adb forward to actually carry traffic, and how many
    # times to re-try the attach behind it.
    FORWARD_WAIT_S = 6.0
    ATTACH_TRIES = 3

    def _wait_forward(self, inst):
        """Wait until this instance's forwarded port answers. True if it did.

        `port_open` on a forwarded port is not the question it looks like: adb accepts
        the host connection whether or not anything is listening on the device, and only
        then fails. So this polls, and the caller still has to treat a transport error
        from the attach as meaningful.

        It replaces a single blind `sleep(1.0)`. One second was enough when one instance
        connected at a time; with six going at once through one adb server, the later
        ones were routinely still settling when their attach was made, which is exactly
        the "the last few don't connect" shape.
        """
        deadline = time.time() + self.FORWARD_WAIT_S
        while time.time() < deadline:
            if port_open(inst.frida_port):
                return True
            time.sleep(0.25)
        return False

    def _attach_app(self, dev, inst):
        """Attach to the Walmart app on `dev`, by display name or by package.

        Retried: frida-server can be listening while still bringing its process list up,
        and a first attach then fails with a transport error that a second one does not.
        Raises the last error if every try fails, with the two names it tried.
        """
        app, pkg = self.cfg["app_name"], self.cfg["pkg"]
        last = None
        for n in range(self.ATTACH_TRIES):
            for target in (app, pkg):      # app_name varies by locale/build
                try:
                    return dev.attach(target)
                except Exception as e:
                    last = e
            if n + 1 < self.ATTACH_TRIES:
                time.sleep(0.6)
        raise last if last else RuntimeError(f"could not attach to {app} / {pkg}")

    def _explain(self, inst, e):
        """Turn a connect exception into something that names the fix.

        A raw frida error is nearly always the wrong sentence to show: the interesting
        failure happened one layer down, and by the time it surfaces here it reads as a
        socket problem. So a reason already worked out (no frida-server, no root) wins,
        and the two errors that do arrive here get translated.
        """
        if inst.fail_reason:
            return inst.fail_reason
        text = str(e)
        low = text.lower()
        if "forcibly closed" in low or "connection closed" in low or "transport" in low:
            return ("frida-server is not answering on this instance — the adb forward is "
                    "up but nothing is listening on the device behind it. Usually "
                    "frida-server is not running there.")
        if "unable to find process" in low or "process not found" in low:
            return (f"frida-server is answering, but the Walmart app is not running on "
                    f"this instance — nothing matched '{self.cfg.get('app_name')}' or "
                    f"'{self.cfg.get('pkg')}'. Open the app there, log in, and Connect "
                    f"again.")
        return text

    def _name_from_conf(self, inst):
        """Look this instance back up in bluestacks.conf, on the way in to a connect.

        Detect runs 200 ms after launch, and an instance can be on adb under its
        `emulator-N` name while its conf port is not open yet. discover() has nothing
        to match on at that moment, so it falls through to naming the instance by its
        SERIAL — and that serial is then what every row tag, every log line and every
        export carries: `[127.0.0.` where `[1]` belongs.

        Connect is the moment the lookup works, because connecting is only possible
        once the instance is up and its port is open. Only an instance still wearing
        its serial as its name is touched, so a real device (whose serial IS its name)
        and an already-named instance are both left alone.

        The KEY is repaired with the name, and that is the half that lasts: `detect()`
        matches instances by key, so an instance left keyed by serial would be matched
        by serial on every later Detect and never pick its name back up. The cost is
        that rows captured while it was mis-identified are keyed to the old serial and
        no longer count as this instance's — they are from a previous session, which
        is already the weaker claim.
        """
        if inst.key != inst.serial:            # already named from the conf
            return
        port = inst.port or port_for_serial(inst.serial)
        meta = next((m for m in bluestacks_instances() if m["port"] == port), None)
        if not meta:
            return
        was = inst.name
        inst.key, inst.name, inst.port = meta["key"], meta["name"], meta["port"]
        self._ui(lambda: self.log(
            f"[{inst.name}] named from bluestacks.conf — it was showing as [{was}] "
            f"because its adb port wasn't open yet when Detect ran."))

    def _connect_one(self, inst):
        self._teardown(inst)   # a reconnect must not leave the old session attached
        # Before anything is logged about this instance, so the whole connect — and
        # every row it goes on to capture — is tagged with its name and not its serial.
        self._name_from_conf(inst)
        inst.fail_reason = ""
        try:
            # The verdict is now acted on. It used to be called and DISCARDED, so an
            # instance with no frida-server carried straight on: the forward went in,
            # the port read as open (adb accepts either way), and the attach died with
            # "An existing connection was forcibly closed" — a socket error standing in
            # for "this instance has no frida-server", six rows deep in a parallel
            # connect. That is the whole of why the last instances looked broken.
            if not self.ensure_frida_server(inst):
                inst.status = "no frida-server"
                reason = inst.fail_reason or "frida-server is not running on this instance."
                self._ui(lambda: self.log(f"[{inst.name}] ✗ {reason}"))
                self._ui(self._refresh_instances)
                return False
            # Each instance forwards its own host port to the device's 27042.
            self.adb(inst, "forward", f"tcp:{inst.frida_port}", "tcp:27042")
            if not self._wait_forward(inst):
                inst.status = "forward not ready"
                inst.fail_reason = (f"the adb forward 127.0.0.1:{inst.frida_port} -> "
                                    f"tcp:27042 never started carrying traffic.")
                self._ui(lambda: self.log(f"[{inst.name}] ✗ {inst.fail_reason}"))
                self._ui(self._refresh_instances)
                return False
            with self._dm_lock:
                dev = self.dm.add_remote_device(inst.addr)
            inst.session = self._attach_app(dev, inst)
            src = self.agent_js
            if os.path.exists(AGENT_PATH):
                src = open(AGENT_PATH, encoding="utf-8").read()
            # The app process gets reaped in the background and relaunched by WorkManager,
            # which kills the agent with it. Without this the instance still reads
            # "connected" while nothing is hooked — mode and guard silently stop applying.
            inst.session.on("detached", lambda *a, i=inst: self._on_detached(i, *a))
            script = inst.session.create_script(src)
            script.on("message", lambda msg, data, i=inst: self._on_message(i, msg, data))
            script.load()
            inst.script = script
            inst.status = "connected"
            inst.fail_reason = ""
            # Push hold/guard/delay now instead of waiting for the agent's 'ready' message:
            # 'ready' is queued to the GUI thread and can be processed before inst.script is
            # set here, which would silently leave a freshly-connected instance un-held.
            self._apply_state(inst)          # -> every registered panel
            self._ui(self._refresh_instances)
            return True
        except Exception as e:
            reason = self._explain(inst, e)
            inst.fail_reason = reason
            # The row stays short; the reason goes to the log whole. Truncating it to 60
            # characters was how the actionable half kept getting lost.
            inst.status = "failed"
            self._ui(lambda: self.log(f"[{inst.name}] ✗ connect failed — {reason}"))
            self._ui(self._refresh_instances)
            return False

    def _on_detached(self, inst, *args):
        """The agent died with the app process — stop claiming the instance is connected."""
        # A detach we asked for is not a crash — _teardown already reported it.
        if inst.disconnecting:
            return
        reason = args[0] if args else "unknown"
        inst.script = None
        inst.session = None
        inst.status = f"detached ({reason})"
        self._ui(self._refresh_instances)
        self._ui(lambda: self.log(
            f"[{inst.name}] ⚠ agent detached ({reason}) — the Walmart app process restarted. "
            f"Mode and checkout guard are NOT active on it. Click 'Connect' to re-attach."))

    def _teardown(self, inst):
        """Drop the session and free the host port. Safe to call on a dead device.

        Each step is guarded independently: if the emulator has gone away, unload() and
        detach() raise (or block until frida gives up) and the steps after them must
        still run, or the adb forward leaks and the next connect finds the port taken.
        """
        inst.disconnecting = True
        try:
            def drop_device():
                with self._dm_lock:
                    self.dm.remove_remote_device(inst.addr)

            for closer in (lambda: inst.script and inst.script.unload(),
                           lambda: inst.session and inst.session.detach(),
                           drop_device):
                try:
                    closer()
                except Exception:
                    pass
            inst.script = inst.session = None
            inst.status = "not connected"
            # Undo the forward this instance's connect installed, or the host port stays
            # bound and a later connect talks to a stale forward.
            try:
                adb_path = self.cfg.get("adb_path", "")
                if adb_path:
                    run([adb_path, "-s", inst.serial, "forward", "--remove",
                         f"tcp:{inst.frida_port}"], timeout=10)
            except Exception:
                pass
            # All three are properties of a live session on a live device: an emulator
            # that went away and came back may have a different clock and a cold okhttp
            # cache, and a stale value here would silently mis-aim the next timed send.
            inst.clock_off_ms = None
            inst.warm_preflight = None
            inst.oneway_ms = None
        finally:
            inst.disconnecting = False

    def disconnect(self):
        """Disconnect on a worker: frida's unload/detach block for seconds once the
        emulator is gone, and doing that on the UI thread freezes the window."""
        self._notify_panels('on_session_dropped')
        targets = [i for i in self.instances if i.connected or i.session is not None]
        if not targets:
            self.log("Nothing connected.")
            return
        self.log("Disconnecting…")
        threading.Thread(target=self._disconnect_worker, args=(targets,), daemon=True).start()

    def _disconnect_worker(self, targets):
        self.pending = None        # an explicit disconnect cancels any pending switch
        for inst in targets:
            self._teardown(inst)
        self._ui(self._refresh_instances)
        names = ", ".join(i.name for i in targets)
        self._ui(lambda: self.log(f"Disconnected from {names}."))

    def _attach_worker(self, inst):
        """Attach ONE instance, ticked while others stay up. Used by the checkbox."""
        try:
            ok = self._connect_one(inst)
            self._ui(lambda: self.log(f"[{inst.name}] connected." if ok
                                      else f"[{inst.name}] could not connect."))
        finally:
            if self.pending is not None and self.pending[0] is inst:
                self.pending = None
            self._ui(self._refresh_instances)

    def _detach_worker(self, inst):
        """Drop ONE instance's session, leaving every other one attached."""
        self._teardown(inst)
        self._ui(self._refresh_instances)
        self._ui(lambda: self.log(f"[{inst.name}] disconnected."))

    def max_instances(self):
        """How many emulators may be attached at once. Settings → max_instances."""
        try:
            return max(1, int(str(self.cfg.get("max_instances", 6)).strip() or 6))
        except Exception:
            return 6

    def _toggle_instance(self, inst):
        """Tick or untick one emulator, and make the connection match immediately.

        The picker was a radio group: clicking a row switched the single session to it
        and tore down the previous one. It is a checkbox now, and the click means what
        the box says — this emulator takes part. So:

        * ticking one while anything is connected attaches it too (the rest stay up),
        * unticking a live one detaches just it,
        * with nothing connected either way is just a tick, and Connect attaches the set.

        Attaching on tick rather than making you tick-then-Connect is deliberate: during
        a walkthrough the tick IS the intent, and the alternative is six clicks followed
        by one more.
        """
        inst.enabled = not inst.enabled
        anything_live = any(i.connected or i.session is not None for i in self.instances)

        if not inst.enabled:
            if inst.connected or inst.session is not None:
                # Only this instance's work is dropped — the panels keep everyone else's.
                self._notify_panels('on_instance_dropped', inst)
                self.log(f"Unticked {inst.name} — disconnecting it…")
                self._refresh_instances()
                threading.Thread(target=self._detach_worker, args=(inst,),
                                 daemon=True).start()
            else:
                self._refresh_instances()
            return

        if not anything_live:
            self.log(f"Ticked {inst.name}. Click Connect to attach the ticked instances.")
            self._refresh_instances()
            return

        live = len([i for i in self.instances if i.connected])
        cap = self.max_instances()
        if live >= cap:
            inst.enabled = False
            self._refresh_instances()
            self.log(f"⚠ {cap} instances are already attached (Settings → max_instances). "
                     f"Untick one before adding {inst.name}.")
            return
        self.pending = (inst, "connecting to")
        self._refresh_instances()
        threading.Thread(target=self._attach_worker, args=(inst,), daemon=True).start()

    # The picker used to be a radio group, so a click meant "switch to this one".
    # Kept as an alias because the ported suites and the panels' delegation blocks
    # still name it — it toggles now, which is what a checkbox click does.
    def _select_instance(self, inst):
        self._toggle_instance(inst)

    def _select_default(self):
        """Nothing to do — the picker's ticks are the user's, every one of them.

        This used to collapse any multi-selection back to a single instance on every
        redraw, because exactly one could be attached. Several are attached at once
        now, so a multi-tick is the normal state and has to survive a redraw.

        It does not fill an empty picker either, tempting as that is. A fresh instance
        arrives ticked (Instance.__init__), so the only way to reach zero is to ask
        for it — "Tick none", or unticking the last one — and quietly re-ticking one
        there is worse than an empty picker: you would clear the board to choose three
        accounts, get a fourth back without being told, and connect to it. Connect
        says what is wrong instead.

        Kept as a method because the panels' delegation blocks and the ported suites
        both call it.
        """
        return

    def select_all(self, on=True):
        """Tick (or untick) every detected instance, up to the cap. No connecting."""
        cap = self.max_instances()
        for n, inst in enumerate(self.instances):
            inst.enabled = bool(on) and n < cap
        if on and len(self.instances) > cap:
            self.log(f"Ticked the first {cap} of {len(self.instances)} instances "
                     f"(Settings → max_instances).")
        self._select_default()
        self._refresh_instances()

    def wanted(self):
        """Every ticked instance, in picker order. What Connect attaches."""
        return [i for i in self.instances if i.enabled]

    def live(self):
        """Every ticked instance that is actually attached — what a send fans out to."""
        return [i for i in self.instances if i.connected and i.enabled]

    def selected(self):
        """The first ticked instance, or None.

        Several instances are ticked at once now, so this is no longer "the one this
        tool talks to" — it is a single representative, for the few places that need
        one (a generated row's owner, a fallback send target). Anything that fans out
        asks for live() instead.
        """
        return next((i for i in self.instances if i.enabled), None)

    def log(self, msg):
        """Append one line, bounded and without paying for a scroll per line.

        Two things matter now that a schedule can repeat for hours:

        `see("end")` costs ~5.9 ms against ~0.04 ms for the insert itself — 150x —
        and a single cycle logs a burst of lines (six per instance). So the scroll
        is coalesced into one call per idle period rather than one per line.

        And the pane is capped: an unbounded Text never gives the memory back, and
        at ~6 lines per cycle per instance a 60 s schedule writes thousands a day.
        """
        if self.logbox is None:
            return
        self.logbox.config(state="normal")
        self.logbox.insert("end", time.strftime("%H:%M:%S ") + msg + "\n")
        excess = int(self.logbox.index("end-1c").split(".")[0]) - self.LOG_MAX_LINES
        if excess > 0:
            self.logbox.delete("1.0", f"{excess + 1}.0")
        self.logbox.config(state="disabled")
        if not self._log_scroll_pending:
            self._log_scroll_pending = True
            self.root.after_idle(self._log_scroll)

    def _log_scroll(self):
        self._log_scroll_pending = False
        try:
            self.logbox.see("end")
        except tk.TclError:
            pass          # window torn down between the schedule and the callback

    # ---------- fan-out to the panels ----------
    def _notify_panels(self, hook, *args):
        """Call an optional hook on every panel. A panel need not implement it."""
        for p in self.panels:
            fn = getattr(p, hook, None)
            if fn is None:
                continue
            try:
                fn(*args)
            except Exception as e:
                self.log(f"[{getattr(p, 'LABEL', '?')}] {hook} failed: {e}")

    def _apply_state(self, inst):
        """Push both halves' state to the freshly-attached agent.

        Done here rather than waiting for the agent's 'ready' message: 'ready' is queued
        to the GUI thread and can be processed before inst.script is set, which would
        leave a freshly-connected instance running the agent's defaults instead of what
        the panels show.
        """
        self._notify_panels("apply_state", inst)

    def _on_message(self, inst, msg, data):
        """Every agent message goes to every panel; each ignores what is not its own.

        One agent now emits both halves' messages ('capture'/'held' for the cart,
        'checkout'/'checkout_response'/'blocked' for checkout, 'error'/'ready' shared),
        so the dispatch is by message type inside each panel rather than by which
        script it came from.
        """
        if msg.get("type") == "error":
            self.log(f"agent error: {msg.get('description') or msg.get('stack') or msg}")
            return
        p = msg.get("payload") or {}
        if p.get("type") == "error":
            self.log(f"[{inst.name}] {p.get('msg')}")
            return
        for panel in self.panels:
            fn = getattr(panel, "on_message", None)
            if fn is None:
                continue
            try:
                fn(inst, p)
            except Exception as e:
                self.log(f"[{getattr(panel, 'LABEL', '?')}] message handling failed: {e}")

    def _pump(self):
        """Drain the frida->GUI queue on the Tk thread. One pump for both halves."""
        try:
            while True:
                item = self.q.get_nowait()
                t = item.get("type")
                if t == "uicall":
                    try:
                        item["fn"]()
                    except Exception:
                        pass
                elif t == "log":
                    self.log(item["msg"])
                else:
                    self._notify_panels("on_queue", item)
        except queue.Empty:
            pass
        self.root.after(150, self._pump)

    # ---------- widgets the session owns ----------
    def build_top_bar(self, parent):
        """Connect / Detect / Disconnect / status / Settings — once, for both halves."""
        top = ttk.Frame(parent, padding=(8, 6))
        # "Connect" attaches every ticked instance, not one — the plural is the point.
        ttk.Button(top, text="Connect ticked", command=self.connect).pack(side="left")
        ttk.Button(top, text="Detect", command=self._detect_clicked).pack(side="left", padx=4)
        ttk.Button(top, text="Disconnect all", command=self.disconnect).pack(side="left")
        self.status = ttk.Label(top, text="● no instances", foreground="red")
        self.status.pack(side="left", padx=10)
        ttk.Button(top, text="Settings", command=self._settings).pack(side="right")
        return top

    def build_instance_panel(self, parent):
        """The instance picker: one checkbox per emulator, several attached at once.

        Above the rows sit the two bulk actions a six-account walkthrough starts with,
        because doing that with six individual ticks is the thing this release exists
        to remove.
        """
        wrap = ttk.Frame(parent)
        bar = ttk.Frame(wrap); bar.pack(fill="x", pady=(0, 3))
        ttk.Button(bar, text="Tick all", width=9,
                   command=lambda: self.select_all(True)).pack(side="left")
        ttk.Button(bar, text="Tick none", width=10,
                   command=lambda: self.select_all(False)).pack(side="left", padx=4)
        ttk.Label(bar, text="tick the emulators to use, then Connect — "
                           "a tick while connected attaches that one on its own",
                  foreground="#6b6b6b").pack(side="left", padx=8)
        self.inst_rows = ttk.Frame(wrap)
        self.inst_rows.pack(fill="x")
        self._refresh_instances()
        return wrap

    def build_log(self, parent):
        """The one log. Both halves write here, in the order things happened."""
        wrap = ttk.Frame(parent)
        bar = ttk.Frame(wrap); bar.pack(fill="x")
        ttk.Button(bar, text="Copy log", command=self.copy_log).pack(side="left")
        ttk.Button(bar, text="Save log…", command=self.save_log).pack(side="left", padx=4)
        ttk.Button(bar, text="Clear", command=self.clear_log).pack(side="left")
        body = ttk.Frame(wrap); body.pack(fill="both", expand=True, pady=(4, 0))
        sb = ttk.Scrollbar(body, orient="vertical")
        self.logbox = tk.Text(body, height=14, wrap="word", state="disabled",
                              yscrollcommand=sb.set)
        sb.config(command=self.logbox.yview)
        sb.pack(side="right", fill="y")
        self.logbox.pack(side="left", fill="both", expand=True)
        return wrap

    def _refresh_instances(self):
        """Redraw the picker. Generic here; each panel contributes its own row note."""
        if self.inst_rows is None:
            return
        for w in self.inst_rows.winfo_children():
            w.destroy()
        if not self.instances:
            ttk.Label(self.inst_rows, text="no instances detected — click Detect",
                      foreground="#6b6b6b").pack(anchor="w", padx=4, pady=2)
        self._select_default()
        self._tick_vars = {}
        for n, inst in enumerate(self.instances, 1):
            row = ttk.Frame(self.inst_rows); row.pack(fill="x", padx=2, pady=1)
            var = tk.BooleanVar(master=self.root, value=bool(inst.enabled))
            self._tick_vars[inst.key] = var
            cb = ttk.Checkbutton(row, text=f"{n}.  {inst.name}  [{inst.serial}]",
                                 variable=var,
                                 command=lambda i=inst: self._toggle_instance(i))
            cb.pack(side="left")
            bad = (not inst.connected) and str(inst.status).startswith(
                ("failed", "detached", "no frida-server", "forward not ready"))
            ttk.Label(row, text=inst.status, foreground=(
                "#0a7d00" if inst.connected else
                "#b30000" if bad else "#6b6b6b")).pack(side="left", padx=8)
            # The first sentence of why, on the row itself. A six-way connect writes
            # six instances' output into one log, so a failure that only says "failed"
            # here means scrolling to find out which of six things went wrong; the
            # whole reason is still in the log and in the tooltip-length text below.
            if bad and inst.fail_reason:
                short = inst.fail_reason.split(" — ")[0].split(". ")[0]
                ttk.Label(row, text=f"· {short[:72]}",
                          foreground="#b06000").pack(side="left", padx=4)
            note = self._panel_note(inst)
            if note:
                ttk.Label(row, text=note, foreground="#6b6b6b").pack(side="left", padx=6)
        # The radio var is kept in step for anything still reading it (the ported
        # suites do); it names the first ticked instance, which is what selected() is.
        try:
            self._pick_var.set(next((i.key for i in self.instances if i.enabled), ""))
        except Exception:
            pass
        self._refresh_status()

    def _refresh_status(self):
        """The header dot. Reports a switch in flight rather than a stale truth."""
        if self.status is None:
            return
        if self.pending is not None:
            inst, verb = self.pending
            self.status.config(text=f"● {verb} {inst.name}…", foreground="#b36b00")
            return
        if not self.instances:
            self.status.config(text="● no instances", foreground="#b30000")
            return
        # Several accounts are attached at once, so the header counts them and names
        # them rather than claiming one. The count against the number ticked is the
        # thing to read mid-walkthrough: "4 of 6" says two never came up.
        live = [i for i in self.instances if i.connected and i.enabled]
        if live:
            names = ", ".join(i.name for i in live)
            want = len(self.wanted())
            self.status.config(
                text=(f"● connected: {len(live)} of {want} ticked — {names}"
                      if len(live) != want else
                      f"● connected: {len(live)} — {names}"),
                foreground=("#0a7d00" if len(live) == want else "#b06000"))
            return
        # A session object with no live connection means a teardown did not finish —
        # say so and name it, rather than reporting a clean "not connected" that hides
        # an instance still holding a frida session and an adb forward.
        stale = next((i for i in self.instances
                      if i.session is not None or i.connected), None)
        if stale:
            self.status.config(text=f"● still attached to {stale.name} — Disconnect",
                               foreground="#b06000")
        else:
            self.status.config(text="● not connected", foreground="#b30000")

    # ---------- settings ----------
    def _settings(self):
        """One dialog for the union of both halves' keys — there is one config.json."""
        w = tk.Toplevel(self.root); w.title("Settings")
        w.geometry(f"640x{min(780, 90 + 30 * (len(self.cfg) + 1))}")
        w.minsize(560, 240)
        entries = {}
        for i, (k, v) in enumerate(self.cfg.items()):
            ttk.Label(w, text=k).grid(row=i, column=0, sticky="e", padx=4, pady=3)
            e = ttk.Entry(w, width=64); e.insert(0, str(v)); e.grid(row=i, column=1, padx=4, pady=3)
            entries[k] = e

        def save():
            for k, e in entries.items():
                self.cfg[k] = e.get().strip()
            save_json(CONFIG_PATH, self.cfg)
            w.destroy()
            self.log("Settings saved.")
            self._notify_panels("on_config_saved")

        ttk.Button(w, text="Save", command=save).grid(row=len(self.cfg), column=1,
                                                      sticky="e", pady=8)

    # ---------- log helpers (the checkout half's, now shared) ----------
    def log_text(self):
        try:
            return self.logbox.get("1.0", "end-1c")
        except Exception:
            return ""

    def copy_log(self):
        text = self.log_text()
        if not text:
            return
        self.root.clipboard_clear()
        self.root.clipboard_append(text)
        self.log(f"Copied {len(text)} chars of log to the clipboard.")

    def save_log(self):
        path = os.path.join(BASE, time.strftime("toolkit_log_%Y%m%d-%H%M%S.txt"))
        try:
            open(path, "w", encoding="utf-8").write(self.log_text())
        except Exception as e:
            messagebox.showerror("Save log", str(e))
            return
        self.log(f"Saved log to {path}")

    def clear_log(self):
        self.logbox.config(state="normal")
        self.logbox.delete("1.0", "end")
        self.logbox.config(state="disabled")

    # ---------- shutdown ----------
    def shutdown(self):
        """Drop the session on the way out, so no agent is left hooked and no adb
        forward stays bound for the next run to trip over."""
        self._notify_panels("on_session_dropped")
        for inst in list(self.instances):
            if inst.connected or inst.session is not None:
                try:
                    self._teardown(inst)
                except Exception:
                    pass
