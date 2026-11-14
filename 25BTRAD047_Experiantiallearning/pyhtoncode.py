#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
CattleWatch - Highway Cow Alert
Python (tkinter) port of the original single-file HTML app.

Run:   python cattlewatch.py          (add --dark for the dark theme)
Needs: only the Python standard library (tkinter ships with Python on Windows / macOS).

Sections follow the same order as the original script:
  constants -> core sim (draw / beep / log / tick / start / brake) -> multi-view renderer
  -> traffic -> voice -> extras (limits, blind spot, fatigue, replay, history, coach)
  -> conditions / scenario / daily challenge / voice commands / copy log / night
"""
import math
import os
import random
import re
import shutil
import subprocess
import sys
import threading
import time
import types
import json
import tkinter as tk
import tkinter.font as tkfont
from datetime import datetime
from tkinter import ttk

try:
    import winsound
except Exception:  # not on Windows
    winsound = None

# ------------------------------------------------------------------ constants
W, H = 480, 340
MAX, BASE, STOP_GAP, PATH, MEDIAN_END = 150, 50, 20, 2.75, 8.25

LIGHT = dict(bg="#eef0f2", panel="#ffffff", text="#16202a", muted="#5b6773", road="#3a4048",
             shoulder="#8b929b", median="#7f9a78", lane="#f3f3f3", safe="#1f8a4c", warn="#c76a00",
             danger="#c62828", accent="#1b5fa8", border="#d5dae0")
DARK = dict(bg="#10151b", panel="#1a222b", text="#eef2f6", muted="#93a1af", road="#262b31",
            shoulder="#171b20", median="#34452f", lane="#d9d9d9", safe="#4cc27f", warn="#ffb020",
            danger="#ff5252", accent="#6db3ff", border="#2b3641")

WHERE = [("0", "Your lane"), ("3.5", "Next lane (same direction)"), ("6.75", "Median"),
         ("10", "Opposite road, near lane"), ("13.5", "Opposite road, far lane")]
WX = [("clear", "Clear"), ("rain", "Rain + wipers"), ("fog", "Fog"), ("glare", "Sun glare (dusk)")]
SURF = [("1", "Dry"), (".65", "Wet"), (".5", "Gravel")]
LOAD = [("1", "Empty"), (".75", "Fully loaded")]
HZ = [("", "COW", "Cow"), ("\U0001F403", "BUFFALO", "Buffalo"), ("\U0001F415", "DOG", "Dog"),
      ("\U0001F6B6", "PERSON", "Person"), ("\U0001F697", "STALLED CAR", "Stalled car")]
LANG = [("en-IN", "English"), ("hi-IN", "\u0939\u093f\u0928\u094d\u0926\u0940"),
        ("te-IN", "\u0c24\u0c46\u0c32\u0c41\u0c17\u0c41")]
DIFF = [("easy", "Easy: clear day"), ("normal", "Normal"), ("hard", "Hard: foggy/rainy night")]

TXT = {
    "en-IN": {"a": lambda d: "Cow ahead, %d metres. Brake now." % d,
              "b": lambda d: "Automatic braking engaged."},
    "hi-IN": {"a": lambda d: "\u0938\u093e\u0935\u0927\u093e\u0928! \u0906\u0917\u0947 \u0917\u093e\u092f, %d \u092e\u0940\u091f\u0930\u0964 \u092c\u094d\u0930\u0947\u0915 \u0932\u0917\u093e\u090f\u0902\u0964" % d,
              "b": lambda d: "\u0911\u091f\u094b\u092e\u0948\u091f\u093f\u0915 \u092c\u094d\u0930\u0947\u0915 \u091a\u093e\u0932\u0942\u0964"},
    "te-IN": {"a": lambda d: "\u0c1c\u0c3e\u0c17\u0c4d\u0c30\u0c24\u0c4d\u0c24! \u0c2e\u0c41\u0c02\u0c26\u0c41 \u0c06\u0c35\u0c41, %d \u0c2e\u0c40\u0c1f\u0c30\u0c4d\u0c32\u0c41. \u0c2c\u0c4d\u0c30\u0c47\u0c15\u0c4d \u0c35\u0c47\u0c2f\u0c02\u0c21\u0c3f." % d,
              "b": lambda d: "\u0c06\u0c1f\u0c4b\u0c2e\u0c47\u0c1f\u0c3f\u0c15\u0c4d \u0c2c\u0c4d\u0c30\u0c47\u0c15\u0c4d \u0c2a\u0c28\u0c3f\u0c1a\u0c47\u0c38\u0c4d\u0c24\u0c4b\u0c02\u0c26\u0c3f."},
}

HZ_NAMES = {"en-IN": ["Cow", "Buffalo", "Dog", "Person", "Stalled vehicle"],
            "hi-IN": ["\u0917\u093e\u092f", "\u092d\u0948\u0902\u0938", "\u0915\u0941\u0924\u094d\u0924\u093e", "\u0935\u094d\u092f\u0915\u094d\u0924\u093f", "\u0916\u0921\u093c\u0940 \u0917\u093e\u0921\u093c\u0940"],
            "te-IN": ["\u0c06\u0c35\u0c41", "\u0c17\u0c47\u0c26\u0c46", "\u0c15\u0c41\u0c15\u0c4d\u0c15", "\u0c35\u0c4d\u0c2f\u0c15\u0c4d\u0c24\u0c3f", "\u0c06\u0c17\u0c3f\u0c28 \u0c35\u0c3e\u0c39\u0c28\u0c02"]}
HERD_NAMES = {"en-IN": "Herd of animals", "hi-IN": "\u091c\u093e\u0928\u0935\u0930\u094b\u0902 \u0915\u093e \u091d\u0941\u0902\u0921",
              "te-IN": "\u0c1c\u0c02\u0c24\u0c41\u0c35\u0c41\u0c32 \u0c2e\u0c02\u0c26"}

CAMS = {
    "cabin": dict(l=0, h=2.4, f=250, hy=135, back=0, zs=2.2),
    "chase": dict(l=0, h=4.2, f=250, hy=118, back=18, zs=-14),
    "drone": dict(l=0, h=18, f=250, hy=60, back=40, zs=-30),
    "thermal": dict(l=0, h=2.4, f=250, hy=135, back=0, zs=2.2),
}

VT = {"car": dict(w=1.8, h=1.5, l=22, c=["#c0392b", "#2980b9", "#ecf0f1", "#f1c40f", "#7f8c8d"]),
      "truck": dict(w=2.5, h=3.3, l=40, c=["#e67e22", "#16a085", "#8e44ad"]),
      "bus": dict(w=2.5, h=3.2, l=38, c=["#d35400", "#c0392b"]),
      "auto": dict(w=1.4, h=1.7, l=18, c=["#f1c40f"]),
      "bike": dict(w=.7, h=1.4, l=14, c=["#34495e"])}

DATA_FILE = os.path.join(os.path.expanduser("~"), ".cattlewatch.json")
NO_WINDOW = 0x08000000 if sys.platform.startswith("win") else 0


# ------------------------------------------------------------------ helpers
def jround(x):
    """JavaScript Math.round"""
    return int(math.floor(x + 0.5))


def _rgb(c):
    if isinstance(c, str):
        c = c.lstrip("#")
        return (int(c[0:2], 16), int(c[2:4], 16), int(c[4:6], 16))
    return tuple(c)


def hx(c):
    if isinstance(c, str):
        return c
    return "#%02x%02x%02x" % tuple(max(0, min(255, int(round(v)))) for v in c)


def blend(fg, a, bg):
    f, b = _rgb(fg), _rgb(bg)
    return hx(tuple(f[i] * a + b[i] * (1 - a) for i in range(3)))


def lerp(c1, c2, t):
    return blend(c2, max(0, min(1, t)), c1)


def stipple_for(a):
    """Tk canvas has no alpha; translucent fills are approximated with stipple patterns."""
    if a >= .9:
        return ""
    if a >= .62:
        return "gray75"
    if a >= .38:
        return "gray50"
    if a >= .18:
        return "gray25"
    if a >= .06:
        return "gray12"
    return None


def P3(l, z, y, k):
    zz = max(.6, z + k["back"])
    sc = k["f"] / zz
    return (W / 2 + (l - k["l"]) * sc, k["hy"] + (k["h"] - y) * sc, sc)


def zoneOf(l):
    a = abs(l)
    if a <= PATH:
        return "path"
    if l <= MEDIAN_END:
        return "watch"
    return "ignore"


def pct(l):
    return (l + 2.5) / 18 * 100


def yFor(d):
    return 22 + max(0, min(d, MAX)) / MAX * (340 - 22 - 78 - 20) + 78


def now_ms():
    return time.perf_counter() * 1000.0


def detect_dark():
    try:
        import winreg
        k = winreg.OpenKey(winreg.HKEY_CURRENT_USER,
                           r"Software\Microsoft\Windows\CurrentVersion\Themes\Personalize")
        return winreg.QueryValueEx(k, "AppsUseLightTheme")[0] == 0
    except Exception:
        return False


# ------------------------------------------------------------------ canvas wrapper
class Gfx:
    """Thin drawing layer over tk.Canvas (alpha via stipple, thermal colour filter)."""

    def __init__(self, cv):
        self.cv = cv
        self.xf = False
        self._fonts = {}

    def font(self, px, bold=True, family="Arial"):
        key = (round(px), bold, family)
        if key not in self._fonts:
            self._fonts[key] = tkfont.Font(family=family, size=-max(1, round(px)),
                                           weight="bold" if bold else "normal")
        return self._fonts[key]

    def col(self, c):
        c = _rgb(c)
        if self.xf:  # thermal: desaturate, tint green, darken
            g = .299 * c[0] + .587 * c[1] + .114 * c[2]
            c = (g * .5 * .55, g * .635 * .55 + 4.5, g * .56 * .55 + 2.25)
        return hx(c)

    def rect(self, x0, y0, x1, y1, fill, a=1):
        st = stipple_for(a)
        if st is None:
            return
        kw = {"stipple": st} if st else {}
        self.cv.create_rectangle(x0, y0, x1, y1, fill=self.col(fill), outline="", **kw)

    def poly(self, pts, fill, a=1):
        st = stipple_for(a)
        if st is None:
            return
        flat = [v for p in pts for v in (p[0], p[1])]
        kw = {"stipple": st} if st else {}
        self.cv.create_polygon(flat, fill=self.col(fill), outline="", **kw)

    def oval(self, cx, cy, rx, ry, fill, a=1):
        st = stipple_for(a)
        if st is None or rx <= 0 or ry <= 0:
            return
        kw = {"stipple": st} if st else {}
        self.cv.create_oval(cx - rx, cy - ry, cx + rx, cy + ry, fill=self.col(fill), outline="", **kw)

    def line(self, pts, fill, width=1, dash=None):
        flat = [v for p in pts for v in (p[0], p[1])]
        kw = {"dash": dash} if dash else {}
        self.cv.create_line(flat, fill=self.col(fill), width=width, **kw)

    def text(self, x, y, s, font, fill, anchor="center", angle=0):
        kw = {"angle": angle} if angle else {}
        self.cv.create_text(x, y, text=s, font=font, fill=self.col(fill), anchor=anchor, **kw)

    def pill(self, x, y, w, h, fill, a=1):
        r = min(8, h / 2, w / 2)
        pts = [(x + r, y), (x + w - r, y), (x + w, y), (x + w, y + r), (x + w, y + h - r), (x + w, y + h),
               (x + w - r, y + h), (x + r, y + h), (x, y + h), (x, y + h - r), (x, y + r), (x, y)]
        st = stipple_for(a)
        if st is None:
            return
        flat = [v for p in pts for v in p]
        kw = {"stipple": st} if st else {}
        self.cv.create_polygon(flat, fill=self.col(fill), outline="", smooth=True, **kw)

    def pool(self, x, y, rx, ry, rgb, a):
        """Radial light pool approximated with 3 stacked stippled ovals."""
        rx = max(1, min(rx, 1200))
        ry = max(1, min(ry, 1200))
        for f, k in ((1, .35), (.62, .4), (.3, .5)):
            self.oval(x, y, rx * f, ry * f, rgb, a * k)


# ------------------------------------------------------------------ speech (stand-in for speechSynthesis)
WIN_SPEAK = ("Add-Type -AssemblyName System.Speech;"
             "$s=New-Object System.Speech.Synthesis.SpeechSynthesizer;"
             "if($env:CW_VOICE){try{$s.SelectVoice($env:CW_VOICE)}catch{}};"
             "$s.Volume=[int]$env:CW_VOL;$s.Speak($env:CW_TEXT)")


class Speech:
    def __init__(self):
        self.voices = []
        self.proc = None
        self.dirty = False
        self.mode = None
        if sys.platform.startswith("win") and shutil.which("powershell"):
            self.mode = "win"
        elif sys.platform == "darwin" and shutil.which("say"):
            self.mode = "mac"
        elif shutil.which("espeak") or shutil.which("espeak-ng"):
            self.mode = "espeak"
        if self.mode:
            threading.Thread(target=self._load, daemon=True).start()

    def _load(self):
        v = []
        try:
            if self.mode == "win":
                out = subprocess.run(
                    ["powershell", "-NoProfile", "-Command",
                     "Add-Type -AssemblyName System.Speech;"
                     "(New-Object System.Speech.Synthesis.SpeechSynthesizer).GetInstalledVoices()|"
                     "ForEach-Object{$_.VoiceInfo.Name+'|'+$_.VoiceInfo.Culture.Name}"],
                    capture_output=True, text=True, timeout=40, creationflags=NO_WINDOW).stdout
                for line in out.splitlines():
                    if "|" in line:
                        n, l = line.strip().split("|", 1)
                        v.append({"name": n, "lang": l})
            elif self.mode == "mac":
                out = subprocess.run(["say", "-v", "?"], capture_output=True, text=True, timeout=20).stdout
                for line in out.splitlines():
                    m = re.match(r"^(.+?)\s{2,}([a-z]{2}[_-][A-Za-z]{2})", line)
                    if m:
                        v.append({"name": m.group(1).strip(), "lang": m.group(2)})
        except Exception:
            pass
        self.voices = v
        self.dirty = True

    def cancel(self):
        try:
            if self.proc and self.proc.poll() is None:
                self.proc.kill()
        except Exception:
            pass

    def speak(self, text, voice, volume):
        self.cancel()
        try:
            if self.mode == "win":
                env = dict(os.environ, CW_TEXT=text, CW_VOICE=voice["name"] if voice else "",
                           CW_VOL=str(int(max(0, min(1, volume)) * 100)))
                self.proc = subprocess.Popen(["powershell", "-NoProfile", "-Command", WIN_SPEAK],
                                             env=env, creationflags=NO_WINDOW)
            elif self.mode == "mac":
                self.proc = subprocess.Popen(["say"] + (["-v", voice["name"]] if voice else []) + [text])
            elif self.mode == "espeak":
                exe = shutil.which("espeak") or shutil.which("espeak-ng")
                self.proc = subprocess.Popen([exe, "-a", str(int(max(0, min(1, volume)) * 200)), text])
        except Exception:
            pass


# ------------------------------------------------------------------ select helper
class Sel:
    def __init__(self, parent, options, command=None, index=0, width=26):
        self.options = options
        self.var = tk.StringVar()
        self.cb = ttk.Combobox(parent, textvariable=self.var, values=[o[-1] for o in options],
                               state="readonly", width=width)
        self.cb.current(index)
        self.command = command
        self.cb.bind("<<ComboboxSelected>>", self._sel)

    def _sel(self, _e=None):
        self.cb.selection_clear()
        if self.command:
            self.command()

    @property
    def index(self):
        return max(0, self.cb.current())

    @property
    def value(self):
        return self.options[self.index][0]

    @property
    def opt(self):
        return self.options[self.index]

    @property
    def text(self):
        return self.options[self.index][-1]

    def set_value(self, v):
        for i, o in enumerate(self.options):
            if o[0] == v:
                self.cb.current(i)
                return

    def set_index(self, i):
        self.cb.current(i)

    def enable(self, on):
        self.cb.configure(state="readonly" if on else "disabled")


# ================================================================== the app
class App:
    def __init__(self, root, dark=False):
        self.root = root
        self.dark = dark
        self.hc = False
        self.lg = False
        self.T = self.theme()
        self._reg = []
        self._quiet = False
        self.fonts = {}
        self.vb_state = {}

        # ---- core sim state (var MAX.., s = {...})
        self.DECEL = 5.0
        self.REACT = 1.5
        self.CROSS_SPEED = 1.5
        self.s = types.SimpleNamespace(
            dist=MAX, lat=0.0, speed=60.0, running=False, braking=False, last=0.0, off=0.0,
            alerted=False, ignLogged=False, watchLogged=False, beepT=0.0, audio=False, autoOn=False,
            autoLogged=False, honkT=0.0, minD=1e9, topV=60.0)
        self.view = "top"
        self.night = False
        self.HERD = False
        self.OFF = [0, 0]
        self.HAZ = ""
        self.HN = "COW"
        self.hb = False
        self.wxv = "clear"
        self.SND = True
        self.VOL = .6
        self.lt = None
        self.bclass = "safe"
        self._bpaint = None
        self.flash_on = False
        # ---- extras state
        self.B = {"s": 0, "b": []}
        self.HS = []
        self.DAILY = False
        self.aT = None
        self.bT = None
        self.tt = 0.0
        self.vF = -1.0
        self.gF = 35.0
        self.brT = 0.0
        self.DB = 0.0
        self.FADE = 0.0
        self.REC = []
        self.rt = 0.0
        self.fat = 0.0
        self.pt = -1.0
        self.pl = 0
        self.odo = 0.0
        self.LIMV = 80
        self.OVER = False
        self.log_items = []
        self.thr_text = ""

        self.speech = Speech()
        self.TR = self.initTr()
        self.RAIN = [[random.random() * W, random.random() * H, 6 + random.random() * 8] for _ in range(110)]
        self.STARS = []
        r = 7
        for _ in range(80):
            r = (r * 9301 + 49297) % 233280
            a = r / 233280
            r = (r * 9301 + 49297) % 233280
            self.STARS.append((a * W, r / 233280, .8 + a * 1.2))

        self.build_ui()
        self.load_data()
        self.hist()
        self.s.speed = 60
        self.draw()
        self.root.after(500, self.vstat)
        self.root.bind("<Key-h>", lambda e: self.honk())
        self.root.bind("<Key-H>", lambda e: self.honk())
        self.root.after(16, self.frame)

    # ------------------------------------------------------------ theme / widget factories
    def theme(self):
        T = dict(DARK if self.dark else LIGHT)
        if self.hc:
            T.update(bg="#000000", panel="#000000", text="#ffffff", muted="#e6e6e6", border="#ffffff")
        return T

    def reg(self, w, fn):
        self._reg.append((w, fn))
        w.configure(**fn(self.T))
        return w

    def restyle(self):
        self.T = self.theme()
        for w, fn in self._reg:
            try:
                w.configure(**fn(self.T))
            except tk.TclError:
                pass
        st = ttk.Style()
        T = self.T
        st.configure("TCombobox", fieldbackground=T["bg"], background=T["panel"], foreground=T["text"],
                     arrowcolor=T["text"], bordercolor=T["border"], lightcolor=T["bg"], darkcolor=T["bg"])
        st.map("TCombobox", fieldbackground=[("readonly", T["bg"]), ("disabled", T["bg"])],
               foreground=[("readonly", T["text"]), ("disabled", T["muted"])],
               selectbackground=[("readonly", T["bg"])], selectforeground=[("readonly", T["text"])])
        self.root.option_add("*TCombobox*Listbox.background", T["panel"])
        self.root.option_add("*TCombobox*Listbox.foreground", T["text"])
        self._bpaint = None
        self.paint_banner()
        self.cv.configure(highlightbackground=T["border"])

    def mkfont(self, name, px, weight="normal"):
        f = tkfont.Font(family="Segoe UI", size=-int(round(px)), weight=weight)
        self.fonts[name] = (f, px)
        return f

    def set_large(self, on):
        k = 1.2 if on else 1
        for name, (f, px) in self.fonts.items():
            p = px * k
            if name == "msg":
                p = 20.8 if on else px
            f.configure(size=-int(round(p)))

    def lab(self, parent, text="", bg="panel", fg="text", font=None, **kw):
        w = tk.Label(parent, text=text, font=font or self.f_base, **kw)
        return self.reg(w, lambda T: {"bg": T.get(bg, bg), "fg": T.get(fg, fg)})

    def frm(self, parent, bg="panel", border=False):
        w = tk.Frame(parent)
        if border:
            return self.reg(w, lambda T: {"bg": T.get(bg, bg), "highlightthickness": 1,
                                          "highlightbackground": T["border"], "highlightcolor": T["border"]})
        return self.reg(w, lambda T: {"bg": T.get(bg, bg)})

    def chk(self, parent, text, var, cmd=None):
        w = tk.Checkbutton(parent, text=text, variable=var, command=cmd, anchor="w", justify="left",
                           wraplength=430, font=self.f_base, bd=0, highlightthickness=0)
        return self.reg(w, lambda T: {"bg": T["panel"], "fg": T["muted"], "activebackground": T["panel"],
                                      "activeforeground": T["muted"], "selectcolor": T["bg"]})

    def btn(self, parent, text, bg, fg, cmd=None):
        w = tk.Button(parent, text=text, command=cmd, font=self.f_btn, bd=0, relief="flat",
                      cursor="hand2", pady=10)
        return self.reg(w, lambda T: {"bg": T.get(bg, bg), "fg": T.get(fg, fg), "activebackground": T.get(bg, bg),
                                      "activeforeground": T.get(fg, fg), "disabledforeground": "#d8d8d8"})

    def scale(self, parent, frm, to, res, val, cmd):
        w = tk.Scale(parent, from_=frm, to=to, resolution=res, orient="horizontal", showvalue=0,
                     command=lambda v: None if self._quiet else cmd(), bd=0, highlightthickness=0, length=300)
        w.set(val)
        return self.reg(w, lambda T: {"bg": T["panel"], "troughcolor": T["border"],
                                      "activebackground": T["accent"]})

    def qset(self, sc, v):
        self._quiet = True
        try:
            sc.set(v)
        finally:
            self._quiet = False

    # ------------------------------------------------------------ UI
    def build_ui(self):
        r = self.root
        self.f_base = self.mkfont("base", 14)
        self.f_h1 = self.mkfont("h1", 18, "bold")
        self.f_sub = self.mkfont("sub", 13)
        self.f_msg = self.mkfont("msg", 17, "bold")
        self.f_dist = self.mkfont("dist", 54, "bold")
        self.f_small = self.mkfont("small", 18, "bold")
        self.f_ttc = self.mkfont("ttc", 13)
        self.f_bsw = self.mkfont("bsw", 12, "bold")
        self.f_hint = self.mkfont("hint", 12)
        self.f_log = self.mkfont("log", 13)
        self.f_h2 = self.mkfont("h2", 15, "bold")
        self.f_btn = self.mkfont("btn", 14, "bold")
        self.f_vb = self.mkfont("vb", 13)
        self.f_bold = self.mkfont("bold", 14, "bold")
        ttk.Style().theme_use("clam")

        outer = tk.Canvas(r, highlightthickness=0)
        sb = tk.Scrollbar(r, orient="vertical", command=outer.yview)
        outer.configure(yscrollcommand=sb.set)
        sb.pack(side="right", fill="y")
        outer.pack(side="left", fill="both", expand=True)
        self.reg(outer, lambda T: {"bg": T["bg"]})
        main = tk.Frame(outer)
        self.reg(main, lambda T: {"bg": T["bg"]})
        win = outer.create_window(0, 0, window=main, anchor="n")
        main.bind("<Configure>", lambda e: outer.configure(scrollregion=(0, 0, main.winfo_reqwidth(), main.winfo_reqheight())))
        outer.bind("<Configure>", lambda e: outer.coords(win, e.width // 2, 0))
        r.bind_all("<MouseWheel>", lambda e: outer.yview_scroll(int(-e.delta / 120) or (-1 if e.delta > 0 else 1), "units"))
        r.bind_all("<Button-4>", lambda e: outer.yview_scroll(-1, "units"))
        r.bind_all("<Button-5>", lambda e: outer.yview_scroll(1, "units"))
        r.unbind_class("TCombobox", "<MouseWheel>")
        r.unbind_class("TCombobox", "<Button-4>")
        r.unbind_class("TCombobox", "<Button-5>")
        pad = dict(padx=14)

        # --- header
        head = self.frm(main, "bg")
        head.pack(fill="x", pady=(14, 6), **pad)
        self.lab(head, "CattleWatch", "bg", "text", self.f_h1, anchor="w").pack(fill="x")
        self.lab(head, "Highway cow alert for truck drivers (simulation, 4-lane divided highway) \u00b7 switch views below",
                 "bg", "muted", self.f_sub, anchor="w", justify="left", wraplength=470).pack(fill="x")

        # --- banner
        self.banner = tk.Frame(main, highlightthickness=2, padx=14, pady=10)
        self.banner.pack(fill="x", pady=6, **pad)
        self.bwidgets = []
        left = tk.Frame(self.banner)
        left.pack(side="left", fill="both", expand=True)
        self.msg = tk.Label(left, text="Road clear. Press Start trip.", font=self.f_msg, anchor="w",
                            justify="left", wraplength=240)
        self.msg.pack(anchor="w")
        right = tk.Frame(self.banner)
        right.pack(side="right")
        drow = tk.Frame(right)
        drow.pack(anchor="e")
        self.dist_num = tk.Label(drow, text="150", font=self.f_dist)
        self.dist_num.pack(side="left")
        self.dist_small = tk.Label(drow, text="m", font=self.f_small)
        self.dist_small.pack(side="left", anchor="s", pady=(0, 8))
        self.ttc = tk.Label(right, text="", font=self.f_ttc, anchor="e", justify="right")
        self.ttc.pack(anchor="e")
        self.bsw = tk.Label(right, text="", font=self.f_bsw, anchor="e", justify="right", wraplength=200)
        self.bsw.pack(anchor="e")
        self.bwidgets = [left, self.msg, right, drow, self.dist_num, self.dist_small, self.ttc, self.bsw]

        # --- views
        views = self.frm(main, "bg")
        views.pack(fill="x", pady=4, **pad)
        self.lab(views, "View", "bg", "muted", self.f_bold).grid(row=0, column=0, sticky="w", padx=(0, 6))
        spec = [("top", "\U0001F6F0 Top"), ("cabin", "\U0001F68B Driver cabin"), ("chase", "\U0001F3A5 Chase cam"),
                ("drone", "\U0001F681 Drone"), ("thermal", "\U0001F321 Thermal"), ("radar", "\U0001F4E1 Radar"),
                ("nt", "\U0001F319 Night"), ("hb", "\U0001F4A1 High beam")]
        self.vbtn = {}
        rows = [spec[:4], spec[4:]]
        for ri, items in enumerate(rows):
            for ci, (key, text) in enumerate(items):
                self.vb_state[key] = (key == "top")
                b = tk.Button(views, text=text, font=self.f_vb, bd=1, relief="solid", cursor="hand2", padx=8, pady=4)
                self.reg(b, lambda T, k=key: ({"bg": T["accent"], "fg": T["bg"], "activebackground": T["accent"],
                                               "highlightbackground": T["accent"]} if self.vb_state[k] else
                                              {"bg": T["panel"], "fg": T["text"], "activebackground": T["panel"],
                                               "highlightbackground": T["border"]}))
                b.grid(row=ri, column=ci + (1 if ri == 0 else 0) + (0), padx=3, pady=3, sticky="w")
                self.vbtn[key] = b
        for key in ("top", "cabin", "chase", "drone", "thermal", "radar"):
            self.vbtn[key].configure(command=lambda k=key: self.set_view(k))
        self.vbtn["nt"].configure(command=self.toggle_night)
        self.vbtn["hb"].configure(command=self.toggle_hb)

        # --- canvas
        self.cv = tk.Canvas(main, width=W, height=H, bg="#000000", highlightthickness=1)
        self.cv.pack(pady=6, **pad)
        self.g = Gfx(self.cv)

        # --- panel 1
        p1 = self.frm(main, "panel", border=True)
        p1.pack(fill="x", pady=6, ipadx=10, ipady=8, **pad)
        row = self.frm(p1)
        row.pack(fill="x", padx=10, pady=4)
        self.lab(row, "Cow location").pack(side="left")
        self.where = Sel(row, WHERE, command=self.on_where)
        self.where.cb.pack(side="right")
        self.cross_v = tk.BooleanVar(value=False)
        self.cross = self.chk(p1, "Cow is crossing toward your lane", self.cross_v)
        self.cross.pack(fill="x", padx=10, pady=2)
        self.lab(p1, "Only a cow in your path gives the red alert and auto-brake. A cow on the opposite road is ignored.",
                 "panel", "muted", self.f_hint, anchor="w", justify="left", wraplength=440).pack(fill="x", padx=10, pady=2)
        row = self.frm(p1)
        row.pack(fill="x", padx=10, pady=(6, 0))
        self.lab(row, "Truck speed").pack(side="left")
        self.spv = self.lab(row, "60 km/h", "panel", "text", self.f_bold)
        self.spv.pack(side="right")
        self.speedIn = self.scale(p1, 20, 100, 1, 60, self.on_speed)
        self.speedIn.pack(fill="x", padx=10)
        self.adapt_v = tk.BooleanVar(value=False)
        self.adapt = self.chk(p1, "Scale alert distance with speed (stopping distance), minimum 50 m", self.adapt_v, self.draw)
        self.adapt.pack(fill="x", padx=10, pady=2)
        self.auto_v = tk.BooleanVar(value=True)
        self.auto = self.chk(p1, "Automatic emergency braking: the truck brakes by itself so it stops at least 20 m before a cow in your path",
                             self.auto_v)
        self.auto.pack(fill="x", padx=10, pady=2)
        btns = self.frm(p1)
        btns.pack(fill="x", padx=10, pady=6)
        btns.columnconfigure(0, weight=1)
        btns.columnconfigure(1, weight=1)
        self.startB = self.btn(btns, "Start trip", "accent", "#ffffff", self.start)
        self.startB.grid(row=0, column=0, sticky="ew", padx=4, pady=4)
        self.brakeB = self.btn(btns, "Hold to brake", "danger", "#ffffff")
        self.brakeB.grid(row=0, column=1, sticky="ew", padx=4, pady=4)
        self.brakeB.configure(state="disabled")
        self.brakeB.bind("<ButtonPress-1>", self.brakeOn)
        self.brakeB.bind("<ButtonRelease-1>", lambda e: self.brakeOff())
        self.brakeB.bind("<Leave>", lambda e: self.brakeOff())
        self.honkB = self.btn(btns, "\U0001F4EF Honk (H)", "warn", "#16202a", self.honk)
        self.honkB.grid(row=1, column=0, sticky="ew", padx=4, pady=4)
        self.alrt = self.btn(btns, "Tap: I\u2019m alert", "danger", "#ffffff", self.on_alert)
        self.alrt.grid(row=1, column=1, sticky="ew", padx=4, pady=4)
        self.alrt.grid_remove()
        self.result = tk.Label(p1, text="", font=self.f_bold, anchor="w")
        self.reg(self.result, lambda T: {"bg": T["panel"]})
        self.result.pack(fill="x", padx=10)

        # --- panel 2 (conditions & options)
        p2 = self.frm(main, "panel", border=True)
        p2.pack(fill="x", pady=6, ipadx=10, ipady=8, **pad)
        self.lab(p2, "Conditions & options", "panel", "text", self.f_h2, anchor="w").pack(fill="x", padx=10, pady=(4, 2))

        def selrow(text, opts, cmd=None, index=0):
            rw = self.frm(p2)
            rw.pack(fill="x", padx=10, pady=4)
            self.lab(rw, text).pack(side="left")
            sl = Sel(rw, opts, command=cmd, index=index, width=24)
            sl.cb.pack(side="right")
            return sl

        self.wx = selrow("Weather", WX, self.on_wx)
        self.surf = selrow("Road surface", SURF, self.cond)
        self.load = selrow("Truck load", LOAD, self.cond)
        rw = self.frm(p2)
        rw.pack(fill="x", padx=10, pady=(4, 0))
        self.lab(rw, "Driver reaction time").pack(side="left")
        self.rtv = self.lab(rw, "1.5 s", "panel", "text", self.f_bold)
        self.rtv.pack(side="right")
        self.rtS = self.scale(p2, 0.5, 3, 0.1, 1.5, self.cond)
        self.rtS.pack(fill="x", padx=10)
        self.hz = selrow("Hazard", HZ, self.on_hz)
        self.lang = selrow("Voice language", LANG, self.vstat)
        self.snd_v = tk.BooleanVar(value=True)
        self.chk(p2, "Sound & voice alerts", self.snd_v, self.on_snd).pack(fill="x", padx=10, pady=2)
        self.vol = self.scale(p2, 0, 100, 1, 60, self.on_vol)
        self.vol.pack(fill="x", padx=10)
        self.diff = selrow("Scenario difficulty", DIFF, None, 1)
        self.herd_v = tk.BooleanVar(value=False)
        self.chk(p2, "Herd mode (3 animals)", self.herd_v, self.on_herd).pack(fill="x", padx=10, pady=2)
        self.lg_v = tk.BooleanVar(value=False)
        self.chk(p2, "Large text", self.lg_v, self.on_lg).pack(fill="x", padx=10, pady=2)
        self.hc_v = tk.BooleanVar(value=False)
        self.chk(p2, "High contrast", self.hc_v, self.on_hc).pack(fill="x", padx=10, pady=2)
        b2 = self.frm(p2)
        b2.pack(fill="x", padx=10, pady=6)
        b2.columnconfigure(0, weight=1)
        b2.columnconfigure(1, weight=1)
        self.rp = self.btn(b2, "Replay last trip", "accent", "bg", self.replay)
        self.scn = self.btn(b2, "Random scenario", "safe", "#ffffff", self.random_scenario)
        self.dly = self.btn(b2, "Daily challenge", "warn", "#16202a", self.daily)
        self.mic = self.btn(b2, "Voice commands: off", "muted", "#ffffff", self.on_mic)
        self.cp = self.btn(b2, "Copy log", "muted", "#ffffff", self.copy_log)
        self.tv = self.btn(b2, "Test voice", "accent", "bg", self.test_voice)
        for i, bw in enumerate([self.rp, self.scn, self.dly, self.mic, self.cp, self.tv]):
            bw.grid(row=i // 2, column=i % 2, sticky="ew", padx=4, pady=4)
        self.vs = self.lab(p2, "", "panel", "muted", self.f_hint, anchor="w", justify="left", wraplength=440)
        self.vs.pack(fill="x", padx=10, pady=2)
        self.rep = self.lab(p2, "Trip report appears here after each trip.", "panel", "muted", self.f_hint,
                            anchor="w", justify="left", wraplength=440)
        self.rep.pack(fill="x", padx=10, pady=2)
        self.hst = self.lab(p2, "", "panel", "muted", self.f_hint, anchor="w", justify="left", wraplength=440)
        self.hst.pack(fill="x", padx=10, pady=2)

        # --- panel 3 (log)
        p3 = self.frm(main, "panel", border=True)
        p3.pack(fill="x", pady=(6, 20), ipadx=10, ipady=8, **pad)
        self.lab(p3, "Alert log", "panel", "text", self.f_h2, anchor="w").pack(fill="x", padx=10, pady=(4, 2))
        self.logbox = self.frm(p3)
        self.logbox.pack(fill="x", padx=10)
        self.render_log()
        self.restyle()

    # ------------------------------------------------------------ banner painting
    def set_banner(self, cls):
        self.bclass = cls
        self.paint_banner()

    def paint_banner(self):
        T = self.T
        cls = self.bclass
        if cls.startswith("alert"):
            bg, fg, bd = T["danger"], "#ffffff", T["danger"]
            if "flash" in cls and self.flash_on:
                bg = hx(tuple(min(255, v * 1.35) for v in _rgb(bg)))
        else:
            bg, fg = T["panel"], T["text"]
            bd = T["safe"] if cls == "safe" else T["warn"]
        key = (bg, fg, bd)
        if key == self._bpaint:
            return
        self._bpaint = key
        self.banner.configure(bg=bg, highlightbackground=bd, highlightcolor=bd)
        for w in self.bwidgets:
            if isinstance(w, tk.Frame):
                w.configure(bg=bg)
            else:
                w.configure(bg=bg, fg=fg)

    # ------------------------------------------------------------ core helpers
    def hn(self):
        return "Stalled vehicle" if self.HN == "STALLED CAR" else self.HN[0] + self.HN[1:].lower()

    def HM(self):
        return (1.4 if self.HERD else 1) * {"PERSON": 1.3, "DOG": .85, "BUFFALO": 1.1}.get(self.HN, 1)

    def stopDist(self, kmph):
        v = kmph / 3.6
        return v * self.REACT + (v * v) / (2 * self.DECEL)

    def threshold(self):
        base = max(BASE, self.stopDist(self.s.speed)) if self.adapt_v.get() else BASE
        return base * self.HM()

    def now_clock(self):
        return datetime.now().strftime("%I:%M:%S %p").lstrip("0")

    def addLog(self, text):
        self.log_items.insert(0, self.now_clock() + " \u2013 " + text)
        self.render_log()

    def render_log(self):
        for w in self.logbox.winfo_children():
            w.destroy()
        items = self.log_items[:200] or ["No alerts yet."]
        for t in items:
            self.lab(self.logbox, "\u2022 " + t, "panel", "muted", self.f_log, anchor="w", justify="left",
                     wraplength=440).pack(fill="x")

    def draw(self):
        s = self.s
        d = max(0, s.dist)
        t = self.threshold()
        zone = zoneOf(s.lat)
        inZone = d <= t
        self.dist_num.configure(text="%.0f" % d)
        self.ttc.configure(text=("Time to impact %.1f s" % (d / (s.speed / 3.6)))
                           if (s.running and zone == "path" and s.speed > 1) else "")
        self.thr_text = "Alert zone %.0f m" % t
        self.spv.configure(text="%.0f km/h" % s.speed)
        if not s.running:
            return
        alert = zone == "path" and (inZone or s.autoOn)
        watch = zone == "watch" and inZone
        self.set_banner("alert flash" if alert else ("watch" if watch else "safe"))
        if alert:
            self.msg.configure(text="Auto-braking engaged" if s.autoOn else "Caution! " + self.hn() + " in your lane ahead")
        elif watch:
            self.msg.configure(text=(self.hn() + " moving toward your lane!") if (self.cross_v.get() and s.lat > PATH)
                               else self.hn() + " beside your lane. Stay alert.")
        elif zone == "ignore" and inZone:
            self.msg.configure(text=self.hn() + " on opposite road. Ignored, no alert.")
        else:
            self.msg.configure(text="Monitoring. Your lane is clear.")

    def tone(self, freq, ms):
        if self.VOL <= 0:
            return
        if winsound:
            threading.Thread(target=lambda: winsound.Beep(int(freq), int(ms)), daemon=True).start()
        else:
            try:
                self.root.bell()
            except Exception:
                pass

    def beep(self):
        if not self.s.audio or not self.SND:
            return
        self.tone(980, 200)

    # ------------------------------------------------------------ trip end / tick / start
    def end(self, text, color):
        s = self.s
        self.report(text)
        s.running = False
        s.braking = False
        self.brakeB.configure(state="disabled")
        self.startB.configure(state="normal", text="Restart trip")
        self.where.enable(True)
        self.cross.configure(state="normal")
        self.result.configure(text=text, fg=self.T[color])
        self.set_banner("safe")
        self.msg.configure(text=text)
        self.draw()

    def tick(self, now):
        s = self.s
        if not s.running:
            return
        dt = min(.05, (now - s.last) / 1000)
        s.last = now
        if s.honkT > 0:
            s.honkT -= dt
            if self.HN != "STALLED CAR" and s.lat < 8:
                s.lat += 2.4 * dt
        if self.cross_v.get() and s.lat > 0:
            s.lat = max(0, s.lat - self.CROSS_SPEED * dt)
        zone = zoneOf(s.lat)
        v0 = s.speed / 3.6
        s.autoOn = bool(self.auto_v.get() and zone == "path" and v0 > 0 and
                        max(0, s.dist) <= (v0 * v0) / (2 * self.DECEL) + STOP_GAP + 1)
        if s.braking or s.autoOn:
            s.speed = max(0, s.speed - self.DECEL * 3.6 * dt)
            self.qset(self.speedIn, s.speed)
        if s.autoOn and not s.autoLogged:
            s.autoLogged = True
            self.say("b", 0)
            self.addLog("Auto-brake engaged at %.0f m, speed %.0f km/h" % (max(0, s.dist), s.speed))
        v = s.speed / 3.6
        s.dist -= v * dt
        s.off += v * dt * 14
        d = max(0, s.dist)
        inZone = d <= self.threshold()
        s.minD = min(s.minD, d)
        if (inZone or s.autoOn) and zone == "path":
            if not s.alerted:
                s.alerted = True
                self.say("a", d)
                self.addLog("Alert: %s in your lane at %.0f m, speed %.0f km/h" % (self.hn().lower(), d, s.speed))
            if now - s.beepT > 600:
                s.beepT = now
                self.beep()
        elif zone != "path":
            s.alerted = False
        if inZone and zone == "watch" and not s.watchLogged:
            s.watchLogged = True
            self.addLog("Advisory: %s beside your lane at %.0f m (no brake)" % (self.hn().lower(), d))
        if inZone and zone == "ignore" and not s.ignLogged:
            s.ignLogged = True
            self.addLog("Opposite-road %s ignored at %.0f m (no alert)" % (self.hn().lower(), d))
        if s.dist <= 0:
            if zone == "path":
                self.end("Collision. Brake earlier next time.", "danger")
            else:
                self.end("Passed safely. The %s was not in your lane." % self.hn().lower(), "safe")
            return
        if s.speed <= 0:
            self.end("Stopped safely, %.1f m from the %s." % (d, self.hn().lower()), "safe")
            return
        self.draw()

    def start(self):
        s = self.s
        s.audio = True
        s.dist = MAX
        s.lat = float(self.where.value)
        s.speed = float(self.speedIn.get())
        s.minD = 1e9
        s.topV = s.speed
        s.honkT = 0
        s.running = True
        s.braking = False
        s.alerted = False
        s.ignLogged = False
        s.watchLogged = False
        s.beepT = 0
        s.autoLogged = False
        s.autoOn = False
        self.result.configure(text="")
        self.brakeB.configure(state="normal")
        self.startB.configure(state="disabled")
        self.where.enable(False)
        self.cross.configure(state="disabled")
        s.last = now_ms()
        # second start listener of the original (extras reset)
        self.REC = []
        self.odo = 0
        self.rt = 0
        self.aT = None
        self.bT = None
        self.tt = 0
        self.vF = -1
        self.gF = 35
        self.brT = 0
        self.bsw.configure(text="")

    def brakeOn(self, _e=None):
        if self.s.running:
            self.s.braking = True

    def brakeOff(self):
        self.s.braking = False

    def on_speed(self):
        self.s.speed = float(self.speedIn.get())
        self.draw()

    def on_where(self):
        self.s.lat = float(self.where.value)
        self.draw()

    # ------------------------------------------------------------ traffic
    def initTr(self):
        sp = [[3.5, 1, "car"], [3.5, 1, "truck"], [3.5, 1, "auto"], [10, -1, "bus"], [10, -1, "car"],
              [13.5, -1, "truck"], [13.5, -1, "bike"], [13.5, -1, "car"]]
        out = []
        for i, q in enumerate(sp):
            T = VT[q[2]]
            out.append({"l": q[0], "d": q[1], "t": q[2], "c": T["c"][i % len(T["c"])],
                        "v": (35 + random.random() * 40) if q[1] > 0 else (50 + random.random() * 40),
                        "z": (30 + i * 55 + random.random() * 20) if q[1] > 0 else (40 + i * 28 + random.random() * 30)})
        return out

    def stepTr(self, t):
        if self.lt is None:
            self.lt = t
        dt = min(.05, (t - self.lt) / 1000)
        self.lt = t
        s = self.s
        if not s.running or dt <= 0:
            return
        vt = s.speed / 3.6
        self.extras(dt, vt)
        for o in self.TR:
            o["v0"] = o.get("v0") or o["v"]
            if s.alerted and o["d"] > 0:
                o["v"] = max(15, o["v"] - 10 * dt)
            else:
                o["v"] = min(o["v0"], o["v"] + 4 * dt)
            o["br"] = bool(s.alerted and o["d"] > 0)
            vo = o["v"] / 3.6
            o["z"] += ((vo - vt) if o["d"] > 0 else -(vo + vt)) * dt
            if o["d"] > 0:
                if o["z"] < -60:
                    o["z"] = 190 + random.random() * 60
                elif o["z"] > 260:
                    o["z"] = -50
            elif o["z"] < -60:
                o["z"] = 200 + random.random() * 60

    # ------------------------------------------------------------ extras (limits, blind spot, fatigue, ...)
    def lim(self):
        m = self.odo % 900
        return 80 if m < 500 else 40 if m < 650 else 60

    def extras(self, dt, vt):
        s = self.s
        self.odo += vt * dt
        self.fat += dt
        self.tt += dt
        if self.bclass.startswith("alert") and self.aT is None:
            self.aT = self.tt
        if s.braking and self.bT is None:
            self.bT = self.tt
        br = s.braking or s.autoOn
        self.FADE = min(.4, self.FADE + dt * .04) if br else max(0, self.FADE - dt * .01)
        self.DECEL = (self.DB or 5) * (1 - self.FADE)
        if self.vF < 0:
            self.vF = vt
        self.brT = self.brT + dt if br else 0
        if self.brT > 1 and self.vF > vt:
            self.vF = max(vt, self.vF - 3.5 * dt)
        self.gF += (vt - self.vF) * dt
        if self.fat > 30 and self.pt < 0:
            self.pt = 0
            self.alrt.grid()
            self.beep()
            self.addLog("Fatigue check: tap the I am alert button")
        if self.pt >= 0:
            self.pt += dt
            if self.pt > 6:
                if self.pt - dt <= 6:
                    self.addLog("Drowsiness alarm: no response")
                q = int(math.floor(self.pt * 2))
                if q != self.pl:
                    self.pl = q
                    self.beep()
        bs = hs = ""
        L = self.lim()
        ov = s.speed > L + 5
        for o in self.TR:
            if o["d"] > 0 and o["l"] == 3.5:
                if -18 < o["z"] < 8:
                    bs = "Vehicle in blind spot"
                elif not bs and -45 < o["z"] <= -18 and o["v"] / 3.6 > vt:
                    bs = "Vehicle overtaking from behind"
                elif not bs and 8 <= o["z"] < 30 and o["v"] / 3.6 < vt:
                    bs = "Closing on vehicle ahead (next lane)"
        om = self.odo % 2400
        for h in (450, 1100, 1900):
            if h > om and h - om < 250:
                hs = "Cattle hotspot in %d m" % jround(h - om)
        if ov and not self.OVER:
            self.beep()
        self.LIMV = L
        self.OVER = ov
        parts = ["Limit %d%s" % (L, " OVER-SPEED" if ov else ""), bs, hs,
                 ("Truck close behind: %.0f m" % max(0, self.gF)) if self.gF < 12 else "",
                 ("Brake fade %d%%" % jround(self.FADE * 100)) if self.FADE > .05 else ""]
        self.bsw.configure(text=" \u00b7 ".join(p for p in parts if p))
        self.rt += dt
        if self.rt > .1:
            self.rt = 0
            self.REC.append([s.dist, s.lat, s.speed, s.off, 1 if (s.braking or s.autoOn) else 0])

    def on_alert(self):
        self.fat = 0
        self.pt = -1
        self.alrt.grid_remove()
        self.addLog("Driver confirmed alert")

    def replay(self):
        s = self.s
        if s.running or not self.REC:
            return
        state = {"i": 0}

        def f():
            if s.running:
                return
            if state["i"] >= len(self.REC):
                self.msg.configure(text="Replay finished")
                return
            r = self.REC[state["i"]]
            state["i"] += 1
            s.dist, s.lat, s.speed, s.off = r[0], r[1], r[2], r[3]
            s.braking = bool(r[4])
            self.msg.configure(text="REPLAY %.1f s" % (state["i"] * .1))
            self.draw()
            self.root.after(100, f)

        f()

    # ------------------------------------------------------------ persistence (replaces localStorage)
    def load_data(self):
        try:
            with open(DATA_FILE, "r", encoding="utf-8") as fh:
                d = json.load(fh)
            self.B = d.get("cwb") or self.B
            self.HS = d.get("cw") or []
        except Exception:
            pass

    def save_data(self):
        try:
            with open(DATA_FILE, "w", encoding="utf-8") as fh:
                json.dump({"cwb": self.B, "cw": self.HS}, fh)
        except Exception:
            pass

    def addB(self, n):
        if n not in self.B["b"]:
            self.B["b"].append(n)

    def hist(self, sc=None):
        if sc is not None:
            if sc >= 60:
                self.B["s"] += 1
                if self.B["s"] == 1:
                    self.addB("First safe stop")
                if self.B["s"] >= 5:
                    self.addB("5-trip streak")
                if self.B["s"] >= 10:
                    self.addB("10 safe stops in a row")
                if self.night:
                    self.addB("Night driver")
                if self.wxv != "clear":
                    self.addB("Weather warrior")
                if self.DAILY:
                    self.addB("Daily challenge done")
            else:
                self.B["s"] = 0
            self.DAILY = False
            self.HS.append(sc)
            self.HS = self.HS[-20:]
            self.save_data()
        if not self.HS:
            return
        bars = "\u2581\u2582\u2583\u2584\u2585\u2586\u2587\u2588"
        spark = "".join(bars[min(7, int(math.floor(v / 12.5)))] for v in self.HS)
        self.hst.configure(text="History (%d trips): %s  best %d, average %d \u00b7 streak %d%s" % (
            len(self.HS), spark, max(self.HS), jround(sum(self.HS) / len(self.HS)), self.B["s"],
            (" \u00b7 badges: " + ", ".join(self.B["b"])) if self.B["b"] else ""))

    def coach(self, txt, sc):
        s = self.s
        r = []
        d = (self.bT - self.aT) if (self.aT is not None and self.bT is not None) else None
        tv = s.topV or 0
        if re.search("Collision", txt):
            r.append("You hit the hazard. Start braking the moment the alert shows; at %.0f km/h you need about %d m to stop." % (
                tv, jround((tv / 3.6) ** 2 / (2 * self.DECEL) + tv / 3.6 * self.REACT)))
        elif re.search("Passed", txt):
            r.append("The hazard stayed out of your lane. Staying alert without over-braking was right.")
        else:
            if d is not None:
                r.append(("You braked %.1f s after the alert; aim for under 1 s." % d) if d > 1
                         else "Good reaction: you braked within %.1f s of the alert." % max(0, d))
            elif s.autoLogged:
                r.append("Auto-brake did the work; try braking yourself as soon as the alert appears.")
            if s.minD < 25:
                r.append("Close call, only %.0f m to spare." % s.minD)
        if self.OVER:
            r.append("You were over the speed limit.")
        if self.FADE > .1:
            r.append("Your brakes were fading from repeated hard braking.")
        return " ".join(r) or "Well done."

    def report(self, txt):
        s = self.s
        if re.search("Collision", txt):
            sc = 0
        elif re.search("Passed", txt):
            sc = 100
        else:
            sc = max(0, min(100, jround(55 + s.minD * 2 - (15 if s.autoLogged else 0))))
        self.rep.configure(text="Trip report: closest approach %.1f m, top speed %.0f km/h, auto-brake %s, score %d/100" % (
            min(s.minD, 999), s.topV or 0, "used" if s.autoLogged else "not needed", sc))
        self.addLog("Score %d/100" % sc)
        self.hist(sc)
        self.rep.configure(text=self.rep.cget("text") + " Coach: " + self.coach(txt, sc))

    # ------------------------------------------------------------ voice
    def pickV(self, L):
        L = L.lower()
        n = lambda v: v["lang"].replace("_", "-").lower()
        f = [v for v in self.speech.voices if n(v).startswith(L)]
        if not f:
            f = [v for v in self.speech.voices if n(v).startswith(L[:2])]
        return f[0] if f else None

    def vstat(self):
        if not self.speech.mode:
            self.vs.configure(text="Voice is not supported on this system, beeps only.")
            return
        v = self.pickV(self.lang.value)
        self.vs.configure(text=("Voice ready: " + v["name"]) if v else
                          "No %s voice found on this device, English voice will be used." % self.lang.text)

    def hzt(self, t, L):
        i = ["COW", "BUFFALO", "DOG", "PERSON", "STALLED CAR"].index(self.HN) if self.HN in \
            ["COW", "BUFFALO", "DOG", "PERSON", "STALLED CAR"] else -1
        N = HZ_NAMES[L][i if i >= 0 else 0]
        if self.HERD and i < 3:
            N = HERD_NAMES[L]
        return re.sub("Cow|\u0917\u093e\u092f|\u0c06\u0c35\u0c41", N, t, count=1)

    def say(self, k, d, force=False):
        try:
            if not self.speech.mode or (not self.SND and not force):
                return
            L = self.lang.value
            v = self.pickV(L)
            en = self.pickV("en-IN") or self.pickV("en")
            vv = v or en
            T = TXT[L if v else "en-IN"]
            text = self.hzt(T[k](jround(d / 5) * 5), L if v else "en-IN")
            self.speech.speak(text, vv, self.VOL)
        except Exception:
            pass

    def test_voice(self):
        self.say("a", 80, True)

    def honk(self):
        s = self.s
        if not s.running:
            return
        s.honkT = 1.4
        if s.audio and self.SND:
            self.tone(330, 500)
        self.addLog("Horn sounded: " + self.HN.lower())

    # ------------------------------------------------------------ option handlers
    def cond(self):
        self.DB = 5 * float(self.surf.value) * float(self.load.value) * (.85 if self.wxv == "rain" else 1)
        self.DECEL = self.DB * (1 - self.FADE)
        self.REACT = float(self.rtS.get())
        self.rtv.configure(text="%.1f s" % self.REACT)
        self.draw()

    def on_wx(self):
        self.wxv = self.wx.value
        self.cond()

    def on_hz(self):
        o = self.hz.opt
        self.HAZ = o[0]
        self.HN = o[1]
        self.CROSS_SPEED = {"COW": 1.5, "BUFFALO": 1.2, "DOG": 3.2, "PERSON": .9, "STALLED CAR": 0}[self.HN]

    def on_snd(self):
        self.SND = self.snd_v.get()
        if not self.SND:
            self.speech.cancel()

    def on_vol(self):
        self.VOL = float(self.vol.get()) / 100

    def on_herd(self):
        self.HERD = self.herd_v.get()

    def on_lg(self):
        self.lg = self.lg_v.get()
        self.set_large(self.lg)

    def on_hc(self):
        self.hc = self.hc_v.get()
        self.restyle()

    def set_view(self, v):
        self.view = v
        for k in ("top", "cabin", "chase", "drone", "thermal", "radar"):
            self.vb_state[k] = (k == v)
        self.restyle()

    def toggle_night(self):
        self.night = not self.night
        self.vb_state["nt"] = self.night
        self.restyle()

    def toggle_hb(self):
        self.hb = not self.hb
        self.vb_state["hb"] = self.hb
        self.restyle()

    def on_mic(self):
        # the original needs the browser SpeechRecognition API, which Python/tkinter does not provide
        self.mic.configure(text="Voice commands not supported here")

    def cmd(self, q):
        if "start" in q and not self.s.running:
            self.start()
        elif re.search("honk|horn", q):
            self.honk()
        elif "replay" in q:
            self.replay()
        elif "night" in q:
            self.toggle_night()
        else:
            for v in ("cabin", "chase", "drone", "thermal", "radar", "top"):
                if v in q:
                    self.set_view(v)

    def copy_log(self):
        t = "\n".join(reversed(self.log_items)) + "\n" + self.rep.cget("text")
        try:
            self.root.clipboard_clear()
            self.root.clipboard_append(t)
            self.cp.configure(text="Copied")
        except Exception:
            self.cp.configure(text="Copy failed")

    def daily(self):
        s = self.s
        if s.running:
            return
        d = datetime.now()
        sd = d.year * 400 + (d.month - 1) * 31 + d.day

        def r(i):
            x = math.sin(sd * 97 + i * 13.7) * 10000
            return x - math.floor(x)

        self.where.set_value(["0", "0", "3.5", "6.75"][int(math.floor(r(1) * 4))])
        self.cross_v.set(r(2) < .5)
        self.qset(self.speedIn, 60 + int(math.floor(r(3) * 35)))
        self.wx.set_value(["clear", "rain", "fog", "glare"][int(math.floor(r(4) * 4))])
        self.wxv = self.wx.value
        self.night = r(5) < .5
        self.vb_state["nt"] = self.night
        self.hz.set_index(int(math.floor(r(6) * len(HZ))))
        self.on_hz()
        self.HERD = r(7) < .4
        self.herd_v.set(self.HERD)
        self.cond()
        s.speed = float(self.speedIn.get())
        self.DAILY = True
        self.addLog("Daily challenge loaded")
        self.restyle()
        self.start()

    def random_scenario(self):
        s = self.s
        if s.running:
            return
        df = self.diff.value

        def ri(a, b):
            return a + int(math.floor(random.random() * b))

        R = lambda a: a[int(math.floor(random.random() * len(a)))]
        self.where.set_value(R(["0", "3.5"] if df == "easy" else ["0", "0", "3.5", "6.75", "10"]))
        self.cross_v.set(df != "easy" and random.random() < .5)
        self.qset(self.speedIn, ri(40, 20) if df == "easy" else ri(80, 20) if df == "hard" else ri(55, 25))
        self.wx.set_value("clear" if df == "easy" else R(["fog", "rain"]) if df == "hard" else R(["clear", "rain"]))
        self.wxv = self.wx.value
        self.surf.set_value(".65" if df == "hard" else "1")
        self.night = df == "hard" or (df == "normal" and random.random() < .3)
        self.vb_state["nt"] = self.night
        self.hz.set_index(ri(0, len(HZ)))
        self.on_hz()
        self.cond()
        s.speed = float(self.speedIn.get())
        self.restyle()
        self.start()

    # ------------------------------------------------------------ main loop
    def frame(self):
        try:
            now = now_ms()
            if self.speech.dirty:
                self.speech.dirty = False
                self.vstat()
            self.flash_on = int(now / 250) % 2 == 1
            if self.bclass == "alert flash":
                self.paint_banner()
            if self.s.running:
                self.tick(now)
            self.stepTr(now)
            self.render(now)
        finally:
            self.root.after(16, self.frame)

    # ================================================================ rendering
    def nd(self, c):
        """Night darkening for scene elements below the horizon."""
        if self.night and self.view != "thermal":
            return blend("#02050f", .85, c)
        return c

    def cowState(self):
        s = self.s
        zone = zoneOf(s.lat)
        inZ = s.dist <= self.threshold()
        al = self.bclass.startswith("alert")
        if al:
            return "#ff3b30"
        if zone == "watch" and inZ:
            return "#ffb020"
        if zone == "ignore":
            return "#9aa7b4"
        return "#ff3b30" if inZ else "#4cc27f"

    # ---------------- top view (the original DOM road)
    def top_view(self, t):
        g, T, s = self.g, self.T, self.s
        g.xf = False
        X = lambda p: W * p / 100.0
        g.rect(0, 0, W, H, T["shoulder"])
        g.rect(X(4.17), 0, X(4.17 + 38.89), H, T["road"])
        g.rect(X(43.06), 0, X(43.06 + 16.67), H, T["median"])
        g.rect(X(43.06), 0, X(43.06) + 3, H, T["warn"])
        g.rect(X(43.06 + 16.67) - 3, 0, X(43.06 + 16.67), H, T["warn"])
        g.rect(X(59.72), 0, X(59.72 + 38.89), H, T["road"])
        sl = blend(T["lane"], .7, T["road"])
        g.rect(X(4.17) - 1.5, 0, X(4.17) + 1.5, H, sl)
        g.rect(X(98.61) - 1.5, 0, X(98.61) + 1.5, H, sl)
        y0 = (s.off % 56) - 56
        for xp in (23.61, 79.17):
            y = y0
            while y < H:
                g.rect(X(xp) - 2, y, X(xp) + 2, y + 26, T["lane"])
                y += 56
        lf = g.font(10)
        lc = blend(T["lane"], .85, T["road"])
        g.text(X(23.6), 8, "YOUR ROAD \u25b2", lf, lc, "n")
        g.text(X(51.4), 8, "MEDIAN", lf, blend(T["lane"], .85, T["median"]), "n")
        g.text(X(79.2), 8, "OPPOSITE \u25bc", lf, lc, "n")
        d = max(0, s.dist)
        th = self.threshold()
        ty = H - yFor(th) - 17
        g.line([(0, ty), (W, ty)], T["warn"], 2, dash=(6, 4))
        g.text(8, ty + 3, "Alert zone %.0f m" % th, g.font(11.5), T["warn"], "nw")
        g.text(X(pct(s.lat)), H - yFor(d), "\U0001F404", tkfont.Font(family=self.emoji_family(), size=-35), "#000000")
        # truck
        cx = X(13.89)
        g.pill(cx - 17, H - 92, 34, 70, T["accent"])
        g.pill(cx - 12, H - 88, 24, 14, blend("#ffffff", .55, T["accent"]))
        g.text(cx, H - 26, "YOU", g.font(10), "#ffffff", "s")
        # traffic (top-view DOM boxes)
        for o in self.TR:
            if not (3 < o["z"] <= MAX):
                continue
            Tv = VT[o["t"]]
            w = Tv["w"] / 18 * W
            hh = Tv["l"]
            x = X(pct(o["l"]))
            y = H - yFor(o["z"])
            g.pill(x - w / 2, y - hh / 2, w, hh, o["c"])
            lc2 = blend("#ffffff", .55, o["c"])
            if o["d"] > 0:
                g.pill(x - w / 2, y + hh / 2 - hh * .22, w, hh * .22, lc2)
            else:
                g.pill(x - w / 2, y - hh / 2, w, hh * .22, lc2)

    def emoji_family(self):
        if sys.platform.startswith("win"):
            return "Segoe UI Emoji"
        if sys.platform == "darwin":
            return "Apple Color Emoji"
        return "Noto Color Emoji"

    # ---------------- 3D scene
    def S(self, l1, l2, z1, z2, col, k):
        self.g.poly([P3(l1, z1, 0, k), P3(l2, z1, 0, k), P3(l2, z2, 0, k), P3(l1, z2, 0, k)], self.nd(col))

    def tree(self, l, z, k):
        g = self.g
        p = P3(l, z, 0, k)
        s2 = p[2]
        if p[0] < -80 or p[0] > W + 80:
            return
        g.rect(p[0] - .18 * s2, p[1] - 2 * s2, p[0] + .18 * s2, p[1], self.nd("#5a3d26"))
        g.oval(p[0], p[1] - 3.2 * s2, 1.7 * s2, 1.7 * s2, self.nd("#2f7a3a"))
        g.oval(p[0] - .5 * s2, p[1] - 3.6 * s2, 1.1 * s2, 1.1 * s2, self.nd("#3f9a4c"))

    def sky(self, k, t):
        g = self.g
        for i, q in enumerate(self.STARS):
            a = .3 + .7 * abs(math.sin(t / 700 + i))
            g.rect(q[0], q[1] * k["hy"] * .95, q[0] + q[2], q[1] * k["hy"] * .95 + q[2], blend("#ffffff", a, "#0b1733"))
        g.pool(W * .8, 36, 52, 52, "#fffae1", .95)
        g.oval(W * .8, 36, 12, 12, "#fffbe6")

    def scene(self, k, t):
        g, s, night = self.g, self.s, self.night
        hy = k["hy"]
        stops = ("#01030b", "#0b1733", "#1d2f55") if night else ("#3f86d6", "#8fc2ea", "#cfe8f7")
        n = max(6, int(hy / 4) + 1)
        for i in range(n):
            y0 = hy * i / n
            y1 = hy * (i + 1) / n + 1
            f = ((y0 + y1) / 2) / hy
            c = lerp(stops[0], stops[1], f / .6) if f < .6 else lerp(stops[1], stops[2], (f - .6) / .4)
            g.rect(0, y0, W, y1, c)
        if night:
            self.sky(k, t)
        cc = "#212e4e" if night else "#e9f3fb"
        for i in range(3):
            cxp = ((t / 90 + i * 190) % (W + 140)) - 70
            g.oval(cxp, 28 + i * 20, 42, 10, cc)
        pts = [(0, hy)] + [(x, hy - 14 - 10 * math.sin(x * .02) - 6 * math.sin(x * .07)) for x in range(0, W + 1, 16)] + [(W, hy)]
        g.poly(pts, self.nd("#0a131c") if night else "#6e8f68")
        g.rect(0, hy, W, H, "#0f2214" if night else "#5d8a47")
        Z = 240
        zs = k["zs"]
        m = s.off / 14
        self.S(-2.9, 16.4, zs, Z, "#a7a399", k)
        self.S(-1.75, 5.25, zs, Z, "#3a4048", k)
        self.S(5.25, 8.25, zs, Z, "#6f9a5e", k)
        self.S(8.25, 15.25, zs, Z, "#3a4048", k)
        self.S(-1.85, -1.65, zs, Z, "#eeeeee", k)
        self.S(15.15, 15.35, zs, Z, "#eeeeee", k)
        self.S(5.15, 5.35, zs, Z, "#e8b923", k)
        self.S(8.15, 8.35, zs, Z, "#e8b923", k)
        z = -(m % 12)
        while z < Z:
            a = max(z, zs)
            b = z + 5
            if b > a:
                self.S(1.7, 1.8, a, b, "#f2f2f2", k)
                self.S(11.7, 11.8, a, b, "#f2f2f2", k)
            z += 12
        bd = (s.speed / 3.6) ** 2 / (2 * self.DECEL)
        t2 = self.threshold()
        self.S(-1.75, 5.25, zs, max(zs + .1, bd), blend((0, 200, 255), .2, "#3a4048"), k)
        self.S(-1.75, 5.25, max(zs, t2 - 1.2), max(zs + .1, t2), blend((255, 160, 0), .6, "#3a4048"), k)
        hc = "#283e69" if night else "#d7e8f5"
        for i in range(8):
            g.rect(0, hy - 4 + i * 5, W, hy + 1 + i * 5, hc, .9 * (1 - i / 8))
        o = m % 30
        q = 210 - o
        while q > zs:
            self.tree(-4.2, q, k)
            self.tree(17.4, q + 12, k)
            q -= 30
        r = 200 - (m % 15)
        while r > zs:
            self.tree(6.75, r, k)
            r -= 15

    def nightFx(self, k, t):
        g, s = self.g, self.s
        m = s.off / 14
        lamps = []
        beams = [3, 8, 14, 21, 29, 38, 49, 62, 78, 96, 120, 150, 180]
        z = 210 - (m % 30)
        while z > k["zs"]:
            lamps.append(z)
            z -= 30
        hb = self.hb

        def bm(z):
            p = P3(0, z, 0, k)
            zz = max(.6, z + k["back"])
            return (p, max(30, 5.4 * p[2]), max(7, k["h"] * k["f"] * (1 / zz - 1 / (zz + 12))),
                    0 if (z > 100 and not hb) else max(.3 if hb else .22, 1 - z / (210 if hb else 115)))

        def lp(z):
            p = P3(6.75, z, 0, k)
            zz = max(.6, z + k["back"])
            return (p, max(10, 6.5 * p[2]), max(5, k["h"] * k["f"] * (1 / zz - 1 / (zz + 9))))

        for z in beams:
            p, rx, ry, a = bm(z)
            g.pool(p[0], p[1], rx, ry, "#fff2b4", a * .55)
        for z in lamps:
            p, rx, ry = lp(z)
            g.pool(p[0], p[1], rx, ry, "#ffbe5a", .55)
            p0 = P3(6.75, z, 0, k)
            h = P3(6.75, z, 7.5, k)
            g.line([(p0[0], p0[1]), (h[0], h[1])], "#1d232b", max(1, .16 * p0[2]))
            g.pool(h[0], h[1], max(6, 1.4 * h[2]), max(6, 1.4 * h[2]), "#ffd782", .95)

    def veh(self, o, k):
        g, night = self.g, self.night
        zz = o["z"]
        if zz < k["zs"] + .5 or zz > 230:
            return
        p = P3(o["l"], zz, 0, k)
        sc = p[2]
        Tv = VT[o["t"]]
        w, h = Tv["w"] * sc, Tv["h"] * sc
        x, y = p[0] - w / 2, p[1] - h
        if x > W + 50 or x + w < -50:
            return
        g.oval(p[0], p[1], w * .6, max(1, w * .08), "#000000", .3)
        g.rect(x, y, x + w, y + h, o["c"])
        if night:
            g.rect(x, y, x + w, y + h, "#020510", min(.8, .4 + zz / 220))
        g.rect(x + w * .12, y + h * .1, x + w * .88, y + h * .1 + h * (.35 if o["t"] == "car" else .3), "#141c26")
        g.rect(x + w * .08, y + h * .92, x + w * .28, y + h * 1.04, "#111111")
        g.rect(x + w * .72, y + h * .92, x + w * .92, y + h * 1.04, "#111111")
        ly = y + h * .62
        lw, lh = max(2, w * .16), max(1.5, h * .1)
        if o["d"] > 0:
            col = "#ff2a2a" if (night or o.get("br")) else "#b02020"
        else:
            col = "#fff6c8" if night else "#e8e4cc"
        g.rect(x + w * .06, ly, x + w * .06 + lw, ly + lh, col)
        g.rect(x + w * .94 - lw, ly, x + w * .94, ly + lh, col)
        if night:
            g.pool(x + w * .06 + lw / 2, ly + lh / 2, max(4, w * .6), max(3, w * .4), col, .6)
            g.pool(x + w * .94 - lw / 2, ly + lh / 2, max(4, w * .6), max(3, w * .4), col, .6)
        if night and o["d"] < 0:
            g.pool(p[0], p[1], w * 3, w * .5, "#fff0be", .4)

    def traf(self, k, f):
        for o in sorted([o for o in self.TR if f(o)], key=lambda o: -o["z"]):
            self.veh(o, k)

    def cowDraw(self, k, x=0):
        g, s = self.g, self.s
        if s.dist < k["zs"] - 1:
            return
        p = P3(s.lat + self.OFF[0], max(0, s.dist + self.OFF[1]), 0, k)
        sz = min(400, max(18, 2.4 * p[2]))
        col = self.cowState()
        g.oval(p[0], p[1], sz * .5, sz * .1, "#000000", .35)
        mv = s.running and (s.honkT > 0 or (self.cross_v.get() and s.lat > 0))
        now = now_ms()
        bb = abs(math.sin(now / (130 if mv else 600))) * sz * (.07 if mv else .015)
        ang = math.sin(now / (130 if mv else 700)) * (.07 if mv else .02)
        if self.view != "thermal":
            g.text(p[0], p[1] - bb - sz * .08, self.HAZ or "\U0001F404",
                   tkfont.Font(family=self.emoji_family(), size=-int(sz)), "#000000", "s", -math.degrees(ang))
        if self.HN == "STALLED CAR" and int(math.floor(now / 400)) % 2:
            r = max(2, sz * .06)
            g.oval(p[0] - sz * .3, p[1] - sz * .3, r, r, "#ffb020")
            g.oval(p[0] + sz * .3, p[1] - sz * .3, r, r, "#ffb020")
        if x:
            return
        tx = "%s %.0f m" % (self.HN, max(0, s.dist))
        f = g.font(11)
        w = f.measure(tx) + 14
        ty = p[1] - sz - 26
        g.pill(p[0] - w / 2, ty, w, 18, col)
        g.text(p[0], ty + 9, tx, f, "#ffffff")
        g.poly([(p[0] - 5, ty + 18), (p[0] + 5, ty + 18), (p[0], ty + 25)], col)

    def herd(self, k):
        if self.HERD:
            for q in ([-1.4, 7], [1.3, -5]):
                self.OFF = q
                self.cowDraw(k, 1)
            self.OFF = [0, 0]

    def pred(self, k):
        g, s = self.g, self.s
        if not s.running or self.HN == "STALLED CAR":
            return
        hk = s.honkT > 0
        if not hk and not (self.cross_v.get() and s.lat > 0):
            return
        dr = 1 if hk else -1
        sp = 2.4 if hk else self.CROSS_SPEED
        l2 = max(0, min(14, s.lat + dr * sp * 3))
        a = P3(s.lat, max(0, s.dist), 0, k)
        b = P3(l2, max(0, s.dist), 0, k)
        g.line([(a[0], a[1]), (b[0], b[1])], "#ffcc00", 3, dash=(6, 5))
        if dr < 0 and s.lat > PATH:
            g.text((a[0] + b[0]) / 2, a[1] + 16, "enters your lane in %.1f s" % ((s.lat - PATH) / sp), g.font(11), "#ffcc00")

    def truckRear(self, k):
        g, s = self.g, self.s
        z, hw, ht = -12, 1.3, 3.3
        f = P3(0, z, 0, k)[2]
        br = s.braking or s.autoOn
        g.poly([P3(-hw, z, ht, k), P3(hw, z, ht, k), P3(hw, -1, ht, k), P3(-hw, -1, ht, k)], "#2d78c4")
        g.poly([P3(-hw, z, .35, k), P3(hw, z, .35, k), P3(hw, z, ht, k), P3(-hw, z, ht, k)], "#1b5fa8")
        a = P3(-hw, z, ht, k)
        b = P3(hw, z, .35, k)
        edge = "#4a8ccb"
        g.line([(a[0] + 4, a[1] + 4), (b[0] - 4, a[1] + 4), (b[0] - 4, b[1] - 4), (a[0] + 4, b[1] - 4), (a[0] + 4, a[1] + 4)], edge, 2)
        g.line([(W / 2, a[1] + 4), (W / 2, b[1] - 4)], edge, 2)
        g.rect(a[0] - 2, b[1] - .1 * f, a[0] - 2 + .4 * f, b[1] - .1 * f + .5 * f, "#0b0d10")
        g.rect(b[0] - .4 * f + 2, b[1] - .1 * f, b[0] + 2, b[1] - .1 * f + .5 * f, "#0b0d10")
        g.text(W / 2, b[1] - .35 * f, "YOU", g.font(min(300, .35 * f)), "#ffffff")
        ly = b[1] - .9 * f
        lc = "#ff2a2a" if br else "#7a1414"
        if br:
            g.rect(a[0] + .15 * f - 6, ly - 6, a[0] + .6 * f + 6, ly + .28 * f + 6, "#ff2a2a", .3)
            g.rect(b[0] - .6 * f - 6, ly - 6, b[0] - .15 * f + 6, ly + .28 * f + 6, "#ff2a2a", .3)
        g.rect(a[0] + .15 * f, ly, a[0] + .6 * f, ly + .28 * f, lc)
        g.rect(b[0] - .6 * f, ly, b[0] - .15 * f, ly + .28 * f, lc)

    def gauge(self, x, y, r, v, mx):
        g, cv = self.g, self.cv
        g.oval(x, y, r, r, "#07090b")
        cv.create_arc(x - r + 3, y - r + 3, x + r - 3, y + r - 3, start=-135, extent=-270, style="arc",
                      outline="#3b4652", width=3)
        a = .75 * math.pi + min(1, v / mx) * 1.5 * math.pi
        g.line([(x, y), (x + math.cos(a) * (r - 6), y + math.sin(a) * (r - 6))], "#ff5a3c", 2.5)
        g.text(x, y + r - 9, "%d km/h" % jround(v), g.font(11), "#cfe3f5")

    def dash(self, t):
        g, s = self.g, self.s
        g.poly([(0, 0), (58, 0), (22, H - 74), (0, H - 74)], "#12161b")
        g.poly([(W, 0), (W - 58, 0), (W - 22, H - 74), (W, H - 74)], "#12161b")
        for i in range(7):
            g.rect(0, i * 4, W, i * 4 + 4, "#0c0f12", 1 - i / 7)
        for x in (4, W - 48):
            g.rect(x, 92, x + 44, 150, "#0b0e11")
            g.rect(x + 3, 95, x + 41, 121, "#8bb0c8")
            g.rect(x + 3, 121, x + 41, 147, "#3f444a")
            g.poly([(x + 3, 147), (x + 41, 147), (x + 26, 121), (x + 18, 121)], "#2c3138")
            for j in range(3):
                yy = 147 - ((j * 9 + s.off / 9) % 27)
                g.rect(x + 21.5, yy, x + 21.5 + 1.2 + (yy - 121) / 9, yy + 3, "#dddddd")
        g.poly([(0, H - 60), (W * .25, H - 80), (W * .5, H - 84), (W * .75, H - 80), (W, H - 60), (W, H), (0, H)], "#1b2128")
        g.rect(0, H - 30, W, H, "#0b0d10", .8)
        self.gauge(W * .3, H - 30, 30, s.speed, 120)
        on = s.autoOn and int(math.floor(t / 250)) % 2
        for lbl, lx, lc in (("AEB", W * .46, ("#ff3b30" if on else "#7a1414") if s.autoOn else "#2a3036"),
                            ("BRK", W * .54, "#ff9f1c" if (s.braking or s.autoOn) else "#2a3036")):
            g.oval(lx, H - 44, 9, 9, lc)
            g.text(lx, H - 44, lbl, g.font(8), "#ffffff")
        self.cv.create_arc(W * .68 - 70, H + 10 - 44, W * .68 + 70, H + 10 + 44, start=0, extent=180,
                           style="arc", outline="#07090b", width=10)
        g.rect(W * .68 - 18, H - 34, W * .68 + 18, H, "#07090b")

    def hud(self, t):
        g = self.g
        al = self.bclass.startswith("alert")
        g.oval(72, 62, 17, 17, "#ff2a2a" if self.OVER else "#d01818")
        g.oval(72, 62, 13, 13, "#ffffff")
        g.text(72, 62, str(self.LIMV), g.font(15), "#111111")
        if al and int(math.floor(t / 250)) % 2:
            self.cv.create_rectangle(5, 5, W - 5, H - 5, outline="#ff3232", width=10)
        tx = self.msg.cget("text")
        f = g.font(13)
        w = min(W - 20, f.measure(tx) + 26)
        y0 = 24 if self.view == "cabin" else 10
        g.pill(W / 2 - w / 2, y0, w, 26, "#c62828" if al else "#0a1016")
        g.text(W / 2, y0 + 13, tx, f, "#ffffff")

    def radar(self, t):
        g, s = self.g, self.s
        BG = "#051a10"
        g.rect(0, 0, W, H, BG)
        X = lambda l: 28 + (l + 2.5) / 18 * (W - 56)
        Y = lambda d: H - 52 - d / MAX * (H - 86)
        bd = min(MAX, (s.speed / 3.6) ** 2 / (2 * self.DECEL))
        g.rect(X(-PATH), Y(MAX), X(PATH), Y(0), blend((76, 194, 127), .16, BG))
        g.rect(X(PATH), Y(MAX), X(MEDIAN_END), Y(0), blend((255, 176, 32), .12, BG))
        g.rect(X(MEDIAN_END), Y(MAX), X(15.25), Y(0), blend((150, 160, 170), .12, BG))
        g.rect(X(-PATH), Y(bd), X(PATH), Y(0), blend((0, 200, 255), .28, BG))
        lf = g.font(10, False)
        for d in (50, 100, 150):
            g.line([(X(-2.5), Y(d)), (X(15.5), Y(d))], blend((120, 255, 170), .35, BG), 1, dash=(4, 4))
            g.text(X(-2.4), Y(d) - 3, "%d m" % d, lf, "#7dffb0", "sw")
        g.line([(X(-2.5), Y(self.threshold())), (X(15.5), Y(self.threshold()))], "#ffb020", 1, dash=(4, 4))
        g.text(X(-PATH) + 4, Y(bd) + 12, "braking %.0f m" % bd, lf, "#4cd9ff", "w")
        sy = Y(0) - ((t / 1800) % 1) * (Y(0) - Y(MAX))
        for i in range(8):
            g.rect(0, sy + i * 5, W, sy + i * 5 + 5, "#78ffaa", .5 * (1 - i / 8))
        bf = g.font(10)
        g.text(X(0), 16, "YOUR PATH", bf, "#9fe8bd")
        g.text(X(5.4), 16, "SIDE / MEDIAN", bf, "#9fe8bd")
        g.text(X(11.5), 16, "OPPOSITE", bf, "#9fe8bd")
        for o in self.TR:
            if 0 < o["z"] <= MAX:
                g.rect(X(o["l"]) - 3, Y(o["z"]) - 5, X(o["l"]) + 3, Y(o["z"]) + 5, blend((160, 200, 255), .85, BG))
        col = self.cowState()
        bx, by = X(s.lat), Y(max(0, s.dist))
        pr = 6 + ((t / 90) % 14)
        al = max(0, 1 - pr / 20)
        self.cv.create_oval(bx - pr, by - pr, bx + pr, by + pr, outline=blend(col, al, BG), width=2)
        g.oval(bx, by, 6, 6, col)
        g.text(bx, by - 12, "%.0f m" % max(0, s.dist), g.font(11), "#ffffff")
        g.rect(X(0) - 8, Y(0), X(0) + 8, Y(0) + 28, "#1b5fa8")
        g.text(X(0), Y(0) + 18, "YOU", g.font(8), "#ffffff")
        g.text(W / 2, H - 8, "RADAR  \u2022  %.0f km/h" % s.speed, g.font(12), "#9fe8bd", "s")

    def thermal(self, k, t):
        g, s = self.g, self.s
        g.xf = False
        hs = g.font(11)

        def h(l, z, ht, r, a, col):
            if z < k["zs"]:
                return
            p = P3(l, z, ht, k)
            rr = max(8, r * p[2])
            g.pool(p[0], p[1], min(rr, 300), min(rr, 300), col, a)

        h(s.lat, max(0, s.dist), .9, 1.5, .95, "#ffa03c" if self.HN == "STALLED CAR" else "#ffffff")
        if self.HERD:
            h(s.lat - 1.4, s.dist + 7, .9, 1.4, .8, "#ffffff")
            h(s.lat + 1.3, s.dist - 5, .9, 1.4, .8, "#ffffff")
        for o in self.TR:
            h(o["l"], o["z"], .5, VT[o["t"]]["w"] * .9, .7, "#ffbe5a")
        g.text(10, H - 8, "THERMAL: sees through fog and darkness", hs, "#9fffd0", "sw")

    def weather(self, k, t):
        g = self.g
        W_ = self.wxv
        night = self.night
        if W_ == "glare":
            g.pool(W * .3, k["hy"] - 15, 300, 300, "#fff5c8", .7)
            return
        if W_ == "clear":
            return
        base = "#3c4658" if night else "#c8d0d8"
        if W_ == "fog":
            q = k["hy"] / H
            bands = 20
            for i in range(bands):
                y0 = H * i / bands
                y1 = H * (i + 1) / bands + 1
                f = (y0 + y1) / 2 / H
                a = (.8 + (.97 - .8) * (f / q)) if f < q else (.97 + (.3 - .97) * ((f - q) / (1 - q)))
                g.rect(0, y0, W, y1, base, a)
            return
        g.rect(0, 0, W, H, "#0a101c" if night else "#465262", .3)
        for q in self.RAIN:
            y = (q[1] + t * .9 * q[2] / 8) % H
            x = q[0] - y * .12
            g.line([(x, y), (x - 1.5, y + q[2])], "#9db0c6", 1)
        if self.view == "cabin":
            ph = abs(math.sin(t / 700))
            a = math.pi * (1 - ph)
            for px in (W * .34, W * .66):
                g.line([(px, H - 72), (px + math.cos(a) * 130, H - 72 - math.sin(a) * 130)], "#0b0d10", 4)

    def render(self, t):
        cv = self.cv
        cv.delete("all")
        self.g.xf = False
        if self.view == "top":
            self.top_view(t)
            return
        if self.view == "drone":
            CAMS["drone"]["l"] = math.sin(t / 3000) * 6
        s = self.s
        sh = s.running and (s.braking or s.autoOn) and s.speed > 0
        self.render0(t)
        if sh:
            cv.move("all", math.sin(t / 17) * 1.2, 3 + math.cos(t / 23))

    def render0(self, t):
        g, view = self.g, self.view
        if view == "radar":
            self.radar(t)
            return
        k = CAMS[view]
        g.xf = (view == "thermal")
        self.scene(k, t)
        if self.night and view != "thermal":
            self.nightFx(k, t)
        s = self.s
        self.traf(k, lambda o: o["z"] >= s.dist)
        self.herd(k)
        self.cowDraw(k)
        self.pred(k)
        self.traf(k, lambda o: o["z"] < s.dist)
        if view == "thermal":
            self.thermal(k, t)
        g.xf = False
        if view not in ("cabin", "thermal"):
            self.truckRear(k)
        if view != "thermal":
            self.weather(k, t)
        if view in ("cabin", "thermal"):
            self.dash(t)
        self.hud(t)


def main():
    root = tk.Tk()
    root.title("CattleWatch \u2013 Highway Cow Alert")
    root.geometry("540x900")
    dark = ("--dark" in sys.argv) or detect_dark()
    App(root, dark)
    root.mainloop()


if __name__ == "__main__":
    main()
