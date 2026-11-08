"""
SAIM SHAFI HISTORY ENGINE
Turns a story script (scripts/*.json) into a finished YouTube video:
AI English voice + animated maps + year clock + numbers + timelines + images + captions
-> output/<name>/video.mp4, thumbnail.jpg, description.txt, captions.srt

Run:  python engine.py                      (asks which script)
      python engine.py scripts/mansa_musa.json
      python engine.py scripts/x.json --preview      (small + fast, to check quickly)
      python engine.py --write "Topic of the video"  (writes a new script with Gemini, free key)
"""
import hashlib
import json
import math
import os
import random
import re
import shutil
import subprocess
import sys
import threading
import time
import urllib.parse
import urllib.request
import wave
from multiprocessing import Pool, cpu_count

import numpy as np
from PIL import Image, ImageDraw, ImageFilter, ImageFont, ImageOps

import socket

# ---- If Windows can't look up a website's address (DNS problem, "getaddrinfo failed"),
#      ask Cloudflare / Google directly by their fixed IP addresses instead.
_ORIG_GAI = socket.getaddrinfo
_DOH_CACHE = {}


def _doh_lookup(host):
    if host in _DOH_CACHE:
        return _DOH_CACHE[host]
    import ssl as _ssl
    ips = []
    for url in (f"https://1.1.1.1/dns-query?name={host}&type=A", f"https://8.8.8.8/resolve?name={host}&type=A", f"https://1.0.0.1/dns-query?name={host}&type=A"):
        try:
            req = urllib.request.Request(url, headers={"Accept": "application/dns-json"})
            with urllib.request.urlopen(req, timeout=15, context=_ssl.create_default_context()) as r:
                d = json.loads(r.read().decode())
            ips = [a["data"] for a in d.get("Answer") or [] if a.get("type") == 1]
            if ips:
                break
        except Exception:
            continue
    _DOH_CACHE[host] = ips
    return ips


def _getaddrinfo(host, *a, **k):
    try:
        return _ORIG_GAI(host, *a, **k)
    except socket.gaierror:
        if not host or re.fullmatch(r"[\d.]+|[0-9a-fA-F:]+", str(host)):
            raise
        ips = _doh_lookup(str(host))
        if not ips:
            raise
        return _ORIG_GAI(ips[0], *a, **k)


socket.getaddrinfo = _getaddrinfo

ROOT = os.path.dirname(os.path.abspath(__file__))
A = lambda *p: os.path.join(ROOT, *p)
FONTS = A("assets", "fonts")
MODEL = A("models", "kokoro.onnx")
VOICES = A("models", "voices.bin")
MODEL_URLS = {
    MODEL: "https://github.com/thewh1teagle/kokoro-onnx/releases/download/model-files-v1.0/kokoro-v1.0.int8.onnx",
    VOICES: "https://github.com/thewh1teagle/kokoro-onnx/releases/download/model-files-v1.0/voices-v1.0.bin",
}
SR = 24000

# ------------------------------------------------------------------ colours (dark documentary look, gold accents)
GOLD = (230, 176, 60)
GOLD_L = (250, 214, 120)
WHITE = (245, 240, 230)
GREY = (170, 165, 155)
INK = (14, 16, 22)
SEA_T, SEA_B = (16, 30, 46), (8, 14, 24)
LAND = (196, 176, 136)
LAND_EDGE = (120, 98, 66)
RIVER = (88, 128, 168)
RED = (214, 72, 52)
DEFAULT_THEME = "archive"
THEME = {"name": "archive"}


def apply_theme(name):
    """'archive' = the Midnight Archive look (gold, sepia). 'nature' = cool ice-blue look for nature/animal videos."""
    global GOLD, GOLD_L, WHITE, GREY, INK, LAND, LAND_EDGE, RIVER, YELLOW
    name = name or DEFAULT_THEME
    THEME["name"] = name
    if name == "nature":
        GOLD, GOLD_L, WHITE, GREY, INK = (70, 196, 255), (176, 234, 255), (246, 251, 255), (160, 182, 198), (5, 12, 22)
        LAND, LAND_EDGE, RIVER = (178, 204, 176), (84, 118, 96), (70, 140, 196)
        YELLOW = (120, 214, 255)


def log(*a):
    print(*a, flush=True)


# ================================================================== fonts

_FC = {}


def font(name, size, weight=None):
    if name == "Cinzel" and THEME["name"] == "nature":  # modern titles for nature videos
        name, weight = "Oswald", ("Bold" if weight in ("Bold", "Black", "SemiBold") else "Medium")
    key = (name, size, weight)
    if key not in _FC:
        f = ImageFont.truetype(os.path.join(FONTS, name + ".ttf"), size)
        if weight:
            try:
                f.set_variation_by_name(weight)
            except Exception:
                pass
        _FC[key] = f
    return _FC[key]


def tw(d, text, f):
    b = d.textbbox((0, 0), text, font=f)
    return b[2] - b[0], b[3] - b[1]


def wrap(d, text, f, maxw):
    words, lines, cur = text.split(), [], ""
    for w in words:
        t = (cur + " " + w).strip()
        if tw(d, t, f)[0] <= maxw or not cur:
            cur = t
        else:
            lines.append(cur)
            cur = w
    if cur:
        lines.append(cur)
    return lines


def shadow_text(img, xy, text, f, fill, shadow=(0, 0, 0), blur=6, offset=(0, 3), anchor="la", alpha=200):
    """Text with a soft shadow. Only the area around the text is blurred (fast)."""
    d = ImageDraw.Draw(img)
    x0, y0, x1, y1 = d.textbbox(xy, text, font=f, anchor=anchor)
    pad = blur * 3 + max(abs(offset[0]), abs(offset[1])) + 4
    bx0, by0 = int(x0 - pad), int(y0 - pad)
    w, h = int(x1 - x0 + 2 * pad), int(y1 - y0 + 2 * pad)
    layer = Image.new("RGBA", (w, h), (0, 0, 0, 0))
    ImageDraw.Draw(layer).text((xy[0] - bx0 + offset[0], xy[1] - by0 + offset[1]), text, font=f, fill=shadow + (alpha,), anchor=anchor)
    layer = layer.filter(ImageFilter.GaussianBlur(blur))
    ImageDraw.Draw(layer).text((xy[0] - bx0, xy[1] - by0), text, font=f, fill=fill + (255,) if len(fill) == 3 else fill, anchor=anchor)
    img.paste(layer, (bx0, by0), layer)


# ================================================================== easing

def clamp(x, a=0.0, b=1.0):
    return max(a, min(b, x))


def ease(x):
    x = clamp(x)
    return x * x * (3 - 2 * x)


def ease_out(x):
    x = clamp(x)
    return 1 - (1 - x) ** 3


def ease_io(x):
    x = clamp(x)
    return 4 * x ** 3 if x < 0.5 else 1 - (-2 * x + 2) ** 3 / 2


# ================================================================== backgrounds

_BG = {}


def noise_tex(w, h, seed=1, amount=10):
    rng = np.random.default_rng(seed)
    n = rng.normal(0, amount, (h // 4 + 1, w // 4 + 1)).astype(np.float32)
    n = np.array(Image.fromarray(n).resize((w, h), Image.BILINEAR))
    return n


def dark_bg(W, H, tint=(34, 28, 20)):
    if THEME["name"] == "nature":  # warm brown -> deep arctic blue
        tint = (int(tint[2] * 0.45), int(tint[1] * 0.95 + 4), int(tint[0] * 1.35 + 10))
    key = ("dark", W, H, tint, THEME["name"])
    if key in _BG:
        return _BG[key].copy()
    y, x = np.mgrid[0:H, 0:W].astype(np.float32)
    r = np.sqrt(((x - W * 0.5) / (W * 0.7)) ** 2 + ((y - H * 0.45) / (H * 0.8)) ** 2)
    v = clamp_arr(1.0 - r * 0.85, 0.08, 1.0)
    base = np.zeros((H, W, 3), np.float32)
    for i in range(3):
        base[..., i] = tint[i] * v + INK[i] * (1 - v)
    base += noise_tex(W, H, 3, 5)[..., None]
    img = Image.fromarray(np.clip(base, 0, 255).astype(np.uint8))
    _BG[key] = img
    return img.copy()


def clamp_arr(a, lo, hi):
    return np.minimum(np.maximum(a, lo), hi)


def vignette(img, strength=0.55):
    W, H = img.size
    key = ("vig", W, H, strength)
    if key not in _BG:
        y, x = np.mgrid[0:H, 0:W].astype(np.float32)
        r = np.sqrt(((x - W / 2) / (W / 2)) ** 2 + ((y - H / 2) / (H / 2)) ** 2) / 1.42
        m = 1 - strength * clamp_arr((r - 0.35) / 0.65, 0, 1) ** 1.6
        _BG[key] = (Image.fromarray((m * 255).astype(np.uint8)), Image.new("RGB", (W, H), (0, 0, 0)))
    mask, black = _BG[key]
    return Image.composite(img, black, mask)


# ================================================================== geography

_WORLD = None


def world():
    global _WORLD
    if _WORLD is None:
        with open(A("assets", "world.json"), encoding="utf-8") as f:
            _WORLD = json.load(f)
    return _WORLD


def fit_bbox(b, aspect):
    """Expands [lon0, lat0, lon1, lat1] to the screen aspect (projected with cos(lat))."""
    lon0, lat0, lon1, lat1 = b
    cl = math.cos(math.radians((lat0 + lat1) / 2))
    w, h = (lon1 - lon0) * cl, lat1 - lat0
    if w / h < aspect:
        nw = h * aspect / cl
        c = (lon0 + lon1) / 2
        lon0, lon1 = c - nw / 2, c + nw / 2
    else:
        nh = w / aspect
        c = (lat0 + lat1) / 2
        lat0, lat1 = c - nh / 2, c + nh / 2
    return [lon0, lat0, lon1, lat1]


class MapBase:
    """One pre-drawn map picture covering a bbox. Frames crop and scale it (fast)."""

    def __init__(self, bbox, px_w, cl, regions, rivers=True, mode="plain"):
        self.bbox, self.cl = bbox, cl
        lon0, lat0, lon1, lat1 = bbox
        self.k = px_w / ((lon1 - lon0) * cl)
        self.W = int(px_w)
        self.H = int((lat1 - lat0) * self.k)
        W, H = self.W, self.H
        # sea
        y = np.linspace(0, 1, H, dtype=np.float32)[:, None]
        sea = np.zeros((H, W, 3), np.float32)
        for i in range(3):
            sea[..., i] = SEA_T[i] * (1 - y) + SEA_B[i] * y
        sea += noise_tex(W, H, 7, 4)[..., None]
        img = Image.fromarray(np.clip(sea, 0, 255).astype(np.uint8))
        d = ImageDraw.Draw(img)
        # graticule
        step = 10 if (lon1 - lon0) > 25 else 5
        for lon in range(int(lon0 // step * step), int(lon1) + step, step):
            x = self.px(lon, 0)[0]
            d.line([(x, 0), (x, H)], fill=(40, 58, 78), width=max(1, int(W / 2400)))
        for lat in range(int(lat0 // step * step), int(lat1) + step, step):
            yy = self.px(0, lat)[1]
            d.line([(0, yy), (W, yy)], fill=(40, 58, 78), width=max(1, int(W / 2400)))
        # land
        lw = max(1, int(W / 1600))
        landmask = Image.new("L", (W, H), 0)
        dm = ImageDraw.Draw(landmask)
        for c in world()["countries"]:
            for poly in c["p"]:
                ring = poly[0]
                xs = [p[0] for p in ring]
                ys = [p[1] for p in ring]
                if max(xs) < lon0 - 5 or min(xs) > lon1 + 5 or max(ys) < lat0 - 5 or min(ys) > lat1 + 5:
                    continue
                dm.polygon([self.px(*p) for p in ring], fill=255)
        # land with a paper texture + soft coast glow
        glow = landmask.filter(ImageFilter.GaussianBlur(max(2, W / 400)))
        img.paste(Image.new("RGB", (W, H), (60, 90, 110)), (0, 0), glow.point(lambda v: int(v * 0.35)))
        paper = np.zeros((H, W, 3), np.float32)
        for i in range(3):
            paper[..., i] = LAND[i]
        paper += noise_tex(W, H, 11, 9)[..., None]
        img.paste(Image.fromarray(np.clip(paper, 0, 255).astype(np.uint8)), (0, 0), landmask)
        # inner shade for depth
        inner = landmask.filter(ImageFilter.GaussianBlur(max(2, W / 250)))
        shade = Image.eval(inner, lambda v: int((255 - v) * 0.5) if v > 0 else 0)
        img.paste(Image.new("RGB", (W, H), LAND_EDGE), (0, 0), Image.composite(shade, Image.new("L", (W, H), 0), landmask))
        d = ImageDraw.Draw(img)
        for c in world()["countries"]:
            for poly in c["p"]:
                ring = poly[0]
                xs = [p[0] for p in ring]
                ys = [p[1] for p in ring]
                if max(xs) < lon0 - 5 or min(xs) > lon1 + 5 or max(ys) < lat0 - 5 or min(ys) > lat1 + 5:
                    continue
                d.line([self.px(*p) for p in ring] + [self.px(*ring[0])], fill=(150, 128, 92), width=lw)
        if rivers:
            for r in world()["rivers"]:
                if r["s"] > (5 if (lon1 - lon0) < 60 else 3):
                    continue
                for line in r["l"]:
                    pts = [self.px(*p) for p in line]
                    if len(pts) > 1:
                        d.line(pts, fill=RIVER, width=max(1, int(lw * 2.2)), joint="curve")
        self.plain = img
        # highlighted empire regions (each with its own colour)
        self.hl = None
        if regions:
            hl = img.copy().convert("RGBA")
            for reg in regions:
                col = tuple(reg.get("rgb", GOLD))
                pts = [self.px(*p) for p in reg["points"]]
                ov = Image.new("RGBA", (W, H), (0, 0, 0, 0))
                od = ImageDraw.Draw(ov)
                od.polygon(pts, fill=col + (int(255 * reg.get("alpha", 0.42)),))
                # hatching for an old-map feel
                hatch = Image.new("L", (W, H), 0)
                hd = ImageDraw.Draw(hatch)
                gap = max(6, int(W / 160))
                for i in range(-H, W, gap):
                    hd.line([(i, 0), (i + H, H)], fill=60, width=max(1, lw))
                pm = Image.new("L", (W, H), 0)
                ImageDraw.Draw(pm).polygon(pts, fill=255)
                hatch = Image.composite(hatch, Image.new("L", (W, H), 0), pm)
                ov.paste(Image.new("RGBA", (W, H), col + (255,)), (0, 0), hatch)
                edge = Image.new("RGBA", (W, H), (0, 0, 0, 0))
                ImageDraw.Draw(edge).line(pts + [pts[0]], fill=col + (255,), width=max(2, lw * 3), joint="curve")
                eg = edge.filter(ImageFilter.GaussianBlur(max(2, W / 500)))
                hl = Image.alpha_composite(hl, ov)
                hl = Image.alpha_composite(hl, eg)
                hl = Image.alpha_composite(hl, edge)
            self.hl = hl.convert("RGB")

    def px(self, lon, lat):
        return ((lon - self.bbox[0]) * self.cl * self.k, (self.bbox[3] - lat) * self.k)

    def contains(self, b):
        return b[0] >= self.bbox[0] - 1e-6 and b[2] <= self.bbox[2] + 1e-6 and b[1] >= self.bbox[1] - 1e-6 and b[3] <= self.bbox[3] + 1e-6

    def view(self, b, W, H, hl_amount):
        x0, y0 = self.px(b[0], b[3])
        x1, y1 = self.px(b[2], b[1])
        x0, y0 = max(0.0, x0), max(0.0, y0)
        x1, y1 = min(float(self.W), max(x0 + 1, x1)), min(float(self.H), max(y0 + 1, y1))
        src = self.plain
        if self.hl is not None and hl_amount >= 0.999:
            src = self.hl
        im = src.resize((W, H), Image.BILINEAR, box=(x0, y0, x1, y1))
        if self.hl is not None and 0.001 < hl_amount < 0.999:
            im2 = self.hl.resize((W, H), Image.BILINEAR, box=(x0, y0, x1, y1))
            im = Image.blend(im, im2, hl_amount)
        return im


# ================================================================== scenes

class Scene:
    def __init__(self, sc, W, H, idx):
        self.sc, self.v, self.W, self.H, self.idx = sc, sc.get("visual") or {}, W, H, idx
        self.s = W / 1920.0

    def S(self, x):
        return int(x * self.s)

    def frame(self, t, dur):
        return dark_bg(self.W, self.H)


class TitleScene(Scene):
    def frame(self, t, dur):
        W, H = self.W, self.H
        img = dark_bg(W, H, (46, 34, 18))
        z = 1 + 0.04 * (t / max(dur, 0.1))
        img = img.resize((int(W * z), int(H * z)), Image.BILINEAR).crop((int(W * (z - 1) / 2), int(H * (z - 1) / 2), int(W * (z - 1) / 2) + W, int(H * (z - 1) / 2) + H))
        d = ImageDraw.Draw(img)
        a = ease_out(t / 1.2)
        kicker = self.v.get("kicker", "")
        title = self.v.get("text", "")
        sub = self.v.get("sub", "")
        cy = H * 0.46
        if kicker:
            f = font("Oswald", self.S(38), "Medium")
            col = tuple(int(c * a) for c in GOLD)
            d.text((W / 2, cy - self.S(150)), kicker.upper(), font=f, fill=col, anchor="mm")
        f = font("Cinzel", self.S(150 if len(title) < 14 else 110), "Black")
        lines = wrap(d, title.upper(), f, W * 0.86)
        lh = f.size * 1.08
        y = cy - (len(lines) - 1) * lh / 2 + (1 - a) * self.S(30)
        for ln in lines:
            shadow_text(img, (W / 2, y), ln, f, GOLD_L + (int(255 * a),), anchor="mm", blur=10, alpha=int(200 * a))
            y += lh
        d = ImageDraw.Draw(img)
        lw = int(W * 0.22 * ease_out((t - 0.4) / 1.0))
        if lw > 2:
            yy = y - lh / 2 + self.S(42)
            d.line([(W / 2 - lw, yy), (W / 2 + lw, yy)], fill=GOLD, width=max(2, self.S(3)))
            d.regular_polygon((W / 2, yy, self.S(9)), 4, fill=GOLD)
        if sub:
            b = ease_out((t - 0.7) / 1.0)
            f2 = font("Inter", self.S(40), "Regular")
            for i, ln in enumerate(wrap(d, sub, f2, W * 0.7)):
                d.text((W / 2, y + self.S(80) + i * self.S(54)), ln, font=f2, fill=tuple(int(c * b) for c in WHITE), anchor="mm")
        return vignette(img)


class CountScene(Scene):
    """Countdown slide: a huge number punches in with a light ring and rays, then the name rises underneath.
    visual: {"type": "count", "number": 10, "text": "Polar Bear", "sub": "The Arctic"}"""

    def frame(self, t, dur):
        W, H = self.W, self.H
        img = dark_bg(W, H, (40, 30, 18))
        d = ImageDraw.Draw(img, "RGBA")
        cx, cy = W / 2, H * 0.40
        num = str(self.v.get("number", ""))
        # light rays turning slowly behind the number
        ra = ease_out(t / 0.6)
        for k in range(16):
            ang = k * math.pi / 8 + t * 0.15
            r0, r1 = self.S(150), self.S(150) + self.S(900) * ra
            w = 0.05
            pts = [(cx + r0 * math.cos(ang - w), cy + r0 * math.sin(ang - w)), (cx + r1 * math.cos(ang - w * 0.4), cy + r1 * math.sin(ang - w * 0.4)),
                   (cx + r1 * math.cos(ang + w * 0.4), cy + r1 * math.sin(ang + w * 0.4)), (cx + r0 * math.cos(ang + w), cy + r0 * math.sin(ang + w))]
            d.polygon(pts, fill=GOLD + (int(26 * ra),))
        # shock ring
        k = clamp(t / 0.9)
        if k < 1:
            rr = self.S(120) + self.S(520) * ease_out(k)
            d.ellipse([cx - rr, cy - rr, cx + rr, cy + rr], outline=GOLD_L + (int(220 * (1 - k)),), width=max(2, int(self.S(10) * (1 - k)) + 1))
        # the number: punches in big, settles with a small bounce
        p = clamp(t / 0.45)
        sc = 1.9 - 0.9 * ease_out(p) + (0.06 * math.sin(min(1.0, (t - 0.45) / 0.4) * math.pi) if t > 0.45 else 0)
        f = font("Oswald", max(10, int(self.S(400) * sc)), "Bold")
        a = clamp(t / 0.2)
        txt = "#" + num if num and not num.startswith("#") else num
        shadow_text(img, (cx, cy), txt, f, WHITE + (int(255 * a),), anchor="mm", blur=18, offset=(0, 8), alpha=int(220 * a))
        glow = Image.new("RGBA", img.size, (0, 0, 0, 0))
        ImageDraw.Draw(glow).text((cx, cy), txt, font=f, fill=GOLD + (int(150 * a),), anchor="mm")
        glow = glow.filter(ImageFilter.GaussianBlur(self.S(26)))
        img.paste(glow, (0, 0), glow)
        d = ImageDraw.Draw(img, "RGBA")
        d.text((cx, cy), txt, font=f, fill=WHITE + (int(255 * a),), anchor="mm")
        # the name rises in, with an accent bar that grows
        b = ease_out((t - 0.35) / 0.6)
        if b > 0:
            name = (self.v.get("text") or "").upper()
            fn = font("Oswald", self.S(110 if len(name) < 16 else 84), "Bold")
            ny = H * 0.74 + (1 - b) * self.S(40)
            shadow_text(img, (cx, ny), name, fn, GOLD_L + (int(255 * b),), anchor="mm", blur=10, alpha=int(150 * b))
            d = ImageDraw.Draw(img, "RGBA")
            bw = d.textlength(name, font=fn) / 2 * ease_out((t - 0.55) / 0.7)
            d.rounded_rectangle([cx - bw, ny + self.S(66), cx + bw, ny + self.S(74)], radius=self.S(4), fill=GOLD + (int(255 * b),))
            if self.v.get("sub"):
                c_ = ease_out((t - 0.8) / 0.6)
                fs = font("Inter", self.S(40), "Medium")
                d.text((cx, ny + self.S(124)), self.v["sub"], font=fs, fill=WHITE + (int(220 * c_),), anchor="mm")
        return vignette(img)


class TextScene(Scene):
    def frame(self, t, dur):
        W, H = self.W, self.H
        img = dark_bg(W, H)
        d = ImageDraw.Draw(img)
        lines = self.v.get("lines") or []
        f = font("Oswald", self.S(84 if len(lines) <= 3 else 66), "SemiBold")
        n = max(1, len(lines))
        gap = max(0.6, min(1.6, (dur * 0.7) / n))
        lh = f.size * 1.35
        total = sum(len(wrap(d, ln, f, W * 0.8)) for ln in lines) * lh
        y = (H - total) / 2 + lh / 2 - self.S(40)
        for i, ln in enumerate(lines):
            a = ease_out((t - 0.3 - i * gap) / 0.6)
            for sub in wrap(d, ln, f, W * 0.8):
                if a > 0:
                    col = GOLD_L if (i == n - 1 and n > 1) else WHITE
                    shadow_text(img, (W / 2 + (1 - a) * self.S(40), y), sub, f, col + (int(255 * a),), anchor="mm", alpha=int(200 * a))
                y += lh
        return vignette(img)


class StatScene(Scene):
    def frame(self, t, dur):
        W, H = self.W, self.H
        img = dark_bg(W, H, (40, 30, 16))
        d = ImageDraw.Draw(img)
        num = float(self.v.get("number", 0))
        p = ease_out((t - 0.2) / max(1.2, min(2.6, dur * 0.45)))
        val = num * p
        dec = int(self.v.get("decimals", 0))
        s = f"{val:,.{dec}f}"
        txt = f"{self.v.get('prefix', '')}{s}{self.v.get('suffix', '')}"
        f = font("Oswald", self.S(230 if len(txt) < 10 else 170), "Bold")
        shadow_text(img, (W / 2, H * 0.42), txt, f, GOLD_L, anchor="mm", blur=14, alpha=230)
        d = ImageDraw.Draw(img)
        a = ease_out((t - 0.6) / 0.8)
        f2 = font("Inter", self.S(46), "Medium")
        y = H * 0.42 + self.S(170)
        for ln in wrap(d, self.v.get("label", ""), f2, W * 0.75):
            d.text((W / 2, y), ln, font=f2, fill=tuple(int(c * a) for c in WHITE), anchor="mm")
            y += self.S(60)
        if self.v.get("note"):
            f3 = font("Inter", self.S(28), "Regular")
            d.text((W / 2, y + self.S(20)), self.v["note"], font=f3, fill=tuple(int(c * a) for c in GREY), anchor="mm")
        return vignette(img)


class YearScene(Scene):
    def frame(self, t, dur):
        W, H = self.W, self.H
        img = dark_bg(W, H, (30, 26, 22))
        d = ImageDraw.Draw(img)
        y0, y1 = int(self.v.get("from", 0)), int(self.v.get("to", 0))
        p = ease_io((t - 0.3) / max(1.0, min(3.0, dur * 0.55)))
        yr = int(round(y0 + (y1 - y0) * p))
        # moving ruler
        cx = W / 2
        f_s = font("Oswald", self.S(30), "Regular")
        span = 40
        for k in range(-span, span + 1):
            yv = yr + k
            x = cx + k * self.S(46) - (y0 + (y1 - y0) * p - yr) * self.S(46)
            big = yv % 10 == 0
            hgt = self.S(60 if big else 28)
            col = GOLD if yv == yr else (110, 100, 86)
            d.line([(x, H * 0.70), (x, H * 0.70 - hgt)], fill=col, width=self.S(3 if big else 2))
            if big:
                d.text((x, H * 0.70 + self.S(34)), str(yv), font=f_s, fill=(140, 128, 110), anchor="mm")
        f = font("Cinzel", self.S(260), "Black")
        shadow_text(img, (W / 2, H * 0.40), str(yr), f, GOLD_L, anchor="mm", blur=16, alpha=230)
        d = ImageDraw.Draw(img)
        a = ease_out((t - 0.8) / 0.8)
        f2 = font("Inter", self.S(46), "Medium")
        d.text((W / 2, H * 0.40 + self.S(175)), self.v.get("label", ""), font=f2, fill=tuple(int(c * a) for c in WHITE), anchor="mm")
        return vignette(img)


class QuoteScene(Scene):
    def frame(self, t, dur):
        W, H = self.W, self.H
        img = dark_bg(W, H, (44, 36, 26))
        d = ImageDraw.Draw(img)
        f = font("Inter", self.S(54), "Medium")
        lines = wrap(d, self.v.get("text", ""), f, W * 0.72)
        lh = self.S(78)
        y = H / 2 - len(lines) * lh / 2 - self.S(30)
        d.text((W * 0.12, y - self.S(40)), "“", font=font("Cinzel", self.S(260), "Black"), fill=(90, 72, 40), anchor="lm")
        per = max(0.35, (dur * 0.6) / max(1, len(lines)))
        for i, ln in enumerate(lines):
            a = ease_out((t - 0.3 - i * per) / 0.7)
            if a > 0:
                d.text((W * 0.16, y + i * lh), ln, font=f, fill=tuple(int(c * a) for c in WHITE), anchor="lm")
        a = ease_out((t - 0.3 - len(lines) * per) / 0.7)
        f2 = font("Oswald", self.S(40), "Medium")
        d.text((W * 0.16, y + len(lines) * lh + self.S(50)), "— " + self.v.get("by", ""), font=f2, fill=tuple(int(c * a) for c in GOLD), anchor="lm")
        return vignette(img)


class BarsScene(Scene):
    """Simple animated bar chart. visual: {"title", "bars": [["label", value], ...], "unit", "note"}"""

    def frame(self, t, dur):
        W, H = self.W, self.H
        img = dark_bg(W, H)
        d = ImageDraw.Draw(img)
        bars = self.v.get("bars") or []
        f_t = font("Oswald", self.S(56), "SemiBold")
        d.text((W / 2, self.S(200)), self.v.get("title", ""), font=f_t, fill=WHITE, anchor="mm")
        if not bars:
            return img
        mx = max(float(b[1]) for b in bars) or 1
        n = len(bars)
        bw = min(self.S(300), int(W * 0.6 / n))
        gap = bw * 0.6
        total = n * bw + (n - 1) * gap
        x = (W - total) / 2
        base_y, maxh = H * 0.78, H * 0.44
        for i, (lab, val) in enumerate(bars):
            p = ease_out((t - 0.4 - i * 0.6) / 1.2)
            h = maxh * float(val) / mx * p
            col = GOLD if i == 0 else RED if float(val) < float(bars[0][1]) else GOLD_L
            d.rounded_rectangle([x, base_y - h, x + bw, base_y], radius=self.S(10), fill=col)
            if p > 0.05:
                d.text((x + bw / 2, base_y - h - self.S(40)), f"{float(val) * p:,.0f}{self.v.get('unit', '')}", font=font("Oswald", self.S(64), "Bold"), fill=WHITE, anchor="mm")
            d.text((x + bw / 2, base_y + self.S(44)), str(lab), font=font("Inter", self.S(36), "Medium"), fill=GREY, anchor="mm")
            x += bw + gap
        if self.v.get("note"):
            d.text((W / 2, base_y + self.S(110)), self.v["note"], font=font("Inter", self.S(28), "Regular"), fill=GREY, anchor="mm")
        return vignette(img)


class TimelineScene(Scene):
    def frame(self, t, dur):
        W, H = self.W, self.H
        img = dark_bg(W, H)
        d = ImageDraw.Draw(img)
        ev = self.v.get("events") or []
        if not ev:
            return img
        x0, x1, y = W * 0.08, W * 0.92, H * 0.52
        lp = ease_out(t / 1.0)
        d.line([(x0, y), (x0 + (x1 - x0) * lp, y)], fill=(120, 108, 90), width=self.S(4))
        n = len(ev)
        per = max(0.8, (dur - 1.2) / n)
        fy = font("Oswald", self.S(54), "Bold")
        ft = font("Inter", self.S(30), "Medium")
        for i, (yr, label) in enumerate(ev):
            x = x0 + (x1 - x0) * (i + 0.5) / n
            a = ease_out((t - 0.8 - i * per) / 0.6)
            if a <= 0:
                continue
            cur = (t - 0.8 - i * per) >= 0 and (i == n - 1 or (t - 0.8 - (i + 1) * per) < 0)
            r = self.S(16 if cur else 11)
            d.ellipse([x - r, y - r, x + r, y + r], fill=GOLD if cur else (180, 160, 120))
            if cur:
                rr = r + self.S(10) * (1 + 0.3 * math.sin(t * 5))
                d.ellipse([x - rr, y - rr, x + rr, y + rr], outline=GOLD, width=self.S(3))
            up = i % 2 == 0
            col = tuple(int(c * a) for c in (GOLD_L if cur else WHITE))
            d.text((x, y + (-self.S(70) if up else self.S(70))), str(yr), font=fy, fill=col, anchor="mm")
            lines = wrap(d, label, ft, (x1 - x0) / n * 1.6)
            yy = y + (-self.S(130) - (len(lines) - 1) * self.S(38) if up else self.S(130))
            for ln in lines:
                d.text((x, yy), ln, font=ft, fill=tuple(int(c * a) for c in (WHITE if cur else GREY)), anchor="mm")
                yy += self.S(38)
        return vignette(img)


def grade(im):
    """One warm, cinematic look for every picture (old paintings, photos, maps all match)."""
    im = im.convert("RGB")
    if THEME["name"] == "nature":  # clean, crisp, slightly cool and vivid
        g = np.asarray(im).astype(np.float32) / 255.0
        lum = g.mean(-1, keepdims=True)
        g = lum + (g - lum) * 1.12
        g = np.clip((g - 0.5) * 1.08 + 0.5, 0, 1) * np.array([0.98, 1.0, 1.03], np.float32)
        return Image.fromarray((np.clip(g, 0, 1) * 255).astype(np.uint8))
    g = np.asarray(im).astype(np.float32) / 255.0
    lum = g @ np.array([0.299, 0.587, 0.114], np.float32)
    sep = np.stack([lum * 1.07, lum * 0.92, lum * 0.72], -1)
    g = g * 0.72 + sep * 0.28
    g = np.clip((g - 0.5) * 1.12 + 0.5, 0, 1)  # a little contrast
    g = g ** 0.95
    return Image.fromarray((g * 255).astype(np.uint8))


class ImageScene(Scene):
    MOVES = ("in", "out", "left", "right", "up", "in")
    RECUT_FOCUS = ((0.28, 0.34), (0.72, 0.34), (0.5, 0.62), (0.3, 0.66), (0.7, 0.66))

    def __init__(self, *a):
        super().__init__(*a)
        self.img = None
        f = self.v.get("file")
        if f and os.path.exists(A("images", f)):
            try:
                im = Image.open(A("images", f))
                im.thumbnail((3200, 3200))
                self.img = grade(im)
            except Exception:
                self.img = None
        self.recut = int(self.v.get("recut") or 0)
        self.move = self.v.get("zoom") or self.MOVES[(self.idx + self.recut * 3) % len(self.MOVES)]
        self.fb = None
        if self.img is not None:
            iw, ih = self.img.size
            fs = [f_ for f_ in (self.v.get("faces") or []) if len(f_) >= 4]
            if fs:
                x0, y0 = min(f_[0] for f_ in fs), min(f_[1] for f_ in fs)
                x1, y1 = max(f_[2] for f_ in fs), max(f_[3] for f_ in fs)
                w_, h_ = x1 - x0, y1 - y0
                # the whole head: hair/hat above, chin and neck below
                self.fb = (max(0.0, x0 - 0.32 * w_) * iw, max(0.0, y0 - 0.55 * h_) * ih, min(1.0, x1 + 0.32 * w_) * iw, min(1.0, y1 + 0.38 * h_) * ih)
            fill_w, fill_h = min(iw, ih * self.W / self.H), min(ih, iw * self.H / self.W)
            too_big = self.fb is not None and ((self.fb[3] - self.fb[1]) > fill_h * 0.97 or (self.fb[2] - self.fb[0]) > fill_w * 0.97)
        else:
            too_big = False
        # tall / square pictures, or faces that don't fit a 16:9 crop: show the WHOLE picture on a soft blurred copy of itself
        self.portrait = self.img is not None and not self.v.get("fill") and (self.img.size[0] / self.img.size[1] < 1.3 or too_big)
        self._bg = None
        # small or every few landscape pictures: a printed photo floating over a blurred copy (Zem TV / Dhruv Rathee style)
        self.card = (self.img is not None and not self.portrait and not self.v.get("fill") and not self.recut
                     and (self.v.get("style") == "card" or (self.v.get("style") != "full" and (self.img.size[0] < self.W * 0.8 or self.idx % 6 == 4))))

    def _title_card(self, t):
        W, H = self.W, self.H
        img = dark_bg(W, H, (50, 38, 22))
        d = ImageDraw.Draw(img)
        f = font("Cinzel", self.S(80), "Bold")
        q = self.v.get("search") or ""
        label = self.v.get("caption") or (q[0] if isinstance(q, list) and q else q)
        lines = wrap(d, label, f, W * 0.75)
        y = H / 2 - (len(lines) - 1) * self.S(50) + (1 - ease_out(t / 1.0)) * self.S(20)
        for ln in lines:
            shadow_text(img, (W / 2, y), ln, f, GOLD_L, anchor="mm")
            y += self.S(100)
        return vignette(img)

    def frame(self, t, dur):
        W, H = self.W, self.H
        if self.img is None:  # no picture found: a clean title card instead, the video still works
            return self._title_card(t)
        if self.portrait:
            return self._portrait_frame(t, dur)
        if self.card:
            return self._card_frame(t, dur)
        im = self.img
        iw, ih = im.size
        sc = max(W / iw, H / ih)
        m = self.move
        detail = self.recut > 0
        if dur > 5.2 and not self.recut:  # long shot: cut to a closer detail of the same picture halfway
            half = dur / 2
            if t >= half:
                t, dur, detail = t - half, dur - half, True
                m = {"in": "left", "out": "in", "left": "right", "right": "in", "up": "out"}.get(m, "in")
            else:
                dur = half
        p = ease_io(t / max(dur, 0.1)) * 0.85 + (t / max(dur, 0.1)) * 0.15
        z = {"in": 1.03 + 0.08 * p, "out": 1.11 - 0.08 * p}.get(m, 1.07)
        if detail:
            z *= 1.45 if self.recut else 1.18
        vw, vh = W / (sc * z), H / (sc * z)
        fb = self.fb
        if fb:
            fx, fy = (fb[0] + fb[2]) / 2 / iw, (fb[1] + fb[3]) / 2 / ih
        else:
            fx, fy = self.v.get("focus", [0.5, 0.42])  # a little above the middle: faces are usually in the upper part
            if self.recut:
                fx, fy = self.RECUT_FOCUS[(self.recut - 1) % len(self.RECUT_FOCUS)]
            elif detail:
                fx, fy = fx + (0.08 if self.idx % 2 else -0.08), fy - 0.04
        if fb:  # never zoom so close that the face doesn't fit
            need_w = max(fb[2] - fb[0], (fb[3] - fb[1]) * W / H) * 1.04
            if vw < need_w:
                vw, vh = need_w, need_w * H / W
        maxw = min(float(iw), ih * W / H)
        if vw > maxw:
            vw, vh = maxw, maxw * H / W
        dx = {"left": 0.06 - 0.12 * p, "right": -0.06 + 0.12 * p}.get(m, (p - 0.5) * 0.03)
        dy = {"up": 0.05 - 0.10 * p}.get(m, 0)
        cx, cy = (fx + dx) * iw, (fy + dy) * ih
        lo_x, hi_x = vw / 2, iw - vw / 2
        lo_y, hi_y = vh / 2, ih - vh / 2
        if fb:  # the face box must stay fully inside the view
            lo_x, hi_x = max(lo_x, fb[2] - vw / 2), min(hi_x, fb[0] + vw / 2)
            lo_y, hi_y = max(lo_y, fb[3] - vh / 2), min(hi_y, fb[1] + vh / 2)
            if lo_x > hi_x:
                lo_x = hi_x = clamp((fb[0] + fb[2]) / 2, vw / 2, iw - vw / 2)
            if lo_y > hi_y:
                lo_y = hi_y = clamp((fb[1] + fb[3]) / 2, vh / 2, ih - vh / 2)
        cx = min(max(cx, lo_x), hi_x) if lo_x <= hi_x else iw / 2
        cy = min(max(cy, lo_y), hi_y) if lo_y <= hi_y else ih / 2
        x0, y0 = max(0.0, cx - vw / 2), max(0.0, cy - vh / 2)  # tiny rounding errors must never give a negative box
        x1, y1 = min(float(iw), x0 + vw), min(float(ih), y0 + vh)
        self.last_box = (x0, y0, x1, y1)
        frame = im.resize((W, H), Image.BILINEAR, box=(x0, y0, x1, y1))
        frame = vignette(frame, 0.62)
        return self._caption(frame, t)

    def _portrait_frame(self, t, dur):
        W, H = self.W, self.H
        im = self.img
        iw, ih = im.size
        if self._bg is None:  # blurred, darker copy that fills the screen behind the picture (made once)
            bw, bh = int(W * 1.12), int(H * 1.12)
            sc = max(bw / iw, bh / ih)
            b = im.resize((max(1, int(iw * sc / 4)), max(1, int(ih * sc / 4))), Image.BILINEAR)
            b = b.filter(ImageFilter.GaussianBlur(10)).resize((int(iw * sc), int(ih * sc)), Image.BILINEAR)
            cx, cy = (b.size[0] - bw) // 2, (b.size[1] - bh) // 2
            b = b.crop((cx, cy, cx + bw, cy + bh))
            self._bg = Image.blend(b, Image.new("RGB", b.size, (12, 10, 8)), 0.45)
        p = ease_io(clamp(t / max(dur, 0.1)))
        if self.move == "out":
            p = 1 - p
        bw, bh = self._bg.size
        ox = int((bw - W) * (0.5 + (p - 0.5) * 0.6))
        frame = self._bg.crop((ox, (bh - H) // 2, ox + W, (bh - H) // 2 + H))
        z = 1.0 + 0.05 * p  # gentle push-in, the whole picture always stays on screen
        fh = H * 0.90 * z
        fw = fh * iw / ih
        if fw > W * 0.94:  # very wide-ish square: keep inside the screen
            fw = W * 0.94
            fh = fw * ih / iw
        fg = im.resize((max(1, int(fw)), max(1, int(fh))), Image.LANCZOS)
        x, y = int((W - fw) / 2), int((H - fh) / 2)
        if self.recut:  # the same tall picture again: put it on one side so the shot looks new
            x = int(W * (0.06 if self.recut % 2 else 0.94) - (0 if self.recut % 2 else fw))
            x = max(0, min(W - int(fw), x))
        sh = Image.new("L", (fg.size[0] + 60, fg.size[1] + 60), 0)
        ImageDraw.Draw(sh).rectangle([30, 30, 30 + fg.size[0], 30 + fg.size[1]], fill=170)
        sh = sh.resize((sh.size[0] // 4, sh.size[1] // 4)).filter(ImageFilter.GaussianBlur(5)).resize(sh.size)
        frame.paste((0, 0, 0), (x - 30, y - 22), sh)
        frame.paste(fg, (x, y))
        frame = vignette(frame, 0.5)
        return self._caption(frame, t)

    def _blur_bg(self):
        if self._bg is None:
            W, H = self.W, self.H
            im = self.img
            iw, ih = im.size
            bw, bh = int(W * 1.12), int(H * 1.12)
            sc = max(bw / iw, bh / ih)
            b = im.resize((max(1, int(iw * sc / 4)), max(1, int(ih * sc / 4))), Image.BILINEAR)
            b = b.filter(ImageFilter.GaussianBlur(10)).resize((int(iw * sc), int(ih * sc)), Image.BILINEAR)
            cx, cy = (b.size[0] - bw) // 2, (b.size[1] - bh) // 2
            b = b.crop((cx, cy, cx + bw, cy + bh))
            self._bg = Image.blend(b, Image.new("RGB", b.size, (12, 10, 8)), 0.5)
        return self._bg

    def _card_frame(self, t, dur):
        """The picture as a printed photo: thin light border, soft shadow, slowly drifting and turning over its own blurred copy."""
        W, H = self.W, self.H
        im = self.img
        iw, ih = im.size
        bg = self._blur_bg()
        p = ease_io(clamp(t / max(dur, 0.1)))
        bw, bh = bg.size
        side = 1 if self.idx % 2 else -1
        ox = int((bw - W) * (0.5 + side * (p - 0.5) * 0.7))
        frame = bg.crop((ox, (bh - H) // 2, ox + W, (bh - H) // 2 + H))
        z = 0.95 + 0.06 * p
        fw = W * 0.74 * z
        fh = fw * ih / iw
        if fh > H * 0.80 * z:
            fh = H * 0.80 * z
            fw = fh * iw / ih
        fg = im.resize((max(1, int(fw)), max(1, int(fh))), Image.LANCZOS)
        bd = max(4, self.S(14))
        framed = Image.new("RGB", (fg.size[0] + bd * 2, fg.size[1] + bd * 2), (236, 230, 216))
        framed.paste(fg, (bd, bd))
        ang = side * (1.6 - 2.4 * p)
        rc = framed.convert("RGBA").rotate(ang, expand=True, resample=Image.BICUBIC)
        x = int((W - rc.size[0]) / 2 + side * (p - 0.5) * W * 0.04)
        y = int((H - rc.size[1]) / 2)
        sh = Image.new("RGBA", rc.size, (0, 0, 0, 0))
        sh.putalpha(rc.getchannel("A").point(lambda a_: int(a_ * 0.65)))
        sh = sh.resize((max(1, sh.size[0] // 4), max(1, sh.size[1] // 4))).filter(ImageFilter.GaussianBlur(5)).resize(rc.size)
        frame.paste((0, 0, 0), (x + self.S(18), y + self.S(26)), sh)
        frame.paste(rc, (x, y), rc)
        frame = vignette(frame, 0.55)
        return self._caption(frame, t)

    def _caption(self, frame, t):
        W, H = self.W, self.H
        if self.v.get("caption"):
            d = ImageDraw.Draw(frame)
            f = font("Oswald", self.S(30), "Medium")
            a = ease_out((t - 0.5) / 0.6)
            txt = self.v["caption"].upper()
            w_, h_ = tw(d, txt, f)
            x, y = self.S(60), H - self.S(110)
            d.line([(x, y - self.S(14)), (x + self.S(60) * a, y - self.S(14))], fill=GOLD, width=self.S(3))
            d.text((x, y), txt, font=f, fill=tuple(int(c * a) for c in WHITE), stroke_width=self.S(3), stroke_fill=(0, 0, 0))
        return frame


class MapScene(Scene):
    def __init__(self, *a):
        super().__init__(*a)
        v = self.v
        aspect = self.W / self.H
        self.b0 = fit_bbox(v.get("from") or v.get("view") or [-20, 0, 40, 40], aspect)
        self.b1 = fit_bbox(v.get("to") or v.get("view") or v.get("from") or [-20, 0, 40, 40], aspect)
        self.cl = math.cos(math.radians((self.b1[1] + self.b1[3]) / 2))
        self.regions = []
        for r in v.get("regions") or []:
            r = dict(r)
            r["rgb"] = hex_rgb(r.get("color", "#e6b03c"))
            self.regions.append(r)
        self.hl_from = float(v.get("highlight_at", 0.8))
        self._bases = None

    def view_at(self, p):
        c0 = ((self.b0[0] + self.b0[2]) / 2, (self.b0[1] + self.b0[3]) / 2)
        c1 = ((self.b1[0] + self.b1[2]) / 2, (self.b1[1] + self.b1[3]) / 2)
        w0, w1 = self.b0[2] - self.b0[0], self.b1[2] - self.b1[0]
        w = math.exp(math.log(w0) + (math.log(w1) - math.log(w0)) * p)
        # move the centre in step with the zoom, so the camera "flies"
        q = (w0 - w) / (w0 - w1) if abs(w0 - w1) > 1e-6 else p
        cx = c0[0] + (c1[0] - c0[0]) * q
        cy = c0[1] + (c1[1] - c0[1]) * q
        h = w * self.cl * self.H / self.W
        return [cx - w / 2, cy - h / 2, cx + w / 2, cy + h / 2]

    def bases(self):
        """A few pre-drawn maps along the camera path, each sharp enough for its part of the zoom."""
        if self._bases is None:
            views = [self.view_at(i / 80) for i in range(81)]
            segs, cur = [], [views[0]]
            for v in views[1:]:
                ws = [x[2] - x[0] for x in cur + [v]]
                if max(ws) / min(ws) > 1.8:
                    segs.append(cur)
                    cur = [cur[-1], v]
                else:
                    cur.append(v)
            segs.append(cur)
            bs = []
            for seg in segs:
                u = [min(x[0] for x in seg), min(x[1] for x in seg), max(x[2] for x in seg), max(x[3] for x in seg)]
                m = 0.02
                u = [u[0] - (u[2] - u[0]) * m, u[1] - (u[3] - u[1]) * m, u[2] + (u[2] - u[0]) * m, u[3] + (u[3] - u[1]) * m]
                minw = min(x[2] - x[0] for x in seg)
                px_w = min(6400, self.W * 1.1 * (u[2] - u[0]) / minw)
                bs.append(MapBase(u, px_w, self.cl, self.regions))
            self._bases = bs
        return self._bases

    def cur_bbox(self, t, dur):
        p = ease_io((t - 0.2) / max(0.5, dur - 0.6)) if self.b0 != self.b1 else 0
        return self.view_at(p)

    def frame(self, t, dur):
        W, H = self.W, self.H
        b = self.cur_bbox(t, dur)
        # sharpest pre-drawn map that contains this view
        cands = [x for x in self.bases() if x.contains(b)] or self.bases()
        base = max(cands, key=lambda x: x.k)
        hl = ease((t - self.hl_from) / 1.0) if self.regions else 0
        img = base.view(b, W, H, hl).convert("RGBA")
        ov = Image.new("RGBA", (W, H), (0, 0, 0, 0))
        d = ImageDraw.Draw(ov)
        to_px = lambda lon, lat: ((lon - b[0]) * self.cl * W / ((b[2] - b[0]) * self.cl), (b[3] - lat) * H / (b[3] - b[1]))
        # region labels
        for r in self.regions:
            if r.get("label") and hl > 0.05:
                pts = r["points"]
                lx = r.get("label_at", [sum(p[0] for p in pts) / len(pts), sum(p[1] for p in pts) / len(pts)])
                x, y = to_px(*lx)
                f = font("Cinzel", self.S(44), "Bold")
                d.text((x, y), r["label"].upper(), font=f, fill=(255, 245, 225, int(255 * hl)), anchor="mm", stroke_width=self.S(4), stroke_fill=(30, 20, 8, int(220 * hl)))
        # geography labels: SAHARA DESERT, ATLANTIC OCEAN, EGYPT ...
        for lb in self.v.get("labels") or []:
            x, y = to_px(*lb["at"])
            sea = lb.get("kind") == "sea"
            f = font("Cinzel", self.S(int(lb.get("size", 34))), "Regular" if sea else "Bold")
            txt = " ".join(lb["text"].upper())
            a = ease_out((t - float(lb.get("at_time", 0.4))) / 0.8)
            col = (150, 185, 215) if sea else (96, 74, 44)
            d.text((x, y), txt, font=f, fill=col + (int(220 * a),), anchor="mm")
        # route (draws itself)
        route = self.v.get("route") or []
        if len(route) > 1:
            r0 = float(self.v.get("route_start", 0.8))
            r1 = float(self.v.get("route_end", max(r0 + 1, dur * 0.85)))
            p = ease_io((t - r0) / max(0.5, r1 - r0))
            pts = [to_px(*x) for x in route]
            segs = [math.dist(pts[i], pts[i + 1]) for i in range(len(pts) - 1)]
            L = sum(segs) or 1
            want = L * p
            out = [pts[0]]
            for i, sl in enumerate(segs):
                if want >= sl:
                    out.append(pts[i + 1])
                    want -= sl
                else:
                    f_ = want / sl if sl else 0
                    out.append((pts[i][0] + (pts[i + 1][0] - pts[i][0]) * f_, pts[i][1] + (pts[i + 1][1] - pts[i][1]) * f_))
                    break
            if p > 0 and len(out) > 1:
                col = hex_rgb(self.v.get("route_color", "#d64834"))
                q = 4
                glow = Image.new("RGBA", (W // q, H // q), (0, 0, 0, 0))
                ImageDraw.Draw(glow).line([(x / q, y / q) for x, y in out], fill=col + (150,), width=max(2, self.S(18) // q), joint="curve")
                glow = glow.filter(ImageFilter.GaussianBlur(max(1, self.S(8) // q))).resize((W, H), Image.BILINEAR)
                img = Image.alpha_composite(img, glow)
                d2 = ImageDraw.Draw(img)
                d2.line(out, fill=col + (255,), width=self.S(7), joint="curve")
                hx, hy = out[-1]
                rr = self.S(13)
                d2.ellipse([hx - rr, hy - rr, hx + rr, hy + rr], fill=(255, 240, 220, 255), outline=col + (255,), width=self.S(4))
        # places
        for i, pt in enumerate(self.v.get("points") or []):
            at = float(pt.get("at_time", 0.5 + i * 0.5))
            a = ease_out((t - at) / 0.5)
            if a <= 0:
                continue
            x, y = to_px(*pt["at"])
            col = hex_rgb(pt.get("color", "#fff2d8"))
            pulse = (t - at) % 1.6 / 1.6
            rr = self.S(10) + self.S(26) * pulse
            d.ellipse([x - rr, y - rr, x + rr, y + rr], outline=col + (int(200 * (1 - pulse) * a),), width=self.S(3))
            r = self.S(10)
            d.ellipse([x - r, y - r, x + r, y + r], fill=col + (int(255 * a),), outline=(30, 20, 10, int(255 * a)), width=self.S(3))
            f = font("Cinzel", self.S(36), "Bold")
            side = pt.get("side", "right")
            tx = x + self.S(24) if side == "right" else x - self.S(24)
            anc = "lm" if side == "right" else "rm"
            if side == "top":
                tx, anc = x, "md"
                y -= self.S(26)
            elif side == "bottom":
                tx, anc = x, "ma"
                y += self.S(26)
            d.text((tx, y), pt["name"], font=f, fill=(255, 248, 232, int(255 * a)), anchor=anc, stroke_width=self.S(4), stroke_fill=(16, 12, 8, int(235 * a)))
            if pt.get("note"):
                f2 = font("Inter", self.S(30), "SemiBold")
                ny = y + self.S(34) if side != "top" else y - self.S(40)
                d.text((tx, ny), pt["note"], font=f2, fill=GOLD_L + (int(255 * a),), anchor=anc, stroke_width=self.S(4), stroke_fill=(16, 12, 8, int(235 * a)))
        img = Image.alpha_composite(img, ov).convert("RGB")
        return vignette(img, 0.5)


def hex_rgb(h):
    h = h.lstrip("#")
    return tuple(int(h[i:i + 2], 16) for i in (0, 2, 4))


SCENES = {"count": CountScene, "title": TitleScene, "text": TextScene, "stat": StatScene, "year": YearScene, "quote": QuoteScene,
          "bars": BarsScene, "timeline": TimelineScene, "image": ImageScene, "map": MapScene}


# ================================================================== voice

def tts_text(s):
    """Makes numbers sound right: 1324 -> thirteen twenty-four, $400 billion -> 400 billion dollars."""
    ones = "zero one two three four five six seven eight nine ten eleven twelve thirteen fourteen fifteen sixteen seventeen eighteen nineteen".split()
    tens = "_ _ twenty thirty forty fifty sixty seventy eighty ninety".split()

    def two(n):
        if n < 20:
            return ones[n]
        return tens[n // 10] + ("-" + ones[n % 10] if n % 10 else "")

    def year(m):
        y = int(m.group(0))
        if 2000 <= y <= 2009:
            return "two thousand" + (" " + ones[y - 2000] if y > 2000 else "")
        hi, lo = divmod(y, 100)
        if lo == 0:
            return two(hi) + " hundred"
        return two(hi) + (" oh " + ones[lo] if lo < 10 else " " + two(lo))

    s = re.sub(r"\bc\.\s?(?=\d)", "around ", s)
    s = re.sub(r"\$\s?([\d,.]+)\s?(thousand|million|billion|trillion)?", lambda m: m.group(1) + (" " + m.group(2) if m.group(2) else "") + " dollars", s)
    s = re.sub(r"(?<![\d,.])(1[0-9]{3}|20[0-9]{2})(?![\d,])(?!\s?(?:people|camels|ships|km|kilometres|miles|men|soldiers|years))", year, s)
    s = s.replace("\u2014", ", ").replace("\u2013", " to ")
    return s


# "Saim": a calm, low, mysterious American storyteller. Made by blending free Kokoro voices, then mastered like a
# documentary narration (warm low end, clear presence, soft de-harsh, gentle compression, a touch of room).
SAIM_MIX = {"saim": [("am_onyx", 0.5), ("am_michael", 0.5)],
            "saim_deep": [("am_onyx", 0.8), ("am_michael", 0.2)],
            "saim_warm": [("am_michael", 0.5), ("am_onyx", 0.3), ("am_puck", 0.2)]}
SAIM_SPEED = 0.9
SAIM_CHAIN = ("highpass=f=70,equalizer=f=160:t=q:w=0.9:g=3,equalizer=f=3500:t=q:w=1.4:g=1.5,equalizer=f=7500:t=q:w=1.2:g=-2,"
              "acompressor=threshold=-22dB:ratio=3:attack=6:release=140:makeup=2.5,aecho=0.85:0.5:23|41:0.10|0.06")


def master_voice(a):
    """Runs the narration through the Saim mastering chain (ffmpeg)."""
    a = np.concatenate([np.asarray(a, np.float32), np.zeros(int(SR * 0.12), np.float32)])
    p = subprocess.run([ffmpeg_exe(), "-v", "error", "-f", "f32le", "-ar", str(SR), "-ac", "1", "-i", "-", "-af", SAIM_CHAIN,
                        "-f", "f32le", "-ar", str(SR), "-ac", "1", "-"], input=a.tobytes(), capture_output=True)
    if p.returncode != 0 or not p.stdout:
        return a
    out = np.frombuffer(p.stdout, np.float32).copy()
    # every sentence at the same loudness (about -19 dBFS RMS of the spoken part), never clipping
    loud = out[np.abs(out) > 0.02]
    rms = float(np.sqrt(np.mean(loud ** 2))) if len(loud) > 100 else 0
    if rms > 0:
        out = out * (0.11 / rms)
    pk = float(np.max(np.abs(out))) if len(out) else 0
    return out * (0.95 / pk) if pk > 0.95 else out


class Voice:
    def __init__(self, cfg):
        self.voice = cfg.get("voice", "saim")
        self.speed = float(cfg.get("speed", 0.95))
        self.kind = None
        self.k = None

    def _kokoro(self):
        if self.k is None:
            from kokoro_onnx import Kokoro
            self.k = Kokoro(MODEL, VOICES)
        return self.k

    def say(self, text):
        """Returns float32 mono audio at 24 kHz."""
        if getattr(self, "clips", None):
            return self.clips.pop(0)
        if self.voice in ("none", "silent", "own"):
            # no AI voice: silence as long as a person needs to say this line (about 2.4 words a second)
            self.kind = "none"
            n_words = len(re.findall(r"\w+", text))
            return np.zeros(int(SR * (0.35 + n_words / (2.4 * max(0.6, self.speed)))), np.float32)
        t = tts_text(text)
        mix = json.dumps(SAIM_MIX.get(self.voice, "")) + SAIM_CHAIN if self.voice.startswith("saim") else ""
        cache = A("cache", "voice", hashlib.sha1(f"{self.voice}|{self.speed}|{mix}|{t}".encode()).hexdigest() + ".npy")
        if os.path.exists(cache):
            return np.load(cache)
        a = None
        errors = []
        if self.voice == "saim_neural":  # Microsoft's natural online voice, slowed and lowered, then mastered
            try:
                a = master_voice(self._edge(t, "en-US-AndrewMultilingualNeural", rate=f"{int((self.speed * 0.92 - 1) * 100):+d}%", pitch="-3Hz"))
                self.kind = "saim_neural"
            except Exception as e:
                errors.append(f"online voice: {e}")
        if a is None and os.path.exists(MODEL):
            try:
                k = self._kokoro()
                v = self.voice if self.voice != "saim_neural" else "saim"
                if v in SAIM_MIX:
                    style = sum(w * k.get_voice_style(n) for n, w in SAIM_MIX[v]).astype(np.float32)
                    a, sr = k.create(t, voice=style, speed=SAIM_SPEED * self.speed / 0.95, lang="en-us")
                    a = master_voice(a)
                else:
                    lang = "en-gb" if v.startswith("b") else "en-us"
                    a, sr = k.create(t, voice=v, speed=self.speed, lang=lang)
                a = np.asarray(a, np.float32)
                self.kind = "kokoro"
            except Exception as e:
                errors.append(f"kokoro: {e}")
        if a is None:
            try:
                a = self._edge(t)
                self.kind = "edge"
            except Exception as e:
                errors.append(f"edge: {e}")
        if a is None:
            raise RuntimeError("No voice worked. " + " | ".join(errors))
        os.makedirs(os.path.dirname(cache), exist_ok=True)
        np.save(cache, a)
        return a

    def _edge(self, t, name=None, rate=None, pitch="+0Hz"):
        import asyncio
        import edge_tts
        name = name or {"bm_george": "en-GB-RyanNeural", "bm_lewis": "en-GB-ThomasNeural", "am_onyx": "en-US-AndrewNeural"}.get(self.voice, "en-US-AndrewNeural")
        tmp = A("cache", f"edge_{os.getpid()}_{threading.get_ident()}.mp3")
        os.makedirs(A("cache"), exist_ok=True)
        rate = rate or f"{int((self.speed - 1) * 100):+d}%"
        asyncio.run(edge_tts.Communicate(t, name, rate=rate, pitch=pitch).save(tmp))
        try:
            return decode_audio(tmp)
        finally:
            try:
                os.remove(tmp)
            except OSError:
                pass


def ffmpeg_exe():
    try:
        import imageio_ffmpeg
        return imageio_ffmpeg.get_ffmpeg_exe()
    except Exception:
        return shutil.which("ffmpeg") or "ffmpeg"


def decode_audio(path):
    p = subprocess.run([ffmpeg_exe(), "-v", "error", "-i", path, "-f", "f32le", "-ac", "1", "-ar", str(SR), "-"], capture_output=True, check=True)
    return np.frombuffer(p.stdout, np.float32).copy()


def write_wav(path, a):
    a = np.clip(a, -1, 1)
    with wave.open(path, "wb") as w:
        w.setnchannels(1)
        w.setsampwidth(2)
        w.setframerate(SR)
        w.writeframes((a * 32767).astype(np.int16).tobytes())


AUDIO_EXT = (".mp3", ".m4a", ".wav", ".ogg", ".aac", ".opus", ".flac", ".mp4")


def own_voice_file(name):
    """voiceover/<script name>.mp3 (or .m4a/.wav...) = your own recording of the whole script."""
    d = A("voiceover")
    if not os.path.isdir(d):
        return None
    for f in sorted(os.listdir(d)):
        b, e = os.path.splitext(f)
        if b.lower() == name.lower() and e.lower() in AUDIO_EXT:
            return os.path.join(d, f)
    return None


def split_own_voice(audio, texts):
    """Cuts one long recording into one clip per sentence.
    Finds the pauses in your recording and picks, for each sentence end, the pause that best fits
    where it should be (by word count). Result: every picture changes exactly when you say it."""
    hop = int(SR * 0.02)
    n = len(audio) // hop
    if n < 10 or not texts:
        return [audio] + [np.zeros(int(SR * 0.3), np.float32)] * (len(texts) - 1)
    rms = np.sqrt(np.mean(audio[:n * hop].reshape(n, hop) ** 2, axis=1) + 1e-12)
    db = 20 * np.log10(rms)
    loud = np.percentile(db, 90)
    floor = np.percentile(db, 10)
    thr = max(floor + 6, loud - 30)
    speech = db > thr
    idx = np.nonzero(speech)[0]
    s0, s1 = (idx[0], idx[-1] + 1) if len(idx) else (0, n)
    # pauses (runs of silence) inside the speech
    pauses = []
    i = s0
    while i < s1:
        if not speech[i]:
            j = i
            while j < s1 and not speech[j]:
                j += 1
            if j - i >= 6:  # 120 ms or longer
                pauses.append(((i + j) / 2, (j - i)))
            i = j
        else:
            i += 1
    words = [max(1, len(re.findall(r"\w+", t))) for t in texts]
    tot = float(sum(words))
    k = len(texts) - 1
    span = s1 - s0
    exp = [s0 + span * sum(words[:q + 1]) / tot for q in range(k)]
    chosen = []
    if k > 0 and len(pauses) >= k:
        # dynamic programming over (sentence end -> pause): each sentence should last about as long as its
        # word count says, long pauses are more likely sentence ends, and we must not drift far overall
        M = len(pauses)
        INF = 1e18
        rate = span / tot
        pos = [pp[0] for pp in pauses]
        bonus = [min(ln, 50) / 10.0 for _, ln in pauses]

        def seg(q, length):
            e = words[q] * rate
            r = length / e if e > 0 else 1
            if r <= 0:
                return INF
            return (math.log(r) ** 2) * 6

        def drift(q, m):
            return ((pos[m] - exp[q]) / span) ** 2 * 60

        cost = [[INF] * M for _ in range(k)]
        back = [[-1] * M for _ in range(k)]
        for m in range(M):
            cost[0][m] = seg(0, pos[m] - s0) - bonus[m] + drift(0, m)
        for q in range(1, k):
            for m in range(q, M):
                best, bi = INF, -1
                for m2 in range(q - 1, m):
                    if cost[q - 1][m2] >= INF:
                        continue
                    v = cost[q - 1][m2] + seg(q, pos[m] - pos[m2])
                    if v < best:
                        best, bi = v, m2
                if bi >= 0:
                    cost[q][m] = best - bonus[m] + drift(q, m)
                    back[q][m] = bi
        m = min(range(M), key=lambda x: cost[k - 1][x] + seg(k, s1 - pos[x]))
        for q in range(k - 1, -1, -1):
            chosen.append(m)
            m = back[q][m]
        chosen = [pauses[x][0] for x in reversed(chosen)]
    else:
        chosen = exp
    cuts = [s0] + [int(x) for x in chosen] + [s1]
    clips = []
    for q in range(len(texts)):
        a, b = cuts[q], max(cuts[q] + 1, cuts[q + 1])
        seg = speech[a:b]
        on = np.nonzero(seg)[0]
        if len(on):
            a2, b2 = a + max(0, on[0] - 4), a + min(len(seg), on[-1] + 5)
        else:
            a2, b2 = a, b
        clip = audio[a2 * hop:b2 * hop].astype(np.float32)
        f = min(len(clip) // 4, int(SR * 0.01))
        if f > 1:
            clip[:f] *= np.linspace(0, 1, f)
            clip[-f:] *= np.linspace(1, 0, f)
        clips.append(clip)
    return clips


def whoosh(sec=0.7, seed=0):
    rng = np.random.default_rng(seed)
    n = int(SR * sec)
    x = rng.normal(0, 1, n).astype(np.float32)
    # band sweep: simple one-pole low-pass with moving cutoff
    out = np.zeros(n, np.float32)
    y = 0.0
    for i in range(n):
        f = 0.02 + 0.25 * math.sin(math.pi * i / n)
        y += f * (x[i] - y)
        out[i] = y
    env = np.sin(np.linspace(0, math.pi, n)) ** 2
    return out * env * 0.5


def tick():
    n = int(SR * 0.03)
    t = np.arange(n) / SR
    return (np.sin(2 * math.pi * 2400 * t) * np.exp(-t * 180)).astype(np.float32) * 0.5




_CLICKS = {}


def type_click(seed=0):
    """A typewriter key: a short bright noise snap plus a soft low knock."""
    k = seed % 5
    if k not in _CLICKS:
        rng = np.random.default_rng(300 + k)
        n = int(SR * 0.045)
        t = np.arange(n) / SR
        snap = rng.normal(0, 1, n).astype(np.float32)
        snap = np.diff(snap, prepend=0) * np.exp(-t * (260 + 40 * k))
        knock = np.sin(2 * math.pi * (190 + 25 * k) * t) * np.exp(-t * 90)
        _CLICKS[k] = (snap * 0.35 + knock * 0.5).astype(np.float32) * (0.8 + 0.08 * k)
    return _CLICKS[k]


def ambient_pad(n, seed=0):
    """A very quiet, slow documentary drone under the voice (no copyright, made here). n = samples."""
    sec = n / SR
    t = np.arange(n, dtype=np.float32) / SR
    out = np.zeros(n, np.float32)
    for f, amp, ph in ((55.0, 0.5, 0.0), (82.41, 0.32, 1.3), (110.0, 0.28, 2.1), (164.81, 0.12, 0.7)):
        lfo = 0.6 + 0.4 * np.sin(2 * math.pi * t / (17 + f % 7) + ph)
        out += amp * lfo * np.sin(2 * math.pi * f * t + ph)
    rng = np.random.default_rng(seed)
    air = rng.normal(0, 1, n // 64 + 2).astype(np.float32)
    air = np.interp(np.arange(n) / 64.0, np.arange(len(air)), air).astype(np.float32)
    out += air * 0.05
    fade = np.minimum(1, np.minimum(t / 3, (sec - t) / 3))
    return out / (np.max(np.abs(out)) or 1) * fade


def impact_sound():
    """Deep 'boom' for pattern interrupts."""
    n = int(SR * 0.9)
    t = np.arange(n) / SR
    f = 38 + 60 * np.exp(-t * 9)
    body = np.sin(2 * math.pi * np.cumsum(f) / SR) * np.exp(-t * 4.5)
    rng = np.random.default_rng(7)
    crack = rng.normal(0, 1, n) * np.exp(-t * 40) * 0.5
    return ((body + crack) * 0.8).astype(np.float32)


def pop_sound():
    n = int(SR * 0.12)
    t = np.arange(n) / SR
    return (np.sin(2 * math.pi * (900 - 2500 * t) * t) * np.exp(-t * 30)).astype(np.float32) * 0.35


# ================================================================== music: a score that follows the story (made here, no copyright)

MOOD_WORDS = {
    "tense": r"\b(kill\w*|murder\w*|dead|death|blood|bod(y|ies)|corpse\w*|smother\w*|police|crime\w*|arrest\w*|chase\w*|attack\w*|war|weapon\w*|gun\w*|knife|fear\w*|danger\w*|hang\w*|execut\w*|threat\w*|escape\w*|caught|trap\w*|panic)\b",
    "mystery": r"\b(secret\w*|unknown|vanish\w*|disappear\w*|nobody knows|strange\w*|myster\w*|legend\w*|hidden|rumou?r\w*|question\w*|clue\w*|never found|missing|night|dark\w*|shadow\w*|whisper\w*)\b",
    "sad": r"\b(died|poor|lost|grief|alone|victim\w*|child\w*|famil\w*|tear\w*|mourn\w*|funeral|grave\w*|widow\w*|sick\w*|starv\w*|suffer\w*|broke|ruin\w*|forgot\w*|regret\w*)\b",
    "epic": r"\b(empire\w*|king\w*|queen\w*|gold|richest|power\w*|arm(y|ies)|conquer\w*|fortune\w*|million\w*|billion\w*|throne|built|rise|rose|legendary|greatest|world|crown\w*|palace\w*|dynast\w*|treasure\w*)\b",
    "hopeful": r"\b(law\w*|changed|finally|saved|free\w*|lesson\w*|today|remember\w*|hope\w*|better|reform\w*|justice|truth|learn\w*|future)\b",
}
MOODS = ("tense", "mystery", "sad", "epic", "hopeful")


def mood_of(text):
    t = (text or "").lower()
    scores = {m: len(re.findall(p, t)) for m, p in MOOD_WORDS.items()}
    scores["mystery"] += 0.5  # the channel's default colour
    return max(scores, key=lambda m: scores[m])


def _hz(m):
    return 440.0 * 2 ** ((m - 69) / 12)


_CH = {"Dm": [50, 53, 57], "Bb": [46, 50, 53], "Gm": [55, 58, 62], "A": [57, 61, 64], "F": [53, 57, 60], "C": [48, 52, 55],
       "Dm9": [50, 53, 57, 64], "Bbmaj7": [46, 50, 53, 57], "Am": [57, 60, 64], "Gm7": [55, 58, 62, 65], "Eb": [51, 55, 58]}
_MOODSPEC = {
    "tense":   {"prog": ["Dm", "Bb", "Gm", "A"], "bar": 4.0, "pad": 0.9, "sub": 0.55, "pulse": 0.75, "tick": 0.18, "trem": 0.22, "piano": 0.0, "str": 0.25, "drum": 0.0},
    "mystery": {"prog": ["Dm9", "Bbmaj7", "Gm7", "Dm"], "bar": 4.8, "pad": 0.85, "sub": 0.35, "pulse": 0.0, "tick": 0.14, "trem": 0.0, "piano": 0.55, "str": 0.0, "drum": 0.0, "box": 0.25},
    "sad":     {"prog": ["Dm", "Bb", "F", "C"], "bar": 5.0, "pad": 0.8, "sub": 0.25, "pulse": 0.0, "tick": 0.0, "trem": 0.0, "piano": 0.75, "str": 0.35, "drum": 0.0},
    "epic":    {"prog": ["Dm", "Bb", "F", "C"], "bar": 3.4, "pad": 0.7, "sub": 0.5, "pulse": 0.0, "tick": 0.0, "trem": 0.0, "piano": 0.0, "str": 0.8, "drum": 0.7},
    "hopeful": {"prog": ["F", "C", "Dm", "Bb"], "bar": 4.0, "pad": 0.75, "sub": 0.2, "pulse": 0.0, "tick": 0.0, "trem": 0.0, "piano": 0.7, "str": 0.3, "drum": 0.0},
}


def _env(n, att, rel):
    e = np.ones(n, np.float32)
    a, r = min(n, int(att * SR)), min(n, int(rel * SR))
    if a:
        e[:a] = np.linspace(0, 1, a, dtype=np.float32) ** 1.5
    if r:
        e[n - r:] *= np.linspace(1, 0, r, dtype=np.float32) ** 1.5
    return e


def _additive(freq, n, harms, detune=0.0, vib=0.0, seed=0):
    t = np.arange(n, dtype=np.float32) / SR
    out = np.zeros(n, np.float32)
    rng = np.random.default_rng(seed)
    vibr = 1 + vib * np.sin(2 * math.pi * 5.1 * t + rng.uniform(0, 6)) if vib else 1.0
    for h, amp in harms:
        for d in ((-detune, detune) if detune else (0.0,)):
            f = freq * h * (1 + d)
            if f > SR / 2.2:
                continue
            out += amp * np.sin(2 * math.pi * f * t * vibr + rng.uniform(0, 6.28)).astype(np.float32)
    return out


def _piano(freq, dur, vel=1.0, seed=0):
    n = int(SR * dur)
    t = np.arange(n, dtype=np.float32) / SR
    out = np.zeros(n, np.float32)
    rng = np.random.default_rng(seed)
    for h in range(1, 9):
        f = freq * h * (1 + 0.0004 * h * h)
        if f > SR / 2.2:
            break
        out += (h ** -1.15) * np.exp(-t * (1.1 + 0.9 * h)) * np.sin(2 * math.pi * f * t + rng.uniform(0, 6.28))
    a = int(SR * 0.004)
    out[:a] *= np.linspace(0, 1, a)
    return out * vel * 0.5


def _heartbeat(n, bpm, seed=0):
    out = np.zeros(n, np.float32)
    step = 60.0 / bpm
    m = int(SR * 0.35)
    tt = np.arange(m, dtype=np.float32) / SR
    thump = np.sin(2 * math.pi * np.cumsum(48 + 40 * np.exp(-tt * 30)) / SR) * np.exp(-tt * 13)
    k = 0.0
    while k < n / SR:
        for off, g in ((0.0, 1.0), (0.21, 0.7)):
            s = int((k + off) * SR)
            e = min(n, s + m)
            if s < n:
                out[s:e] += thump[:e - s] * g
        k += step
    return out


def _drum(n, bpm, seed=0):
    out = np.zeros(n, np.float32)
    step = 60.0 / bpm
    m = int(SR * 0.8)
    tt = np.arange(m, dtype=np.float32) / SR
    rng = np.random.default_rng(seed)
    hit = np.sin(2 * math.pi * np.cumsum(55 + 70 * np.exp(-tt * 18)) / SR) * np.exp(-tt * 5) + rng.normal(0, 1, m) * np.exp(-tt * 45) * 0.1
    beat = 0
    k = 0.0
    while k < n / SR:
        if beat % 4 in (0, 2) or (beat % 8 == 7):
            s = int(k * SR)
            e = min(n, s + m)
            out[s:e] += hit[:e - s] * (1.0 if beat % 4 == 0 else 0.7)
        k += step
        beat += 1
    return out


def _ticks(n, every=1.0):
    out = np.zeros(n, np.float32)
    m = int(SR * 0.025)
    tt = np.arange(m, dtype=np.float32) / SR
    tk = np.sin(2 * math.pi * 2100 * tt) * np.exp(-tt * 220)
    tc = np.sin(2 * math.pi * 1500 * tt) * np.exp(-tt * 200)
    k, i = 0.0, 0
    while k < n / SR:
        s = int(k * SR)
        e = min(n, s + m)
        out[s:e] += (tk if i % 2 == 0 else tc)[:e - s]
        k += every
        i += 1
    return out


def _reverb(x):
    out = x.copy()
    for d, g in ((0.031, 0.42), (0.047, 0.36), (0.071, 0.31), (0.103, 0.26), (0.149, 0.21), (0.211, 0.16), (0.293, 0.12), (0.401, 0.08), (0.557, 0.05)):
        k = int(d * SR)
        out[k:] += x[:-k] * g
    return out


_LOOPS = {}


def _mood_loop(mood, seed=0):
    key = (mood, seed)
    if key not in _LOOPS:
        _LOOPS[key] = _mood_loop_make(mood, seed)
    return _LOOPS[key]


def _mood_loop_make(mood, seed=0):
    """4 bars of one mood + a tail, so loops can be laid end to end smoothly."""
    sp = _MOODSPEC[mood]
    bar = sp["bar"]
    L = int(SR * bar * len(sp["prog"]))
    tail = int(SR * 3.0)
    out = np.zeros(L + tail, np.float32)
    rng = np.random.default_rng(seed + sum(map(ord, mood)))
    nb = int(SR * bar)
    pad_h = [(1, 1.0), (2, 0.42), (3, 0.24), (4, 0.13), (5, 0.08), (6, 0.05)]
    str_h = [(h, 1.0 / h) for h in range(1, 13)]
    for bi, ch in enumerate(sp["prog"]):
        notes = _CH[ch]
        s = bi * nb
        n = nb + int(SR * 2.2)  # overlaps into the next bar (smooth chord changes)
        env = _env(n, 1.1, 2.2)
        if sp["pad"]:
            pad = sum(_additive(_hz(m_), n, pad_h, detune=0.0025, seed=seed + bi * 7 + m_) for m_ in notes) / len(notes)
            out[s:s + n] += pad * env * sp["pad"] * 0.5
        if sp["sub"]:
            out[s:s + n] += _additive(_hz(notes[0] - 12), n, [(1, 1.0), (2, 0.2)], seed=seed + bi) * env * sp["sub"] * 0.35
        if sp["str"]:
            se = env * np.linspace(0.55, 1.0, n, dtype=np.float32)  # each chord swells
            strg = sum(_additive(_hz(m_ + 12), n, str_h, detune=0.003, vib=0.0025, seed=seed + bi * 11 + m_) for m_ in notes) / len(notes)
            out[s:s + n] += strg * se * sp["str"] * 0.12
        if sp.get("piano"):
            # broken chord, a little different every bar
            pattern = [0, 1, 2, 1] if mood != "hopeful" else [0, 2, 1, 2]
            step = bar / (4 if mood == "sad" else 6)
            k = 0
            tt = 0.0
            while tt < bar - 0.05:
                if mood == "sad" and k % 4 == 3 and rng.random() < 0.5:
                    tt += step
                    k += 1
                    continue
                m_ = notes[pattern[k % len(pattern)] % len(notes)] + 12 + (12 if (mood == "hopeful" and k % 5 == 4) else 0)
                note = _piano(_hz(m_), 3.0, vel=rng.uniform(0.6, 1.0), seed=seed + bi * 31 + k)
                p0 = s + int(tt * SR)
                p1 = min(len(out), p0 + len(note))
                out[p0:p1] += note[:p1 - p0] * sp["piano"] * 0.55
                tt += step
                k += 1
        if sp.get("box") and rng.random() < 0.7:  # music-box notes, high and far away
            for j in range(2):
                m_ = notes[rng.integers(0, len(notes))] + 24
                note = _piano(_hz(m_), 2.5, vel=0.5, seed=seed + bi * 53 + j)
                p0 = s + int(SR * (rng.uniform(0.3, bar - 0.5)))
                p1 = min(len(out), p0 + len(note))
                out[p0:p1] += note[:p1 - p0] * sp["box"] * 0.5
        if sp["trem"]:
            tn = n
            tr = _additive(_hz(notes[-1] + 12), tn, [(1, 1.0), (2, 0.3), (3, 0.15)], seed=seed + bi) * (0.5 + 0.5 * np.sin(2 * math.pi * 7.5 * np.arange(tn) / SR))
            out[s:s + tn] += tr.astype(np.float32) * env * sp["trem"] * 0.18
    full = len(out)
    if sp["pulse"]:
        out += _heartbeat(full, 62, seed) * sp["pulse"] * 0.6
    if sp["drum"]:
        out += _drum(full, 72, seed) * sp["drum"] * 0.45
    if sp["tick"]:
        out += _ticks(full, 1.0) * sp["tick"] * 0.5
    out = _reverb(out)
    r = np.sqrt(np.mean(out[:L] ** 2)) or 1
    return out / r * 0.1, L


def _user_tracks(mood):
    """Your own music: music/<mood>/*.mp3 (or any file in music/ for every mood)."""
    d = A("music", mood)
    files = []
    if os.path.isdir(d):
        files = [os.path.join(d, f) for f in sorted(os.listdir(d)) if f.lower().endswith((".mp3", ".wav", ".m4a", ".ogg"))]
    if not files and os.path.isdir(A("music")):
        files = [A("music", f) for f in sorted(os.listdir(A("music"))) if f.lower().endswith((".mp3", ".wav", ".m4a", ".ogg"))]
    return files


_UCACHE = {}


def _fill(mood, n, seed, use_files=True):
    """n samples of one mood, from your files if there are any, otherwise made here."""
    files = _user_tracks(mood) if use_files else []
    if files:
        f = files[seed % len(files)]
        if f not in _UCACHE:
            try:
                a = decode_audio(f)
                r = np.sqrt(np.mean(a ** 2)) or 1
                _UCACHE[f] = (a / r * 0.1).astype(np.float32)
            except Exception:
                _UCACHE[f] = None
        a = _UCACHE[f]
        if a is not None and len(a) > SR * 5:
            reps = int(np.ceil(n / len(a))) + 1
            return np.tile(a, reps)[:n]
    out = np.zeros(n + int(SR * 3.5), np.float32)
    pos, v = 0, 0
    while pos < n:
        loop, L = _mood_loop(mood, (seed % 2) * 2 + v)
        e = min(len(out), pos + len(loop))
        out[pos:e] += loop[:e - pos]
        pos += L
        v = (v + 1) % 2  # two variations, alternating
    return out[:n]


def make_score(pl, script, speech):
    """Music under the narration: changes mood with each chapter, builds up before every 'hit', ducks under the voice."""
    n = len(speech)
    beats = pl["beats"]
    scenes = script["scenes"]
    # one mood per chapter (from the script's "mood", or guessed from the words)
    segs = []
    cur_ch, start, text, forced = None, 0.0, "", None
    for si, sc in enumerate(scenes):
        b = next((x for x in beats if x["scene"] == si), None)
        if b is None:
            continue
        ch = b["chapter"]
        if ch != cur_ch and si > 0:
            segs.append([start, b["start"], forced or mood_of(text)])
            start, text, forced = b["start"], "", None
        cur_ch = ch
        text += " " + (sc.get("say") or "")
        if sc.get("mood") in MOODS:
            forced = forced or sc["mood"]
    segs.append([start, n / SR, forced or mood_of(text)])
    # merge neighbours with the same mood
    merged = []
    for s_ in segs:
        if merged and merged[-1][2] == s_[2]:
            merged[-1][1] = s_[1]
        else:
            merged.append(s_)
    music = np.zeros(n, np.float32)
    xf = int(SR * 3.0)
    for i, (a, b, mood) in enumerate(merged):
        s0 = max(0, int(a * SR) - (xf if i else 0))
        s1 = min(n, int(b * SR) + xf)
        seg = _fill(mood, s1 - s0, i * 3)
        g = np.ones(s1 - s0, np.float32)
        if i:
            g[:xf] = np.sin(np.linspace(0, math.pi / 2, xf)) ** 2
        if i < len(merged) - 1 and s1 - s0 > xf:
            g[-xf:] = np.cos(np.linspace(0, math.pi / 2, xf)) ** 2
        music[s0:s1] += seg * g
    # build-ups before the pattern interrupts, and a short silence right before the hit
    rng = np.random.default_rng(5)
    for b in beats:
        if not b.get("hit"):
            continue
        th = int(b["start"] * SR)
        rl = int(SR * 2.0)
        r0 = max(0, th - rl - int(SR * 0.1))
        m_ = th - int(SR * 0.1) - r0
        if m_ <= 0:
            continue
        tt = np.arange(m_, dtype=np.float32) / SR
        env = (tt / max(tt[-1], 0.01)) ** 2.2
        noise = rng.normal(0, 1, m_).astype(np.float32)
        noise = np.convolve(noise, np.ones(6, np.float32) / 6, mode="same")
        sweep = np.sin(2 * math.pi * np.cumsum(220 + 900 * env) / SR).astype(np.float32)
        music[r0:r0 + m_] += (noise * 0.6 + sweep * 0.35) * env * 0.16
        d0, d1 = max(0, th - int(SR * 0.12)), min(n, th + int(SR * 0.6))
        duck = np.ones(d1 - d0, np.float32) * 0.15
        att = min(len(duck), int(SR * 0.05))
        duck[:att] = np.linspace(1, 0.15, att)  # no click
        rel = min(len(duck) - att, int(SR * 0.45))
        if rel > 0:
            duck[-rel:] = np.linspace(0.15, 1, rel)
        music[d0:d1] *= duck
    # duck under the voice
    w = int(SR * 0.25)
    env = np.convolve(np.abs(speech), np.ones(w, np.float32) / w, mode="same")
    talk = np.clip(env / 0.04, 0, 1)
    music *= (1 - 0.5 * talk)
    # level: about 17 dB below the voice
    voiced = speech[env > 0.02]
    vr = np.sqrt(np.mean(voiced ** 2)) if len(voiced) else 0.12
    mr = np.sqrt(np.mean(music ** 2)) or 1
    vol = float(script.get("music_volume", 1.0))
    music *= (vr * 10 ** (-17 / 20)) / mr * vol
    fade = int(SR * 2.5)
    music[:fade] *= np.linspace(0, 1, fade)
    music[-fade:] *= np.linspace(1, 0, fade)
    return music, [(round(a, 1), round(b, 1), m) for a, b, m in merged]


def coin_sound():
    n = int(SR * 0.5)
    t = np.arange(n, dtype=np.float32) / SR
    out = sum(a * np.sin(2 * math.pi * f * t) * np.exp(-t * d) for f, a, d in ((2093, 0.5, 9), (2794, 0.35, 11), (4186, 0.25, 15), (5274, 0.15, 20)))
    return out.astype(np.float32) * 0.35


def bell_sound():
    n = int(SR * 1.6)
    t = np.arange(n, dtype=np.float32) / SR
    out = sum(a * np.sin(2 * math.pi * f * t) * np.exp(-t * d) for f, a, d in ((110, 0.6, 2.2), (220.5, 0.35, 3.0), (331, 0.2, 4.0), (587, 0.1, 6.0)))
    return out.astype(np.float32) * 0.4


# ================================================================== the build: voice -> timings -> beats

QUIET_TYPES = ("stat", "year", "bars", "timeline", "quote", "text", "title", "count", "date", "type", "casefile")
NUM_RE = re.compile(r"(\$\s?\d[\d,]*(?:\.\d+)?(?:\s(?:thousand|million|billion|trillion))?|\b\d[\d,]*(?:\.\d+)?(?:\s(?:thousand|million|billion|trillion))?(?:\s(?:people|camels|ships|kilometres|km|miles|pounds|years|dirhams|soldiers|men|days|months|percent|tons|tonnes|coins|bars))?)", re.I)


def split_sentences(text):
    parts = re.split(r"(?<=[.!?])\s+(?=[A-Z\"'“0-9$])", (text or "").strip())
    return [p.strip() for p in parts if p.strip()]


def word_times(sentence, start, end):
    words = sentence.split()
    w = [len(x) + 1.5 for x in words]
    total = sum(w) or 1
    out, t = [], start
    for word, ww in zip(words, w):
        d = (end - start) * ww / total
        out.append([round(t, 3), round(t + d, 3), word])
        t += d
    return out


def group_lines(words, max_chars=30, max_words=6):
    """Caption lines from timed words."""
    lines, cur = [], []
    for w in words:
        cur.append(w)
        txt = " ".join(x[2] for x in cur)
        if len(txt) >= max_chars or len(cur) >= max_words or (re.search(r"[,;:.!?]$", w[2]) and len(cur) >= 3):
            lines.append(cur)
            cur = []
    if cur:
        if lines and len(cur) <= 2 and len(" ".join(x[2] for x in lines[-1] + cur)) < max_chars + 10:
            lines[-1] += cur
        else:
            lines.append(cur)
    return lines


def plan(script):
    """Voice for every sentence, exact timings, beats (a new visual every few seconds) and floating callouts."""
    voice = Voice(script)
    gap, tail, lead = 0.25, 0.45, 0.3
    if script.get("_own_voice"):
        texts = [x for sc in script["scenes"] for x in split_sentences(sc.get("say", ""))]
        log(f"  using YOUR recording: {os.path.basename(script['_own_voice'])}")
        rec = decode_audio(script["_own_voice"])
        pk = float(np.max(np.abs(rec))) if len(rec) else 0
        if pk > 0:
            rec = rec * (0.89 / pk)
        voice.clips = split_own_voice(rec, texts)
        voice.kind = "own"
        gap = 0.18
    beats, sentences, words, pops, audio, scene_starts = [], [], [], [], [], []
    t = 0.0
    chapter, date = "", ""
    n = len(script["scenes"])
    for si, sc in enumerate(script["scenes"]):
        log(f"  voice {si + 1}/{n}")
        sents = split_sentences(sc.get("say", ""))
        parts = [np.zeros(int(SR * lead), np.float32)]
        st = t + lead
        sw = []
        for s in sents:
            a = voice.say(s)
            d = len(a) / SR
            wt = word_times(s, st, st + d)
            sentences.append({"scene": si, "start": round(st, 3), "end": round(st + d, 3), "text": s})
            sw += wt
            g_ = gap
            if str(script.get("voice", "")).startswith("saim"):  # a storyteller breathes: longer after questions and "..."
                g_ = 0.62 if s.rstrip().endswith(("?", "...", "…", "!")) else 0.36
            parts += [a, np.zeros(int(SR * g_), np.float32)]
            st += d + g_
        speech = np.concatenate(parts)
        dur = max(len(speech) / SR + tail, float(sc.get("min_seconds", 2.5)))
        speech = np.concatenate([speech, np.zeros(max(0, int(round(SR * dur)) - len(speech)), np.float32)])[:int(round(SR * dur))]
        dur = len(speech) / SR
        audio.append(speech)
        words += sw
        scene_starts.append(t)
        chapter = sc.get("chapter", chapter)
        date = sc.get("date", date)
        vis = sc.get("visuals") or [sc.get("visual") or {"type": "title", "text": ""}]
        # beat cuts land on word boundaries, spread evenly over the scene
        m = len(vis)
        cuts = [t]
        if m > 1:
            cands = [w[0] for w in sw[1:]] or [t + dur * k / m for k in range(1, m)]
            for k in range(1, m):
                target = t + dur * k / m
                c = min(cands, key=lambda x: abs(x - target))
                c = max(c, cuts[-1] + 1.2)
                cuts.append(c)
        cuts.append(t + dur)
        bdate = date
        for j, v in enumerate(vis):
            bdate = str(v.get("date", bdate))
            b0, b1 = cuts[j], cuts[j + 1]
            if b1 - b0 < 0.6:
                continue
            beats.append({"i": len(beats), "scene": si, "start": round(b0, 3), "dur": round(b1 - b0, 3), "visual": v,
                          "chapter": chapter, "date": bdate, "new_scene": j == 0})
        date = bdate
        # floating callouts: from the script ("pops"), or automatically when a number is spoken
        for p in sc.get("pops") or []:
            key = (p.get("on") or p.get("text") or "").lower().split()
            at = None
            if key:
                for k in range(len(sw)):
                    seq = [re.sub(r"[^\w$]", "", x[2].lower()) for x in sw[k:k + len(key)]]
                    if seq == [re.sub(r"[^\w$]", "", x) for x in key]:
                        at = sw[k][0]
                        break
            if at is None:
                at = t + float(p.get("at", 0.5))
            pops.append({"t": at, "text": p.get("text", ""), "label": p.get("label", ""), "script": True,
                         "kind": pop_kind(p.get("text", ""), p.get("label", ""), p.get("kind"))})
        if sc.get("auto_pops", True):
            for snt in [x for x in sentences if x["scene"] == si]:
                for m_ in NUM_RE.finditer(snt["text"]):
                    tok = m_.group(0).strip().rstrip(",.;:!?")
                    if re.fullmatch(r"1\d{3}|20\d{2}", tok) or len(re.sub(r"\D", "", tok)) < 2:
                        continue  # years are on the clock already
                    first = tok.split()[0]
                    hit = next((w for w in sw if w[0] >= snt["start"] - 0.01 and re.sub(r"[^\w$]", "", w[2]) == re.sub(r"[^\w$]", "", first)), None)
                    if hit:
                        after = snt["text"][m_.end():m_.end() + 40]
                        pops.append({"t": hit[0], "text": tok.upper(), "label": "", "script": False, "kind": pop_kind(tok + " " + after)})
        t += dur
    total = t
    # no shot longer than MAX_SHOT: long picture shots get a second, closer framing (if that picture may still be used),
    # long clips jump to a later moment of the same clip
    uses = {}
    for b in beats:
        f_ = b["visual"].get("file")
        if b["visual"].get("type") == "image" and f_:
            uses[f_] = uses.get(f_, 0) + 1
    out_b = []
    for b in beats:
        v = b["visual"]
        n_ = math.ceil(b["dur"] / (MAX_SHOT + 0.3))
        if n_ <= 1 or v.get("type") not in ("image", "video"):
            out_b.append(b)
            continue
        if v.get("type") == "image" and (not v.get("file") or uses.get(v["file"], 0) >= MAX_USES):
            out_b.append(b)
            continue
        n_ = min(n_, 2) if v.get("type") == "image" else min(n_, 3)
        part = b["dur"] / n_
        for j in range(n_):
            nb = dict(b)
            nb["start"] = round(b["start"] + j * part, 3)
            nb["dur"] = round(part, 3)
            if j:
                nv = dict(v)
                if v["type"] == "image":
                    nv["recut"] = int(v.get("recut") or 0) + 1
                    nv.pop("caption", None)
                    uses[v["file"]] = uses.get(v["file"], 0) + 1
                else:
                    nv["clip_off"] = round(float(v.get("clip_off") or 0) + j * (part + 1.0), 2)
                nb["visual"] = nv
                nb["new_scene"] = False
            out_b.append(nb)
    beats = out_b
    for i_, b in enumerate(beats):
        b["i"] = i_
    last_hit = -99
    for b in beats:
        v = b["visual"]
        if v.get("hit") is True or (v.get("hit") is not False and v.get("type") in ("text", "stat", "title", "year") and b["start"] - last_hit > 75 and b["start"] > 8):
            b["hit"] = True
            last_hit = b["start"]
    # tidy callouts: one at a time, 1.8-3.4 s each, never on number/text slides
    pops.sort(key=lambda p: p["t"])
    out, last_end = [], -1
    for p in pops:
        b = next((x for x in beats if x["start"] <= p["t"] < x["start"] + x["dur"]), None)
        if not b or b["visual"].get("type") in (QUIET_TYPES if not p["script"] else ("stat", "year", "title", "text", "quote")):
            continue
        if p["t"] < last_end + (0.3 if p["script"] else 14):  # numbers spoken aloud get a card only now and then
            continue
        end = min(p["t"] + 3.4, b["start"] + b["dur"] - 0.2)
        if end - p["t"] < 1.4:
            continue
        p["end"] = end
        p["side"] = len(out) % 2
        fs = b["visual"].get("faces") if b["visual"].get("type") == "image" else None
        if fs:  # never cover a face: put the card on the other side
            fxc = sum((f_[0] + f_[2]) / 2 for f_ in fs) / len(fs)
            p["side"] = 0 if fxc < 0.5 else 1
        out.append(p)
        last_end = end
    pops = out
    track = np.concatenate(audio)
    speech = track.copy()
    # "Like + Subscribe" animation (3 s) in the middle of the long video, on a calm photo, away from cards and Shorts
    sub_at = None
    total_ = len(track) / SR
    if script.get("subscribe_anim", True) and total_ > 90:
        busy = set()
        for sh in script.get("shorts") or []:
            try:
                busy.update(range(int(sh.get("from_scene", -1)), int(sh.get("to_scene", -2)) + 1))
            except Exception:
                pass
        best = None
        for b in beats:
            st = b["start"]
            if b.get("hit") or b["visual"].get("type") not in ("image", "map", "video") or b["scene"] in busy:
                continue
            if not (0.35 * total_ < st < 0.68 * total_) or b["dur"] < 1.5:
                continue
            if any(p_["t"] < st + 3.8 and p_["end"] > st - 0.3 for p_ in pops):
                continue
            sc_ = abs(st - 0.5 * total_)
            if best is None or sc_ < best[0]:
                best = (sc_, st + 0.4)
        if best is None:
            for b in beats:
                if not b.get("hit") and 0.4 * total_ < b["start"] < 0.6 * total_:
                    best = (0, b["start"] + 0.4)
                    break
        if best:
            sub_at = round(best[1], 3)
            pops = [p_ for p_ in pops if not (p_["t"] < sub_at + 3.4 and p_["end"] > sub_at)]
    # sound design
    for b in beats:
        if b["new_scene"] and b["start"] > 0.5:
            k = int(b["start"] * SR) - int(SR * 0.35)
            w = whoosh(0.7, b["i"]) * 0.2
            if 0 <= k < len(track) - len(w):
                track[k:k + len(w)] += w
        if b["visual"].get("type") == "year":
            v = b["visual"]
            y0, y1 = int(v.get("from", 0)), int(v.get("to", 0))
            steps = min(abs(y1 - y0), 40)
            span = max(1.0, min(3.0, b["dur"] * 0.55))
            for j in range(steps):
                k = int((b["start"] + 0.3 + span * j / max(1, steps)) * SR)
                tk = tick() * 0.22
                if k + len(tk) < len(track):
                    track[k:k + len(tk)] += tk
    for b in beats:  # typewriter clicks for typed words, date cards and case files, and a thump for the case-file stamp
        v = b["visual"]
        typ = v.get("type")
        if typ in ("date", "type"):
            txt = str(v.get("text") or "")
            cps = max(10.0, len(txt) / max(0.6, min(1.3, b["dur"] * 0.4)))
            for j in range(len(txt)):
                if txt[j] == " ":
                    continue
                k = int((b["start"] + 0.15 + j / cps) * SR)
                tk = type_click(j * 7) * 0.5
                if k + len(tk) < len(track):
                    track[k:k + len(tk)] += tk
        elif typ == "casefile":
            fields = [x for x in (v.get("fields") or []) if isinstance(x, (list, tuple)) and len(x) >= 2][:6]
            per = max(0.35, (b["dur"] - 1.6) / max(1, len(fields)))
            for i_, (_, val) in enumerate(fields):
                n_ = min(len(str(val)), 26)
                for j in range(n_):
                    k = int((b["start"] + 0.55 + i_ * per + j * per * 0.7 / max(1, len(str(val)))) * SR)
                    tk = type_click(j * 3 + i_) * 0.42
                    if k + len(tk) < len(track):
                        track[k:k + len(tk)] += tk
            if v.get("stamp"):
                k = int((b["start"] + 0.55 + len(fields) * per) * SR)
                im = impact_sound() * 0.45
                if k + len(im) < len(track):
                    track[k:k + len(im)] += im
    for b in beats:
        if b.get("hit"):
            k = int(b["start"] * SR)
            im = impact_sound() * 0.55
            if k + len(im) < len(track):
                track[k:k + len(im)] += im
    for p in pops:
        k = int(p["t"] * SR)
        ps = {"money": coin_sound, "death": bell_sound}.get(p.get("kind"), pop_sound)()
        if p.get("kind") == "death":
            ps = ps * 0.6
        if k + len(ps) < len(track):
            track[k:k + len(ps)] += ps
    if sub_at is not None:
        for off, snd, vol in ((0.0, whoosh(0.5, 77), 0.18), (1.0, pop_sound(), 0.9), (2.0, pop_sound(), 0.9), (2.35, bell_sound(), 0.35)):
            if callable(snd):
                snd = snd()
            k = int((sub_at + off) * SR)
            if k + len(snd) < len(track):
                track[k:k + len(snd)] += snd * vol
    peak = np.max(np.abs(track)) or 1
    track = track / peak * 0.9
    speech = speech / peak * 0.9
    moods = []
    if script.get("music", script.get("ambient", True)) is not False:
        try:
            music, moods = make_score({"beats": beats}, script, speech)
            track = track + music
            log("   music: " + ", ".join(f"{fmt_ts(a)} {m}" for a, b, m in moods))
        except Exception as e:
            log(f"   (music skipped: {str(e)[:80]})")
            track += ambient_pad(len(track)) * 0.035
    pk = np.max(np.abs(track))
    if pk > 0.98:
        track = track / pk * 0.98
    lines = []
    for snt in sentences:
        ws = [w for w in words if snt["start"] - 0.01 <= w[0] < snt["end"] + 0.01]
        for ln in group_lines(ws):
            lines.append({"start": ln[0][0], "end": ln[-1][1], "words": ln})
    return {"beats": beats, "sentences": sentences, "words": words, "lines": lines, "pops": pops, "total": total,
            "scene_starts": scene_starts, "voice": voice.kind, "moods": moods, "sub_at": sub_at}, track


# ------------------------------------------------------------------ ambience: gold dust, light leak

_DUST = {}


def dust(img, t, strength=1.0, seed=3):
    W, H = img.size
    key = (W, H, seed)
    if key not in _DUST:
        rng = np.random.default_rng(seed)
        n = 70
        _DUST[key] = np.stack([rng.uniform(0, W, n), rng.uniform(0, H, n), rng.uniform(-8, 8, n) * W / 1920, rng.uniform(6, 22, n) * W / 1920,
                               rng.uniform(0.8, 3.2, n) * W / 1920, rng.uniform(0, 6.28, n), rng.uniform(0.4, 1.2, n)], 1)
    ov = Image.new("RGBA", img.size, (0, 0, 0, 0))
    d = ImageDraw.Draw(ov)
    for x0, y0, vx, vy, r, ph, sp in _DUST[key]:
        x = (x0 + vx * t + 14 * math.sin(t * 0.4 * sp + ph)) % W
        y = (y0 - vy * t) % H
        a = int(255 * strength * (0.25 + 0.35 * (1 + math.sin(t * 1.7 * sp + ph))))
        d.ellipse([x - r, y - r, x + r, y + r], fill=((236, 246, 255) if THEME["name"] == "nature" else (255, 214, 140)) + (max(0, min(255, a)),))
    img.paste(ov, (0, 0), ov)
    return img


_LEAK = {}


def light_leak(img, t, seed=0):
    W, H = img.size
    key = (W, H, THEME["name"])
    if key not in _LEAK:
        s = int(H * 1.1)
        y, x = np.mgrid[0:s, 0:s].astype(np.float32)
        r = np.sqrt((x - s / 2) ** 2 + (y - s / 2) ** 2) / (s / 2)
        m = np.clip(1 - r, 0, 1) ** 2.2
        g = np.stack([m * 14, m * 44, m * 72], -1) if THEME["name"] == "nature" else np.stack([m * 70, m * 42, m * 14], -1)
        _LEAK[key] = Image.fromarray(g.astype(np.uint8))
    from PIL import ImageChops
    lk = _LEAK[key]
    s = lk.size[0]
    cx = W * (0.5 + 0.42 * math.sin(t * 0.13 + seed))
    cy = H * (0.35 + 0.2 * math.sin(t * 0.09 + seed * 2))
    box = (int(cx - s / 2), int(cy - s / 2))
    x0, y0 = max(0, box[0]), max(0, box[1])
    x1, y1 = min(W, box[0] + s), min(H, box[1] + s)
    if x1 <= x0 or y1 <= y0:
        return img
    reg = img.crop((x0, y0, x1, y1))
    part = lk.crop((x0 - box[0], y0 - box[1], x1 - box[0], y1 - box[1]))
    img.paste(ImageChops.add(reg, part), (x0, y0))
    return img


# ------------------------------------------------------------------ overlay: year clock, chapter, callouts, captions, progress

def draw_clock(d, cx, cy, r, ang, col):
    d.ellipse([cx - r, cy - r, cx + r, cy + r], outline=col, width=max(2, int(r / 6)))
    d.line([(cx, cy), (cx + r * 0.55 * math.sin(ang / 12), cy - r * 0.55 * math.cos(ang / 12))], fill=col, width=max(2, int(r / 6)))
    d.line([(cx, cy), (cx + r * 0.8 * math.sin(ang), cy - r * 0.8 * math.cos(ang))], fill=col, width=max(2, int(r / 9)))


def draw_caption(img, t, lines, W, H, y, size, box=True, max_w=None):
    """Caption with the word being spoken in gold."""
    ln = next((x for x in lines if x["start"] - 0.05 <= t < x["end"] + 0.15), None)
    if not ln:
        return
    d = ImageDraw.Draw(img, "RGBA")
    f = font("Inter", size, "ExtraBold")
    ws = [w[2] for w in ln["words"]]
    sp = d.textlength(" ", font=f)
    widths = [d.textlength(w, font=f) for w in ws]
    rows, cur, cw = [], [], 0
    lim = max_w or W * 0.86
    for i, wd in enumerate(widths):
        if cur and cw + sp + wd > lim:
            rows.append(cur)
            cur, cw = [], 0
        cur.append(i)
        cw += (sp if len(cur) > 1 else 0) + wd
    rows.append(cur)
    lh = size * 1.22
    top = y - lh * len(rows) / 2
    if box:
        mw = max(sum(widths[i] for i in r) + sp * (len(r) - 1) for r in rows)
        pad = size * 0.4
        d.rounded_rectangle([W / 2 - mw / 2 - pad, top - pad * 0.6, W / 2 + mw / 2 + pad, top + lh * len(rows) + pad * 0.3], radius=int(size * 0.25), fill=(0, 0, 0, 160))
    for r_i, r in enumerate(rows):
        rw = sum(widths[i] for i in r) + sp * (len(r) - 1)
        x = W / 2 - rw / 2
        yy = top + r_i * lh
        for i in r:
            w = ln["words"][i]
            on = w[0] <= t < w[1] + 0.05
            col = GOLD_L if on else WHITE
            d.text((x, yy), ws[i], font=f, fill=col + (255,), stroke_width=max(2, size // 12), stroke_fill=(0, 0, 0, 255))
            x += widths[i] + sp


POP_COLORS = {"money": (232, 178, 58), "death": (206, 52, 42), "law": (122, 152, 205), "people": (226, 216, 196), "place": (64, 168, 186),
              "date": (232, 148, 58), "person": (226, 216, 196), "fact": (232, 178, 58)}


def pop_kind(text, label="", given=None):
    """What a floating callout is about, so it gets the right colour, icon and sound."""
    if given in POP_COLORS:
        return given
    t = f"{text} {label}".lower()
    if re.search(r"[$£€]|\b(pounds?|dollars?|shillings?|gold|coins?|million|billion|fortune|price|paid|rich\w*|wealth|cash|money|worth|salary|wage\w*)\b", t):
        return "money"
    if re.search(r"\b(kill\w*|murder\w*|dead|death|died|victims?|bod(y|ies)|hang\w*|execut\w*|corpse\w*|poison\w*|blood|lives lost)\b", t):
        return "death"
    if re.search(r"\b(laws?|act|court|trial|verdict|guilty|sentence\w*|police|arrest\w*|prison|jail|judge|banned)\b", t):
        return "law"
    if re.search(r"\b(people|men|women|students|soldiers|crowd|workers|children|lives|passengers|slaves|citizens)\b", t):
        return "people"
    if re.search(r"\b(street|square|close|city|town|village|cave|castle|river|island|school|house|hall|palace|port|road|harbou?r|mine|kingdom|empire)\b", t):
        return "place"
    if re.search(r"\b(1[0-9]{3}|20[0-9]{2})\b|\b(january|february|march|april|may|june|july|august|september|october|november|december|halloween|christmas)\b", t):
        return "date"
    words = re.findall(r"[A-Za-z'’.]+", text)
    if 1 < len(words) <= 4 and not re.search(r"\d", text):
        return "person"
    return "fact"


_ICONS = {}


def pop_icon(kind, size, text=""):
    """Small round icon for a callout, drawn here (cached)."""
    sym = "£" if "£" in text else ("€" if "€" in text else "$")
    key = (kind, size, sym)
    if key in _ICONS:
        return _ICONS[key]
    S = size * 4
    im = Image.new("RGBA", (S, S), (0, 0, 0, 0))
    d = ImageDraw.Draw(im)
    col = POP_COLORS.get(kind, GOLD)
    dark = (18, 14, 10, 255)
    d.ellipse([0, 0, S - 1, S - 1], fill=col + (255,))
    d.ellipse([S * 0.06, S * 0.06, S * 0.94, S * 0.94], outline=(255, 255, 255, 70), width=max(2, S // 40))
    c = S / 2
    if kind == "money":
        d.ellipse([S * 0.2, S * 0.2, S * 0.8, S * 0.8], outline=dark, width=S // 18)
        d.text((c, c + S * 0.02), sym, font=font("Oswald", int(S * 0.42), "Bold"), fill=dark, anchor="mm")
    elif kind == "death":
        w = (255, 246, 236, 255)
        d.ellipse([S * 0.27, S * 0.2, S * 0.73, S * 0.62], fill=w)
        d.rounded_rectangle([S * 0.36, S * 0.52, S * 0.64, S * 0.76], radius=S // 20, fill=w)
        for ex in (0.4, 0.6):
            d.ellipse([S * (ex - 0.075), S * 0.36, S * (ex + 0.075), S * 0.5], fill=col + (255,))
        d.polygon([(c, S * 0.52), (c - S * 0.035, S * 0.59), (c + S * 0.035, S * 0.59)], fill=col + (255,))
        for tx in (0.43, 0.5, 0.57):
            d.line([(S * tx, S * 0.66), (S * tx, S * 0.76)], fill=col + (255,), width=max(2, S // 50))
    elif kind == "law":
        d.line([(c, S * 0.22), (c, S * 0.74)], fill=dark, width=S // 22)
        d.line([(S * 0.24, S * 0.32), (S * 0.76, S * 0.32)], fill=dark, width=S // 22)
        d.rectangle([S * 0.38, S * 0.72, S * 0.62, S * 0.78], fill=dark)
        for px in (0.27, 0.73):
            d.line([(S * px, S * 0.32), (S * (px - 0.08), S * 0.52)], fill=dark, width=S // 40)
            d.line([(S * px, S * 0.32), (S * (px + 0.08), S * 0.52)], fill=dark, width=S // 40)
            d.chord([S * (px - 0.11), S * 0.44, S * (px + 0.11), S * 0.6], 0, 180, fill=dark)
    elif kind in ("people", "person"):
        heads = [(0.5, 1.0)] if kind == "person" else [(0.3, 0.72), (0.7, 0.72), (0.5, 0.92)]
        for hx, sc_ in heads:
            r = S * 0.12 * sc_
            hy = S * (0.4 if kind == "person" else 0.42)
            d.ellipse([S * hx - r, hy - r, S * hx + r, hy + r], fill=dark)
            d.chord([S * hx - r * 2.0, hy + r * 1.1, S * hx + r * 2.0, hy + r * 4.6], 180, 360, fill=dark)
    elif kind == "place":
        d.ellipse([S * 0.3, S * 0.18, S * 0.7, S * 0.58], fill=dark)
        d.polygon([(S * 0.32, S * 0.44), (S * 0.68, S * 0.44), (c, S * 0.82)], fill=dark)
        d.ellipse([S * 0.42, S * 0.3, S * 0.58, S * 0.46], fill=col + (255,))
    elif kind == "date":
        d.rounded_rectangle([S * 0.25, S * 0.28, S * 0.75, S * 0.74], radius=S // 25, outline=dark, width=S // 22)
        d.rectangle([S * 0.25, S * 0.28, S * 0.75, S * 0.4], fill=dark)
        for rx in (0.36, 0.64):
            d.line([(S * rx, S * 0.2), (S * rx, S * 0.33)], fill=dark, width=S // 22)
        for gx in (0.36, 0.5, 0.64):
            for gy in (0.5, 0.62):
                d.rectangle([S * gx - S * 0.03, S * gy - S * 0.03, S * gx + S * 0.03, S * gy + S * 0.03], fill=dark)
    else:
        d.text((c, c), "!", font=font("Oswald", int(S * 0.55), "Bold"), fill=dark, anchor="mm")
    im = im.resize((size, size), Image.LANCZOS)
    _ICONS[key] = im
    return im


def draw_pop(img, t, p, W, H):
    s = W / 1920
    a_in = ease_out((t - p["t"]) / 0.35)
    a_out = 1 - ease((t - (p["end"] - 0.3)) / 0.3)
    a = max(0.0, min(a_in, a_out))
    if a <= 0:
        return
    kind = p.get("kind") or "fact"
    col = POP_COLORS.get(kind, GOLD)
    f = font("Oswald", int(62 * s), "Bold")
    fl = font("Oswald", int(25 * s), "Medium")
    d = ImageDraw.Draw(img, "RGBA")
    text = p["text"]
    tw_ = d.textlength(text, font=f)
    lw = d.textlength(p.get("label", "").upper(), font=fl) if p.get("label") else 0
    ic = int(74 * s)
    pad = int(26 * s)
    w = ic + pad * 3 + max(tw_, lw)
    h = int((126 if p.get("label") else 104) * s)
    bob = math.sin((t - p["t"]) * 2.2) * 5 * s
    slide = (1 - a_in) * 80 * s
    if p["side"] == 0:
        x1 = W - int(70 * s) + slide
        x0 = x1 - w
    else:
        x0 = int(70 * s) - slide
        x1 = x0 + w
    y0 = int(150 * s) + bob
    # glass card with a coloured edge
    d.rounded_rectangle([x0 + int(6 * s), y0 + int(8 * s), x1 + int(6 * s), y0 + h + int(8 * s)], radius=int(18 * s), fill=(0, 0, 0, int(90 * a)))
    d.rounded_rectangle([x0, y0, x1, y0 + h], radius=int(18 * s), fill=(12, 10, 9, int(215 * a)), outline=col + (int(235 * a),), width=max(2, int(3 * s)))
    d.rectangle([x0 + pad + ic + pad, y0 + h - int(15 * s), x0 + pad + ic + pad + max(tw_, lw) * ease_out((t - p["t"] - 0.1) / 0.8), y0 + h - int(10 * s)], fill=col + (int(255 * a),))
    # icon pops in with a little bounce
    k = (t - p["t"]) / 0.4
    sc_ = 0 if k <= 0 else (1.18 * ease_out(min(1, k / 0.6)) if k < 0.6 else 1.18 - 0.18 * ease_out(min(1, (k - 0.6) / 0.4)))
    if sc_ > 0.05:
        icon = pop_icon(kind, ic, text)
        sz = max(2, int(ic * sc_))
        im_ = icon.resize((sz, sz), Image.BILINEAR)
        if a < 1:
            al = im_.getchannel("A").point(lambda v_: int(v_ * a))
            im_.putalpha(al)
        cx, cy = x0 + pad + ic / 2, y0 + h / 2
        img.paste(im_, (int(cx - sz / 2), int(cy - sz / 2)), im_)
    tx = x0 + pad + ic + pad
    if p.get("label"):
        d.text((tx, y0 + int(30 * s)), p["label"].upper(), font=fl, fill=col + (int(255 * a),), anchor="lm")
        d.text((tx, y0 + int(76 * s)), text, font=f, fill=WHITE + (int(255 * a),), anchor="lm")
    else:
        d.text((tx, y0 + h / 2 - int(4 * s)), text, font=f, fill=WHITE + (int(255 * a),), anchor="lm")


def overlay(img, t, plan_, cur, prev, W, H, captions=False):
    s = W / 1920
    d = ImageDraw.Draw(img, "RGBA")
    total = plan_["total"]
    date = cur["date"]
    if date:
        changing = prev is not None and prev["date"] != date and (t - cur["start"]) < 1.4
        p = clamp((t - cur["start"]) / 1.2)
        shown = date
        if changing:
            a, b = re.findall(r"\d{3,4}", prev["date"] or ""), re.findall(r"\d{3,4}", date)
            if a and b:
                v = int(round(int(a[0]) + (int(b[0]) - int(a[0])) * ease_io(p)))
                shown = re.sub(r"\d{3,4}", str(v), date, count=1)
        f = font("Oswald", int(44 * s), "SemiBold")
        wv = d.textbbox((0, 0), shown, font=f)[2]
        x, y, h = int(40 * s), int(36 * s), int(78 * s)
        d.rounded_rectangle([x, y, x + wv + int(108 * s), y + h], radius=int(14 * s), fill=(10, 10, 12, 175), outline=GOLD + (200,), width=max(1, int(2 * s)))
        draw_clock(d, x + int(42 * s), y + h / 2, int(20 * s), t * (14 if changing else 0.6), GOLD_L)
        d.text((x + int(78 * s), y + h / 2), shown, font=f, fill=WHITE, anchor="lm")
    if cur["chapter"]:
        f = font("Oswald", int(28 * s), "Medium")
        a = ease_out((t - cur["start"]) / 0.8) if (prev is None or prev["chapter"] != cur["chapter"]) else 1
        d.text((W - int(44 * s), int(75 * s)), cur["chapter"].upper(), font=f, fill=GREY + (int(220 * a),), anchor="rm")
    for p in plan_["pops"]:
        if p["t"] <= t < p["end"]:
            draw_pop(img, t, p, W, H)
    sa = plan_.get("sub_at")
    if sa is not None and sa <= t < sa + SUB_DUR:
        draw_subscribe(img, t - sa, W, H)
    if captions:
        draw_caption(img, t, plan_["lines"], W, H, H - int(120 * s), int(50 * s))
    return img


SUB_DUR = 3.3


def _thumb(d, cx, cy, r, fill):
    """A thumbs-up icon drawn from shapes (r = half size)."""
    u = r / 10
    d.rounded_rectangle([cx - 10 * u, cy - 2 * u, cx - 5.5 * u, cy + 9 * u], radius=1.2 * u, fill=fill)  # cuff
    d.rounded_rectangle([cx - 4 * u, cy - 3 * u, cx + 8.5 * u, cy + 9 * u], radius=2.2 * u, fill=fill)  # fist
    d.polygon([(cx - 4 * u, cy - 1 * u), (cx - 0.5 * u, cy - 9.5 * u), (cx + 2.6 * u, cy - 9.2 * u),
               (cx + 2.2 * u, cy - 3 * u), (cx - 1 * u, cy - 1 * u)], fill=fill)  # thumb
    d.ellipse([cx - 1.2 * u, cy - 11 * u, cx + 2.9 * u, cy - 7.4 * u], fill=fill)


def _bell(d, cx, cy, r, fill, ang=0.0):
    u = r / 10
    ca, sa_ = math.cos(ang), math.sin(ang)

    def R(x, y):
        return (cx + (x * ca - y * sa_) * u, cy + (x * sa_ + y * ca) * u)

    body = [R(-7, 5), R(-6, -1), R(-5, -5), R(-2.5, -7.5), R(0, -8), R(2.5, -7.5), R(5, -5), R(6, -1), R(7, 5), R(8.5, 6.5), R(-8.5, 6.5)]
    d.polygon(body, fill=fill)
    kx, ky = R(0, 8.6)
    d.ellipse([kx - 2 * u, ky - 2 * u, kx + 2 * u, ky + 2 * u], fill=fill)
    tx, ty = R(0, -9)
    d.ellipse([tx - 1.3 * u, ty - 1.3 * u, tx + 1.3 * u, ty + 1.3 * u], fill=fill)


def _cursor(d, x, y, sz, press=0.0):
    k = sz * (1 - 0.15 * press)
    pts = [(0, 0), (0, 17), (4.2, 13), (7.2, 19.5), (9.8, 18.3), (6.9, 12), (12.4, 12)]
    pts = [(x + px * k / 20, y + py * k / 20) for px, py in pts]
    d.polygon([(px + 2, py + 3) for px, py in pts], fill=(0, 0, 0, 90))
    d.polygon(pts, fill=(255, 255, 255, 255), outline=(20, 20, 20, 255))


def draw_subscribe(img, lt, W, H):
    """3-second 'Like + Subscribe' moment: a card slides up, a cursor clicks LIKE (it turns blue and pops),
    then SUBSCRIBE (red turns to grey 'SUBSCRIBED'), and the bell rings."""
    s = W / 1920
    SS = 2  # draw at 2x and shrink for smooth edges
    cw, ch = int(860 * s), int(150 * s)
    L = Image.new("RGBA", (cw * SS, ch * SS), (0, 0, 0, 0))
    d = ImageDraw.Draw(L)
    u = s * SS
    inn = ease_out(lt / 0.42)
    out = ease_io((lt - (SUB_DUR - 0.4)) / 0.4) if lt > SUB_DUR - 0.4 else 0
    vis = inn * (1 - out)
    # glass card
    d.rounded_rectangle([0, 0, cw * SS - 1, ch * SS - 1], radius=int(75 * u), fill=(12, 20, 32, 215), outline=GOLD + (170,), width=max(2, int(2.5 * u)))
    cy = ch * SS / 2
    # LIKE button
    lx0, lx1 = 36 * u, 290 * u
    liked = lt >= 1.0
    pres1 = clamp(1 - abs(lt - 1.0) / 0.12)
    bounce = 1 + (0.22 * math.sin(clamp((lt - 1.0) / 0.35) * math.pi) if liked else 0)
    d.rounded_rectangle([lx0, cy - 46 * u, lx1, cy + 46 * u], radius=int(46 * u), fill=(GOLD + (255,)) if liked else (255, 255, 255, 34))
    _thumb(d, lx0 + 66 * u, cy + 2 * u, 26 * u * bounce, (255, 255, 255, 255) if liked else (235, 240, 245, 255))
    fl = font("Oswald", int(44 * u), "SemiBold")
    d.text((lx0 + 112 * u, cy), "LIKE", font=fl, fill=(255, 255, 255, 255), anchor="lm")
    if liked and lt < 1.6:  # little burst around the thumb
        k = clamp((lt - 1.0) / 0.6)
        for i in range(10):
            ang = i * math.pi / 5
            r0, r1 = (34 + 40 * k) * u, (44 + 58 * k) * u
            bx, by = lx0 + 66 * u, cy
            d.line([(bx + r0 * math.cos(ang), by + r0 * math.sin(ang)), (bx + r1 * math.cos(ang), by + r1 * math.sin(ang))],
                   fill=GOLD_L + (int(255 * (1 - k)),), width=max(2, int(4 * u)))
    # SUBSCRIBE button
    sx0, sx1 = 320 * u, 690 * u
    subd = lt >= 2.0
    pulse = 1 + (0.05 * math.sin(lt * 9) if 1.2 < lt < 2.0 else 0)
    if subd:
        d.rounded_rectangle([sx0, cy - 46 * u, sx1, cy + 46 * u], radius=int(46 * u), fill=(70, 78, 88, 255))
        d.text(((sx0 + sx1) / 2, cy), "SUBSCRIBED", font=fl, fill=(225, 230, 236, 255), anchor="mm")
    else:
        mx = (sx1 - sx0) * (pulse - 1) / 2
        d.rounded_rectangle([sx0 - mx, cy - 46 * u * pulse, sx1 + mx, cy + 46 * u * pulse], radius=int(46 * u), fill=(230, 33, 23, 255))
        d.text(((sx0 + sx1) / 2, cy), "SUBSCRIBE", font=fl, fill=(255, 255, 255, 255), anchor="mm")
    # bell (rings after subscribing)
    bx = 760 * u
    ring = math.sin((lt - 2.3) * 28) * 0.45 * math.exp(-(lt - 2.3) * 3) if lt > 2.3 else 0
    _bell(d, bx, cy, 30 * u, (255, 255, 255, 255) if lt > 2.3 else (200, 208, 216, 255), ring)
    if lt > 2.3:
        k = clamp((lt - 2.3) / 0.6)
        for side in (-1, 1):
            d.arc([bx - (40 + 18 * k) * u, cy - (40 + 18 * k) * u, bx + (40 + 18 * k) * u, cy + (40 + 18 * k) * u],
                  start=-40 + (180 if side < 0 else 0), end=40 + (180 if side < 0 else 0), fill=GOLD_L + (int(255 * (1 - k)),), width=max(2, int(4 * u)))
    # the cursor: comes in, clicks LIKE at 1.0 s, moves and clicks SUBSCRIBE at 2.0 s, leaves
    p_like = (lx0 + 150 * u, cy + 14 * u)
    p_sub = ((sx0 + sx1) / 2 + 40 * u, cy + 14 * u)
    p_off = (cw * SS + 60 * u, ch * SS + 40 * u)
    if lt < 0.95:
        k = ease_io(clamp((lt - 0.35) / 0.6))
        cx_, cy_ = p_off[0] + (p_like[0] - p_off[0]) * k, p_off[1] + (p_like[1] - p_off[1]) * k
    elif lt < 1.95:
        k = ease_io(clamp((lt - 1.3) / 0.6))
        cx_, cy_ = p_like[0] + (p_sub[0] - p_like[0]) * k, p_like[1] + (p_sub[1] - p_like[1]) * k
    else:
        k = ease_io(clamp((lt - 2.4) / 0.5))
        cx_, cy_ = p_sub[0] + (p_off[0] - p_sub[0]) * k, p_sub[1] + (p_off[1] - p_sub[1]) * k
    press = max(pres1, clamp(1 - abs(lt - 2.0) / 0.12))
    if press > 0:
        rr = (14 + 26 * (1 - press)) * u
        d.ellipse([cx_ - rr, cy_ - rr, cx_ + rr, cy_ + rr], outline=(255, 255, 255, int(200 * press)), width=max(2, int(3 * u)))
    _cursor(d, cx_, cy_, 46 * u, press)
    L = L.resize((cw, ch), Image.LANCZOS)
    if vis < 1:
        a = L.getchannel("A").point(lambda v: int(v * vis))
        L.putalpha(a)
    x = (W - cw) // 2
    y = int(H - ch - 70 * s + (1 - inn) * 160 * s + out * 160 * s)
    sh = Image.new("RGBA", (cw + int(80 * s), ch + int(80 * s)), (0, 0, 0, 0))
    ImageDraw.Draw(sh).rounded_rectangle([int(40 * s), int(48 * s), int(40 * s) + cw, int(48 * s) + ch], radius=int(75 * s), fill=(0, 0, 0, int(120 * vis)))
    sh = sh.filter(ImageFilter.GaussianBlur(int(18 * s) + 1))
    img.paste(sh, (x - int(40 * s), y - int(40 * s)), sh)
    img.paste(L, (x, y), L)


# ------------------------------------------------------------------ frame workers (run in parallel)

_W = {}


def _init_worker(plan_path, W, H, fps, captions):
    with open(plan_path, encoding="utf-8") as f:
        pl = json.load(f)
    apply_theme(pl.get("theme"))
    _W.update(plan=pl, W=W, H=H, fps=fps, captions=captions, objs={})


def _beat_obj(i):
    o = _W["objs"].get(i)
    if o is None:
        b = _W["plan"]["beats"][i]
        v = b["visual"]
        cls = SCENES.get(v.get("type", "title"), TitleScene)
        o = cls({"visual": v}, _W["W"], _W["H"], i)
        for k in list(_W["objs"]):
            if k < i - 1:
                del _W["objs"][k]
        _W["objs"][i] = o
    return o


def beat_frame(i, lt):
    """One beat's picture at local time lt, with ambience and a gentle 'punch' on long still slides."""
    W, H = _W["W"], _W["H"]
    b = _W["plan"]["beats"][i]
    typ = b["visual"].get("type", "title")
    img = _beat_obj(i).frame(lt, b["dur"])
    if typ in QUIET_TYPES:
        img = light_leak(img, b["start"] + lt, seed=i % 5)
        img = dust(img, b["start"] + lt, 0.8)
        if b["dur"] > 6 and typ in ("text", "quote", "stat", "bars"):
            k = int(lt // 3.5)
            if k > 0:  # a soft zoom step every few seconds keeps long slides alive
                z = 1 + 0.035 * (k % 2 == 1) * ease_out((lt - k * 3.5) / 0.5) + 0.035 * (k % 2 == 0) * (1 - ease_out((lt - k * 3.5) / 0.5))
                if z > 1.001:
                    cw, ch = W / z, H / z
                    img = img.resize((W, H), Image.BILINEAR, box=((W - cw) / 2, (H - ch) / 2, (W + cw) / 2, (H + ch) / 2))
    elif typ == "image":
        img = dust(img, b["start"] + lt, 0.45, seed=5)
    if b.get("hit") and lt < 0.6:  # pattern interrupt: slam in, shake, flash
        z = 1 + 0.28 * (1 - ease_out(lt / 0.22))
        cw, ch = W / z, H / z
        mx = (W - cw) / 2
        sh = max(-mx, min(mx, 18 * (W / 1920) * math.exp(-lt * 9) * math.sin(lt * 70)))
        sv = max(-(H - ch) / 2, min((H - ch) / 2, sh * 0.6))
        img = img.resize((W, H), Image.BILINEAR, box=((W - cw) / 2 + sh, (H - ch) / 2 - sv, (W + cw) / 2 + sh, (H + ch) / 2 - sv))
        if lt < 0.12:
            img = Image.blend(img, Image.new("RGB", (W, H), (255, 244, 220)), 0.55 * (1 - lt / 0.12))
        return img
    if lt < 0.5 and typ != "map":  # settle-in zoom at the start of each slide
        z = 1 + 0.04 * (1 - ease_out(lt / 0.5))
        cw, ch = W / z, H / z
        img = img.resize((W, H), Image.BILINEAR, box=((W - cw) / 2, (H - ch) / 2, (W + cw) / 2, (H + ch) / 2))
    return img


def render_frame(n):
    fps, pl, W, H = _W["fps"], _W["plan"], _W["W"], _W["H"]
    t = n / fps
    beats = pl["beats"]
    idx = 0
    for j, b in enumerate(beats):
        if b["start"] <= t:
            idx = j
    cur = beats[idx]
    lt = t - cur["start"]
    img = beat_frame(idx, lt)
    fade = 0.45 if cur["new_scene"] else 0.28
    style = THEME.get("name")
    if idx > 0 and not cur.get("hit") and style == "nature" and lt < 0.4:
        prev = beats[idx - 1]
        pimg = beat_frame(idx - 1, prev["dur"] - 0.01 + lt)
        kind = ("whip", "zoom", "whip", "fade")[idx % 4] if not cur["new_scene"] else "zoom"
        if kind == "whip" and lt < 0.34:  # fast slide with motion blur, like a camera whip pan
            p = ease_io(lt / 0.34)
            dx = int(W * p)
            canvas = Image.new("RGB", (W, H))
            canvas.paste(pimg, (-dx, 0))
            canvas.paste(img, (W - dx, 0))
            blur = math.sin(math.pi * p)
            if blur > 0.05:
                soft = canvas.resize((max(8, W // 14), H), Image.BILINEAR).resize((W, H), Image.BILINEAR)
                canvas = Image.blend(canvas, soft, min(0.85, blur * 0.9))
            img = canvas
        elif kind == "zoom" and lt < 0.4:  # the old shot rushes toward you, the new one appears through it
            p = ease_io(lt / 0.4)
            z = 1 + 0.35 * p
            cw, ch = W / z, H / z
            pz = pimg.resize((W, H), Image.BILINEAR, box=((W - cw) / 2, (H - ch) / 2, (W + cw) / 2, (H + ch) / 2))
            z2 = 1.18 - 0.18 * p
            cw2, ch2 = W / z2, H / z2
            iz = img.resize((W, H), Image.BILINEAR, box=((W - cw2) / 2, (H - ch2) / 2, (W + cw2) / 2, (H + ch2) / 2))
            img = Image.blend(pz, iz, p)
        elif lt < fade:
            img = Image.blend(pimg, img, ease(lt / fade))
    elif idx > 0 and lt < fade and not cur.get("hit"):
        prev = beats[idx - 1]
        pimg = beat_frame(idx - 1, prev["dur"] - 0.01 + lt)
        img = Image.blend(pimg, img, ease(lt / fade))
    img = overlay(img, t, pl, cur, beats[idx - 1] if idx > 0 else None, W, H, _W["captions"])
    return img.convert("RGB").tobytes()


# ------------------------------------------------------------------ real pictures: Wikimedia Commons (free, credited), AI painting as backup

UA = {"User-Agent": "SaimShafiHistoryEngine/4.0 (https://github.com/Saimshafi0; personal documentary maker)"}


def http_json(url, data=None, headers=None, timeout=25):
    req = urllib.request.Request(url, data=data, headers={**UA, **(headers or {})})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return json.loads(r.read().decode())


def http_bytes(url, timeout=120):
    with urllib.request.urlopen(urllib.request.Request(url, headers=UA), timeout=timeout) as r:
        return r.read()


def img_key(v):
    q = v.get("search") or v.get("ai") or v.get("caption") or "picture"
    q = q[0] if isinstance(q, list) else q
    return re.sub(r"[^a-z0-9]+", "_", q.lower()).strip("_")[:60] or "picture"


class SourceDown(Exception):
    pass


def _net_error(e):
    t = str(e)
    return any(x in t for x in ("10054", "10060", "10061", "11001", "getaddrinfo", "timed out", "Connection reset", "forcibly closed",
                                "Connection refused", "EOF occurred", "SSL", "Tunnel connection failed", "Network is unreachable"))


def _search_many(name, queries, fn):
    """Runs fn(query) for each query; raises SourceDown if the website can't be reached at all."""
    out, errs, tried = [], 0, 0
    for q in queries:
        tried += 1
        try:
            out += fn(q)
        except Exception as e:
            if _net_error(e):
                errs += 1
                log(f"    {name}: can't connect ({str(e)[:70]})")
            else:
                log(f"    {name} search failed for '{q}': {str(e)[:70]}")
        if len(out) >= 8:
            break
    if not out and errs and errs == tried:
        raise SourceDown(name)
    seen, uniq = set(), []
    for c in out:
        if c["url"] not in seen:
            seen.add(c["url"])
            uniq.append(c)
    return uniq


def commons_candidates(queries):
    def one(q):
        url = "https://commons.wikimedia.org/w/api.php?" + urllib.parse.urlencode({
            "action": "query", "format": "json", "generator": "search", "gsrnamespace": 6, "gsrsearch": q + " filetype:bitmap", "gsrlimit": 20,
            "prop": "imageinfo", "iiprop": "url|extmetadata|size|mime", "iiurlwidth": 2400})
        data = http_json(url)
        res = []
        pages = sorted((data.get("query") or {}).get("pages", {}).values(), key=lambda p: p.get("index", 99))
        for p in pages:
            ii = (p.get("imageinfo") or [{}])[0]
            meta = ii.get("extmetadata") or {}
            lic = (meta.get("LicenseShortName") or {}).get("value", "")
            title = p.get("title", "")
            if ii.get("mime") not in ("image/jpeg", "image/png", "image/webp") or ii.get("width", 0) < 900 or ii.get("height", 0) < 500:
                continue
            if not re.search(r"public domain|\bpd\b|pd-|cc0|cc[- ]by", lic, re.I) or re.search(r"\b(nc|nd)\b|-nc|-nd", lic, re.I):
                continue
            if re.search(r"logo|icon|flag of|coat of arms|signature|\.svg|locator|location map|diagram", title, re.I):
                continue
            artist = re.sub(r"<[^>]+>", "", (meta.get("Artist") or {}).get("value", "")).strip()[:80]
            res.append({"title": title.replace("File:", ""), "url": ii.get("thumburl") or ii.get("url"), "src": "commons",
                        "credit": f"{title.replace('File:', '')} - {artist or 'unknown'} - {lic} - {ii.get('descriptionurl', '')}"})
        return res
    return _search_many("Wikimedia", queries, one)


def openverse_candidates(queries):
    def one(q):
        url = "https://api.openverse.org/v1/images/?" + urllib.parse.urlencode({"q": q, "license_type": "commercial", "page_size": 20, "mature": "false"})
        data = http_json(url)
        res = []
        for r in data.get("results") or []:
            u = r.get("url") or ""
            if not u or (r.get("width") or 0) < 900 or "wikimedia.org" in u:
                continue
            lic = f"{(r.get('license') or '').upper()} {r.get('license_version') or ''}".strip()
            if re.search(r"\b(NC|ND)\b|-NC|-ND", lic):
                continue
            res.append({"title": (r.get("title") or q)[:120], "url": u, "src": "openverse",
                        "credit": f"{r.get('title') or 'Untitled'} - {r.get('creator') or 'unknown'} - {lic} - {r.get('foreign_landing_url', '')}"})
        return res
    return _search_many("Openverse", queries, one)


def met_candidates(queries):
    """The Metropolitan Museum of Art: public-domain paintings, coins, manuscripts, maps."""
    def one(q):
        d = http_json("https://collectionapi.metmuseum.org/public/collection/v1/search?" + urllib.parse.urlencode({"hasImages": "true", "isPublicDomain": "true", "q": q}))
        res = []
        for oid in (d.get("objectIDs") or [])[:6]:
            try:
                o = http_json(f"https://collectionapi.metmuseum.org/public/collection/v1/objects/{oid}")
            except Exception:
                continue
            img = o.get("primaryImage") or ""
            if img and o.get("isPublicDomain"):
                res.append({"title": (o.get("title") or q)[:120], "url": img, "src": "met",
                            "credit": f"{o.get('title') or 'Untitled'} - {o.get('artistDisplayName') or 'unknown'} - Public domain (The Met) - {o.get('objectURL', '')}"})
        return res
    return _search_many("The Met", queries, one)


def aic_candidates(queries):
    """Art Institute of Chicago: public-domain artworks."""
    def one(q):
        d = http_json("https://api.artic.edu/api/v1/artworks/search?" + urllib.parse.urlencode(
            {"q": q, "query[term][is_public_domain]": "true", "fields": "id,title,image_id,artist_display", "limit": 10}))
        res = []
        for r in d.get("data") or []:
            if r.get("image_id"):
                res.append({"title": (r.get("title") or q)[:120], "url": f"https://www.artic.edu/iiif/2/{r['image_id']}/full/1686,/0/default.jpg", "src": "aic",
                            "credit": f"{r.get('title') or 'Untitled'} - {(r.get('artist_display') or 'unknown').splitlines()[0]} - Public domain (Art Institute of Chicago) - https://www.artic.edu/artworks/{r['id']}"})
        return res
    return _search_many("Art Institute of Chicago", queries, one)


def bing_candidates(queries):
    """Bing Images, only pictures marked free to share and use (license filter). Skips sites your internet blocks."""
    ua = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/130.0 Safari/537.36",
          "Accept-Language": "en-US,en;q=0.9"}

    def one(q):
        res = []
        for lic in ("L2_L3", "L1"):
            url = "https://www.bing.com/images/async?" + urllib.parse.urlencode(
                {"q": q, "first": 0, "count": 35, "mmasync": 1, "qft": f"+filterui:license-{lic}+filterui:imagesize-large"})
            req = urllib.request.Request(url, headers=ua)
            with urllib.request.urlopen(req, timeout=25) as r:
                page = r.read().decode("utf-8", "replace")
            for m_ in re.finditer(r'm="(\{[^"]+\})"', page):
                try:
                    d = json.loads(html_unescape(m_.group(1)))
                except Exception:
                    continue
                u = d.get("murl") or ""
                if not u.startswith("http") or re.search(r"wikimedia\.org|wikipedia\.org|pinterest|shutterstock|alamy|getty|istock|dreamstime|123rf|adobe", u, re.I):
                    continue
                res.append({"title": (d.get("t") or q)[:120], "url": u, "src": "bing",
                            "credit": f"{d.get('t') or q} - via Bing (free-to-use license filter) - {d.get('purl') or u}"})
            if len(res) >= 6:
                break
        return res
    return _search_many("Bing Images", queries, one)


def html_unescape(t):
    import html as _h
    return _h.unescape(t)


# Bing is NOT used: its "free license" results were random junk (logos, name pages).
def loc_candidates(queries):
    """Library of Congress: photos, newspapers, prints. Only items marked 'no known restrictions'."""
    def one(q):
        url = "https://www.loc.gov/photos/?" + urllib.parse.urlencode({"q": q, "fo": "json", "c": 40})
        data = http_json(url)
        res = []
        for r in data.get("results") or []:
            blob = json.dumps(r).lower()
            if "no known restrictions" not in blob and "public domain" not in blob:
                continue
            imgs = [u for u in (r.get("image_url") or []) if isinstance(u, str)]
            if not imgs:
                continue
            u = imgs[-1].split("#")[0]
            if u.startswith("//"):
                u = "https:" + u
            title = r.get("title") or q
            res.append({"title": str(title)[:140], "url": u, "src": "loc",
                        "credit": f"{str(title)[:90]} - Library of Congress - No known restrictions - {r.get('url', '')}"})
        return res
    return _search_many("Library of Congress", queries, one)


def pixabay_photo_candidates(queries):
    """Pixabay photos (free key): modern real photos of places, cities, objects."""
    key = secret("pixabay_key")
    if not key:
        return []

    def one(q):
        url = "https://pixabay.com/api/?" + urllib.parse.urlencode({"key": key, "q": q[:95], "image_type": "photo", "per_page": 30, "safesearch": "true"})
        data = http_json(url)
        return [{"title": h.get("tags") or q, "url": h.get("largeImageURL"), "src": "pixabay",
                 "credit": f"{h.get('tags', 'photo')} - {h.get('user', 'unknown')} on Pixabay - Pixabay Content License - {h.get('pageURL', '')}"}
                for h in data.get("hits") or [] if h.get("largeImageURL") and int(h.get("imageWidth") or 0) >= 1200]
    return _search_many("Pixabay photos", queries, one)


SOURCES = [("commons", commons_candidates), ("openverse", openverse_candidates), ("loc", loc_candidates), ("met", met_candidates),
           ("aic", aic_candidates), ("pixabay", pixabay_photo_candidates)]


def ai_painting(prompt, path):
    """Backup when no real picture exists: a free AI painting (pollinations.ai). Marked as AI in the credits."""
    style = ", oil painting, historical, cinematic lighting, muted warm colors, highly detailed, no text"
    url = "https://image.pollinations.ai/prompt/" + urllib.parse.quote(prompt + style) + "?width=1920&height=1080&nologo=true&seed=" + str(abs(hash(prompt)) % 10000)
    raw = http_bytes(url, timeout=50)
    Image.open(__import__("io").BytesIO(raw)).convert("RGB").save(path, quality=92)


def _download_to(url, path):
    raw = http_bytes(url, timeout=60)
    im = Image.open(__import__("io").BytesIO(raw))
    if min(im.size) < 400:
        raise ValueError("too small")
    im = im.convert("RGB")
    im.thumbnail((3200, 3200))
    im.save(path, quality=92)
    return path


# words that say nothing about WHAT is in the picture
_STOP = set("""the a an of in on at to and or for with from by is are was were his her its their this that these those into over under after before
century painting portrait photograph photo old engraving illustration image picture view drawing print sketch lithograph art artwork museum
early late circa new great file jpg png""".split())


def _sig_words(s):
    """Meaningful words, cut to 5 letters so 'moonlit' matches 'moonlight' and 'murders' matches 'murderer'."""
    return {w[:5] for w in re.findall(r"[a-z]{3,}", (s or "").lower()) if w not in _STOP}


def _rank_candidates(cands, queries):
    """Pictures whose title shares real words with the search come first. Titles that share nothing are marked weak (often junk)."""
    qw = set()
    for q in queries:
        qw |= _sig_words(q)
    scored = []
    need = 1 if len(qw) <= 2 else 2  # a long search must share at least 2 real words with the title
    for i, c in enumerate(cands):
        s = len(qw & _sig_words(c.get("title", ""))) if qw else 1
        c = dict(c)
        c["weak"] = s < need
        scored.append((-s, i, c))
    scored.sort(key=lambda x: (x[0], x[1]))
    return [c for _, _, c in scored]


def _queries(v):
    q = v.get("search") or []
    return [q] if isinstance(q, str) else [x for x in q if x]


def _find_candidates(key, v, use_ai, state):
    """All the candidate pictures for one search (cached in images/<key>.json). Nothing is downloaded here."""
    meta_p = A("images", key + ".json")
    meta = _json_read(meta_p, {})
    q = _queries(v)
    if meta.get("source") == "bing":  # old junk from Bing
        meta = {}
        for f in (A("images", key + ".jpg"),):
            if os.path.exists(f):
                try:
                    os.remove(f)
                except OSError:
                    pass
    cands = [c for c in (meta.get("candidates") or []) if c.get("url")]
    if cands and meta.get("cver", 0) >= 4:
        return key, meta
    if cands and len([c for c in cands if not c.get("weak")]) >= 4:
        meta["candidates"] = _rank_candidates(cands, q)
        meta["cver"] = 4
        _json_write(meta_p, meta)
        return key, meta
    found = list(cands)
    for name, fn in SOURCES:
        if not q:
            break
        with state["lock"]:
            if name in state["dead"]:
                continue
        try:
            got = fn(q)
        except SourceDown:
            with state["lock"]:
                state["fails"][name] = state["fails"].get(name, 0) + 1
                if state["fails"][name] >= 2 and name not in state["dead"]:
                    state["dead"].add(name)
                    log(f"  {name}: not reachable from this internet, skipping it for now.")
            continue
        seen = {c["url"] for c in found}
        found += [c for c in got if c["url"] not in seen]
        if len([c for c in _rank_candidates(found, q) if not c.get("weak")]) >= 14:
            break  # enough good options, don't ask the next website
    meta["candidates"] = _rank_candidates(found, q)
    meta["cver"] = 4
    _json_write(meta_p, meta)
    return key, meta


def _dhash(path):
    """64-bit picture fingerprint: two copies of the same picture (even resized) give almost the same number."""
    try:
        g = Image.open(path).convert("L").resize((9, 8), Image.BILINEAR)
        a = np.asarray(g, np.int16)
        bits = (a[:, 1:] > a[:, :-1]).flatten()
        return int("".join("1" if b else "0" for b in bits), 2)
    except Exception:
        return None


def _same_picture(h, used):
    return h is not None and any(u is not None and bin(h ^ u).count("1") <= 6 for u in used)


# ------------------------------------------------------------------ faces: never cut a face

_FACE_LOCK = threading.Lock()
_CASCADES = None


def _cascades():
    global _CASCADES
    if _CASCADES is None:
        _CASCADES = []
        try:
            import cv2
            for f in ("haarcascade_frontalface_alt2.xml", "haarcascade_frontalface_default.xml", "haarcascade_profileface.xml"):
                p = A("assets", "haar", f)
                if not os.path.exists(p):
                    try:
                        p = os.path.join(cv2.data.haarcascades, f)
                    except Exception:
                        continue
                c = cv2.CascadeClassifier(p)
                if not c.empty():
                    _CASCADES.append((f, c))
        except Exception:
            _CASCADES = []
    return _CASCADES


def detect_faces(path):
    """Faces in a picture as [x0, y0, x1, y1] (0-1). Uses OpenCV if it is installed, otherwise returns []."""
    cas = _cascades()
    if not cas:
        return []
    try:
        import cv2
        im = Image.open(path).convert("L")
        sc = min(1.0, 1000 / max(im.size))
        if sc < 1:
            im = im.resize((int(im.width * sc), int(im.height * sc)), Image.BILINEAR)
        g = cv2.equalizeHist(np.asarray(im))
        h, w = g.shape
        ms = max(24, int(min(h, w) * 0.05))
        boxes = []
        for name, c in cas:
            for flip in ((False, True) if "profile" in name else (False,)):
                gg = g[:, ::-1].copy() if flip else g
                for (x, y, bw, bh) in c.detectMultiScale(gg, 1.08, 6, minSize=(ms, ms)):
                    x = w - x - bw if flip else x
                    boxes.append([x / w, y / h, (x + bw) / w, (y + bh) / h, name])
        # merge overlapping boxes, count votes
        merged = []
        for b in boxes:
            for m in merged:
                ix = max(0, min(b[2], m[2]) - max(b[0], m[0]))
                iy = max(0, min(b[3], m[3]) - max(b[1], m[1]))
                inter = ix * iy
                uni = (b[2] - b[0]) * (b[3] - b[1]) + (m[2] - m[0]) * (m[3] - m[1]) - inter
                if uni > 0 and inter / uni > 0.3:
                    m[5] += 1
                    m[:4] = [min(b[0], m[0]), min(b[1], m[1]), max(b[2], m[2]), max(b[3], m[3])]
                    break
            else:
                merged.append(b[:5] + [1])
        strong = [m for m in merged if m[5] >= 2]
        if not strong:
            strong = [m for m in merged if m[4] == "haarcascade_frontalface_alt2.xml"]
        return [[round(float(v), 4) for v in m[:4]] for m in strong[:6]]
    except Exception:
        return []


def faces_for(fname):
    """Cached face boxes for images/<fname>."""
    idx_p = A("images", "_faces.json")
    with _FACE_LOCK:
        idx = _json_read(idx_p, {})
        if fname in idx:
            return idx[fname]
    f = detect_faces(A("images", fname))
    with _FACE_LOCK:
        idx = _json_read(idx_p, {})
        idx[fname] = f
        _json_write(idx_p, idx)
    return f


# ------------------------------------------------------------------ choosing pictures: every slide gets its OWN picture

ERA = {"max": None}


def _too_modern(c):
    """A photo dated long after the story (e.g. a 2015 photo in a story that ends in 1910) is skipped."""
    if not ERA["max"] or ERA["max"] >= 1990:
        return False
    ys = [int(y) for y in re.findall(r"(?<!\d)(1[89]\d\d|20[0-2]\d)(?!\d)", c.get("title", ""))]
    return bool(ys) and min(ys) > ERA["max"] + 20


def set_era(script):
    era = script.get("era") or []
    ys = [int(y) for y in era if str(y).isdigit()] if isinstance(era, list) else []
    if not ys:
        ys = [int(y) for sc in script["scenes"] for y in re.findall(r"\b(1[0-9]{3}|20[0-2][0-9])\b", str(sc.get("date", "")))]
    ERA["max"] = max(ys) if ys else None
    region = (script.get("region") or "").strip()
    if region:  # every search names the place, so we don't get Budapest for an Australian story
        rw = _sig_words(region)
        for sc in script["scenes"]:
            for v in sc.get("visuals") or []:
                if v.get("type") in ("image", "video") and v.get("search"):
                    q = _queries(v)
                    if q and not (rw & _sig_words(q[0])) and not re.search(r"\b[A-Z][a-z]+", q[0]):
                        v["search"] = [q[0] + " " + region] + q[1:]


def resolve_pictures(script, use_ai=True):
    """Finds a real picture for every image slide. The same picture is never used twice in one video:
    if a search repeats, the next picture for that search is used; copies of the same picture are detected by fingerprint."""
    from concurrent.futures import ThreadPoolExecutor
    os.makedirs(A("images"), exist_ok=True)
    slides, keys, scene_of = [], {}, {}
    for si, sc in enumerate(script["scenes"]):
        for v in (sc.get("visuals") or [sc.get("visual") or {}]):
            if v.get("type") != "image":
                continue
            if v.get("file_fixed") and os.path.exists(A("images", v["file_fixed"])):
                continue
            key = img_key(v)
            slides.append((key, v))
            scene_of[id(v)] = si
            keys.setdefault(key, v)
    state = {"dead": set(), "fails": {}, "lock": threading.Lock()}
    metas = {}
    n = len(keys)
    log(f"  {len(slides)} picture slides ({n} different searches)")
    with ThreadPoolExecutor(6) as ex:
        futs = [ex.submit(_find_candidates, k, v, use_ai, state) for k, v in keys.items()]
        for i, f in enumerate(futs, 1):
            try:
                k, m = f.result()
                metas[k] = m
            except Exception as e:
                log(f"    picture search error: {str(e)[:80]}")
            print(f"\r   searching pictures {i}/{n}  ({i * 50 // max(1, n)}%)", end="", flush=True)
    print()

    def cand_file(key, c):
        if c.get("url", "").startswith("own:"):
            return key + ".jpg"
        return f"{key}__{hashlib.sha1(c['url'].encode()).hexdigest()[:10]}.jpg"

    # the options for each search, in order: your own picture, then the chosen one, then the rest (good matches before weak ones)
    options = {}
    for key, meta in metas.items():
        own = os.path.exists(A("images", key + ".jpg")) and (meta.get("source") == "own" or (not meta.get("candidates") and meta.get("source") not in ("ai",)))
        cands = list(meta.get("candidates") or [])
        ch = int(meta.get("choice", 0) or 0)
        if 0 < ch < len(cands):
            cands = [cands[ch]] + cands[:ch] + cands[ch + 1:]
        strong = [c for c in cands if not c.get("weak") and not _too_modern(c)]
        weak = [c for c in cands if c.get("weak") and not _too_modern(c)]
        opts = ([{"url": "own:" + key, "credit": meta.get("credit", ""), "title": "your picture"}] if own else []) + strong
        options[key] = (opts, weak)
        # old cache: images/<key>.jpg is the chosen candidate; reuse it instead of downloading again
        if not own and cands and os.path.exists(A("images", key + ".jpg")):
            f0 = A("images", cand_file(key, cands[0]))
            if not os.path.exists(f0):
                try:
                    shutil.copyfile(A("images", key + ".jpg"), f0)
                except OSError:
                    pass

    # download, in parallel, the pictures we will probably need (one per slide + 2 spare per search)
    need = {}
    for key, _ in slides:
        need[key] = need.get(key, 0) + 1
    jobs = []
    for key, (opts, weak) in options.items():
        for c in (opts + weak)[:need.get(key, 1) + 2]:
            if not c["url"].startswith("own:") and not os.path.exists(A("images", cand_file(key, c))):
                jobs.append((key, c))

    def dl(job):
        key, c = job
        try:
            _download_to(c["url"], A("images", cand_file(key, c)))
            return True
        except Exception:
            c["bad"] = True
            return False
    if jobs:
        with ThreadPoolExecutor(8) as ex:
            for i, _ in enumerate(ex.map(dl, jobs), 1):
                print(f"\r   downloading pictures {i}/{len(jobs)}  ({50 + i * 50 // len(jobs)}%)", end="", flush=True)
        print()

    used_urls, used_hash, credits, missing, last_in_scene = set(), [], [], [], []
    uses = {}  # file -> how many times it was used (only > 1 when there was truly no other picture)
    by_key = {}

    def take(key, c):
        if c.get("bad"):
            return None
        fn = cand_file(key, c)
        path = A("images", fn)
        if not os.path.exists(path):
            try:
                _download_to(c["url"], path)
            except Exception:
                c["bad"] = True
                return None
        h = _dhash(path)
        if _same_picture(h, used_hash):
            used_urls.add(c["url"])
            return None
        return fn, h

    def first_unused(key, pool):
        for c in pool:
            if c["url"] in used_urls:
                continue
            r = take(key, c)
            if r:
                return (r[0], r[1], c)
        return None

    def related_files(key):
        """Pictures already used for a search about the same thing (shares real words)."""
        kw = _sig_words(key.replace("_", " "))
        out = []
        for k2, fs in by_key.items():
            if k2 != key and kw & _sig_words(k2.replace("_", " ")):
                out += fs
        return out

    for key, v in slides:
        opts, weak = options.get(key, ([], []))
        v.pop("recut", None)
        picked = first_unused(key, opts)
        if not picked and not by_key.get(key) and len(_sig_words(key.replace("_", " "))) <= 1:
            picked = first_unused(key, weak)  # a one-word search: titles can't be judged, try them
        if picked:
            fn, h, c = picked
            used_urls.add(c["url"])
            used_hash.append(h)
            uses[fn] = 1
            by_key.setdefault(key, []).append(fn)
            v["file"] = fn
            last_in_scene.append((scene_of.get(id(v), -1), fn))
            if c.get("credit") and c["credit"] not in credits:
                credits.append(c["credit"])
            if len(by_key[key]) == 1:
                meta = metas.get(key) or {}
                meta["first_file"] = fn
                metas[key] = meta
        else:
            # truly nothing new for this search: show a DIFFERENT part of a picture from the same search
            mine = by_key.get(key) or related_files(key)
            if not mine:  # nothing about this exact thing: a close-up of the picture just before it in the same part of the story
                si = scene_of.get(id(v), -1)
                near = [x for x in last_in_scene if abs(x[0] - si) <= 1]
                mine = [near[-1][1]] if near else []
            if mine:
                fn = min(mine, key=lambda x: uses.get(x, 1))
                uses[fn] = uses.get(fn, 1) + 1
                v["file"] = fn
                v["recut"] = uses[fn] - 1
                log(f"    only one picture exists for '{key}': using a different part of it")
            else:
                v.pop("file", None)
                missing.append(v.get("caption") or key)
    # AI painting as the very last resort (if the free service works)
    if missing and use_ai:
        for key, v in slides:
            if v.get("file") or "ai" in state["dead"]:
                continue
            p = A("images", key + "__ai.jpg")
            try:
                if not os.path.exists(p):
                    ai_painting(v.get("ai") or (_queries(v) or [key])[0], p)
                v["file"] = key + "__ai.jpg"
                credits.append(f"AI-generated illustration: {v.get('ai') or key}")
                missing.remove(v.get("caption") or key)
            except Exception as e:
                state["dead"].add("ai")
                if "402" not in str(e):
                    log(f"    AI painting failed ({str(e)[:60]})")
    for key, meta in metas.items():
        _json_write(A("images", key + ".json"), meta)
    # faces, so no picture ever cuts a head off
    files = sorted({v["file"] for _, v in slides if v.get("file")})
    if _cascades():
        fx = {}
        for i, f in enumerate(files, 1):  # one at a time: the face finder is not thread-safe
            fx[f] = faces_for(f)
            print(f"\r   finding faces {i}/{len(files)}", end="", flush=True)
        print()
    else:
        fx = {}
        log("  (face finder not installed: pictures are framed by the middle. Run START.bat once to install it.)")
    for _, v in slides:
        if v.get("file"):
            v["faces"] = fx.get(v["file"], [])
    reused = sum(1 for _, v in slides if v.get("recut"))
    log(f"  pictures: {len(files)} different pictures for {len(slides)} slides" + (f", {reused} shown as a close-up of another part" if reused else "")
        + (f", {len(missing)} without a picture" if missing else ""))
    if missing:
        log(f"  {len(missing)} picture(s) not found. Real-picture websites reachable: "
            + (", ".join(n_ for n_, _ in SOURCES if n_ not in state["dead"]) or "none"))
    return credits, missing


# ================================================================== REAL VIDEO CLIPS (b-roll): archive footage + free stock footage + your own clips
#
# Only footage we are allowed to use:
#   - Wikimedia Commons videos: public domain, CC0, CC BY, CC BY-SA (never NC / ND)
#   - Internet Archive films: only items whose license is public domain / CC0 / CC BY / CC BY-SA
#   - Pexels and Pixabay videos (free keys): their licenses allow use in monetized videos
#   - your own clips (clips_own/<slide>.mp4): YOUR responsibility (see MEDIA-RULES.txt)
# Every clip is credited in the description.

CLIP_SEC = 15.0         # how much of each clip we cut: enough for 3 different moments of 4-5 seconds
_OK_LIC = re.compile(r"public ?domain|publicdomain|\bpd\b|pd-|cc0|cc[- ]?by|creativecommons\.org/licenses/by(-sa)?/|creativecommons\.org/publicdomain", re.I)
_BAD_LIC = re.compile(r"\bnc\b|\bnd\b|-nc|-nd|by-nc|by-nd|noncommercial|noderiv", re.I)


def _lic_ok(lic):
    return bool(lic) and bool(_OK_LIC.search(lic)) and not _BAD_LIC.search(lic)


def vid_key(v):
    return "v_" + img_key(v)


def secret(name):
    """API keys: from the cloud's secret store (env) or from settings.json on this PC."""
    return (os.environ.get(name.upper()) or settings().get(name.lower()) or "").strip()


def commons_video_candidates(queries):
    def one(q):
        url = "https://commons.wikimedia.org/w/api.php?" + urllib.parse.urlencode({
            "action": "query", "format": "json", "generator": "search", "gsrnamespace": 6, "gsrsearch": q + " filetype:video", "gsrlimit": 20,
            "prop": "videoinfo|imageinfo", "viprop": "url|size|mime|extmetadata|derivatives", "iiprop": "url|size|mime|extmetadata"})
        data = http_json(url)
        res = []
        pages = sorted((data.get("query") or {}).get("pages", {}).values(), key=lambda p: p.get("index", 99))
        for p in pages:
            vi = (p.get("videoinfo") or p.get("imageinfo") or [{}])[0]
            if not str(vi.get("mime", "video")).startswith(("video", "application/ogg")):
                continue
            meta = vi.get("extmetadata") or {}
            lic = (meta.get("LicenseShortName") or {}).get("value", "")
            if not _lic_ok(lic):
                continue
            dur = float(vi.get("duration") or 0)
            if dur and dur < 3:
                continue
            # a ready-made smaller copy (720p/480p) downloads much faster than the original
            ders = [d for d in (vi.get("derivatives") or []) if d.get("src") and int(d.get("height") or 0) >= 360]
            ders.sort(key=lambda d: abs(int(d.get("height") or 0) - 720))
            src = ders[0]["src"] if ders else vi.get("url")
            if not src:
                continue
            title = p.get("title", "").replace("File:", "")
            artist = re.sub(r"<[^>]+>", "", (meta.get("Artist") or {}).get("value", "")).strip()[:80]
            res.append({"title": title, "url": src, "src": "commons", "duration": dur, "kind": "archive",
                        "credit": f"{title} - {artist or 'unknown'} - {lic} - {vi.get('descriptionurl', '')}"})
        return res
    return _search_many("Wikimedia video", queries, one)


def archive_candidates(queries):
    def one(q):
        url = "https://archive.org/advancedsearch.php?" + urllib.parse.urlencode(
            [("q", f"({q}) AND mediatype:(movies)"), ("fl[]", "identifier"), ("fl[]", "title"), ("fl[]", "licenseurl"),
             ("fl[]", "collection"), ("rows", "40"), ("output", "json")])
        data = http_json(url)
        res = []
        for d in (data.get("response") or {}).get("docs", []):
            lic = d.get("licenseurl") or ""
            cols = d.get("collection") or []
            cols = cols if isinstance(cols, list) else [cols]
            if not lic and "prelinger" in cols:  # the Prelinger Archives are public domain
                lic = "http://creativecommons.org/publicdomain/mark/1.0/"
            if not _lic_ok(lic):
                continue
            title = d.get("title") or d["identifier"]
            title = title[0] if isinstance(title, list) else title
            res.append({"title": str(title), "url": "ia:" + d["identifier"], "src": "archive.org", "kind": "archive", "lic": lic,
                        "credit": f"{title} - Internet Archive - {lic} - https://archive.org/details/{d['identifier']}"})
        return res
    return _search_many("Internet Archive", queries, one)


def _ia_file(ident):
    """The best mp4 of an Internet Archive item and its length."""
    meta = http_json("https://archive.org/metadata/" + urllib.parse.quote(ident), timeout=30)
    best = None
    for f in meta.get("files") or []:
        name, fmt = f.get("name", ""), (f.get("format") or "").lower()
        if not name.lower().endswith((".mp4", ".mpeg4", ".m4v", ".ogv", ".webm")):
            continue
        h = int(f.get("height") or 0)
        size = int(f.get("size") or 0)
        rank = (0 if "h.264" in fmt else 1, abs((h or 480) - 720), size)
        if best is None or rank < best[0]:
            ln = f.get("length") or "0"
            try:
                secs = float(ln) if ":" not in str(ln) else sum(float(x) * 60 ** i for i, x in enumerate(reversed(str(ln).split(":"))))
            except ValueError:
                secs = 0.0
            best = (rank, name, secs)
    if not best:
        raise ValueError("no video file")
    return f"https://archive.org/download/{urllib.parse.quote(ident)}/{urllib.parse.quote(best[1])}", best[2]


def pexels_candidates(queries):
    key = secret("pexels_key")
    if not key:
        return []

    def one(q):
        url = "https://api.pexels.com/videos/search?" + urllib.parse.urlencode({"query": q, "per_page": 15, "orientation": "landscape"})
        data = http_json(url, headers={"Authorization": key})
        res = []
        for v in data.get("videos") or []:
            files = [f for f in v.get("video_files") or [] if f.get("link") and int(f.get("width") or 0) >= 1200 and (f.get("file_type") or "").endswith("mp4")]
            if not files or float(v.get("duration") or 0) < 3:
                continue
            files.sort(key=lambda f: abs(int(f.get("width") or 0) - 1920))
            slug = re.sub(r"[-/]+", " ", (v.get("url") or "").rstrip("/").split("/")[-1])
            slug = re.sub(r"\d+$", "", slug).strip()
            user = (v.get("user") or {}).get("name", "unknown")
            res.append({"title": slug or q, "url": files[0]["link"], "src": "pexels", "duration": float(v.get("duration") or 0), "kind": "stock",
                        "credit": f"{slug or 'video'} - {user} on Pexels - Pexels License - {v.get('url', '')}"})
        return res
    return _search_many("Pexels", queries, one)


def pixabay_candidates(queries):
    key = secret("pixabay_key")
    if not key:
        return []

    def one(q):
        url = "https://pixabay.com/api/videos/?" + urllib.parse.urlencode({"key": key, "q": q[:95], "per_page": 20, "safesearch": "true"})
        data = http_json(url)
        res = []
        for h in data.get("hits") or []:
            vids = h.get("videos") or {}
            f = next((vids[k] for k in ("large", "medium") if (vids.get(k) or {}).get("url") and int((vids.get(k) or {}).get("width") or 0) >= 1200), None)
            if not f or float(h.get("duration") or 0) < 3:
                continue
            res.append({"title": h.get("tags") or q, "url": f["url"], "src": "pixabay", "duration": float(h.get("duration") or 0), "kind": "stock",
                        "credit": f"{h.get('tags', 'video')} - {h.get('user', 'unknown')} on Pixabay - Pixabay Content License - {h.get('pageURL', '')}"})
        return res
    return _search_many("Pixabay", queries, one)


VIDEO_SOURCES = {"archive": [("commons-video", commons_video_candidates), ("archive.org", archive_candidates)],
                 "stock": [("pexels", pexels_candidates), ("pixabay", pixabay_candidates)]}


def _clip_dir(key, c, W, H, fps):
    tag = "own" if c.get("src") == "own" else hashlib.sha1(c["url"].encode()).hexdigest()[:10]
    return A("clips", f"{key}__{tag}_{W}x{H}_{fps}")


def _cut_clip(c, out_dir, W, H, fps, start=None):
    """Cuts CLIP_SEC seconds of the clip into frames (JPEG) at the video's size. Returns the number of frames."""
    url, dur = c["url"], float(c.get("duration") or 0)
    if url.startswith("ia:"):
        url, dur2 = _ia_file(url[3:])
        dur = dur or dur2
    if start is None:
        if dur > CLIP_SEC + 1:
            # skip the opening (titles, black leader); start about a quarter in
            start = min(max(dur * 0.25, 2.0 if c.get("kind") == "archive" else 0.5), dur - CLIP_SEC - 0.5)
        else:
            start = 0.0
    tmp = out_dir + ".part"
    shutil.rmtree(tmp, ignore_errors=True)
    os.makedirs(tmp, exist_ok=True)
    cmd = [ffmpeg_exe(), "-v", "error", "-y"]
    if url.startswith("http"):
        cmd += ["-user_agent", UA["User-Agent"], "-rw_timeout", "60000000"]
    cmd += ["-ss", f"{start:.2f}", "-t", f"{CLIP_SEC:.2f}", "-i", url, "-an",
            "-vf", f"fps={fps},scale={W}:{H}:force_original_aspect_ratio=increase,crop={W}:{H},setsar=1", "-q:v", "3",
            os.path.join(tmp, "%04d.jpg")]
    r = subprocess.run(cmd, capture_output=True, timeout=300)
    frames = sorted(f for f in os.listdir(tmp) if f.endswith(".jpg"))
    if r.returncode != 0 or len(frames) < fps * 2:
        shutil.rmtree(tmp, ignore_errors=True)
        raise ValueError((r.stderr or b"").decode("utf-8", "replace")[-160:] or "too short")
    # reject black / blank footage (film leaders, fades) and frozen frames
    dark = 0
    sample = frames[:: max(1, len(frames) // 8)]
    prev, still = None, 0
    for f in sample:
        im = Image.open(os.path.join(tmp, f)).convert("L").resize((64, 36))
        a = np.asarray(im, np.float32)
        if a.mean() < 16:
            dark += 1
        if prev is not None and np.abs(a - prev).mean() < 0.6:
            still += 1
        prev = a
    if dark > len(sample) * 0.4:
        shutil.rmtree(tmp, ignore_errors=True)
        raise ValueError("mostly black")
    shutil.rmtree(out_dir, ignore_errors=True)
    os.replace(tmp, out_dir)
    _json_write(os.path.join(out_dir, "info.json"), {"n": len(frames), "fps": fps, "credit": c.get("credit", ""), "src": c.get("src"),
                                                     "kind": c.get("kind"), "start": start, "still": still > len(sample) * 0.7})
    return len(frames)


def _video_candidates(key, v, state):
    meta_p = A("clips", key + ".json")
    meta = _json_read(meta_p, {})
    q = _queries(v)
    if meta.get("candidates") and meta.get("q") == q and time.time() - meta.get("at", 0) < 14 * 86400:
        return meta["candidates"]
    want = v.get("source") or "any"
    order = (["archive", "stock"] if want in ("any", "archive") else ["stock", "archive"]) if want != "stock" else ["stock"]
    if want == "archive":
        order = ["archive"]
    found = []
    for group in order:
        for name, fn in VIDEO_SOURCES[group]:
            with state["lock"]:
                if name in state["dead"]:
                    continue
            try:
                got = fn(q)
            except SourceDown:
                with state["lock"]:
                    state["dead"].add(name)
                log(f"  {name}: not reachable, skipping it.")
                continue
            seen = {c["url"] for c in found}
            found += [c for c in got if c["url"] not in seen]
        if len([c for c in _rank_candidates(found, q) if not c.get("weak")]) >= 3:
            break
    qw = set()
    for x in q:
        qw |= _sig_words(x)
    ranked = []
    for c in _rank_candidates(found, q):
        c["weak"] = not (qw & _sig_words(c.get("title", ""))) if qw else False
        ranked.append(c)
    ranked.sort(key=lambda c: c["weak"])
    _json_write(meta_p, {"q": q, "at": time.time(), "candidates": ranked})
    return ranked


MAX_SHOT = 4.6   # seconds one visual may stay on screen
MAX_USES = 2     # how often the same picture/clip moment may appear in one video


def expand_visuals(script):
    """Every scene gets enough visuals that none stays longer than MAX_SHOT seconds.
    Extra slots reuse the scene's own searches: the engine then takes the NEXT picture/clip for that search,
    so they are new, real and on topic. Scenes with no picture search borrow the previous scene's searches."""
    added = 0
    last_pool = []
    backups = [{"type": "image", "search": [q], "backup": True} for q in backup_searches(script)]
    bk = 0
    for sc in script["scenes"]:
        say = sc.get("say") or ""
        est = 0.4 + len(say.split()) / 2.35 + 0.45 * max(1, len(split_sentences(say)))
        vis = sc.get("visuals") or ([sc["visual"]] if sc.get("visual") else [])
        need = max(1, math.ceil(est / MAX_SHOT))
        pool = [v for v in vis if v.get("type") in ("image", "video") and _queries(v)]
        if not pool and backups:  # a map / text scene: new real pictures of the story's places, not the last scene again
            pool = [backups[(bk + j) % len(backups)] for j in range(3)]
            bk += 3
        pool = pool or last_pool
        k = 0
        while len(vis) < need and pool:
            src = pool[k % len(pool)]
            nv = {kk: vv for kk, vv in src.items() if kk in ("type", "search", "source", "look", "year", "ai", "label", "backup")}
            nv["extra"] = True
            pos = min(len(vis), 1 + 2 * (k + 1))  # spread the new shots between the planned ones
            vis.insert(pos, nv)
            k += 1
            added += 1
        sc["visuals"] = vis
        sc.pop("visual", None)
        if pool:
            last_pool = [v for v in vis if v.get("type") in ("image", "video") and _queries(v)][-3:]
    log(f"  {added} extra shots planned so no picture stays longer than about 4-5 seconds")
    return added


VIDEO_REPORT = []


def resolve_videos(script, W, H, fps):
    """Finds a real clip for every "video" slide. A slide with no usable clip becomes a picture slide (same search)."""
    from concurrent.futures import ThreadPoolExecutor
    os.makedirs(A("clips"), exist_ok=True)
    slides = []
    for si, sc in enumerate(script["scenes"]):
        for v in (sc.get("visuals") or [sc.get("visual") or {}]):
            if v.get("type") == "video":
                slides.append((vid_key(v), v))
    if not slides:
        return []
    log(f"  {len(slides)} video slides")
    state = {"dead": set(), "lock": threading.Lock()}
    cands = {}
    with ThreadPoolExecutor(4) as ex:
        futs = {k: ex.submit(_video_candidates, k, v, state) for k, v in dict(slides).items()}
        for i, (k, f) in enumerate(futs.items(), 1):
            try:
                cands[k] = f.result()
            except Exception as e:
                log(f"    video search error: {str(e)[:80]}")
                cands[k] = []
            print(f"\r   searching clips {i}/{len(futs)}  ({i * 30 // max(1, len(futs))}%)", end="", flush=True)
    print()
    used, credits, got = set(), [], 0
    report = []
    seg_uses = {}
    for i, (key, v) in enumerate(slides, 1):
        print(f"\r   cutting clips {i}/{len(slides)}  ({30 + i * 20 // len(slides)}%)", end="", flush=True)
        own = next((A("clips_own", key + e) for e in (".mp4", ".mov", ".webm", ".mkv", ".m4v") if os.path.exists(A("clips_own", key + e))), None)
        pool = ([{"url": own, "src": "own", "kind": "own", "credit": v.get("credit") or ""}] if own else []) + \
               [c for c in cands.get(key, []) if not c.get("weak")] + [c for c in cands.get(key, []) if c.get("weak")][:1]
        done = None
        why = []
        for c in pool[:8]:
            if c["url"] in used:
                continue
            d = _clip_dir(key, c, W, H, fps)
            try:
                if not os.path.exists(os.path.join(d, "info.json")):
                    _cut_clip(c, d, W, H, fps, start=0.0 if c["src"] == "own" else None)
                done = (c, d)
                break
            except Exception as e:
                c["bad"] = True
                why.append(f"{c.get('src')}: {str(e)[:90]}")
        if not done:  # nothing new: show a LATER moment of a clip already cut for this search (max 3 moments per clip)
            for (k2, d2), n_used in list(seg_uses.items()):
                if k2 == key and n_used < 3:
                    info2 = _json_read(os.path.join(d2, "info.json"), {})
                    if int(info2.get("n") or 0) >= (n_used + 1) * MAX_SHOT * fps:
                        seg_uses[(k2, d2)] = n_used + 1
                        v["clip"] = os.path.relpath(d2, ROOT).replace(os.sep, "/")
                        v["clip_off"] = round(n_used * MAX_SHOT, 2)
                        v["clip_kind"] = info2.get("kind")
                        got += 1
                        report.append(f"OK    {' / '.join(_queries(v))}  ->  another moment of the same clip")
                        done = "segment"
                        break
            if done == "segment":
                continue
        if done:
            c, d = done
            used.add(c["url"])
            seg_uses[(key, d)] = 1
            info = _json_read(os.path.join(d, "info.json"), {})
            v["clip"] = os.path.relpath(d, ROOT).replace(os.sep, "/")
            v["clip_kind"] = c.get("kind") or info.get("kind")
            v["clip_src"] = c.get("src")
            if c.get("credit") and c["credit"] not in credits:
                credits.append(c["credit"])
            got += 1
            report.append(f"OK    {' / '.join(_queries(v))}  ->  {c.get('src')}: {c.get('title', '')[:70]}")
        else:
            v["type"] = "image"   # no footage: the same search as a picture
            v["was_video"] = True
            report.append(f"NONE  {' / '.join(_queries(v))}  ->  {len(cands.get(key, []))} found" + (" | " + " | ".join(why[:3]) if why else ""))
    print()
    log(f"  clips: {got} real clips, {len(slides) - got} slide(s) changed to pictures")
    dead = sorted(state["dead"])
    if dead:
        log("  clip websites not reachable: " + ", ".join(dead))
    if not secret("pexels_key") and not secret("pixabay_key"):
        log("  (no Pexels/Pixabay key: only archive footage was searched. Add the free keys in the app, Help tab.)")
    VIDEO_REPORT[:] = report
    return credits


# ------------------------------------------------------------------ the looks a clip can have

_GRAIN = {}


def _grain(W, H, k, amount=14):
    key = (W, H, k % 6, amount)
    if key not in _GRAIN:
        rng = np.random.default_rng(100 + k % 6)
        _GRAIN[key] = rng.normal(0, amount, (H // 2, W // 2)).astype(np.float32)
    g = _GRAIN[key]
    return np.repeat(np.repeat(g, 2, 0), 2, 1)[:H, :W]


def look_film(img, t, seed=0):
    """Old film: faded warm black-and-white-ish colour, grain, flicker, scratches, a little gate weave."""
    W, H = img.size
    a = np.asarray(img).astype(np.float32)
    lum = a @ np.array([0.299, 0.587, 0.114], np.float32)
    sep = np.stack([lum * 1.06, lum * 0.95, lum * 0.78], -1)
    a = a * 0.25 + sep * 0.75
    fl = 1 + 0.045 * math.sin(t * 23 + seed) * math.sin(t * 7.3)
    a = (a - 128) * 1.08 * fl + 128
    a += _grain(W, H, int(t * 24))[..., None]
    rng = random.Random(int(t * 24) + seed * 99)
    for _ in range(rng.randint(0, 2)):
        x = rng.randint(0, W - 1)
        a[:, x:x + max(1, W // 900)] += rng.choice((-70, 60))
    img = Image.fromarray(np.clip(a, 0, 255).astype(np.uint8))
    dx = int(round(math.sin(t * 9 + seed) * W / 1400))
    if dx:
        img = img.transform(img.size, Image.AFFINE, (1, 0, dx, 0, 1, 0), Image.BILINEAR)
    return vignette(img, 0.75)


def look_tv(img, t, seed=0):
    """Old TV: scanlines, colour fringes, rounded dark edges."""
    W, H = img.size
    r, g, b = img.split()
    sh = max(1, W // 640)
    r = r.transform(img.size, Image.AFFINE, (1, 0, -sh, 0, 1, 0))
    b = b.transform(img.size, Image.AFFINE, (1, 0, sh, 0, 1, 0))
    a = np.asarray(Image.merge("RGB", (r, g, b))).astype(np.float32)
    lines = (np.arange(H) % 3 == 0).astype(np.float32)[:, None, None]
    a = a * (1 - 0.22 * lines) + _grain(W, H, int(t * 25), 7)[..., None]
    roll = int((t * 40) % H)
    a[roll:roll + max(2, H // 90)] *= 1.18
    return vignette(Image.fromarray(np.clip(a, 0, 255).astype(np.uint8)), 0.9)


def look_rec(img, t, seed=0):
    """Camcorder: REC light, running timecode, corner marks, battery."""
    W, H = img.size
    s = W / 1920
    d = ImageDraw.Draw(img, "RGBA")
    m, L, w = int(70 * s), int(70 * s), max(2, int(4 * s))
    for (x, y, dx, dy) in ((m, m, 1, 1), (W - m, m, -1, 1), (m, H - m, 1, -1), (W - m, H - m, -1, -1)):
        d.line([(x, y), (x + dx * L, y)], fill=(255, 255, 255, 220), width=w)
        d.line([(x, y), (x, y + dy * L)], fill=(255, 255, 255, 220), width=w)
    f = font("Inter", int(40 * s), "SemiBold")
    if int(t * 2) % 2 == 0:
        d.ellipse([m + 30 * s, m + 34 * s, m + 62 * s, m + 66 * s], fill=(230, 40, 40, 255))
    d.text((m + 76 * s, m + 50 * s), "REC", font=f, fill=(255, 255, 255, 235), anchor="lm")
    tt = t + 3600 * 0 + seed * 7.3
    tc = f"00:{int(tt // 60) % 60:02d}:{int(tt) % 60:02d}:{int((tt % 1) * 25):02d}"
    d.text((m + 30 * s, H - m - 50 * s), tc, font=font("Inter", int(34 * s), "Medium"), fill=(255, 255, 255, 230), anchor="lm")
    bx, by = W - m - 150 * s, m + 32 * s
    d.rectangle([bx, by, bx + 100 * s, by + 36 * s], outline=(255, 255, 255, 230), width=w)
    d.rectangle([bx + 100 * s, by + 10 * s, bx + 110 * s, by + 26 * s], fill=(255, 255, 255, 230))
    d.rectangle([bx + 8 * s, by + 8 * s, bx + 70 * s, by + 28 * s], fill=(255, 255, 255, 230))
    return img


def look_glitch(img, t, seed=0):
    """Short digital glitches: colour split + sliced rows, a few times a second."""
    W, H = img.size
    rng = random.Random(int(t * 12) + seed * 31)
    if rng.random() > 0.35:
        return img
    r, g, b = img.split()
    sh = rng.randint(4, 14) * max(1, W // 1280)
    r = r.transform(img.size, Image.AFFINE, (1, 0, -sh, 0, 1, 0))
    b = b.transform(img.size, Image.AFFINE, (1, 0, sh, 0, 1, 0))
    img = Image.merge("RGB", (r, g, b))
    a = np.asarray(img).copy()
    for _ in range(rng.randint(1, 4)):
        y = rng.randint(0, H - 20)
        hgt = rng.randint(4, max(6, H // 30))
        a[y:y + hgt] = np.roll(a[y:y + hgt], rng.randint(-W // 20, W // 20), axis=1)
    return Image.fromarray(a)


LOOKS = {"film": look_film, "tv": look_tv, "rec": look_rec, "glitch": look_glitch}


def draw_tag(img, text, t, side="left"):
    """A small label in the corner: ARCHIVE FOOTAGE, 1969 / ILLUSTRATIVE."""
    if not text:
        return img
    W, H = img.size
    s = W / 1920
    a = ease_out((t - 0.3) / 0.5)
    if a <= 0:
        return img
    d = ImageDraw.Draw(img, "RGBA")
    f = font("Inter", int(26 * s), "SemiBold")
    tw_ = d.textlength(text, font=f)
    x = int(48 * s) if side == "left" else int(W - 48 * s - tw_ - 28 * s)
    y = int(H - 96 * s)
    d.rectangle([x, y, x + tw_ + 28 * s, y + 46 * s], fill=(0, 0, 0, int(150 * a)))
    d.rectangle([x, y, x + 4 * s, y + 46 * s], fill=RED + (int(255 * a),))
    d.text((x + 16 * s, y + 23 * s), text, font=f, fill=(240, 236, 228, int(240 * a)), anchor="lm")
    return img


class VideoScene(Scene):
    """A real moving clip, played at normal speed (a little slower if it is short), with a slow push-in and the chosen look."""

    def __init__(self, *a):
        super().__init__(*a)
        self.dir = A(self.v["clip"]) if self.v.get("clip") else None
        info = _json_read(os.path.join(self.dir, "info.json"), {}) if self.dir else {}
        self.fps = int(info.get("fps") or 25)
        n_all = int(info.get("n") or 0)
        self.off = max(0, min(int(float(self.v.get("clip_off") or 0) * self.fps), n_all - int(MAX_SHOT * self.fps)))
        self.n = max(0, n_all - self.off)
        self.cache = (None, None)
        kind = self.v.get("clip_kind") or info.get("kind")
        self.look = self.v.get("look") or ("film" if (kind == "archive" and int(self.v.get("year") or 3000) < 1975) else None)
        tag = self.v.get("caption")
        if tag is None:
            if kind == "archive":
                tag = "ARCHIVE FOOTAGE" + (f", {self.v['year']}" if self.v.get("year") else "")
            elif kind == "stock" and settings().get("label_stock", True) and self.v.get("label", True):
                tag = "ILLUSTRATIVE"
        self.tag = (tag or "").upper()

    def _frame(self, i):
        if self.cache[0] == i:
            return self.cache[1].copy()
        p = os.path.join(self.dir, f"{i + 1 + self.off:04d}.jpg")
        im = Image.open(p).convert("RGB")
        if im.size != (self.W, self.H):
            im = im.resize((self.W, self.H), Image.BILINEAR)
        self.cache = (i, im)
        return im.copy()

    def frame(self, t, dur):
        if not self.n:
            return dark_bg(self.W, self.H)
        need = dur * self.fps
        speed = 1.0 if self.n >= need else max(0.55, (self.n - 1) / max(1.0, need))
        i = min(self.n - 1, int(t * self.fps * speed))
        img = self._frame(i)
        z = 1 + 0.05 * clamp(t / max(1.0, dur))  # slow push-in keeps even calm clips moving
        if z > 1.001:
            cw, ch = self.W / z, self.H / z
            img = img.resize((self.W, self.H), Image.BILINEAR, box=((self.W - cw) / 2, (self.H - ch) / 2, (self.W + cw) / 2, (self.H + ch) / 2))
        if self.look in LOOKS:
            img = LOOKS[self.look](img, t, self.idx)
        else:
            img = Image.blend(img, grade(img), 0.55)
            img = vignette(img, 0.45)
        return draw_tag(img, self.tag, t)


SCENES["video"] = VideoScene


# ================================================================== documentary graphics: date cards, typed words, case files

def _fog_bg(W, H, t, seed=0):
    """Near-black background with slow drifting fog (made from cached noise, cheap)."""
    key = ("fog", W, H, seed, THEME["name"])
    if key not in _BG:
        rng = np.random.default_rng(seed + 40)
        n = rng.random((H // 40 + 3, W // 40 + 3)).astype(np.float32)
        n = Image.fromarray((n * 255).astype(np.uint8)).resize((W + W // 4, H + H // 4), Image.BICUBIC)
        n = np.asarray(n.filter(ImageFilter.GaussianBlur(max(4, W // 60)))).astype(np.float32) / 255
        n = (n - n.min()) / max(1e-3, n.max() - n.min())
        _BG[key] = n
    n = _BG[key]
    ox = int((math.sin(t * 0.15 + seed) * 0.5 + 0.5) * (W // 4))
    oy = int((math.cos(t * 0.11 + seed) * 0.5 + 0.5) * (H // 4))
    f = n[oy:oy + H, ox:ox + W]
    base = np.full((H, W, 3), 9, np.float32)
    tint = np.array([58, 62, 72] if THEME["name"] != "nature" else [40, 70, 100], np.float32)
    img = base + (f[..., None] ** 2) * tint * 0.65 + _grain(W, H, int(t * 12), 4)[..., None]
    return vignette(Image.fromarray(np.clip(img, 0, 255).astype(np.uint8)), 0.7)


class TypeScene(Scene):
    """Words typed out letter by letter with a blinking cursor.
    {"type":"date","text":"October 4, 2023","sub":"Hangzhou, China"}  -> calm date card
    {"type":"type","text":"SOCIAL MEDIA","sub":"optional small line"}    -> big typed word with a glitch at the end"""

    def frame(self, t, dur):
        W, H = self.W, self.H
        img = _fog_bg(W, H, t + self.idx * 3, self.idx % 3)
        d = ImageDraw.Draw(img, "RGBA")
        txt = str(self.v.get("text") or "")
        is_date = self.v.get("type") == "date"
        f = font("CourierPrime-Bold" if not is_date else "CourierPrime", self.S(118 if not is_date else 92))
        cps = max(10.0, len(txt) / max(0.6, min(1.3, dur * 0.4)))  # letters per second
        k = int(clamp((t - 0.15) * cps / max(1, len(txt))) * len(txt))
        shown = txt[:k]
        full_w = d.textlength(txt, font=f)
        x0, y = (W - full_w) / 2, H * (0.46 if self.v.get("sub") else 0.5)
        col = WHITE if is_date else (240, 240, 240)
        d.text((x0, y), shown, font=f, fill=col + (255,), anchor="lm")
        cx = x0 + d.textlength(shown, font=f) + self.S(6)
        if int(t * 2.4) % 2 == 0 or k < len(txt):
            d.rectangle([cx, y - f.size * 0.42, cx + self.S(10), y + f.size * 0.38], fill=(RED if not is_date else GOLD_L) + (230,))
        if self.v.get("sub") and k >= len(txt):
            a = ease_out((t - 0.15 - len(txt) / cps - 0.2) / 0.5)
            fs = font("Inter", self.S(40), "Medium")
            d.line([(W / 2 - self.S(70) * a, y + self.S(92)), (W / 2 + self.S(70) * a, y + self.S(92))], fill=GOLD + (int(220 * a),), width=self.S(3))
            d.text((W / 2, y + self.S(140)), str(self.v["sub"]).upper(), font=fs, fill=GREY + (int(235 * a),), anchor="mm")
        if not is_date and k >= len(txt):
            img = look_glitch(img, t, self.idx)
        return img


class CaseFileScene(Scene):
    """A case file on a dark desk: the card slides in, the facts type in one by one, then a red stamp slams on.
    {"type":"casefile","title":"CASE FILE 1983-114","fields":[["Name","..."],["Last seen","..."],["Place","..."]],"stamp":"MISSING"}"""

    def __init__(self, *a):
        super().__init__(*a)
        self._paper = None

    def paper(self, w, h):
        if self._paper is None:
            rng = np.random.default_rng(7)
            base = np.ones((h, w, 3), np.float32) * np.array([226, 214, 186], np.float32)
            n = rng.normal(0, 6, (h // 3 + 1, w // 3 + 1)).astype(np.float32)
            n = np.repeat(np.repeat(n, 3, 0), 3, 1)[:h, :w]
            yy, xx = np.mgrid[0:h, 0:w].astype(np.float32)
            stain = np.exp(-(((xx - w * 0.8) / (w * 0.25)) ** 2 + ((yy - h * 0.25) / (h * 0.3)) ** 2)) * 26
            base = base + n[..., None] - stain[..., None] * np.array([0.4, 0.7, 1.2])
            self._paper = Image.fromarray(np.clip(base, 0, 255).astype(np.uint8))
        return self._paper.copy()

    def frame(self, t, dur):
        W, H = self.W, self.H
        img = _fog_bg(W, H, t, 5)
        fields = [x for x in (self.v.get("fields") or []) if isinstance(x, (list, tuple)) and len(x) >= 2][:6]
        cw, ch = int(W * 0.56), int(H * 0.74)
        card = self.paper(cw, ch)
        d = ImageDraw.Draw(card, "RGBA")
        ink = (34, 30, 28)
        ft = font("SpecialElite", self.S(60))
        fl = font("CourierPrime-Bold", self.S(34))
        fv = font("SpecialElite", self.S(40))
        d.text((self.S(56), self.S(58)), str(self.v.get("title") or "CASE FILE").upper(), font=ft, fill=ink + (255,), anchor="lm")
        d.line([(self.S(56), self.S(104)), (cw - self.S(56), self.S(104))], fill=ink + (200,), width=self.S(3))
        per = max(0.35, (dur - 1.6) / max(1, len(fields)))
        y = self.S(160)
        for i, (lab, val) in enumerate(fields):
            st = 0.55 + i * per
            if t < st:
                break
            d.text((self.S(56), y), str(lab).upper() + ":", font=fl, fill=(110, 40, 34, 255), anchor="lm")
            val = str(val)
            k = int(clamp((t - st) / max(0.2, per * 0.7)) * len(val))
            lines = wrap(d, val[:k], fv, cw - self.S(380))[:2]
            for j, ln in enumerate(lines):
                d.text((self.S(330), y + j * self.S(46)), ln, font=fv, fill=ink + (255,), anchor="lm")
            y += self.S(76) + (len(lines) - 1) * self.S(46)
        # the stamp
        stamp = str(self.v.get("stamp") or "").upper()
        ts = 0.55 + len(fields) * per
        if stamp and t >= ts:
            k = clamp((t - ts) / 0.18)
            z = 1.9 - 0.9 * ease_out(k)
            fs = font("Anton", int(self.S(96) * z))
            sw = d.textlength(stamp, font=fs)
            lay = Image.new("RGBA", (int(sw + self.S(80)), int(fs.size * 1.6)), (0, 0, 0, 0))
            ld = ImageDraw.Draw(lay)
            ld.rounded_rectangle([self.S(8), self.S(8), lay.size[0] - self.S(8), lay.size[1] - self.S(8)], radius=self.S(14), outline=(178, 30, 30, int(230 * k)), width=max(3, self.S(9)))
            ld.text((lay.size[0] / 2, lay.size[1] / 2), stamp, font=fs, fill=(178, 30, 30, int(230 * k)), anchor="mm")
            lay = lay.rotate(-12, expand=True, resample=Image.BICUBIC)
            card.paste(lay, (int(cw * 0.62 - lay.size[0] / 2), int(ch * 0.74 - lay.size[1] / 2)), lay)
        # card slides up into place, slightly turned, with a shadow
        p = ease_out(t / 0.6)
        ang = -2.2 + 1.2 * clamp(t / max(1.0, dur))
        rc = card.convert("RGBA").rotate(ang, expand=True, resample=Image.BICUBIC)
        x = int((W - rc.size[0]) / 2)
        yv = int((H - rc.size[1]) / 2 + (1 - p) * H * 0.35)
        sh = Image.new("RGBA", rc.size, (0, 0, 0, 0))
        sh.putalpha(rc.getchannel("A").point(lambda a_: int(a_ * 0.6)))
        sh = sh.filter(ImageFilter.GaussianBlur(self.S(22)))
        img.paste((0, 0, 0), (x + self.S(16), yv + self.S(26)), sh)
        img.paste(rc, (x, yv), rc)
        if t < 0.18 + ts and t > ts and stamp:  # tiny shake on the stamp
            sx = int(math.sin(t * 90) * self.S(6) * (1 - (t - ts) / 0.18))
            img = img.transform(img.size, Image.AFFINE, (1, 0, sx, 0, 1, 0), Image.BILINEAR)
        return img


SCENES["date"] = TypeScene
SCENES["type"] = TypeScene
SCENES["casefile"] = CaseFileScene




TEXTY = ("text", "title", "quote", "stat", "type", "year", "bars", "timeline", "count")


def backup_searches(script):
    """Broad, real searches about the same story (its places, people, era) to fill gaps with NEW real pictures instead of repeats."""
    given = [q for q in (script.get("backup_searches") or []) if isinstance(q, str) and q.strip()]
    if given:
        return given
    cnt = {}
    for sc in script["scenes"]:
        for v in sc.get("visuals") or []:
            if v.get("type") in ("image", "video"):
                for w in re.findall(r"[A-Za-z][A-Za-z']{3,}", " ".join(_queries(v))):
                    if w.lower()[:5] in _STOP or w.lower() in _STOP:
                        continue
                    cnt[w] = cnt.get(w, 0) + (2 if w[0].isupper() else 1)
    words = [w for w, _ in sorted(cnt.items(), key=lambda x: -x[1])][:14]
    years = sorted({int(y) for sc in script["scenes"] for y in re.findall(r"\b(1[0-9]{3}|20[0-2][0-9])\b", str(sc.get("date", "")))})
    out = []
    for i, w in enumerate(words):
        out.append(w)
        if years and i < 6:
            out.append(f"{w} {years[min(i, len(years) - 1)]}")
    return out


def curate_visuals(script, final=True):
    """Before the video is made: only REAL, fitting visuals stay.
    - a slide whose picture/clip was not found is removed (never a text card with the search words)
    - the same picture is not shown again as a 'close-up' when the scene has anything else
    - text slides are kept rare (about 1 per 90 seconds); real pictures and clips carry the video
    The narration stays the same: the remaining visuals simply stay on screen longer, still moving."""
    scenes = script["scenes"]
    words = sum(len((sc.get("say") or "").split()) for sc in scenes)
    minutes = max(1.0, words / 140)
    text_budget = max(3, int(minutes / 1.5))
    real = lambda v: (v.get("type") == "image" and v.get("file")) or (v.get("type") == "video" and v.get("clip")) or v.get("type") in ("map", "date", "casefile")
    shot = lambda v: (v.get("type") == "image" and v.get("file")) or (v.get("type") == "video" and v.get("clip"))
    # which text slides to keep: the punchy ones ("hit") first, then spread evenly
    texts = [(si, j, v) for si, sc in enumerate(scenes) for j, v in enumerate(sc.get("visuals") or []) if v.get("type") in TEXTY]
    texts.sort(key=lambda x: (0 if x[2].get("hit") else 1, x[0]))
    keep_text, last = set(), []
    for si, j, v in texts:
        if len(keep_text) >= text_budget:
            break
        if any(abs(si - k) < max(2, len(scenes) // (text_budget + 1)) for k in last):
            continue
        keep_text.add(id(v))
        last.append(si)
    dropped = {"missing": 0, "repeat": 0, "text": 0}
    used_files = {}
    prev_real = None
    backups = backup_searches(script) if not final else []
    bi = [0]
    recent = []

    def backup_slot():
        q = backups[bi[0] % len(backups)]
        bi[0] += 1
        return {"type": "image", "search": [q], "extra": True, "backup": True}
    for sc in scenes:
        vis = sc.get("visuals") or ([sc["visual"]] if sc.get("visual") else [])
        out = []
        for v in vis:
            t = v.get("type")
            if t == "image" and not v.get("file"):
                dropped["missing"] += 1
                if backups and not v.get("backup"):
                    out.append(backup_slot())
                continue
            if t == "image" and used_files.get(v.get("file"), 0) >= MAX_USES:
                dropped["repeat"] += 1
                if backups and not v.get("backup"):
                    out.append(backup_slot())
                continue
            if t == "image" and v.get("recut"):
                if any(real(x) for x in vis if x is not v and not x.get("recut")):
                    dropped["repeat"] += 1
                    continue
            if t in TEXTY and id(v) not in keep_text and (any(real(x) for x in vis if x is not v) or prev_real is not None):
                dropped["text"] += 1
                continue
            if t == "image":
                used_files[v["file"]] = used_files.get(v["file"], 0) + 1
            out.append(v)
        if not out and prev_real is not None:  # nothing real here: a recent real shot that may still be used, never a text card
            cand = [x for x in reversed(recent) if x.get("type") == "video" or used_files.get(x.get("file"), 0) < MAX_USES]
            v2 = dict(cand[0] if cand else prev_real)
            if v2.get("type") == "image":
                used_files[v2["file"]] = used_files.get(v2["file"], 0) + 1
            if v2.get("type") == "image":
                v2["recut"] = int(v2.get("recut") or 0) + 1
            v2.pop("caption", None)
            out = [v2]
        for v in out:
            if shot(v):
                prev_real = v
                recent = (recent + [v])[-8:]
        if out:
            sc["visuals"] = out
            sc.pop("visual", None)
    if final:
        log(f"  visuals checked: {sum(dropped.values())} removed ({dropped['missing']} not found, {dropped['repeat']} repeats, {dropped['text']} extra text slides)")
    else:
        log(f"  {bi[0]} gaps will get new real pictures from broader searches ({', '.join(backups[:6])}...)")
    return bi[0] if not final else sum(dropped.values())


def next_picture(key):
    """Switch an image slide to the next candidate (used by the app's Pictures screen)."""
    meta_p = A("images", key + ".json")
    meta = _json_read(meta_p, {})
    cands = meta.get("candidates") or []
    if not cands:
        raise ValueError("No other pictures found for this slide.")
    k = (int(meta.get("choice", 0)) + 1) % len(cands)
    c = cands[k]
    fn = f"{key}__{hashlib.sha1(c['url'].encode()).hexdigest()[:10]}.jpg"
    if not os.path.exists(A("images", fn)):
        _download_to(c["url"], A("images", fn))
    shutil.copyfile(A("images", fn), A("images", key + ".jpg"))
    meta.update(choice=k, credit=c["credit"], source=c.get("src", "commons"), first_file=fn)
    _json_write(meta_p, meta)
    return c


def _json_read(p, default):
    try:
        with open(p, encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return default


def _json_write(p, d):
    os.makedirs(os.path.dirname(p), exist_ok=True)
    tmp = p + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(d, f, ensure_ascii=False, indent=1)
    os.replace(tmp, p)


# ------------------------------------------------------------------ thumbnail, description, captions file

def make_thumbnail(script, plan_, out_dir):
    th = script.get("thumbnail") or {}
    beats = plan_["beats"]
    # background: the chosen beat, or the first real picture, or the first map
    pick = None
    if "beat" in th:
        pick = beats[min(int(th["beat"]), len(beats) - 1)]
    if pick is None:
        pick = next((b for b in beats if b["visual"].get("type") == "image" and b["visual"].get("file")), None) or \
            next((b for b in beats if b["visual"].get("type") == "map"), beats[0])
    v = dict(pick["visual"])
    if v.get("type") == "map":
        v = {**v, "points": [], "labels": [], "route": v.get("route")}
        for r in v.get("regions") or []:
            r["label"] = ""
    cls = SCENES.get(v.get("type", "title"), TitleScene)
    bg = cls({"visual": v}, 1920, 1080, pick["i"]).frame(min(pick["dur"], 30) * 0.9, max(pick["dur"], 1)).resize((1280, 720), Image.LANCZOS)
    img = bg.convert("RGBA")
    grad = Image.new("L", (1280, 720), 0)
    gd = ImageDraw.Draw(grad)
    for x in range(1280):
        gd.line([(x, 0), (x, 720)], fill=int(235 * clamp(1 - x / 860) ** 1.2))
    img.paste(Image.new("RGBA", (1280, 720), (8, 8, 10, 255)), (0, 0), grad)
    img = img.convert("RGB")
    # Midnight Archive style: white line(s) on top, last line black on a yellow box
    lines = (th.get("text") or script.get("title", "")).upper().split("\n")
    longest = max(len(x) for x in lines)
    size = 150 if longest <= 11 else 124 if longest <= 14 else 104
    f = font("Oswald", size, "Bold")
    d = ImageDraw.Draw(img)
    lh = int(size * 1.05)
    total = lh * len(lines) + 40
    y = (720 - total) // 2
    for i, ln in enumerate(lines):
        bb = d.textbbox((0, 0), ln, font=f)
        if i == len(lines) - 1:
            w, h = bb[2] - bb[0], bb[3] - bb[1]
            y += 12
            d = ImageDraw.Draw(img)
            d.rectangle([56, y, 56 + w + 36, y + h + 42], fill=(255, 213, 74))
            d.text((56 + 18 - bb[0], y + 18 - bb[1]), ln, font=f, fill=(12, 12, 12))
        else:
            shadow_text(img, (66 - bb[0], y - bb[1]), ln, f, (245, 240, 230), blur=8, alpha=230)
            d = ImageDraw.Draw(img)
            y += lh
    img.save(os.path.join(out_dir, "thumbnail.jpg"), quality=93)


# ------------------------------------------------------------------ 3 thumbnails (A/B/C) from the real pictures, in the channel's style

YELLOW = (255, 213, 74)


def _pictures_used(pl):
    seen = {}
    for b in pl["beats"]:
        v = b["visual"]
        if v.get("type") == "image" and v.get("file") and not v.get("recut") and os.path.exists(A("images", v["file"])) and not v["file"].endswith("__ai.jpg"):
            if v["file"] not in seen:
                seen[v["file"]] = {"file": v["file"], "faces": v.get("faces") or [], "scene": b["scene"], "t": b["start"],
                                   "words": _sig_words(" ".join(_queries(v)) + " " + (v.get("caption") or ""))}
    return list(seen.values())


def _face_area(p):
    return max([(f[2] - f[0]) * (f[3] - f[1]) for f in p["faces"]] or [0])


def _pick_picture(concept, pool, used, total):
    cands = [p for p in pool if p["file"] not in used] or pool
    if not cands:
        return None
    want = _sig_words(concept.get("picture", ""))
    if want:
        best = max(cands, key=lambda p: (len(want & p["words"]), _face_area(p)))
        if want & best["words"]:
            return best
    style = concept.get("style", "face")

    def score(p):
        early = 1.25 if p["t"] < total * 0.3 else 1.0
        return (_face_area(p) * 10 + 0.01) * early if style in ("face", "circle") else (0.5 + _face_area(p) * 3) * early
    return max(cands, key=score)


def _tone(im):
    """Old black & white prints become warm parchment; colour pictures get a dark cinematic grade."""
    small = im.resize((64, 64))
    hsv = np.asarray(small.convert("HSV")).astype(np.float32)
    if hsv[..., 1].mean() < 30:  # an engraving or old photo
        g = np.asarray(ImageOps.grayscale(im)).astype(np.float32) / 255
        lo, hi = np.percentile(g, 3), np.percentile(g, 97)
        g = np.clip((g - lo) / max(0.05, hi - lo), 0, 1) ** 1.12
        p_, k_ = np.array([192, 152, 100], np.float32), np.array([14, 10, 8], np.float32)
        rgb = k_ + (p_ - k_) * g[..., None]
        return Image.fromarray(np.clip(rgb, 0, 255).astype(np.uint8))
    a = np.asarray(im.convert("RGB")).astype(np.float32) / 255
    lum = a.mean(-1, keepdims=True)
    a = a * 0.85 + lum * 0.15
    a = np.clip((a - 0.5) * 1.22 + 0.5, 0, 1)
    a = a * np.array([1.06, 0.98, 0.88]) + (1 - lum) ** 3 * np.array([0.0, 0.02, 0.05])
    return Image.fromarray((np.clip(a, 0, 1) * 255).astype(np.uint8))


def _fit_text(lines, max_w, max_size=168, min_size=84, max_h=620):
    d = ImageDraw.Draw(Image.new("RGB", (10, 10)))
    size = max_size
    while size > min_size:
        f = font("Oswald", size, "Bold")
        ok = True
        for i, ln in enumerate(lines):
            w = d.textbbox((0, 0), ln, font=f)[2] + (36 if i == len(lines) - 1 else 10)
            if w > max_w:
                ok = False
                break
        if ok and size * 1.08 * len(lines) + 60 < max_h:
            break
        size -= 6
    return size


def brand_text(img, lines, x0=52, max_w=560, y_mid=None):
    """White line(s) on top, the last line black in a yellow box (the Midnight Archive look)."""
    W, H = img.size
    lines = [ln.strip().upper() for ln in lines if ln.strip()][:3] or ["?"]
    size = _fit_text(lines, max_w, max_size=210 if H > W else 168, max_h=H * 0.36 if H > W else 620)
    f = font("Oswald", size, "Bold")
    d = ImageDraw.Draw(img)
    lh = int(size * 1.08)
    total = lh * (len(lines) - 1) + size + 56
    y = int((y_mid if y_mid is not None else H / 2) - total / 2)
    for i, ln in enumerate(lines):
        bb = d.textbbox((0, 0), ln, font=f)
        w, h = bb[2] - bb[0], bb[3] - bb[1]
        if i == len(lines) - 1:
            y += 16
            d.rectangle([x0, y, x0 + w + 36, y + h + 40], fill=YELLOW)
            d.text((x0 + 18 - bb[0], y + 17 - bb[1]), ln, font=f, fill=(12, 12, 12))
        else:
            lay = Image.new("RGBA", (W, H), (0, 0, 0, 0))
            ImageDraw.Draw(lay).text((x0 + 8 - bb[0], y - bb[1] + 6), ln, font=f, fill=(0, 0, 0, 255))
            lay = lay.filter(ImageFilter.GaussianBlur(10))
            img.paste(lay, (0, 0), lay)
            d = ImageDraw.Draw(img)
            d.text((x0 + 8 - bb[0], y - bb[1]), ln, font=f, fill=(245, 240, 230))
            y += lh
    return img


def _face_box_px(faces, iw, ih, head=True):
    if not faces:
        return None
    x0, y0 = min(f[0] for f in faces), min(f[1] for f in faces)
    x1, y1 = max(f[2] for f in faces), max(f[3] for f in faces)
    w, h = x1 - x0, y1 - y0
    if head:
        x0, x1, y0, y1 = x0 - 0.3 * w, x1 + 0.3 * w, y0 - 0.5 * h, y1 + 0.35 * h
    return (max(0, x0) * iw, max(0, y0) * ih, min(1, x1) * iw, min(1, y1) * ih)


def render_thumb(path, faces, lines, style="face", W=1280, H=720, vertical=False):
    """One thumbnail. Picture on the right (faces whole and big), text on the left. vertical=True makes a Shorts cover."""
    im = _tone(Image.open(path).convert("RGB"))
    iw, ih = im.size
    lines = [ln.strip().upper() for ln in lines if ln.strip()][:3] or ["?"]
    if vertical and len(faces) > 1:  # a tall cover: one big face is stronger than two small ones
        faces = [max(faces, key=lambda f: (f[2] - f[0]) * (f[3] - f[1]))]
    if style == "circle" and not faces:
        style = "face"
    text_w = 0
    if not vertical:
        size = _fit_text(lines, 560)
        f_ = font("Oswald", size, "Bold")
        dd = ImageDraw.Draw(Image.new("RGB", (8, 8)))
        text_w = max(dd.textbbox((0, 0), ln, font=f_)[2] + (36 if i == len(lines) - 1 else 10) for i, ln in enumerate(lines))
    canvas = im.resize((max(1, iw // 8), max(1, ih // 8))).filter(ImageFilter.GaussianBlur(3))
    sc0 = max(W / canvas.width, H / canvas.height)
    canvas = canvas.resize((int(canvas.width * sc0) + 2, int(canvas.height * sc0) + 2), Image.BILINEAR).crop((0, 0, W, H))
    canvas = Image.blend(canvas, Image.new("RGB", (W, H), (8, 7, 6)), 0.55)
    if vertical:
        rx0, rw, cy_t = 0, W, 0.52
    else:
        rx0 = int(min(W * 0.52, max(W * 0.36, 52 + text_w + 28)))
        rw, cy_t = W - rx0, 0.46
    fb = _face_box_px(faces, iw, ih)
    cover = max(rw / iw, H / ih)
    if fb:
        fw, fh = fb[2] - fb[0], fb[3] - fb[1]
        k = min((0.66 if style != "circle" else 0.56) * H / fh, 0.94 * rw / fw)
        if vertical:
            k = min(0.34 * H / fh, 0.92 * W / fw)
        k = max(k, min(cover, 0.94 * rw / fw, 0.94 * H / fh))
        fcx, fcy = (fb[0] + fb[2]) / 2 * k, (fb[1] + fb[3]) / 2 * k
        tx, ty = rx0 + rw * 0.52, H * cy_t
    else:
        k = cover * 1.04
        fcx, fcy = iw * 0.5 * k, ih * 0.42 * k
        tx, ty = rx0 + rw / 2, H * 0.45
    pic = im.resize((max(1, int(iw * k)), max(1, int(ih * k))), Image.LANCZOS)
    ox, oy = int(tx - fcx), int(ty - fcy)
    # keep the picture covering its area when it is big enough
    if pic.width >= rw:
        ox = min(max(ox, rx0 + rw - pic.width), rx0)
    if pic.height >= H:
        oy = min(max(oy, H - pic.height), 0)
    if fb:  # ...but never push the face out of the frame
        fx0, fy0, fx1, fy1 = fb[0] * k + ox, fb[1] * k + oy, fb[2] * k + ox, fb[3] * k + oy
        if fx1 > W - 10:
            ox -= int(fx1 - (W - 10))
        if fy0 < 6:
            oy += int(6 - fy0)
        if fy1 > H - 6:
            oy -= int(fy1 - (H - 6))
        if not vertical and fx0 < rx0 - 10:
            ox += int(rx0 - 10 - fx0)
    # soft edges wherever the picture doesn't reach the frame edge (no hard paper borders)
    mask = np.full((pic.height, pic.width), 255.0, np.float32)
    fe = 150
    for side, inside in (("l", ox > 0), ("r", ox + pic.width < W), ("t", oy > 0), ("b", oy + pic.height < H)):
        if not inside and not (side == "l" and not vertical and ox > -fe):
            continue
        ramp = (np.arange(fe, dtype=np.float32) / fe) ** 1.3 * 255
        if side == "l":
            n_ = min(fe, pic.width)
            mask[:, :n_] = np.minimum(mask[:, :n_], ramp[:n_][None, :])
        elif side == "r":
            n_ = min(fe, pic.width)
            mask[:, -n_:] = np.minimum(mask[:, -n_:], ramp[:n_][::-1][None, :])
        elif side == "t":
            n_ = min(fe, pic.height)
            mask[:n_, :] = np.minimum(mask[:n_, :], ramp[:n_][:, None])
        else:
            n_ = min(fe, pic.height)
            mask[-n_:, :] = np.minimum(mask[-n_:, :], ramp[:n_][::-1][:, None])
    canvas.paste(pic, (ox, oy), Image.fromarray(mask.astype(np.uint8)))
    arr = np.asarray(canvas).astype(np.float32)
    yy, xx = np.mgrid[0:H, 0:W].astype(np.float32)
    if vertical:  # darker top and bottom for the text
        g = np.clip(1 - np.abs(yy / H - 0.42) / 0.42, 0, 1)
        dark = 1 - 0.75 * (1 - g) ** 1.6
        arr *= dark[..., None]
    else:
        k_ = np.clip(1 - xx / (W * 0.62), 0, 1) ** 1.25 * (250 / 255)
        arr = arr * (1 - k_[..., None]) + np.array([6, 5, 4]) * k_[..., None]
    v = np.sqrt(((xx - W / 2) / (W / 2)) ** 2 + ((yy - H / 2) / (H / 2)) ** 2) / 1.42
    arr *= np.clip(1 - 0.55 * np.clip((v - 0.38) / 0.62, 0, 1) ** 1.4, 0, 1)[..., None]
    if style == "dark":
        arr = np.clip((arr / 255 - 0.5) * 1.15 + 0.5, 0, 1) * 255 * np.array([1.0, 0.94, 0.9])
    img = Image.fromarray(np.clip(arr, 0, 255).astype(np.uint8))
    if style == "circle":
        d = ImageDraw.Draw(img)
        if fb:
            cx, cy = (fb[0] + fb[2]) / 2 * k + ox, (fb[1] + fb[3]) / 2 * k + oy
            r = max(fb[2] - fb[0], fb[3] - fb[1]) * k * 0.62
        else:
            cx, cy, r = tx, ty, H * 0.22
        r = max(70, min(r, H * 0.42))
        d.ellipse([cx - r, cy - r * 1.08, cx + r, cy + r * 1.08], outline=(226, 36, 28), width=12)
    if vertical:
        return brand_text(img, lines, x0=60, max_w=W - 120, y_mid=H * 0.2)
    return brand_text(img, lines, max_w=560)


# ------------------------------------------------------------------ documentary thumbnails (v4): cut-out subject, glow, big white + red words

THUMB_RED = (226, 30, 24)
_REMBG = {}


def cutout(path):
    """The main subject without its background (RGBA), using rembg when it is installed (the cloud installs it). None if not possible."""
    key = path + "|cut"
    if key in _REMBG:
        return _REMBG[key]
    res = None
    try:
        os.environ.setdefault("U2NET_HOME", A("models", "rembg"))
        from rembg import new_session, remove
        if "s" not in _REMBG:
            _REMBG["s"] = new_session("isnet-general-use")
        im = Image.open(path).convert("RGB")
        im.thumbnail((1600, 1600))
        out = remove(im, session=_REMBG["s"])
        a = np.asarray(out.getchannel("A")).astype(np.float32) / 255
        cover = float((a > 0.5).mean())
        if 0.06 < cover < 0.75:  # a real subject, not empty and not the whole picture
            res = out
    except Exception as e:
        log(f"   (cut-out not available: {str(e)[:60]})")
    _REMBG[key] = res
    return res


def doc_text(img, lines, red=None, x0=56, max_w=600, y_mid=None, align="left"):
    """Huge condensed words, white with a deep shadow; the key word in red with a red bar under the last line."""
    W, H = img.size
    lines = [ln.strip().upper() for ln in lines if ln.strip()][:3] or ["?"]
    red = (red or "").strip().upper()
    if not red:  # the most important word: the longest in the last line
        red = max(lines[-1].split(), key=len)
    d = ImageDraw.Draw(img)
    size = 230 if H > W else 190
    while size > 70:
        f = font("Anton", size)
        if all(d.textlength(ln, font=f) <= max_w for ln in lines) and size * 1.05 * len(lines) < (H * 0.42 if H > W else H * 0.78):
            break
        size -= 6
    f = font("Anton", size)
    lh = int(size * 1.04)
    total = lh * len(lines)
    y = int((y_mid if y_mid is not None else H / 2) - total / 2)
    sh = Image.new("RGBA", (W, H), (0, 0, 0, 0))
    sd = ImageDraw.Draw(sh)
    pos = []
    for ln in lines:
        w = d.textlength(ln, font=f)
        x = x0 if align == "left" else (W - w) / 2
        pos.append((x, y, ln, w))
        sd.text((x + 6, y + 10), ln, font=f, fill=(0, 0, 0, 235))
        y += lh
    sh = sh.filter(ImageFilter.GaussianBlur(max(6, size // 14)))
    img.paste(sh, (0, 0), sh)
    d = ImageDraw.Draw(img)
    for x, y_, ln, w in pos:
        cx = x
        for wi, word in enumerate(ln.split(" ")):
            col = THUMB_RED if re.sub(r"[^A-Z0-9]", "", word) == re.sub(r"[^A-Z0-9]", "", red) else (250, 248, 242)
            d.text((cx, y_), word, font=f, fill=col, stroke_width=max(2, size // 40), stroke_fill=(10, 8, 8))
            cx += d.textlength(word + " ", font=f)
    x, y_, ln, w = pos[-1]
    bot = d.textbbox((x, y_), ln, font=f, stroke_width=max(2, size // 40))[3]
    gap = max(8, size // 12)
    d.rectangle([x, bot + gap, x + min(w, size * 2.2), bot + gap + max(8, size // 14)], fill=THUMB_RED)
    return img


def _grade_thumb(im, style):
    a = np.asarray(im.convert("RGB")).astype(np.float32) / 255
    lum = a @ np.array([0.299, 0.587, 0.114], np.float32)
    a = a * 0.7 + lum[..., None] * 0.3  # a little less colour
    a = np.clip((a - 0.5) * 1.25 + 0.5, 0, 1)
    shadows = (1 - lum) ** 2
    a = a + shadows[..., None] * np.array([-0.02, 0.01, 0.05])  # cold shadows
    if style == "dark":
        a = a * 0.8
    return Image.fromarray((np.clip(a, 0, 1) * 255).astype(np.uint8))


def render_thumb_doc(path, faces, lines, style="face", red=None, W=1280, H=720, vertical=False):
    """Documentary thumbnail. With a person: cut out, big, with a white rim and red glow over a dark blurred copy.
    Without: the picture full-bleed with a cinematic grade. Text: huge white words, one red word."""
    src = Image.open(path).convert("RGB")
    cut = cutout(path) if faces and style in ("face", "circle") else None
    bg = _grade_thumb(src, style)
    sc = max(W / bg.width, H / bg.height)
    bgf = bg.resize((int(bg.width * sc) + 2, int(bg.height * sc) + 2), Image.LANCZOS)
    ox, oy = (bgf.width - W) // 2, (bgf.height - H) // 2
    if faces and not cut:
        fb = _face_box_px(faces, bg.width, bg.height)
        if fb:  # keep the face in the right half
            fcx = (fb[0] + fb[2]) / 2 * sc
            ox = int(clamp(fcx - W * (0.5 if vertical else 0.68), 0, bgf.width - W))
            oy = int(clamp((fb[1] + fb[3]) / 2 * sc - H * 0.42, 0, bgf.height - H))
    canvas = bgf.crop((ox, oy, ox + W, oy + H))
    if cut is not None:
        canvas = canvas.filter(ImageFilter.GaussianBlur(14))
        canvas = Image.blend(canvas, Image.new("RGB", (W, H), (6, 6, 8)), 0.55)
    arr = np.asarray(canvas).astype(np.float32)
    yy, xx = np.mgrid[0:H, 0:W].astype(np.float32)
    if vertical:
        dark = np.clip(1 - np.abs(yy / H - 0.55) / 0.55, 0, 1)
        arr *= (1 - 0.7 * (1 - dark) ** 1.5)[..., None]
    else:  # dark on the text side
        k_ = np.clip(1 - xx / (W * 0.62), 0, 1) ** 1.3 * 0.92
        arr = arr * (1 - k_[..., None]) + np.array([5, 5, 7]) * k_[..., None]
    v = np.sqrt(((xx - W / 2) / (W / 2)) ** 2 + ((yy - H / 2) / (H / 2)) ** 2) / 1.42
    arr *= np.clip(1 - 0.6 * np.clip((v - 0.35) / 0.65, 0, 1) ** 1.3, 0, 1)[..., None]
    img = Image.fromarray(np.clip(arr, 0, 255).astype(np.uint8))
    if cut is not None:
        c = cut
        cw0, ch0 = c.size
        bb = c.getchannel("A").point(lambda a_: 255 if a_ > 40 else 0).getbbox() or (0, 0, cw0, ch0)
        c = c.crop(bb)
        target_h = H * (0.66 if vertical else 1.02)
        k = min(target_h / c.height, (W * (0.95 if vertical else 0.58)) / c.width)
        c = c.resize((max(1, int(c.width * k)), max(1, int(c.height * k))), Image.LANCZOS)
        c = Image.merge("RGBA", (*_grade_thumb(c.convert("RGB"), style).split(), c.getchannel("A")))
        x = int((W - c.width) / 2) if vertical else int(W - c.width - W * 0.02)
        y = int(H - c.height) if not vertical else int(max(H * 0.30, H * 0.91 - c.height))
        alpha = c.getchannel("A")
        # red glow, then a thin white rim, then the person
        glow = Image.new("RGBA", (W, H), (0, 0, 0, 0))
        ga = Image.new("L", (W, H), 0)
        ga.paste(alpha.filter(ImageFilter.MaxFilter(9)), (x, y))
        glow.putalpha(ga.filter(ImageFilter.GaussianBlur(28)).point(lambda a_: int(a_ * 0.85)))
        red_layer = Image.new("RGBA", (W, H), THUMB_RED + (0,))
        red_layer.putalpha(glow.getchannel("A"))
        img.paste(red_layer, (0, 0), red_layer)
        rim = Image.new("L", (W, H), 0)
        rim.paste(alpha.filter(ImageFilter.MaxFilter(7)), (x, y))
        img.paste((245, 245, 245), (0, 0), rim)
        img.paste(c, (x, y), c)
        cut_map = (cw0, ch0, bb, k, x, y)  # to find the face again on the cut-out
    if style == "circle":
        d = ImageDraw.Draw(img)
        if faces:
            f0 = max(faces, key=lambda f: (f[2] - f[0]) * (f[3] - f[1]))
            if cut is not None:
                cw0, ch0, bb, k, x, y = cut_map
                cx = ((f0[0] + f0[2]) / 2 * cw0 - bb[0]) * k + x
                cy = ((f0[1] + f0[3]) / 2 * ch0 - bb[1]) * k + y
                r = max((f0[2] - f0[0]) * cw0, (f0[3] - f0[1]) * ch0) * k * 0.75
            else:
                cx = (f0[0] + f0[2]) / 2 * bg.width * sc - ox
                cy = (f0[1] + f0[3]) / 2 * bg.height * sc - oy
                r = max(f0[2] - f0[0], f0[3] - f0[1]) * bg.width * sc * 0.7
        else:
            cx, cy, r = W * 0.7, H * 0.45, H * 0.22
        r = max(70, min(r, H * 0.4))
        for w_, col in ((16, (0, 0, 0)), (11, THUMB_RED)):
            d.ellipse([cx - r, cy - r * 1.06, cx + r, cy + r * 1.06], outline=col, width=w_)
    if vertical:
        return doc_text(img, lines, red, x0=60, max_w=W - 120, y_mid=H * 0.18, align="center")
    return doc_text(img, lines, red, max_w=W * 0.5)


def _auto_concepts(script, pl):
    th = script.get("thumbnail") or {}
    title = script.get("title", "")
    a = (th.get("text") or " ".join(title.split()[:4])).upper()
    money = [p["text"] for p in pl.get("pops", []) if p.get("kind") == "money"]
    nums = sorted(money, key=lambda x: -len(re.sub(r"\D", "", x)))
    b = (nums[0] + "?") if nums else ""
    hits = []
    for x in pl["beats"]:
        v = x["visual"]
        if v.get("type") == "text" and v.get("hit"):
            t_ = " ".join(v.get("lines") or [])
            if 6 <= len(t_) <= 24:
                hits.append(v.get("lines"))
    c = "\n".join(hits[0]) if hits else ""
    out = [{"text": a, "style": "face"}]
    out.append({"text": b or ("\n".join(hits[1]) if len(hits) > 1 else a), "style": "dark"})
    out.append({"text": c or a, "style": "circle"})
    return out


def make_thumbnails(script, pl, out_dir):
    pool = _pictures_used(pl)
    concepts = [dict(c) for c in (script.get("thumbnails") or [])][:3]
    auto = _auto_concepts(script, pl)
    while len(concepts) < 3:
        concepts.append(auto[len(concepts)])
    styles = ("face", "dark", "circle")
    used, made = set(), []
    names = ("thumbnail.jpg", "thumbnail_B.jpg", "thumbnail_C.jpg")
    for i, c in enumerate(concepts):
        c.setdefault("style", styles[i])
        lines = (c.get("text") or "?").replace("\\n", "\n").split("\n")
        if len(lines) == 1 and len(lines[0].split()) >= 2:
            w_ = lines[0].split()
            cut = max(1, len(w_) // 2)
            lines = [" ".join(w_[:cut]), " ".join(w_[cut:])]
        p = _pick_picture(c, pool, used, pl["total"])
        try:
            if p:
                used.add(p["file"])
                if settings().get("thumb_style", "doc") == "doc":
                    img = render_thumb_doc(A("images", p["file"]), p["faces"], lines, c["style"], red=c.get("red"))
                else:
                    img = render_thumb(A("images", p["file"]), p["faces"], lines, c["style"])
            else:
                raise ValueError("no picture")
        except Exception as e:
            log(f"   thumbnail {'ABC'[i]}: no real picture ({str(e)[:50]}), using a slide instead")
            img = _slide_thumb(script, pl, lines)
        img.save(os.path.join(out_dir, names[i]), quality=94)
        made.append((names[i], "\n".join(lines), p["file"] if p else ""))
    titles = [t for t in (script.get("titles") or []) if t][:3]
    if len(titles) < 3:
        titles = ([script["title"]] if script.get("title") and script["title"] not in titles else []) + titles
    titles = (titles + [c.get("title", "") for c in concepts] + [script.get("title", "")] * 3)[:3]
    with open(os.path.join(out_dir, "titles.txt"), "w", encoding="utf-8") as f:
        f.write("THREE THUMBNAILS + THREE TITLES (YouTube Studio > Test & compare)\n\n")
        for i, (n_, txt, pic) in enumerate(made):
            ttl = (concepts[i].get("title") or (titles[i] if i < len(titles) else "")) or script.get("title", "")
            f.write(f"{'ABC'[i]}: {n_}\n   Thumbnail text: {txt.replace(chr(10), ' / ')}\n   Title: {ttl}  ({len(ttl)} characters)\n\n")
    log(f"   3 thumbnails made: {', '.join(n for n, _, _ in made)}")


def _slide_thumb(script, pl, lines):
    """Backup thumbnail when a video has no real pictures: a map or slide from the video."""
    beats = pl["beats"]
    pick = next((b for b in beats if b["visual"].get("type") == "map"), beats[0])
    v = dict(pick["visual"])
    if v.get("type") == "map":
        v = {**v, "points": [], "labels": []}
    cls = SCENES.get(v.get("type", "title"), TitleScene)
    bg = cls({"visual": v}, 1920, 1080, pick["i"]).frame(min(pick["dur"], 30) * 0.9, max(pick["dur"], 1)).resize((1280, 720), Image.LANCZOS)
    arr = np.asarray(bg).astype(np.float32)
    xx = np.arange(1280, dtype=np.float32)
    k_ = np.clip(1 - xx / 800, 0, 1) ** 1.2 * 0.9
    arr = arr * (1 - k_)[None, :, None]
    return brand_text(Image.fromarray(arr.astype(np.uint8)), lines)


def fmt_ts(t):
    t = int(t)
    return f"{t // 3600}:{t % 3600 // 60:02d}:{t % 60:02d}" if t >= 3600 else f"{t // 60}:{t % 60:02d}"


def srt_t(x):
    ms = int(round(x * 1000))
    return f"{ms // 3600000:02d}:{ms % 3600000 // 60000:02d}:{ms % 60000 // 1000:02d},{ms % 1000:03d}"


def _credit_parts(c):
    """'title - author - licence - url' -> (author, licence, url)"""
    c = c.strip()
    m = re.match(r"(.+?\.(?:jpe?g|png|tiff?|webp|gif)) - (.*) - (.+?) - (\S+)$", c, re.I)
    if m:
        return m.group(2).strip(), m.group(3).strip(), m.group(4)
    parts = c.rsplit(" - ", 2)
    if len(parts) == 3:
        rest, lic, url = parts
        author = rest.split(" - ", 1)[1] if " - " in rest else ""
        return author.strip(), lic.strip(), url
    return "", c, ""


def _needs_credit(lic):
    return bool(re.search(r"\bBY\b|BY-SA|CC BY", lic, re.I)) and not re.search(r"public domain|cc0|\bpd\b", lic, re.I)


def write_texts(script, pl, credits, out_dir):
    chapters, last = [], None
    for b in pl["beats"]:
        if b["chapter"] and b["chapter"] != last:
            chapters.append((b["start"], b["chapter"]))
            last = b["chapter"]
    if chapters:
        chapters[0] = (0, chapters[0][1])
    # chapters must be at least 10 seconds apart for YouTube
    clean = []
    for t, c in chapters:
        if clean and t - clean[-1][0] < 10:
            continue
        clean.append((t, c))
    channel = script.get("channel") or settings().get("channel_name") or "Midnight Archive"
    lines = []
    if script.get("description"):
        lines += [script["description"], ""]
    if len(clean) >= 3:
        lines += ["Chapters"] + [f"{fmt_ts(t)} {c}" for t, c in clean] + [""]
    lines += [script.get("subscribe_line") or f"Subscribe to {channel} for the true stories history tried to forget.", ""]
    if script.get("sources"):
        src = script["sources"]
        lines += ["Sources: " + (src if isinstance(src, str) else "; ".join(src)), ""]
    if str(script.get("voice", "")).lower() not in ("none", "silent", "own", "own-recording"):
        lines += ["Narration uses an AI voice. Maps and graphics are made for this video."]
    # short credit list (who must be named), the full list goes in credits.txt
    names, seen = [], set()
    for c in credits:
        author, lic, url = _credit_parts(c)
        if c.startswith("AI-generated"):
            continue
        if _needs_credit(lic):
            k = (author or "unknown") + " (" + lic + ")"
            if k not in seen:
                seen.add(k)
                names.append(k)
    if names:
        lines += ["", "Image credits (Wikimedia Commons and others):"] + names + ["All other images are public domain or CC0. Full list: credits.txt"]
    tags = [t for t in (script.get("tags") or []) if t]
    hashtags = script.get("hashtags") or ["#" + re.sub(r"[^A-Za-z0-9]", "", t.title()) for t in tags[:3]]
    if hashtags:
        lines += ["", " ".join(h if h.startswith("#") else "#" + h for h in hashtags[:3])]
    desc = "\n".join(lines)
    if len(desc) > 4800:  # YouTube's limit is 5,000
        keep = [ln for ln in lines if ln not in names]
        desc = "\n".join(keep)[:4800]
    with open(os.path.join(out_dir, "description.txt"), "w", encoding="utf-8") as f:
        f.write(desc)
    with open(os.path.join(out_dir, "credits.txt"), "w", encoding="utf-8") as f:
        f.write("Pictures used in this video\n\n" + "\n".join(credits) + "\n")
    tag_line, n_ = [], 0
    for t in tags:
        if n_ + len(t) + 2 > 480:
            break
        tag_line.append(t)
        n_ += len(t) + 2
    with open(os.path.join(out_dir, "tags.txt"), "w", encoding="utf-8") as f:
        f.write(", ".join(tag_line))
    with open(os.path.join(out_dir, "captions.srt"), "w", encoding="utf-8") as f:
        for i, ln in enumerate(pl["lines"], 1):
            f.write(f"{i}\n{srt_t(ln['start'])} --> {srt_t(ln['end'])}\n{' '.join(w[2] for w in ln['words'])}\n\n")
    if script.get("pinned_comment"):
        with open(os.path.join(out_dir, "pinned_comment.txt"), "w", encoding="utf-8") as f:
            f.write(script["pinned_comment"])


# ------------------------------------------------------------------ main build

def load_script(path):
    with open(path, encoding="utf-8") as f:
        s = json.load(f)
    if not s.get("scenes"):
        raise ValueError("This script has no scenes.")
    return s


def settings():
    return _json_read(A("settings.json"), {})


def ensure_models():
    os.makedirs(A("models"), exist_ok=True)
    for path, url in MODEL_URLS.items():
        if os.path.exists(path) and os.path.getsize(path) > 1_000_000:
            continue
        log(f"Downloading the AI voice ({os.path.basename(path)}), one time only...")
        tmp = path + ".part"
        with urllib.request.urlopen(urllib.request.Request(url, headers=UA), timeout=300) as r, open(tmp, "wb") as f:
            total = int(r.headers.get("Content-Length") or 0)
            got = 0
            while True:
                b = r.read(1 << 20)
                if not b:
                    break
                f.write(b)
                got += len(b)
                if total:
                    print(f"\r  {got * 100 // total}%", end="", flush=True)
        print()
        os.replace(tmp, path)


def encode(cmd_tail, frames_iter, W, H, fps, audio_wav, out, music=None, music_vol=0.12, crf="20", norm=True):
    cmd = [ffmpeg_exe(), "-y", "-v", "error", "-f", "rawvideo", "-pix_fmt", "rgb24", "-s", f"{W}x{H}", "-r", str(fps), "-i", "-", "-i", audio_wav]
    if music:
        cmd += ["-stream_loop", "-1", "-i", music, "-filter_complex",
                f"[2:a]volume={music_vol},aformat=sample_rates=48000:channel_layouts=stereo[m];[1:a]aformat=sample_rates=48000:channel_layouts=stereo[v];[v][m]amix=inputs=2:duration=first:normalize=0[a]",
                "-map", "0:v", "-map", "[a]"]
    else:
        cmd += ["-map", "0:v", "-map", "1:a"]
    if not music and norm:  # YouTube plays everything at about -14 LUFS: match it so the voice is never quiet
        cmd += ["-af", "loudnorm=I=-14:TP=-1.5:LRA=11,aresample=48000"]
    cmd += ["-c:v", "libx264", "-preset", "veryfast", "-crf", crf, "-pix_fmt", "yuv420p", "-c:a", "aac", "-b:a", "192k", "-shortest", "-movflags", "+faststart", out]
    ff = subprocess.Popen(cmd, stdin=subprocess.PIPE)
    for fr in frames_iter:
        ff.stdin.write(fr)
    ff.stdin.close()
    ff.wait()
    if ff.returncode != 0:
        raise RuntimeError("ffmpeg could not make the video.")


def build(script_path, preview=False, captions=None):
    t0 = time.time()
    script = load_script(script_path)
    apply_theme(script.get("theme"))
    cfg = settings()
    name = os.path.splitext(os.path.basename(script_path))[0]
    W, H, fps = (960, 540, 15) if preview else (1920, 1080, int(script.get("fps", 25)))
    if captions is None:
        captions = bool(cfg.get("captions_on_long", False))
    out_dir = A("output", name + ("-preview" if preview else ""))
    os.makedirs(out_dir, exist_ok=True)
    log(f"\n== {script.get('title', name)} ==")
    try:
        ensure_models()
    except Exception as e:
        log(f"  couldn't download the offline voice ({e}); using the online voice instead.")
    log("STEP 1/4 Pictures and clips")
    set_era(script)
    expand_visuals(script)
    vcredits = resolve_videos(script, W, H, fps)
    credits, missing = resolve_pictures(script, use_ai=cfg.get("ai_pictures", True))
    if curate_visuals(script, final=False):  # gaps and repeats -> new real pictures from broader searches
        credits, missing = resolve_pictures(script, use_ai=False)
    credits = vcredits + [c for c in credits if c not in vcredits]
    curate_visuals(script)
    if missing:
        log(f"  {len(missing)} slide(s) without a picture use a gold title card instead.")
    log("STEP 2/4 Voice")
    own = own_voice_file(name)
    if own:
        script["_own_voice"] = own
        script["voice"] = "own-recording"
    pl, track = plan(script)
    wav = os.path.join(out_dir, "narration.wav")
    write_wav(wav, track)
    pl.update(title=script.get("title", ""), fps=fps, W=W, H=H, shorts=script.get("shorts") or [], voice_name=script.get("voice", "bm_george"),
              speed=script.get("speed", 0.95), script=os.path.basename(script_path), tags=script.get("tags") or [],
              channel=script.get("channel") or cfg.get("channel_name") or "Midnight Archive", theme=script.get("theme") or DEFAULT_THEME)
    plan_path = os.path.join(out_dir, "timeline.json")
    _json_write(plan_path, pl)
    nframes = int(pl["total"] * fps)
    log(f"   video length {fmt_ts(pl['total'])}  ({nframes} frames, {len(pl['beats'])} visuals, {len(pl['pops'])} callouts)")
    log("STEP 3/4 Frames (the long part)")
    music_dir = A("music")
    music = [os.path.join(music_dir, x) for x in sorted(os.listdir(music_dir)) if x.lower().endswith((".mp3", ".wav", ".m4a", ".ogg"))] if os.path.isdir(music_dir) else []
    procs = max(1, min(cpu_count() - 1, 6))
    state = {"last": 0}

    def frames():
        with Pool(procs, initializer=_init_worker, initargs=(plan_path, W, H, fps, captions)) as pool:
            for i, fr in enumerate(pool.imap(render_frame, range(nframes), chunksize=6)):
                yield fr
                if time.time() - state["last"] > 2 or i == nframes - 1:
                    print(f"\r   {i + 1}/{nframes} frames  ({(i + 1) * 100 // nframes}%)", end="", flush=True)
                    state["last"] = time.time()
        print()

    mp4 = os.path.join(out_dir, "video.mp4")
    silent = str(script.get("voice", "")).lower() in ("none", "silent", "own")
    encode(None, frames(), W, H, fps, wav, mp4, None, 0, "28" if preview else "20", norm=not silent)
    log("STEP 4/4 Thumbnail prompts, description, captions")
    if cfg.get("thumb_mode", "prompt") == "images":
        try:
            make_thumbnails(script, pl, out_dir)
        except Exception as e:
            log(f"   (3 thumbnails failed: {str(e)[:80]}; making the simple one)")
            make_thumbnail(script, pl, out_dir)
    else:
        try:
            write_thumbnail_prompts(script, pl, out_dir)
        except Exception as e:
            log(f"   (thumbnail prompts failed: {str(e)[:80]})")
    write_texts(script, pl, credits, out_dir)
    if VIDEO_REPORT:
        with open(os.path.join(out_dir, "clips_report.txt"), "w", encoding="utf-8") as f:
            f.write("REAL CLIPS: what was found for every video slide\n\n" + "\n".join(VIDEO_REPORT) + "\n")
    if silent:
        with open(os.path.join(out_dir, "voiceover_guide.txt"), "w", encoding="utf-8") as f:
            f.write("VOICE-OVER GUIDE: say each line at the time shown (the video has no voice, only music)\n\n")
            last = -1
            for snt in pl["sentences"]:
                if snt["scene"] != last:
                    sc_ = script["scenes"][snt["scene"]]
                    f.write(f"\n--- {sc_.get('chapter') or ''} ---\n" if sc_.get("chapter") else "\n")
                    last = snt["scene"]
                f.write(f"[{fmt_ts(snt['start'])} - {fmt_ts(snt['end'])}]  {snt['text']}\n")
        log("   voiceover_guide.txt written (no AI voice in this video)")
    save_pictures(script, out_dir)
    log(f"\nDONE in {int(time.time() - t0) // 60} min. Your video is here:\n  {out_dir}")
    return out_dir


def save_pictures(script, out_dir):
    """Copy the real pictures used in this video to output/<name>/pictures (for making thumbnails later)."""
    try:
        d = os.path.join(out_dir, "pictures")
        os.makedirs(d, exist_ok=True)
        n, seen = 0, set()
        for sc in script.get("scenes", []):
            for v in (sc.get("visuals") or [sc.get("visual") or {}]):
                if v.get("type") != "image":
                    continue
                fn = v.get("file") or ""
                src = A("images", fn)
                if not fn or fn in seen or not os.path.exists(src):
                    continue
                seen.add(fn)
                key = os.path.splitext(fn)[0]
                im = Image.open(src).convert("RGB")
                im.thumbnail((2000, 2000))
                im.save(os.path.join(d, key + ".jpg"), quality=88)
                n += 1
        log(f"  saved {n} pictures in the 'pictures' folder (for thumbnails)")
    except Exception as e:
        log(f"  (couldn't save the pictures folder: {e})")


# ================================================================== SHORTS: 3-4 vertical clips from a finished long video

HOOK_WORDS = re.compile(r"\b(but|never|only|richest|biggest|secret|crash|crashed|twist|died|lost|first|nobody|everyone|impossible|billion|million|gold|war|fell|borrow|debt)\b", re.I)


def pick_shorts(pl, n=4, min_len=38, max_len=50):
    """Each Short is 40-50 seconds in the end (the clip + the 'full video' ending), and always ends on a full sentence."""
    sents = pl["sentences"]
    manual = []
    for s in pl.get("shorts") or []:
        a, b = int(s.get("from_scene", 0)), int(s.get("to_scene", s.get("from_scene", 0)))
        idx = [i for i, x in enumerate(sents) if a <= x["scene"] <= b]
        if not idx:
            continue
        i0 = idx[0]

        def miss(j):  # how far this ending is from the 41-47 s window (+ a small cost for leaving the planned scenes)
            dd = sents[j]["end"] - sents[i0]["start"]
            return max(0, min_len - dd, dd - max_len) + 0.2 * abs(j - idx[-1]) ** 0.5

        i1 = min(range(i0, min(len(sents), i0 + 40)), key=miss)
        manual.append({"start": max(0, sents[i0]["start"] - 0.15), "end": sents[i1]["end"] + 0.4, "hook": s.get("hook", ""),
                       "title": s.get("title", ""), "comment": s.get("comment", "")})
    if manual:
        return manual[:n]
    cands = []
    for i, s in enumerate(sents):
        end_i = i
        while end_i + 1 < len(sents) and sents[end_i + 1]["end"] - s["start"] <= max_len:
            end_i += 1
        dur = sents[end_i]["end"] - s["start"]
        if dur < min_len:
            continue
        txt = " ".join(x["text"] for x in sents[i:end_i + 1])
        score = 3 * len(HOOK_WORDS.findall(s["text"])) + len(HOOK_WORDS.findall(txt)) + 2 * len(NUM_RE.findall(txt))
        score += 4 if (i == 0 or sents[i - 1]["scene"] != s["scene"]) else 0
        cands.append((score, s["start"], sents[end_i]["end"] + 0.4, s["text"]))
    cands.sort(key=lambda c: -c[0])
    out = []
    for sc, a, b, first in cands:
        if all(b <= o["start"] or a >= o["end"] for o in out):
            out.append({"start": max(0, a - 0.15), "end": b, "hook": " ".join(first.split()[:7]).rstrip(",.") + "...", "title": ""})
        if len(out) >= n:
            break
    return sorted(out, key=lambda o: o["start"])


def make_shorts(out_dir, n=1):
    pl = _json_read(os.path.join(out_dir, "timeline.json"), None)
    if pl:
        apply_theme(pl.get("theme"))
        sc_ = _json_read(A("scripts", pl.get("script") or ""), {}) if pl.get("script") else {}
        if (sc_.get("summary_short") or {}).get("say"):
            try:
                ensure_models()
            except Exception:
                pass
            return make_summary_short(out_dir, sc_)
        n = 1  # no summary in this script: one Short from the strongest moment
    if not pl:
        raise ValueError("This folder has no timeline.json. Make the long video with this engine first.")
    src = os.path.join(out_dir, "video.mp4")
    if not os.path.exists(src):
        raise ValueError("video.mp4 not found in " + out_dir)
    sdir = os.path.join(out_dir, "shorts")
    os.makedirs(sdir, exist_ok=True)
    try:
        ensure_models()
    except Exception:
        pass
    voice = Voice({"voice": pl.get("voice_name", "bm_george"), "speed": pl.get("speed", 0.95)})
    cta_text = "The full story is on the channel."
    try:
        cta = voice.say(cta_text)
    except Exception:
        cta = np.zeros(int(SR * 1.5), np.float32)
    segs = pick_shorts(pl, n)
    W, H, fps = 1080, 1920, 25
    info = []
    for k, seg in enumerate(segs, 1):
        log(f"Short {k}/{len(segs)}: {fmt_ts(seg['start'])} - {fmt_ts(seg['end'])}")
        dur = seg["end"] - seg["start"]
        cta_dur = len(cta) / SR + 0.9
        total = dur + cta_dur
        # audio: the clip + the call to action
        a = subprocess.run([ffmpeg_exe(), "-v", "error", "-ss", f"{seg['start']:.3f}", "-t", f"{dur:.3f}", "-i", src, "-f", "f32le", "-ac", "1", "-ar", str(SR), "-"], capture_output=True, check=True)
        clip = np.frombuffer(a.stdout, np.float32).copy()
        clip = np.concatenate([clip, np.zeros(max(0, int(dur * SR) - len(clip)), np.float32)])[:int(dur * SR)]
        fade = int(SR * 0.25)
        clip[-fade:] *= np.linspace(1, 0, fade)
        tail = np.concatenate([np.zeros(int(SR * 0.3), np.float32), cta * 0.95, np.zeros(int(SR * 0.6), np.float32)])
        wav = os.path.join(sdir, f"short_{k}.wav")
        write_wav(wav, np.concatenate([clip, tail]))
        lines = []
        for snt in pl["sentences"]:
            if snt["end"] <= seg["start"] or snt["start"] >= seg["end"]:
                continue
            ws = [[w[0] - seg["start"], w[1] - seg["start"], w[2]] for w in pl["words"] if snt["start"] - 0.01 <= w[0] < snt["end"] + 0.01 and seg["start"] <= w[0] < seg["end"]]
            for ln in group_lines(ws, max_chars=18, max_words=4):
                lines.append({"start": ln[0][0], "end": ln[-1][1], "words": ln})
        hook = (seg.get("hook") or pl.get("title", "")).upper()
        # designed cover (also the first frame, so YouTube's frame picker can use it)
        cover = None
        try:
            pics = []
            for b in pl["beats"]:
                v = b["visual"]
                if v.get("type") == "image" and v.get("file") and b["start"] < seg["end"] and b["start"] + b["dur"] > seg["start"] and os.path.exists(A("images", v["file"])):
                    pics.append(v)
            if not pics:
                pics = [b["visual"] for b in pl["beats"] if b["visual"].get("type") == "image" and b["visual"].get("file") and os.path.exists(A("images", b["visual"]["file"]))][:1]
            if pics:
                best = max(pics, key=lambda v: max([(f[2] - f[0]) * (f[3] - f[1]) for f in (v.get("faces") or [])] or [0]))
                words = re.sub(r"[.…]+$", "", hook).split()
                cut = max(1, (len(words) + 1) // 2)
                cl = [" ".join(words[:cut]), " ".join(words[cut:])] if len(words) > 2 else [" ".join(words)]
                cover = (render_thumb_doc(A("images", best["file"]), best.get("faces") or [], cl, "face", W=1080, H=1920, vertical=True)
                         if settings().get("thumb_style", "doc") == "doc" else render_thumb(A("images", best["file"]), best.get("faces") or [], cl, "face", W=1080, H=1920, vertical=True))
                d_ = ImageDraw.Draw(cover)
                d_.text((540, 1800), (pl.get("channel") or "MIDNIGHT ARCHIVE").upper(), font=font("Oswald", 40, "Medium"), fill=(235, 228, 214), anchor="mm")
                cover.save(os.path.join(sdir, f"short_{k}_cover.jpg"), quality=93)
        except Exception as e:
            log(f"   (cover for short {k} failed: {str(e)[:60]})")
            cover = None
        dec = subprocess.Popen([ffmpeg_exe(), "-v", "error", "-ss", f"{seg['start']:.3f}", "-t", f"{dur:.3f}", "-i", src, "-vf", f"scale=1080:608,fps={fps}",
                                "-f", "rawvideo", "-pix_fmt", "rgb24", "-"], stdout=subprocess.PIPE)
        nclip = int(dur * fps)

        def frames():
            last = None
            for i in range(int(total * fps)):
                t = i / fps
                if i < nclip:
                    raw = dec.stdout.read(1080 * 608 * 3)
                    if raw and len(raw) == 1080 * 608 * 3:
                        last = Image.frombytes("RGB", (1080, 608), raw)
                fr = short_frame(last, t, dur, total, hook, lines, pl.get("title", ""))
                if cover is not None and t < 0.8:  # open on the cover, then melt into the clip
                    z = 1 + 0.03 * t
                    cv = cover.resize((int(1080 * z), int(1920 * z)), Image.BILINEAR).crop((int((1080 * z - 1080) / 2), int((1920 * z - 1920) / 2), int((1080 * z - 1080) / 2) + 1080, int((1920 * z - 1920) / 2) + 1920))
                    fr = cv if t < 0.55 else Image.blend(cv, fr, ease((t - 0.55) / 0.25))
                yield fr.tobytes()
                if i % 50 == 0:
                    done = ((k - 1) + i / max(1, total * fps)) / len(segs)
                    print(f"\r   short {k}/{len(segs)}  ({int(done * 100)}%)", end="", flush=True)

        out = os.path.join(sdir, f"short_{k}.mp4")
        try:
            encode(None, frames(), W, H, fps, wav, out)
        finally:
            try:
                dec.stdout.close()
                dec.kill()
            except Exception:
                pass
            dec.wait()
        os.remove(wav)
        title = seg.get("title") or (hook.title().rstrip(".") + " #shorts")
        tags = [t for t in (pl.get("tags") or []) if t][:2]
        hs = " ".join("#" + re.sub(r"[^A-Za-z0-9]", "", t.title()) for t in tags) or "#history"
        info.append(f"SHORT {k}  ({fmt_ts(seg['start'])}-{fmt_ts(seg['end'])} of the long video)\n"
                    f"File: short_{k}.mp4   Cover: short_{k}_cover.jpg (it is also the first frame)\n"
                    f"Title: {title}\n"
                    f"Description: {seg.get('hook') or pl.get('title', '')} The full documentary is on the channel. {hs} #shorts\n"
                    f"Pinned comment: {seg.get('comment') or 'Did you know this before? Tell me below.'}\n"
                    f"In YouTube Studio > this Short > 'Related video': pick the long video.\n")
    with open(os.path.join(sdir, "shorts.txt"), "w", encoding="utf-8") as f:
        f.write("\n".join(info))
    log(f"\nDONE. {len(segs)} shorts in:\n  {sdir}")
    return sdir


# ================================================================== ONE SUMMARY SHORT: the whole story in 45-55 seconds, full-screen vertical

def _short_shots(pl, n):
    """The best real shots of the long video, spread over the whole story, in order."""
    shots = []
    seen = set()
    for b in pl["beats"]:
        v = b["visual"]
        if v.get("type") == "image" and v.get("file") and not v.get("recut") and os.path.exists(A("images", v["file"])):
            k = v["file"]
            score = 2 + 3 * max([(f[2] - f[0]) * (f[3] - f[1]) for f in (v.get("faces") or [])] or [0])
        elif v.get("type") == "video" and v.get("clip") and os.path.exists(os.path.join(A(v["clip"]), "info.json")):
            k = v["clip"] + "|" + str(v.get("clip_off") or 0)
            score = 4
        else:
            continue
        if k in seen:
            continue
        seen.add(k)
        shots.append((b["start"], score, v))
    if not shots:
        return []
    shots.sort(key=lambda x: x[0])
    out = []
    for i in range(n):  # one per part of the story, the strongest in each part
        lo, hi = len(shots) * i // n, max(len(shots) * (i + 1) // n, len(shots) * i // n + 1)
        part = shots[lo:hi] or shots[-1:]
        out.append(max(part, key=lambda x: x[1])[2])
    return out


class VShot:
    """One vertical full-screen shot from a picture or a clip: sharp middle band over its own blurred copy, slow push-in."""

    def __init__(self, v, W=1080, H=1920):
        self.v, self.W, self.H = v, W, H
        self.clip = None
        if v.get("type") == "video":
            self.clip = VideoScene({"visual": dict(v)}, 1920, 1080, 0)
            self.img = None
        else:
            im = Image.open(A("images", v["file"])).convert("RGB")
            im.thumbnail((2400, 2400))
            self.img = grade(im)
        self.faces = v.get("faces") or []

    def _src(self, t, dur):
        if self.clip is not None:
            return self.clip.frame(t, dur)
        return self.img

    def frame(self, t, dur):
        W, H = self.W, self.H
        src = self._src(t, dur)
        iw, ih = src.size
        p = clamp(t / max(dur, 0.1))
        # background: the same shot, blurred and dark
        k = max(W / iw, H / ih)
        bg = src.resize((max(1, int(iw * k / 8)), max(1, int(ih * k / 8))), Image.BILINEAR).filter(ImageFilter.GaussianBlur(4))
        bg = bg.resize((int(iw * k) + 2, int(ih * k) + 2), Image.BILINEAR)
        bx, by = (bg.width - W) // 2, (bg.height - H) // 2
        img = Image.blend(bg.crop((bx, by, bx + W, by + H)), Image.new("RGB", (W, H), (6, 6, 8)), 0.5)
        # foreground: fills the full width, 70% of the height, centred on the face if there is one
        fh = int(H * 0.70)
        z = 1.0 + 0.07 * ease_io(p)
        k2 = max(W / iw, fh / ih) * z
        fw_full, fh_full = iw * k2, ih * k2
        if self.faces:
            f0 = max(self.faces, key=lambda f: (f[2] - f[0]) * (f[3] - f[1]))
            cx, cy = (f0[0] + f0[2]) / 2 * fw_full, (f0[1] + f0[3]) / 2 * fh_full
        else:
            cx, cy = fw_full * (0.5 + 0.06 * math.sin(p * 2)), fh_full * 0.45
        x0 = clamp(cx - W / 2, 0, max(0, fw_full - W))
        y0 = clamp(cy - fh / 2, 0, max(0, fh_full - fh))
        box = (x0 / k2, y0 / k2, (x0 + W) / k2, (y0 + fh) / k2)
        fg = src.resize((W, fh), Image.BILINEAR, box=box)
        top = int(H * 0.15)
        img.paste(fg, (0, top))
        return vignette(img, 0.5)


def make_summary_short(out_dir, script):
    """ONE Short that tells the whole story in about 50 seconds, with its own narration and the best real shots."""
    pl = _json_read(os.path.join(out_dir, "timeline.json"), None)
    if not pl:
        raise ValueError("Make the long video first.")
    apply_theme(pl.get("theme"))
    ss = script.get("summary_short") or {}
    say = (ss.get("say") or "").strip()
    sdir = os.path.join(out_dir, "shorts")
    os.makedirs(sdir, exist_ok=True)
    vname = pl.get("voice_name") or "saim"
    if vname in ("none", "silent", "own", "own-recording"):
        vname = "saim"  # your own voice isn't there for the summary: Saim tells it
    voice = Voice({"voice": vname, "speed": pl.get("speed", 0.95)})
    sents = split_sentences(say)
    parts, words, sentences, t = [np.zeros(int(SR * 0.25), np.float32)], [], [], 0.25
    for s_ in sents:
        a = voice.say(s_)
        d = len(a) / SR
        words += word_times(s_, t, t + d)
        sentences.append({"start": t, "end": t + d, "text": s_})
        g = 0.45 if s_.rstrip().endswith(("?", "...", "…")) else 0.22
        parts += [a, np.zeros(int(SR * g), np.float32)]
        t += d + g
    speech_end = t
    end_card = 2.6
    total = speech_end + end_card
    speech = np.concatenate(parts)
    speech = np.concatenate([speech, np.zeros(int(total * SR) - len(speech) + 10, np.float32)])[:int(total * SR)]
    # music: the story's mood, quiet under the voice
    mood = next((m for _, _, m in (pl.get("moods") or [])), "mystery")
    try:
        music = _fill(mood, len(speech), 7)
        env = np.abs(speech)
        k_ = int(SR * 0.3)
        env = np.convolve(env, np.ones(k_, np.float32) / k_, mode="same")
        duck = 1 - 0.75 * np.clip(env / (env.max() * 0.25 + 1e-6), 0, 1)
        mix = speech + music[:len(speech)] * 0.16 * duck
    except Exception:
        mix = speech
    nshots = max(8, int(round(speech_end / 3.0)))
    shots = _short_shots(pl, nshots)
    if not shots:
        raise ValueError("No real pictures in the long video to use.")
    seg = speech_end / len(shots)
    for i in range(1, len(shots)):  # a whoosh on every cut
        k = int((i * seg - 0.18) * SR)
        w = whoosh(0.35, i) * 0.12
        if 0 <= k < len(mix) - len(w):
            mix[k:k + len(w)] += w
    pk = float(np.max(np.abs(mix))) or 1
    wav = os.path.join(sdir, "short_1.wav")
    write_wav(wav, mix * (0.92 / pk))
    lines = [{"start": ln[0][0], "end": ln[-1][1], "words": ln} for ln in group_lines(words, max_chars=16, max_words=3)]
    hook = (ss.get("hook") or pl.get("title", "")).upper()
    W, H, fps = 1080, 1920, 25
    objs = {}

    def shot(i):
        if i not in objs:
            objs.clear()
            objs[i] = VShot(shots[i], W, H)
        return objs[i]

    def frames():
        for fi in range(int(total * fps)):
            tt = fi / fps
            if tt < speech_end:
                i = min(len(shots) - 1, int(tt / seg))
                lt = tt - i * seg
                img = shot(i).frame(lt, seg)
                if lt < 0.14 and i > 0:  # quick punch on each cut
                    z = 1 + 0.08 * (1 - lt / 0.14)
                    cw, ch = W / z, H / z
                    img = img.resize((W, H), Image.BILINEAR, box=((W - cw) / 2, (H - ch) / 2, (W + cw) / 2, (H + ch) / 2))
                d = ImageDraw.Draw(img, "RGBA")
                if tt < 3.2:  # the hook, only at the start
                    a = ease_out(tt / 0.35) * (1 - clamp((tt - 2.8) / 0.4))
                    f = font("Anton", 86)
                    hl = wrap(d, hook, f, W * 0.86)[:3]
                    y = 150
                    for j, ln in enumerate(hl):
                        col = THUMB_RED if j == len(hl) - 1 else (250, 248, 242)
                        d.text((W / 2, y), ln, font=f, fill=col + (int(255 * a),), anchor="mm", stroke_width=5, stroke_fill=(0, 0, 0, int(255 * a)))
                        y += 98
                else:
                    d.text((W / 2, 120), (pl.get("channel") or "MIDNIGHT ARCHIVE").upper(), font=font("Oswald", 34, "Medium"), fill=(230, 226, 216, 200), anchor="mm")
                draw_caption(img, tt, lines, W, H, int(H * 0.80), 84, box=False, max_w=W * 0.88)
            else:  # end card
                lt = tt - speech_end
                img = shot(len(shots) - 1).frame(seg + lt, seg + end_card)
                img = Image.blend(img, Image.new("RGB", (W, H), (6, 6, 8)), 0.6)
                d = ImageDraw.Draw(img, "RGBA")
                a = ease_out(lt / 0.4)
                d.text((W / 2, 820), "WATCH THE", font=font("Anton", 110), fill=(250, 248, 242, int(255 * a)), anchor="mm")
                d.text((W / 2, 950), "FULL STORY", font=font("Anton", 130), fill=THUMB_RED + (int(255 * a),), anchor="mm")
                d.text((W / 2, 1090), "on the channel", font=font("Inter", 46, "SemiBold"), fill=(220, 216, 206, int(230 * a)), anchor="mm")
            yield img.tobytes()
            if fi % 50 == 0:
                print(f"\r   summary Short  ({int(fi * 100 / (total * fps))}%)", end="", flush=True)
        print()

    out = os.path.join(sdir, "short_1.mp4")
    encode(None, frames(), W, H, fps, wav, out)
    os.remove(wav)
    title = ss.get("title") or (hook.title() + " #shorts")
    tags = [x for x in (pl.get("tags") or []) if x][:2]
    hs = " ".join("#" + re.sub(r"[^A-Za-z0-9]", "", x.title()) for x in tags) or "#history"
    with open(os.path.join(sdir, "shorts.txt"), "w", encoding="utf-8") as f:
        f.write("THE SUMMARY SHORT (the whole story in under a minute)\n"
                f"File: short_1.mp4   ({fmt_ts(total)})\n"
                f"Title: {title}\n"
                f"Description: {ss.get('hook') or pl.get('title', '')} The full documentary is on the channel. {hs} #shorts\n"
                f"Pinned comment: {ss.get('comment') or 'Did you know this story? Tell me below.'}\n"
                "Cover: see thumbnail_prompts.txt (SHORT COVER).\n"
                "In YouTube Studio > this Short > 'Related video': pick the long video.\n")
    log(f"\nDONE. Summary Short: {out}")
    return sdir


# ================================================================== THUMBNAIL PROMPTS for ChatGPT (instead of finished thumbnails)

def write_thumbnail_prompts(script, pl, out_dir):
    pool = _pictures_used(pl)
    concepts = [dict(c) for c in (script.get("thumbnails") or [])][:3]
    auto = _auto_concepts(script, pl)
    while len(concepts) < 3:
        concepts.append(auto[len(concepts)])
    titles = (list(script.get("titles") or []) + [script.get("title", "")] * 3)[:3]
    used = set()
    out = ["THUMBNAIL PROMPTS FOR CHATGPT",
           "How: open ChatGPT > attach the real picture named below (from the 'pictures' folder) > paste the prompt > download > upload to YouTube.",
           "Test & compare: make all three, upload A, then add B and C in YouTube Studio > Thumbnail > Test & compare.",
           "Real people: always attach their REAL photo. Never let the AI invent the face of a real victim or criminal.", ""]
    style = ("Style: dark cinematic true-crime / history documentary thumbnail (like big documentary YouTube channels). Very high contrast, deep blacks, "
             "desaturated colours with cold blue-grey shadows, subtle film grain, a soft red glow (#E21E18) behind the main subject, strong vignette. "
             "Photorealistic, sharp, readable on a phone at small size. No logos, no watermark, no extra words, no borders.")
    for i, c in enumerate(concepts):
        lines = [x.strip().upper() for x in (c.get("text") or "?").replace("\\n", "\n").split("\n") if x.strip()]
        if len(lines) == 1 and len(lines[0].split()) >= 2:
            w_ = lines[0].split()
            lines = [" ".join(w_[:len(w_) // 2]), " ".join(w_[len(w_) // 2:])]
        red = (c.get("red") or max(lines[-1].split(), key=len)).upper()
        p = _pick_picture(c, pool, used, pl["total"])
        pic = ""
        subj = c.get("picture") or script.get("title", "")
        if p:
            used.add(p["file"])
            pic = os.path.splitext(p["file"])[0] + ".jpg"
        person = bool(p and p.get("faces"))
        st = c.get("style", ("face", "dark", "circle")[i])
        if person:
            comp = ("Use the attached photo. Keep the person's face exactly as in the photo (do not change or invent the face). "
                    "Cut the person out and place them big on the RIGHT third, head and shoulders, looking serious; thin white rim light and a red glow around them. "
                    "Background: a dark, blurred version of the scene.")
        else:
            comp = (f"Use the attached photo as the scene ({subj}). Make it moody and dramatic, the main subject on the RIGHT half, "
                    "the left side darker so the text stands out.")
        if st == "circle":
            comp += " Add one thick bright red hand-drawn circle around the most important detail, and a small red arrow pointing at it."
        text = (f'Text on the LEFT side, huge bold condensed font (like Anton/Impact), white with a thick black outline and drop shadow: "{lines[0]}"'
                + (f' on the first line and "{" ".join(lines[1:])}" on the second line' if len(lines) > 1 else "")
                + f'. The word "{red}" in bright red (#E21E18). A short red bar under the last line. Spell the words exactly like this.')
        out += [f"===== THUMBNAIL {'ABC'[i]}  (title: {titles[i]}) =====",
                f"Attach this picture: pictures/{pic}" if pic else "Attach a real picture of: " + subj,
                "Prompt:",
                f"Create a YouTube thumbnail, 16:9, 1280x720. {comp} {text} {style}", ""]
    ss = script.get("summary_short") or {}
    hook = (ss.get("hook") or script.get("title", "")).upper()
    out += ["===== SHORT COVER (vertical) =====",
            f"Attach the same picture as thumbnail A.",
            "Prompt:",
            f"Create a vertical YouTube Shorts cover, 9:16, 1080x1920. The main subject big in the lower two thirds. At the top, huge bold condensed white text with "
            f'black outline: "{hook}", the last word in bright red (#E21E18). At the bottom, small text: "MIDNIGHT ARCHIVE". {style}', ""]
    with open(os.path.join(out_dir, "thumbnail_prompts.txt"), "w", encoding="utf-8") as f:
        f.write("\n".join(out))
    log("   thumbnail_prompts.txt written (3 thumbnails + Short cover for ChatGPT)")


def short_frame(clip, t, dur, total, hook, lines, long_title):
    W, H = 1080, 1920
    if clip is None:
        clip = Image.new("RGB", (1080, 608), (12, 10, 8))
    # blurred, dark background from the same picture
    bg = clip.crop((369, 0, 711, 608)).resize((135, 240), Image.BILINEAR).filter(ImageFilter.GaussianBlur(5)).point(lambda v: int(v * 0.45)).resize((W, H), Image.BILINEAR)
    img = bg
    if t < dur:
        z = 1 + 0.025 * math.sin(t * 0.5)
        cl = clip.resize((int(1080 * z), int(608 * z)), Image.BILINEAR).crop((int((1080 * z - 1080) / 2), int((608 * z - 608) / 2), int((1080 * z - 1080) / 2) + 1080, int((608 * z - 608) / 2) + 608))
        y0 = 640
        img.paste(cl, (0, y0))
        d = ImageDraw.Draw(img, "RGBA")
        d.line([(0, y0), (W, y0)], fill=GOLD + (200,), width=3)
        d.line([(0, y0 + 608), (W, y0 + 608)], fill=GOLD + (200,), width=3)
        # hook on top
        a = ease_out(t / 0.5)
        f = font("Oswald", 84, "Bold")
        hl = wrap(d, hook, f, W * 0.88)[:3]
        yy = 400 - (len(hl) - 1) * 50
        for i, ln in enumerate(hl):
            col = GOLD_L if i == len(hl) - 1 else WHITE
            d.text((W / 2, yy + (1 - a) * 30), ln, font=f, fill=col + (int(255 * a),), anchor="mm", stroke_width=5, stroke_fill=(0, 0, 0, int(255 * a)))
            yy += 100
        # captions in the middle (below the picture), word by word
        draw_caption(img, t, lines, W, H, 1430, 74, box=False, max_w=W * 0.9)
        # bottom pill
        d = ImageDraw.Draw(img, "RGBA")
        f2 = font("Oswald", 36, "Medium")
        txt = "FULL STORY ON THE CHANNEL"
        w2 = d.textlength(txt, font=f2)
        d.rounded_rectangle([W / 2 - w2 / 2 - 60, 1640, W / 2 + w2 / 2 + 30, 1710], radius=35, fill=(10, 10, 10, 190), outline=GOLD + (230,), width=3)
        d.polygon([(W / 2 - w2 / 2 - 38, 1657), (W / 2 - w2 / 2 - 38, 1693), (W / 2 - w2 / 2 - 12, 1675)], fill=GOLD_L)
        d.text((W / 2 - 12, 1675), txt, font=f2, fill=WHITE, anchor="mm")
    else:
        # end card
        lt = t - dur
        a = ease_out(lt / 0.5)
        d = ImageDraw.Draw(img, "RGBA")
        f = font("Oswald", 96, "Bold")
        d.text((W / 2, 760), "WATCH THE", font=f, fill=WHITE + (int(255 * a),), anchor="mm")
        d.text((W / 2, 870), "FULL STORY", font=f, fill=GOLD_L + (int(255 * a),), anchor="mm")
        f3 = font("Inter", 44, "SemiBold")
        yy = 1010
        for ln in wrap(d, long_title, f3, W * 0.8)[:3]:
            d.text((W / 2, yy), ln, font=f3, fill=GREY + (int(255 * a),), anchor="mm")
            yy += 60
        r = 70 + 6 * math.sin(lt * 6)
        cx, cy = W / 2, 1290
        d.ellipse([cx - r, cy - r, cx + r, cy + r], fill=GOLD + (int(240 * a),))
        d.polygon([(cx - 22, cy - 34), (cx - 22, cy + 34), (cx + 36, cy)], fill=(15, 12, 8, int(255 * a)))
    d = ImageDraw.Draw(img, "RGBA")
    return dust(img, t, 0.5, seed=9)


# ------------------------------------------------------------------ voices: hear them all, pick one

VOICE_LIST = [("saim", "SAIM: calm, low, mysterious American storyteller (free, on this PC)"), ("saim_deep", "SAIM deep: darker and slower"), ("saim_warm", "SAIM warm: softer, closer"), ("saim_neural", "SAIM natural: most human-like (online voice, made in the cloud)"), ("none", "No AI voice: you record your own voice-over"), ("bm_george", "British, deep, documentary"), ("bm_fable", "British, storyteller"), ("bm_lewis", "British, calm"), ("bm_daniel", "British, clear"),
              ("am_onyx", "American, deep"), ("am_michael", "American, warm"), ("am_adam", "American, strong"), ("am_eric", "American, news"),
              ("am_liam", "American, young"), ("af_heart", "American female, warm"), ("bf_emma", "British female, clear"), ("af_nicole", "American female, soft")]


def voice_samples(text=None):
    ensure_models()
    text = text or "On the night she disappeared, the town went quiet. Nobody saw a thing. Or at least, that is what they told the police."
    os.makedirs(A("output", "_voices"), exist_ok=True)
    for v, desc in VOICE_LIST:
        if v == "none":
            continue
        p = A("output", "_voices", v + ".wav")
        if not os.path.exists(p):
            log(f"  {v} ({desc})")
            write_wav(p, Voice({"voice": v, "speed": 0.95}).say(text))
    log("DONE voices")


# ------------------------------------------------------------------ script writer: a free AI key (Cerebras or Groq), written in parts

AI_PROVIDERS = {  # key prefix -> (name, API address, model)
    "csk-": ("Cerebras", "https://api.cerebras.ai/v1", "gpt-oss-120b"),
    "gsk_": ("Groq", "https://api.groq.com/openai/v1", "openai/gpt-oss-120b"),
    "sk-or-": ("OpenRouter", "https://openrouter.ai/api/v1", "openai/gpt-oss-120b:free"),
}

NICHE = ("Midnight Archive: cinematic documentaries about the DARK side of real history: what was done to people, to whole nations, "
         "and especially to women. Kidnappings, disappearances, cults, wars and massacres, cover-ups, injustices, crimes that shocked "
         "countries, and the people who survived them. American audience.")

STYLE_RULES = """VOICE OF THE STORY (this is what makes people stay)
- Narrated by "Saim": calm, low, mysterious, like a late-night storyteller. Never shouting, never hype words ("insane", "crazy").
- Short sentences. Spoken English. Vary rhythm: a long sentence, then a very short one. Use "..." where the narrator should pause.
- Second person and questions pull people in: "Now imagine...", "So why did nobody call the police?"
- Every 30-45 seconds open a new loop: a question, a contradiction, "but that was not the strangest part".
- Facts must be real and documented. If sources disagree, say so. Never invent names, quotes, dialogue or numbers.
  For living people and unproven accusations use "police said", "she later told reporters", "allegedly".
- RESPECT THE VICTIMS: say what happened, never describe sexual violence, wounds or bodies in detail. No details that sexualize anyone.
  Minors: no names unless widely published, never any sexual detail. The story honours the victim, never the criminal.
- YouTube-safe: no slurs, no gore, no glorifying violence (keeps ads on)."""

VISUAL_RULES = """VISUALS (the engine shows them one after another while the scene is spoken; 1 visual every 4-5 seconds = about 2 per 22 words; each visual is on screen max 5 seconds)
EVERYTHING ON SCREEN MUST BE REAL AND ABOUT THIS STORY. Viewers leave when the picture doesn't match the words.
Mix, per chapter: about 35% "video", 50% "image", a few maps, dates and case files. Text slides ("text", "type", "stat", "quote") at most ONE per chapter.
Every image/video search must name a SPECIFIC REAL thing that has photos or footage online: the actual person (if public photos exist),
the actual town, street, building, court house, prison, newspaper front page, ship, army, protest, ruins, document. Add the year or country.
NEVER vague searches like "sad woman", "dark room", "crime scene", "mystery". If no real picture of a moment exists, show the real PLACE where it happened.
- {"type":"video","search":["english search","second search"],"source":"archive"|"stock","year":1969,"look":"film|tv|rec|glitch" (optional)}
    "archive" = REAL footage of that time/place/event (Wikimedia Commons, Internet Archive): name the real thing, e.g. "Vietnam war helicopter 1968", "Berlin wall 1961 newsreel", "VOA news Kabul 2001".
    "stock" = modern mood footage that illustrates without pretending to be the real people: "police car lights at night", "rain on window night", "empty forest road fog", "hand typing keyboard dark", "old film projector".
    Stock clips must NOT show a recognizable person's face as a victim or criminal (the stock licenses forbid showing people in a bad light):
    use hands, silhouettes, backs, shadows, empty rooms, streets, objects, weather.
    look: "film" for footage before 1975, "tv" for TV news, "rec" for found-footage moments.
- {"type":"image","search":["Wikimedia Commons search","second"],"caption":"Name, year (for real people/places)","style":"card" (optional, printed photo look)}
    Real, specific things: named people, buildings, streets, documents, newspapers, court houses, places. Every image has its OWN search.
- {"type":"date","text":"October 4, 2023","sub":"Place"}  whenever time jumps.
- {"type":"type","text":"ONE TO THREE WORDS"}  a theme word typed out: "SOCIAL MEDIA", "THE LETTER", "11 DAYS LATER".
- {"type":"casefile","title":"CASE FILE <year>","fields":[["Name","..."],["Last seen","..."],["Date","..."]],"stamp":"MISSING|UNSOLVED|CLOSED|GUILTY"}  once per crime story, real facts only.
- {"type":"map","view":[lonW,latS,lonE,latN],"points":[{"name":"City","note":"short","at":[lon,lat],"at_time":0.3,"side":"right"}]}
- {"type":"stat","number":1600000,"suffix":" FOLLOWERS","label":"what it means"}
- {"type":"text","lines":["short","punchline"],"hit":true}  at most one per chapter, only for the biggest twist.
- {"type":"quote","text":"real quote","by":"who, when"}  only real, sourced quotes.
FLOATING CARDS: "pops":[{"text":"NAME OR NUMBER","label":"small line","on":"a word from the narration","kind":"person|money|death|place|date|law|people"}] 1-2 per scene.
MUSIC: "mood" on the first scene of each chapter: tense | mystery | sad | epic | hopeful."""


def _ai_conf():
    cfg = settings()
    key = (cfg.get("ai_key") or os.environ.get("AI_KEY") or "").strip()
    if not key:
        raise RuntimeError("No AI key yet. Make a free Cerebras key (cloud.cerebras.ai) or Groq key (console.groq.com/keys) and paste it in the app (New script tab).")
    for pre, (name, base, model) in AI_PROVIDERS.items():
        if key.startswith(pre):
            return name, cfg.get("ai_base") or base, cfg.get("ai_model") or model, key
    if key.startswith("AIza"):
        return "Gemini", "gemini", cfg.get("gemini_model") or "gemini-2.5-flash", key
    if cfg.get("ai_base"):
        return "AI", cfg["ai_base"], cfg.get("ai_model") or "gpt-oss-120b", key
    raise RuntimeError("This key isn't one I know. Use a Cerebras key (starts with csk-) or a Groq key (starts with gsk_).")


def _ai(prompt, system="", temperature=0.8, max_tokens=4096, tries=7):
    """One question to the free AI. Waits and tries again when the free limit per minute is reached."""
    import urllib.error
    name, base, model, key = _ai_conf()
    last = ""
    for attempt in range(tries):
        try:
            if base == "gemini":
                url = f"https://generativelanguage.googleapis.com/v1beta/models/{model}:generateContent?key={urllib.parse.quote(key)}"
                body = {"contents": [{"parts": [{"text": (system + "\n\n" + prompt).strip()}]}],
                        "generationConfig": {"responseMimeType": "application/json", "temperature": temperature}}
                d = http_json(url, json.dumps(body).encode(), {"Content-Type": "application/json"}, timeout=300)
                return d["candidates"][0]["content"]["parts"][0]["text"]
            msgs = ([{"role": "system", "content": system}] if system else []) + [{"role": "user", "content": prompt}]
            body = {"model": model, "messages": msgs, "temperature": temperature, "max_tokens": max_tokens, "response_format": {"type": "json_object"}}
            req = urllib.request.Request(base.rstrip("/") + "/chat/completions", data=json.dumps(body).encode(), method="POST",
                                         headers={**UA, "Content-Type": "application/json", "Authorization": "Bearer " + key})
            with urllib.request.urlopen(req, timeout=300) as r:
                d = json.loads(r.read().decode())
            txt = ((d.get("choices") or [{}])[0].get("message") or {}).get("content") or ""
            if not txt.strip():
                raise ValueError("empty answer")
            return txt
        except urllib.error.HTTPError as e:
            raw = e.read()[:300].decode("utf-8", "replace")
            last = f"{e.code} {raw}"
            if e.code in (429, 500, 502, 503, 504, 529):
                wait = float(e.headers.get("retry-after") or 0) or min(60, 12 * (attempt + 1))
                log(f"    {name} is busy (free limit), waiting {int(wait)} s...")
                time.sleep(min(90, wait + 1))
                continue
            if e.code == 400 and "response_format" in raw and "response_format" in body:
                body.pop("response_format")
                continue
            if e.code in (401, 403):
                raise RuntimeError(f"{name} didn't accept the key. Make a new free key and paste it again.")
            raise RuntimeError(f"{name}: {last}")
        except Exception as e:
            last = str(e)[:200]
            time.sleep(5)
    raise RuntimeError(f"{name} didn't answer: {last}")


def _ai_json(prompt, system="", **kw):
    for attempt in range(3):
        txt = _ai(prompt, system, **kw)
        t = re.sub(r"^```(?:json)?|```$", "", txt.strip(), flags=re.M).strip()
        i, j = t.find("{"), t.rfind("}")
        try:
            return json.loads(t[i:j + 1])
        except Exception:
            prompt += "\n\nIMPORTANT: answer with ONE valid JSON object only."
    raise RuntimeError("The AI's answer wasn't valid JSON three times. Try again.")


_VTYPES = {"image", "video", "map", "date", "type", "casefile", "stat", "text", "quote", "title", "year", "timeline", "bars", "count"}


def _clean_scenes(scenes, used_searches):
    out = []
    for sc in scenes or []:
        if not isinstance(sc, dict) or not (sc.get("say") or "").strip():
            continue
        vis = []
        for v in sc.get("visuals") or []:
            if not isinstance(v, dict) or v.get("type") not in _VTYPES:
                continue
            if v["type"] in ("image", "video"):
                q = v.get("search") or []
                q = [q] if isinstance(q, str) else [x for x in q if isinstance(x, str) and x.strip()]
                if not q:
                    continue
                q = [x for x in q if x.lower().strip() not in used_searches] or q
                if q[0].lower().strip() in used_searches:  # every picture/clip has its own search
                    for extra in (" detail", " close-up", " wide view", " photograph", " archive", " 2", " 3", " 4"):
                        if (q[0] + extra).lower().strip() not in used_searches:
                            q = [q[0] + extra] + q[1:]
                            break
                used_searches.add(q[0].lower().strip())
                v["search"] = q
                if v["type"] == "video" and v.get("source") not in ("archive", "stock", "any"):
                    v["source"] = "any"
            vis.append(v)
        if not vis:
            vis = [{"type": "text", "lines": [sc["say"].split(".")[0][:40]]}]
        sc["visuals"] = vis
        sc["pops"] = [p for p in (sc.get("pops") or []) if isinstance(p, dict) and p.get("text")][:2]
        out.append(sc)
    return out


def write_script(topic):
    """Writes a full documentary in 3 steps: research + outline, then each chapter, then titles/thumbnails/Shorts."""
    name, base, model, _ = _ai_conf()
    log(f"STEP 1/3 Research and story outline ({name})")
    system = "You are the head writer and researcher of a top documentary YouTube channel. " + NICHE
    outline = _ai_json(f"""Topic: {topic}

First, research from what you reliably know. Then plan a 13-16 minute documentary (2,000-2,400 spoken words).
Answer ONLY JSON:
{{"working_title": "...",
 "facts": ["20-35 short, checkable facts: names, dates, places, numbers, what happened, what happened after"],
 "unsure": ["things that are disputed or that you are not sure about (the script must not state these as fact)"],
 "sources": ["real books, court records, news outlets or reports this is based on"],
 "backup_searches": ["15 broad searches for REAL photos/footage of this story's places, people and era, e.g. 'Hangzhou old town', 'Edinburgh 1820s', 'Khmer Rouge soldiers 1975'"],
 "region": "the ONE country or city where this story happens, in English (e.g. 'Australia')",
 "era": [first year of the story, last year of the story],
 "hook": "the first 2 sentences: a true, shocking, quiet hook (no 'welcome back', no 'in this video')",
 "chapters": [{{"name": "Chapter name", "mood": "tense|mystery|sad|epic|hopeful", "covers": "what this chapter tells, which facts", "open_loop": "the question it leaves", "words": 260}}]
}}
Use 7 to 9 chapters: cold open -> who/where -> how it started -> it gets worse -> the turning point -> the truth comes out -> what happened after -> why it still matters (2-3 short lessons) -> a one-line ending.
If this is NOT a real, documented story, say so in "unsure" and keep "facts" empty.""", system, temperature=0.5, max_tokens=4096)
    facts = outline.get("facts") or []
    if len(facts) < 8:
        raise RuntimeError("The AI couldn't find enough real facts about this topic. Choose a better documented topic.")
    chapters = [c for c in outline.get("chapters") or [] if isinstance(c, dict) and c.get("name")][:10]
    if len(chapters) < 5:
        raise RuntimeError("The AI's outline was too short. Try again.")
    used, scenes = set(), []
    for ci, ch in enumerate(chapters, 1):
        log(f"STEP 2/3 Writing chapter {ci}/{len(chapters)}: {ch['name']}")
        prev = " ".join(sc["say"] for sc in scenes[-3:])
        part = _ai_json(f"""Documentary topic: {topic}
TRUE FACTS you may use: {json.dumps(facts)}
DO NOT state as fact: {json.dumps(outline.get('unsure') or [])}
{"OPENING HOOK (start with it): " + outline.get("hook", "") if ci == 1 else "The story so far ended with: " + prev[-700:]}

Write chapter {ci} of {len(chapters)}: "{ch['name']}" (mood: {ch.get('mood', 'mystery')}).
It covers: {ch.get('covers', '')}
It ends on this open loop: {ch.get('open_loop', '')}
About {int(ch.get('words') or 260)} spoken words in 5-9 scenes (each scene 1-4 sentences).

{STYLE_RULES}

{VISUAL_RULES}

Answer ONLY JSON: {{"scenes": [{{"say": "...", "visuals": [...], "pops": [...]}}]}}
Put "chapter": "{ch['name']}" and "mood": "{ch.get('mood', 'mystery')}" on the FIRST scene only.
EVERY image/video search must contain "{outline.get('region', '')}" or a real place/person name inside it, and must fit the time of the story
({outline.get('era', '')}): never show modern buildings or modern photos for an old event.""", system, temperature=0.85, max_tokens=5000)
        new = _clean_scenes(part.get("scenes"), used)
        if new:
            new[0]["chapter"] = ch["name"]
            new[0]["mood"] = ch.get("mood") or new[0].get("mood") or "mystery"
        scenes += new
    if len(scenes) < 25:
        raise RuntimeError("The script came out too short. Try again.")
    log("STEP 3/3 Titles, thumbnails and Shorts")
    index = "\n".join(f"{i}: {sc['say'][:110]}" for i, sc in enumerate(scenes))
    meta = _ai_json(f"""Topic: {topic}
These are the scenes of the finished documentary (number: start of the narration):
{index}

Make the packaging. Views depend on title + thumbnail. Everything must be TRUE to the story.
Answer ONLY JSON:
{{"title": "best YouTube title, under 60 characters: curiosity + the key fact, no clickbait lies",
 "titles": ["title A", "title B", "title C"],
 "description": "2-3 sentences; the first sentence is the hook with the main keyword",
 "tags": ["15 tags: the case name, the person, the place, the year, 'true crime documentary', 'dark history', long-tail questions people search"],
 "hashtags": ["#One", "#Two", "#DarkHistory"],
 "pinned_comment": "one short question viewers will want to answer",
 "thumbnails": [{{"text": "2-4 WORDS\\nON TWO LINES", "picture": "the image search of the best picture for this", "style": "face", "red": "the ONE word to colour red"}},
                {{"text": "...", "picture": "...", "style": "dark", "red": "..."}},
                {{"text": "...", "picture": "...", "style": "circle", "red": "..."}}],
 "summary_short": {{"hook": "max 7 words on screen, the most shocking true fact", "say": "the WHOLE story told in 110-130 spoken words: a hook, what happened, the twist, how it ended. Short sentences, Saim's calm voice. Last sentence: 'The full story is on the channel.'", "title": "Short title under 60 characters #shorts", "comment": "pinned question"}},
 "shorts": [1 x {{"from_scene": i, "to_scene": j, "hook": "short hook line", "title": "Short title #shorts", "comment": "pinned question"}}]
}}
Thumbnail words must NOT repeat the title; they add curiosity ("SHE KNEW\\nHIM", "11 DAYS\\nOF SILENCE").""",
                    system, temperature=0.8, max_tokens=3000)
    first_img = next((v["search"][0] for sc in scenes for v in sc["visuals"] if v.get("type") == "image"), topic)
    thumbs = [t for t in (meta.get("thumbnails") or []) if isinstance(t, dict) and t.get("text")][:3]
    for t in thumbs:
        t.setdefault("picture", first_img)
    script = {"title": meta.get("title") or outline.get("working_title") or topic, "titles": (meta.get("titles") or [])[:3],
              "description": meta.get("description", ""), "tags": (meta.get("tags") or [])[:20], "hashtags": (meta.get("hashtags") or [])[:3],
              "sources": outline.get("sources") or [], "pinned_comment": meta.get("pinned_comment", ""), "voice": "saim", "speed": 0.95,
              "thumbnail": {"text": thumbs[0]["text"] if thumbs else "THE TRUTH\nCAME OUT"}, "thumbnails": thumbs,
              "shorts": [s for s in (meta.get("shorts") or []) if isinstance(s, dict) and "from_scene" in s][:1],
              "summary_short": meta.get("summary_short") if isinstance(meta.get("summary_short"), dict) else {},
              "region": outline.get("region") or "", "era": outline.get("era") or [],
              "facts_to_check": facts, "unsure": outline.get("unsure") or [],
              "backup_searches": [q for q in (outline.get("backup_searches") or []) if isinstance(q, str)][:20], "written_by": f"{name} {model}", "scenes": scenes}
    slug = re.sub(r"[^a-z0-9]+", "_", topic.lower()).strip("_")[:40] or "new_video"
    path = A("scripts", slug + ".json")
    _json_write(path, script)
    words = sum(len(sc["say"].split()) for sc in scenes)
    log(f"Script saved: {path}  ({len(scenes)} scenes, {words} words, about {words / 150:.0f} minutes)")
    log("Read it once and check the facts (they are listed in 'facts_to_check'), then make the video.")
    return path


def _gemini(prompt, temperature=0.9, timeout=240):  # old name, kept for older code
    return _ai(prompt, temperature=temperature)


def more_topics(n=5):
    """5 fresh real-story ideas from the free AI, saved for the app's Topics tab."""
    have = _json_read(A("assets", "topics.json"), []) + _json_read(A("topics_extra.json"), [])
    titles = [x.get("t", "") for x in have]
    d = _ai_json(f"""You find documentary topics for {NICHE}
Give {n} NEW topics that really happened, are well documented (court records, major news, history books) and have a shocking true hook.
Mix countries and eras (ancient to 2020s). Not too famous to be boring, not so obscure that there is no footage or pictures.
Do not repeat any of these: {json.dumps(titles[-150:])}
Answer ONLY JSON: {{"topics": [{{"t": "YouTube-style title under 60 characters", "h": "one-sentence true hook", "c": "women|nations|crime|cults|war|cover-up|disappearance"}}]}}""",
                 temperature=1.0, max_tokens=2000)
    new = [x for x in (d.get("topics") or []) if isinstance(x, dict) and x.get("t") and x["t"] not in titles][:n]
    for x in new:
        x["new"] = time.strftime("%Y-%m-%d")
    extra = _json_read(A("topics_extra.json"), [])
    _json_write(A("topics_extra.json"), new + extra)
    log(f"DONE: {len(new)} new topics")
    for x in new:
        log("  - " + x["t"])
    return new


def unlock_private():
    """In the cloud: opens your locked (encrypted) recordings, clips and pictures with the MEDIA_KEY secret."""
    import base64
    key = os.environ.get("MEDIA_KEY", "")
    n = 0
    for d in ("voiceover", "clips_own", "images"):
        if not os.path.isdir(A(d)):
            continue
        for f in os.listdir(A(d)):
            if not f.endswith(".enc"):
                continue
            if not key:
                log("  locked files found but no MEDIA_KEY secret: press Make video again from the app.")
                return
            from nacl.secret import SecretBox
            with open(A(d, f), "rb") as fh:
                data = SecretBox(base64.b64decode(key)).decrypt(fh.read())
            with open(A(d, f[:-4]), "wb") as fh:
                fh.write(data)
            n += 1
    log(f"  {n} private file(s) unlocked")


def choose_script():
    files = sorted(f for f in os.listdir(A("scripts")) if f.endswith(".json"))
    if not files:
        raise SystemExit("No scripts in the scripts folder.")
    print("\nScripts:")
    for i, f in enumerate(files, 1):
        print(f"  {i}. {f}")
    n = input("Number of the script to make (Enter = 1): ").strip() or "1"
    return A("scripts", files[int(n) - 1])


if __name__ == "__main__":
    args = sys.argv[1:]
    try:
        if args and args[0] == "--write":
            write_script(" ".join(args[1:]).strip() or input("Video topic: ").strip())
        elif args and args[0] == "--shorts":
            make_shorts(args[1] if len(args) > 1 else A("output", os.path.splitext(os.path.basename(choose_script()))[0]), int(args[2]) if len(args) > 2 else 4)
        elif args and args[0] == "--pictures":
            sc_ = load_script(args[1])
            log("STEP Pictures")
            cr, miss = resolve_pictures(sc_, use_ai=settings().get("ai_pictures", True))
            log(f"DONE pictures: {len(cr)} found, {len(miss)} missing")
        elif args and args[0] == "--topics":
            more_topics(int(args[1]) if len(args) > 1 else 5)
        elif args and args[0] == "--unlock":
            unlock_private()
        elif args and args[0] == "--voices":
            voice_samples()
        elif args and args[0] == "--next-picture":
            c = next_picture(args[1])
            log("Now using: " + c["title"])
        else:
            path = next((a for a in args if a.endswith(".json")), None) or choose_script()
            cap = True if "--captions" in args else (False if "--no-captions" in args else None)
            build(path, preview="--preview" in args, captions=cap)
    except KeyboardInterrupt:
        pass
    except Exception as e:
        import traceback
        traceback.print_exc()
        print("\nERROR:", e)
        sys.exit(1)
