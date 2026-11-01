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
from PIL import Image, ImageDraw, ImageFilter, ImageFont

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


def log(*a):
    print(*a, flush=True)


# ================================================================== fonts

_FC = {}


def font(name, size, weight=None):
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
    key = ("dark", W, H, tint)
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
            shadow_text(img, (W / 2, y), ln, f, tuple(int(c * a + 20 * (1 - a)) for c in GOLD_L), anchor="mm", blur=10)
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
                    shadow_text(img, (W / 2 + (1 - a) * self.S(40), y), sub, f, tuple(int(c * a) for c in col), anchor="mm")
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
    g = np.asarray(im).astype(np.float32) / 255.0
    lum = g @ np.array([0.299, 0.587, 0.114], np.float32)
    sep = np.stack([lum * 1.07, lum * 0.92, lum * 0.72], -1)
    g = g * 0.72 + sep * 0.28
    g = np.clip((g - 0.5) * 1.12 + 0.5, 0, 1)  # a little contrast
    g = g ** 0.95
    return Image.fromarray((g * 255).astype(np.uint8))


class ImageScene(Scene):
    MOVES = ("in", "out", "left", "right", "up", "in")

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
        self.move = self.v.get("zoom") or self.MOVES[self.idx % len(self.MOVES)]

    def frame(self, t, dur):
        W, H = self.W, self.H
        if self.img is None:  # no picture found: a clean title card instead, the video still works
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
        im = self.img
        iw, ih = im.size
        sc = max(W / iw, H / ih)
        m = self.move
        detail = False
        if dur > 5.2:  # long shot: cut to a closer detail of the same picture halfway
            half = dur / 2
            if t >= half:
                t, dur, detail = t - half, dur - half, True
                m = {"in": "left", "out": "in", "left": "right", "right": "in", "up": "out"}.get(m, "in")
            else:
                dur = half
        p = ease_io(t / max(dur, 0.1)) * 0.85 + (t / max(dur, 0.1)) * 0.15
        z = {"in": 1.05 + 0.13 * p, "out": 1.18 - 0.13 * p}.get(m, 1.14)
        if detail:
            z *= 1.32
        vw, vh = W / (sc * z), H / (sc * z)
        fx, fy = self.v.get("focus", [0.5, 0.5])
        if detail:
            fx, fy = fx + (0.12 if self.idx % 2 else -0.12), fy - 0.06
        dx = {"left": 0.06 - 0.12 * p, "right": -0.06 + 0.12 * p}.get(m, (p - 0.5) * 0.03)
        dy = {"up": 0.05 - 0.10 * p}.get(m, 0)
        cx = clamp(fx + dx, vw / iw / 2, 1 - vw / iw / 2) * iw
        cy = clamp(fy + dy, vh / ih / 2, 1 - vh / ih / 2) * ih
        frame = im.resize((W, H), Image.BILINEAR, box=(cx - vw / 2, cy - vh / 2, cx + vw / 2, cy + vh / 2))
        frame = vignette(frame, 0.62)
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


SCENES = {"title": TitleScene, "text": TextScene, "stat": StatScene, "year": YearScene, "quote": QuoteScene,
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


class Voice:
    def __init__(self, cfg):
        self.voice = cfg.get("voice", "bm_george")
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
        t = tts_text(text)
        cache = A("cache", "voice", hashlib.sha1(f"{self.voice}|{self.speed}|{t}".encode()).hexdigest() + ".npy")
        if os.path.exists(cache):
            return np.load(cache)
        a = None
        errors = []
        if os.path.exists(MODEL):
            try:
                k = self._kokoro()
                lang = "en-gb" if self.voice.startswith("b") else "en-us"
                a, sr = k.create(t, voice=self.voice, speed=self.speed, lang=lang)
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

    def _edge(self, t):
        import asyncio
        import edge_tts
        name = {"bm_george": "en-GB-RyanNeural", "bm_lewis": "en-GB-ThomasNeural", "am_onyx": "en-US-AndrewNeural"}.get(self.voice, "en-US-GuyNeural")
        tmp = A("cache", "edge.mp3")
        os.makedirs(A("cache"), exist_ok=True)
        rate = f"{int((self.speed - 1) * 100):+d}%"
        asyncio.run(edge_tts.Communicate(t, name, rate=rate).save(tmp))
        return decode_audio(tmp)


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


# ================================================================== the build: voice -> timings -> beats

QUIET_TYPES = ("stat", "year", "bars", "timeline", "quote", "text", "title")
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
            parts += [a, np.zeros(int(SR * gap), np.float32)]
            st += d + gap
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
            pops.append({"t": at, "text": p.get("text", ""), "label": p.get("label", ""), "script": True})
        if sc.get("auto_pops", True):
            for snt in [x for x in sentences if x["scene"] == si]:
                for m_ in NUM_RE.finditer(snt["text"]):
                    tok = m_.group(0).strip().rstrip(",.;:!?")
                    if re.fullmatch(r"1\d{3}|20\d{2}", tok) or len(re.sub(r"\D", "", tok)) < 2:
                        continue  # years are on the clock already
                    first = tok.split()[0]
                    hit = next((w for w in sw if w[0] >= snt["start"] - 0.01 and re.sub(r"[^\w$]", "", w[2]) == re.sub(r"[^\w$]", "", first)), None)
                    if hit:
                        pops.append({"t": hit[0], "text": tok.upper(), "label": "", "script": False})
        t += dur
    total = t
    last_hit = -99
    for b in beats:
        v = b["visual"]
        if v.get("hit") is True or (v.get("hit") is not False and v.get("type") in ("text", "stat", "title", "year") and b["start"] - last_hit > 45 and b["start"] > 8):
            b["hit"] = True
            last_hit = b["start"]
    # tidy callouts: one at a time, 1.8-3.4 s each, never on number/text slides
    pops.sort(key=lambda p: p["t"])
    out, last_end = [], -1
    for p in pops:
        b = next((x for x in beats if x["start"] <= p["t"] < x["start"] + x["dur"]), None)
        if not b or b["visual"].get("type") in (QUIET_TYPES if not p["script"] else ("stat", "year", "title", "text", "quote")):
            continue
        if p["t"] < last_end + 0.3:
            continue
        end = min(p["t"] + 3.4, b["start"] + b["dur"] - 0.2)
        if end - p["t"] < 1.4:
            continue
        p["end"] = end
        p["side"] = len(out) % 2
        out.append(p)
        last_end = end
    pops = out
    track = np.concatenate(audio)
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
    for b in beats:
        if b.get("hit"):
            k = int(b["start"] * SR)
            im = impact_sound() * 0.55
            if k + len(im) < len(track):
                track[k:k + len(im)] += im
    for p in pops:
        k = int(p["t"] * SR)
        ps = pop_sound()
        if k + len(ps) < len(track):
            track[k:k + len(ps)] += ps
    peak = np.max(np.abs(track)) or 1
    track = track / peak * 0.9
    if script.get("ambient", True):
        track += ambient_pad(len(track)) * float(script.get("ambient_volume", 0.035))
    lines = []
    for snt in sentences:
        ws = [w for w in words if snt["start"] - 0.01 <= w[0] < snt["end"] + 0.01]
        for ln in group_lines(ws):
            lines.append({"start": ln[0][0], "end": ln[-1][1], "words": ln})
    return {"beats": beats, "sentences": sentences, "words": words, "lines": lines, "pops": pops, "total": total,
            "scene_starts": scene_starts, "voice": voice.kind}, track


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
        d.ellipse([x - r, y - r, x + r, y + r], fill=(255, 214, 140, max(0, min(255, a))))
    img.paste(ov, (0, 0), ov)
    return img


_LEAK = {}


def light_leak(img, t, seed=0):
    W, H = img.size
    key = (W, H)
    if key not in _LEAK:
        s = int(H * 1.1)
        y, x = np.mgrid[0:s, 0:s].astype(np.float32)
        r = np.sqrt((x - s / 2) ** 2 + (y - s / 2) ** 2) / (s / 2)
        m = np.clip(1 - r, 0, 1) ** 2.2
        g = np.stack([m * 70, m * 42, m * 14], -1)
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


def draw_pop(img, t, p, W, H):
    s = W / 1920
    a_in = ease_out((t - p["t"]) / 0.35)
    a_out = 1 - ease((t - (p["end"] - 0.3)) / 0.3)
    a = max(0.0, min(a_in, a_out))
    if a <= 0:
        return
    f = font("Oswald", int(64 * s), "Bold")
    fl = font("Oswald", int(26 * s), "Medium")
    d = ImageDraw.Draw(img, "RGBA")
    tw_ = d.textlength(p["text"], font=f)
    w = tw_ + int(70 * s)
    h = int((118 if p.get("label") else 96) * s)
    bob = math.sin((t - p["t"]) * 2.2) * 6 * s
    slide = (1 - a_in) * 70 * s
    if p["side"] == 0:
        x1 = W - int(70 * s) + slide
        x0 = x1 - w
    else:
        x0 = int(70 * s) - slide
        x1 = x0 + w
    y0 = int(150 * s) + bob
    d.rounded_rectangle([x0, y0, x1, y0 + h], radius=int(16 * s), fill=(12, 10, 8, int(205 * a)), outline=GOLD + (int(230 * a),), width=max(2, int(3 * s)))
    d.rectangle([x0 + int(18 * s), y0 + h - int(14 * s), x0 + int(18 * s) + (w - int(36 * s)) * ease_out((t - p["t"]) / 0.9), y0 + h - int(10 * s)], fill=GOLD + (int(255 * a),))
    ty = y0 + h / 2 - (int(8 * s) if not p.get("label") else -int(4 * s))
    if p.get("label"):
        d.text((x0 + w / 2, y0 + int(26 * s)), p["label"].upper(), font=fl, fill=GOLD_L + (int(255 * a),), anchor="mm")
    d.text((x0 + w / 2, ty), p["text"], font=f, fill=WHITE + (int(255 * a),), anchor="mm")


def overlay(img, t, plan_, cur, prev, W, H, captions=False):
    s = W / 1920
    d = ImageDraw.Draw(img, "RGBA")
    total = plan_["total"]
    d.rectangle([0, 0, W * t / total, max(3, int(4 * s))], fill=GOLD + (230,))
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
    if captions:
        draw_caption(img, t, plan_["lines"], W, H, H - int(120 * s), int(50 * s))
    return img


# ------------------------------------------------------------------ frame workers (run in parallel)

_W = {}


def _init_worker(plan_path, W, H, fps, captions):
    with open(plan_path, encoding="utf-8") as f:
        pl = json.load(f)
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
    if idx > 0 and lt < fade and not cur.get("hit"):
        prev = beats[idx - 1]
        pimg = beat_frame(idx - 1, prev["dur"] - 0.01 + lt)
        img = Image.blend(pimg, img, ease(lt / fade))
    img = overlay(img, t, pl, cur, beats[idx - 1] if idx > 0 else None, W, H, _W["captions"])
    return img.convert("RGB").tobytes()


# ------------------------------------------------------------------ real pictures: Wikimedia Commons (free, credited), AI painting as backup

UA = {"User-Agent": "SaimShafiHistoryEngine/2.2 (https://github.com/Saimshafi0; personal documentary maker)"}


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
SOURCES = [("commons", commons_candidates), ("aic", aic_candidates), ("openverse", openverse_candidates)]


def ai_painting(prompt, path):
    """Backup when no real picture exists: a free AI painting (pollinations.ai). Marked as AI in the credits."""
    style = ", oil painting, historical, cinematic lighting, muted warm colors, highly detailed, no text"
    url = "https://image.pollinations.ai/prompt/" + urllib.parse.quote(prompt + style) + "?width=1920&height=1080&nologo=true&seed=" + str(abs(hash(prompt)) % 10000)
    raw = http_bytes(url, timeout=50)
    Image.open(__import__("io").BytesIO(raw)).convert("RGB").save(path, quality=92)


def _download_any(cands, path, start=0):
    order = list(range(start, len(cands))) + list(range(0, start))
    for k in order:
        c = cands[k]
        try:
            raw = http_bytes(c["url"], timeout=60)
            im = Image.open(__import__("io").BytesIO(raw))
            if min(im.size) < 400:
                continue
            im.convert("RGB").save(path, quality=92)
            return k, c
        except Exception:
            continue
    return None, None


def _fetch_picture(v, use_ai, state):
    """One image slide: Wikimedia -> Openverse -> The Met -> Art Institute -> AI painting."""
    key = img_key(v)
    meta_p = A("images", key + ".json")
    meta = _json_read(meta_p, {})
    path = A("images", key + ".jpg")
    q = v.get("search") or []
    q = [q] if isinstance(q, str) else q
    if os.path.exists(path) and meta.get("source") == "bing":  # old junk from Bing: throw it away and look again
        try:
            os.remove(path)
        except OSError:
            pass
        meta = {}
    if os.path.exists(path) and meta.get("source") not in ("ai", None, ""):
        return key, meta.get("credit", ""), True
    if os.path.exists(path) and not meta:
        return key, "", True  # your own picture
    got = False
    cands = [c for c in (meta.get("candidates") or []) if c.get("url")]
    if cands:
        k, c = _download_any(cands, path, int(meta.get("choice", 0)) % len(cands))
        if c:
            meta.update(choice=k, credit=c["credit"], source=c.get("src", "commons"))
            got = True
    for name, fn in SOURCES:
        if got or not q:
            break
        with state["lock"]:
            if name in state["dead"]:
                continue
        try:
            found = fn(q)
        except SourceDown:
            with state["lock"]:
                state["fails"][name] = state["fails"].get(name, 0) + 1
                if state["fails"][name] >= 2 and name not in state["dead"]:
                    state["dead"].add(name)
                    log(f"  {name}: not reachable from this internet, skipping it for now.")
            continue
        if not found:
            continue
        k, c = _download_any(found, path)
        if c:
            meta.update(candidates=found, choice=k, credit=c["credit"], source=c.get("src", name))
            got = True
            log(f"    picture ({name}): {c['title'][:60]}")
    if not got and os.path.exists(path) and meta.get("source") == "ai":
        got = True
    if not got and use_ai and (v.get("ai") or q):
        with state["lock"]:
            ai_ok = "ai" not in state["dead"]
        if ai_ok:
            try:
                ai_painting(v.get("ai") or q[0], path)
                meta.update(source="ai", credit=f"AI-generated illustration: {v.get('ai') or q[0]}")
                got = True
                log(f"    AI painting: {(v.get('ai') or q[0])[:60]}")
            except Exception as e:
                with state["lock"]:
                    state["fails"]["ai"] = state["fails"].get("ai", 0) + 1
                    if "402" in str(e) or state["fails"]["ai"] >= 3:
                        state["dead"].add("ai")
                log(f"    AI painting failed ({str(e)[:60]})")
    _json_write(meta_p, meta)
    return key, meta.get("credit", "") if got else "", got


def resolve_pictures(script, use_ai=True):
    """Finds a real picture for every image slide (6 at a time). Remembers each choice in images/<key>.json."""
    from concurrent.futures import ThreadPoolExecutor, as_completed
    os.makedirs(A("images"), exist_ok=True)
    todo, slides = {}, []
    for sc in script["scenes"]:
        for v in (sc.get("visuals") or [sc.get("visual") or {}]):
            if v.get("type") != "image":
                continue
            if v.get("file") and os.path.exists(A("images", v["file"])):
                continue
            key = img_key(v)
            slides.append((key, v))
            todo.setdefault(key, v)
    state = {"dead": set(), "fails": {}, "lock": threading.Lock()}
    found = {}
    n = len(todo)
    with ThreadPoolExecutor(6) as ex:
        futs = [ex.submit(_fetch_picture, v, use_ai, state) for v in todo.values()]
        for i, f in enumerate(as_completed(futs), 1):
            try:
                key, credit, ok = f.result()
                found[key] = (credit, ok)
            except Exception as e:
                log(f"    picture error: {str(e)[:80]}")
            print(f"\r   pictures {i}/{n}  ({i * 100 // max(1, n)}%)", end="", flush=True)
    print()
    credits, missing = [], []
    for key, v in slides:
        credit, ok = found.get(key, ("", False))
        if ok and os.path.exists(A("images", key + ".jpg")):
            v["file"] = key + ".jpg"
            if credit and credit not in credits:
                credits.append(credit)
        else:
            v.pop("file", None)
            missing.append(v.get("caption") or key)
    if missing:
        log(f"  {len(missing)} picture(s) not found. Real-picture websites reachable: "
            + (", ".join(n_ for n_, _ in SOURCES if n_ not in state["dead"]) or "none"))
    return credits, missing


def next_picture(key):
    """Switch an image slide to the next candidate (used by the app's Pictures screen)."""
    meta_p = A("images", key + ".json")
    meta = _json_read(meta_p, {})
    cands = meta.get("candidates") or []
    if not cands:
        raise ValueError("No other pictures found for this slide.")
    k = (int(meta.get("choice", 0)) + 1) % len(cands)
    c = cands[k]
    raw = http_bytes(c["url"])
    Image.open(__import__("io").BytesIO(raw)).convert("RGB").save(A("images", key + ".jpg"), quality=92)
    meta.update(choice=k, credit=c["credit"], source=c.get("src", "commons"))
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
    lines = (th.get("text") or script.get("title", "")).upper().split("\n")
    y = 360 - len(lines) * 72
    for i, ln in enumerate(lines):
        f = font("Oswald", 132 if len(ln) < 11 else 104, "Bold")
        shadow_text(img, (60, y), ln, f, GOLD_L if i == len(lines) - 1 else WHITE, blur=8, alpha=255)
        y += 144
    img.save(os.path.join(out_dir, "thumbnail.jpg"), quality=93)


def fmt_ts(t):
    t = int(t)
    return f"{t // 3600}:{t % 3600 // 60:02d}:{t % 60:02d}" if t >= 3600 else f"{t // 60}:{t % 60:02d}"


def srt_t(x):
    ms = int(round(x * 1000))
    return f"{ms // 3600000:02d}:{ms % 3600000 // 60000:02d}:{ms % 60000 // 1000:02d},{ms % 1000:03d}"


def write_texts(script, pl, credits, out_dir):
    chapters, last = [], None
    for b in pl["beats"]:
        if b["chapter"] and b["chapter"] != last:
            chapters.append((b["start"], b["chapter"]))
            last = b["chapter"]
    if chapters:
        chapters[0] = (0, chapters[0][1])
    lines = [script.get("title", ""), "", script.get("description", ""), ""]
    if len(chapters) >= 3:
        lines += ["Chapters"] + [f"{fmt_ts(t)} {c}" for t, c in chapters] + [""]
    if credits:
        lines += ["Pictures"] + credits + [""]
    lines += ["Narration uses an AI voice. Maps and graphics are made for this video."]
    if script.get("tags"):
        lines += ["", "Tags: " + ", ".join(script["tags"])]
    with open(os.path.join(out_dir, "description.txt"), "w", encoding="utf-8") as f:
        f.write("\n".join(lines))
    with open(os.path.join(out_dir, "captions.srt"), "w", encoding="utf-8") as f:
        for i, ln in enumerate(pl["lines"], 1):
            f.write(f"{i}\n{srt_t(ln['start'])} --> {srt_t(ln['end'])}\n{' '.join(w[2] for w in ln['words'])}\n\n")


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


def encode(cmd_tail, frames_iter, W, H, fps, audio_wav, out, music=None, music_vol=0.12, crf="20"):
    cmd = [ffmpeg_exe(), "-y", "-v", "error", "-f", "rawvideo", "-pix_fmt", "rgb24", "-s", f"{W}x{H}", "-r", str(fps), "-i", "-", "-i", audio_wav]
    if music:
        cmd += ["-stream_loop", "-1", "-i", music, "-filter_complex",
                f"[2:a]volume={music_vol},aformat=sample_rates=48000:channel_layouts=stereo[m];[1:a]aformat=sample_rates=48000:channel_layouts=stereo[v];[v][m]amix=inputs=2:duration=first:normalize=0[a]",
                "-map", "0:v", "-map", "[a]"]
    else:
        cmd += ["-map", "0:v", "-map", "1:a"]
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
    log("STEP 1/4 Pictures")
    credits, missing = resolve_pictures(script, use_ai=cfg.get("ai_pictures", True))
    if missing:
        log(f"  {len(missing)} slide(s) without a picture use a gold title card instead.")
    log("STEP 2/4 Voice")
    pl, track = plan(script)
    wav = os.path.join(out_dir, "narration.wav")
    write_wav(wav, track)
    pl.update(title=script.get("title", ""), fps=fps, W=W, H=H, shorts=script.get("shorts") or [], voice_name=script.get("voice", "bm_george"),
              speed=script.get("speed", 0.95), script=os.path.basename(script_path))
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
    encode(None, frames(), W, H, fps, wav, mp4, music[0] if music else None, float(script.get("music_volume", 0.12)), "28" if preview else "20")
    log("STEP 4/4 Thumbnail, description, captions")
    make_thumbnail(script, pl, out_dir)
    write_texts(script, pl, credits, out_dir)
    log(f"\nDONE in {int(time.time() - t0) // 60} min. Your video is here:\n  {out_dir}")
    return out_dir


# ================================================================== SHORTS: 3-4 vertical clips from a finished long video

HOOK_WORDS = re.compile(r"\b(but|never|only|richest|biggest|secret|crash|crashed|twist|died|lost|first|nobody|everyone|impossible|billion|million|gold|war|fell|borrow|debt)\b", re.I)


def pick_shorts(pl, n=4, min_len=28, max_len=52):
    sents = pl["sentences"]
    manual = []
    for s in pl.get("shorts") or []:
        a, b = int(s.get("from_scene", 0)), int(s.get("to_scene", s.get("from_scene", 0)))
        ss = [x for x in sents if a <= x["scene"] <= b]
        if ss:
            manual.append({"start": max(0, ss[0]["start"] - 0.15), "end": min(ss[-1]["end"] + 0.4, ss[0]["start"] + max_len + 4), "hook": s.get("hook", ""),
                           "title": s.get("title", "")})
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


def make_shorts(out_dir, n=4):
    pl = _json_read(os.path.join(out_dir, "timeline.json"), None)
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
                yield short_frame(last, t, dur, total, hook, lines, pl.get("title", "")).tobytes()
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
        info.append(f"SHORT {k}  ({fmt_ts(seg['start'])}-{fmt_ts(seg['end'])} of the long video)\nTitle: {title}\n"
                    f"Description: {pl.get('title', '')} - full story on the channel. #history #shorts\n"
                    f"In YouTube Studio > this Short > 'Related video': pick the long video.\n")
    with open(os.path.join(sdir, "shorts.txt"), "w", encoding="utf-8") as f:
        f.write("\n".join(info))
    log(f"\nDONE. {len(segs)} shorts in:\n  {sdir}")
    return sdir


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
    d.rectangle([0, 0, W * t / total, 8], fill=GOLD + (230,))
    return dust(img, t, 0.5, seed=9)


# ------------------------------------------------------------------ voices: hear them all, pick one

VOICE_LIST = [("bm_george", "British, deep, documentary"), ("bm_fable", "British, storyteller"), ("bm_lewis", "British, calm"), ("bm_daniel", "British, clear"),
              ("am_onyx", "American, deep"), ("am_michael", "American, warm"), ("am_adam", "American, strong"), ("am_eric", "American, news"),
              ("am_liam", "American, young"), ("af_heart", "American female, warm"), ("bf_emma", "British female, clear"), ("af_nicole", "American female, soft")]


def voice_samples(text=None):
    ensure_models()
    text = text or "In 1324, a king walked out of West Africa with so much gold, that he crashed its price in Cairo for twelve years."
    os.makedirs(A("output", "_voices"), exist_ok=True)
    for v, desc in VOICE_LIST:
        p = A("output", "_voices", v + ".wav")
        if not os.path.exists(p):
            log(f"  {v} ({desc})")
            write_wav(p, Voice({"voice": v, "speed": 0.95}).say(text))
    log("DONE voices")


# ------------------------------------------------------------------ script writer (Gemini, free API key)

def write_script(topic):
    cfg = settings()
    key = (cfg.get("gemini_key") or "").strip()
    if not key:
        key = input("Paste your free Gemini API key (from aistudio.google.com/apikey): ").strip()
        cfg["gemini_key"] = key
        _json_write(A("settings.json"), cfg)
    with open(A("SCRIPT-PROMPT.txt"), encoding="utf-8") as f:
        prompt = f.read().replace("[TOPIC]", topic)
    example = open(A("scripts", "mansa_musa.json"), encoding="utf-8").read()
    prompt += "\n\nHere is a finished example in the exact format (copy its pace: a new visual every 3-4 seconds):\n" + example
    errors = []
    for model in [cfg.get("gemini_model")] + ["gemini-2.5-flash", "gemini-flash-latest", "gemini-2.5-pro", "gemini-2.0-flash"]:
        if not model:
            continue
        try:
            url = f"https://generativelanguage.googleapis.com/v1beta/models/{model}:generateContent?key={urllib.parse.quote(key)}"
            body = {"contents": [{"parts": [{"text": prompt}]}], "generationConfig": {"responseMimeType": "application/json", "temperature": 0.8}}
            d = http_json(url, json.dumps(body).encode(), {"Content-Type": "application/json"}, timeout=240)
            txt = d["candidates"][0]["content"]["parts"][0]["text"]
            sc = json.loads(txt[txt.find("{"):txt.rfind("}") + 1])
            if not sc.get("scenes"):
                raise ValueError("no scenes")
            slug = re.sub(r"[^a-z0-9]+", "_", topic.lower()).strip("_")[:40] or "new_video"
            path = A("scripts", slug + ".json")
            _json_write(path, sc)
            log(f"Script saved: {path}\nRead it once (facts!), then make the video.")
            return path
        except Exception as e:
            errors.append(f"{model}: {str(e)[:120]}")
    raise RuntimeError("Gemini didn't work: " + " | ".join(errors))


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
