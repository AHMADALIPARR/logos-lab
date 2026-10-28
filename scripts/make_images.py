# SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
# Copyright Ahmad Ali Parr
"""Draws the retro gallery in docs/img/ with Pillow. The Prolog answers in the
terminal image come from running swipl on the parent/ancestor program of
logic_kernels/metagol.pl."""
import os, random, subprocess, tempfile
from PIL import Image, ImageDraw, ImageFont, ImageFilter, ImageChops

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, "docs", "img")
MONO = "/usr/share/fonts/truetype/dejavu/DejaVuSansMono.ttf"
BOLD = "/usr/share/fonts/truetype/dejavu/DejaVuSansMono-Bold.ttf"
def F(sz, bold=False): return ImageFont.truetype(BOLD if bold else MONO, sz)

def save(img, name):
    img = img.convert("RGB")
    p = os.path.join(OUT, name)
    img.save(p, optimize=True)
    if os.path.getsize(p) > 280_000:
        img.quantize(colors=128, method=Image.Quantize.MEDIANCUT).save(p, optimize=True)
    print(name, os.path.getsize(p))

def glow(layer, r=4, k=1.0):
    b = layer.filter(ImageFilter.GaussianBlur(r))
    return ImageChops.add(layer, b.point(lambda v: int(v * k)))

def scanlines(img, strength=70, step=3):
    d = ImageDraw.Draw(img, "RGBA")
    for y in range(0, img.height, step):
        d.line([(0, y), (img.width, y)], fill=(0, 0, 0, strength))
    return img

def vignette(img, power=1.6, amt=0.55):
    w, h = img.size
    m = Image.radial_gradient("L").resize((w, h))
    m = m.point(lambda v: int(255 * (1 - amt * (v / 255) ** power)))
    return ImageChops.multiply(img, Image.merge("RGB", (m, m, m)))

def crt(draw_fn, size, ink, bg, name, bezel=True):
    w, h = size
    txt = Image.new("RGB", (w, h), (0, 0, 0))
    draw_fn(ImageDraw.Draw(txt), txt)
    scr = Image.new("RGB", (w, h), bg)
    scr = ImageChops.add(scr, glow(txt, 5, 0.9))
    scr = ImageChops.lighter(scr, txt)
    scr = vignette(scanlines(scr))
    if not bezel:
        save(scr, name); return
    pad = 34
    full = Image.new("RGB", (w + 2 * pad, h + 2 * pad), (58, 52, 44))
    d = ImageDraw.Draw(full)
    d.rectangle([0, 0, full.width - 1, full.height - 1], outline=(30, 27, 22), width=6)
    d.rectangle([pad - 6, pad - 6, pad + w + 5, pad + h + 5], fill=(12, 12, 10))
    mask = Image.new("L", (w, h), 0)
    ImageDraw.Draw(mask).rounded_rectangle([0, 0, w - 1, h - 1], 28, fill=255)
    full.paste(scr, (pad, pad), mask)
    d.ellipse([full.width - 54, full.height - 26, full.width - 40, full.height - 12], fill=ink)
    d.text((pad, full.height - 28), "LOGOS-LAB  MODEL 1", font=F(12, True), fill=(150, 140, 120))
    save(full, name)

# ---------- 1. banner ----------
def banner():
    w, h = 1200, 300
    amber = (255, 176, 0)
    def draw(d, im):
        d.text((60, 52), "LOGOS-LAB", font=F(104, True), fill=amber)
        d.text((64, 178), "unify  >  search  >  prove", font=F(34), fill=amber)
        d.text((64, 232), "Prolog . miniKanren . Twelf . Boogie . Why3 . DLV . Logica", font=F(20), fill=(200, 140, 0))
        for i, lab in enumerate(["Var", "Atom", "Pair", "Nil"]):
            x = 880 + (i % 2) * 150; y = 70 + (i // 2) * 90
            d.rounded_rectangle([x, y, x + 120, y + 60], 8, outline=amber, width=3)
            d.text((x + 60, y + 30), lab, font=F(26, True), fill=amber, anchor="mm")
        d.text((1000, 255), "term := Var | Atom | Pair | Nil", font=F(15), fill=(200, 140, 0), anchor="mm")
    crt(draw, (w, h), amber, (14, 8, 0), "banner.png", bezel=False)

# ---------- 2. green phosphor terminal ----------
def prolog_session():
    prog = open(os.path.join(ROOT, "logic_kernels", "metagol.pl")).read()
    facts = [l.strip() for l in prog.splitlines() if l.startswith("parent(")]
    rules = ["ancestor(A,B) :- parent(A,B).", "ancestor(A,B) :- parent(A,C), ancestor(C,B)."]
    with tempfile.NamedTemporaryFile("w", suffix=".pl", delete=False) as f:
        f.write("\n".join(facts + rules) + "\n"); path = f.name
    def ask(goal, var):
        out = subprocess.check_output(["swipl", "-q", "-g",
            f"forall({goal},(write({var}),nl))", "-t", "halt", path], text=True).split()
        return out
    a = ask("ancestor(ada,X)", "X"); b = ask("ancestor(bob,X)", "X")
    c = subprocess.check_output(["swipl", "-q", "-g",
        "(ancestor(dee,ada)->write(true);write(false)),nl", "-t", "halt", path], text=True).strip()
    os.unlink(path)
    return facts, rules, a, b, c

def terminal():
    facts, rules, a, b, c = prolog_session()
    lines = ["SWI-Prolog  --  logic_kernels/metagol.pl facts", "", "?- listing(parent/2)."]
    lines += ["  " + x for x in facts] + ["", "?- listing(ancestor/2)."] + ["  " + r for r in rules] + [""]
    lines += ["?- ancestor(ada, X)."]
    lines += [f"X = {v} ;" if i < len(a) - 1 else f"X = {v}." for i, v in enumerate(a)]
    lines += ["", "?- ancestor(bob, X)."]
    lines += [f"X = {v} ;" if i < len(b) - 1 else f"X = {v}." for i, v in enumerate(b)]
    lines += ["", "?- ancestor(dee, ada).", c + ".", "", "?- "]
    green = (80, 255, 120)
    sz = 22; lh = 28
    h = lh * len(lines) + 60
    def draw(d, im):
        for i, l in enumerate(lines):
            col = green if not l.startswith("  ") else (60, 205, 95)
            d.text((40, 30 + i * lh), l, font=F(sz, l.startswith("?-")), fill=col)
        d.rectangle([40 + 3 * 13.2, 30 + (len(lines) - 1) * lh + 3, 40 + 4 * 13.2, 30 + len(lines) * lh - 4], fill=green)
    crt(draw, (860, h), green, (0, 12, 4), "crt_prolog.png")
    return lines

# ---------- 3. mainframe panel + punched card ----------
HOLL = {}
for i, ch in enumerate("ABCDEFGHI"): HOLL[ch] = (12, i + 1)
for i, ch in enumerate("JKLMNOPQR"): HOLL[ch] = (11, i + 1)
for i, ch in enumerate("STUVWXYZ"): HOLL[ch] = (0, i + 2)
for i in range(10): HOLL[str(i)] = (i,)
HOLL.update({"(": (12, 5, 8), ")": (12, 4, 8), ",": (0, 3, 8), ".": (12, 3, 8), " ": ()})
ROWS = [12, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

def mainframe():
    w, h = 1200, 760
    img = Image.new("RGB", (w, h), (176, 168, 148))
    d = ImageDraw.Draw(img)
    rnd = random.Random(7)
    for _ in range(9000):  # paint grain
        x, y = rnd.randrange(w), rnd.randrange(h); v = rnd.randrange(-10, 10)
        img.putpixel((x, y), (176 + v, 168 + v, 148 + v))
    d.rectangle([0, 0, w - 1, h - 1], outline=(70, 64, 52), width=8)
    d.rectangle([24, 24, w - 25, 150], fill=(52, 60, 70), outline=(30, 34, 40), width=4)
    d.text((48, 36), "LOGOS-LAB  CENTRAL PROCESSOR", font=F(34, True), fill=(232, 224, 200))
    d.text((48, 86), "UNIFICATION  /  SEARCH  /  PROOF", font=F(20), fill=(190, 184, 164))
    # goal lamps from Logos.mlw
    goals = ["SUCCESS", "FAILURE", "EQ", "CONJ", "DISJ", "DELAY"]
    kern = ["METAGOL", "TWELF", "BOOGIE", "LOGICA", "DLV"]
    def lamps(labels, y, color, title):
        nonlocal img, d
        d = ImageDraw.Draw(img)
        d.text((48, y - 78), title, font=F(18, True), fill=(40, 36, 28))
        gap = (w - 96) // len(labels)
        for i, lab in enumerate(labels):
            cx = 48 + gap * i + gap // 2
            lamp = Image.new("RGB", (w, h), (0, 0, 0))
            ImageDraw.Draw(lamp).ellipse([cx - 26, y - 26, cx + 26, y + 26], fill=color)
            img = ImageChops.add(img, glow(lamp, 14, 0.9))
            d = ImageDraw.Draw(img)
            d.ellipse([cx - 34, y - 34, cx + 34, y + 34], outline=(50, 46, 38), width=6)
            d.ellipse([cx - 26, y - 26, cx + 26, y + 26], fill=color)
            d.ellipse([cx - 14, y - 20, cx - 2, y - 10], fill=tuple(min(255, c + 90) for c in color))
            d.text((cx, y + 52), lab, font=F(19, True), fill=(40, 36, 28), anchor="mm")
        return d
    d = lamps(goals, 250, (255, 150, 30), "GOAL FORMS  (Logos.mlw)")
    d = lamps(kern, 400, (120, 255, 110), "KERNELS  (logic_kernels/)")
    # punched card
    cx0, cy0, cw, ch = 70, 500, 1060, 220
    d.rectangle([cx0 + 6, cy0 + 6, cx0 + cw + 6, cy0 + ch + 6], fill=(110, 104, 90))
    d.polygon([(cx0, cy0 + 30), (cx0 + 30, cy0), (cx0 + cw, cy0), (cx0 + cw, cy0 + ch), (cx0, cy0 + ch)], fill=(238, 226, 190), outline=(120, 108, 80))
    d.rectangle([cx0, cy0 + ch - 10, cx0 + cw, cy0 + ch], fill=(228, 200, 120))
    text = "ANCESTOR(ADA,X)."
    colw = 12.6; x0 = cx0 + 36; rowh = 14.2; y0 = cy0 + 52
    d.text((x0, cy0 + 8), text, font=F(15, True), fill=(150, 40, 30))
    for col in range(80):
        ch_ = text[col] if col < len(text) else " "
        punch = HOLL.get(ch_, ())
        x = x0 + col * colw
        for r, row in enumerate(ROWS):
            y = y0 + r * rowh
            if row in punch:
                d.rectangle([x + 1, y + 1, x + 7, y + 10], fill=(62, 56, 44))
            else:
                if row not in (11, 12):
                    d.text((x + 4, y + 5), str(row), font=F(8), fill=(190, 160, 140), anchor="mm")
    d = ImageDraw.Draw(img)
    img = vignette(img, 2.0, 0.35)
    save(img, "mainframe_panel.png")

# ---------- 4. amber unify diagram ----------
def unify_diagram():
    amber = (255, 176, 0); dim = (200, 135, 0)
    W, H = 1000, 640
    def box(d, cx, cy, lab, w=150, hh=54, col=amber):
        d.rounded_rectangle([cx - w // 2, cy - hh // 2, cx + w // 2, cy + hh // 2], 8, outline=col, width=3)
        d.text((cx, cy), lab, font=F(22, True), fill=col, anchor="mm")
    def arrow(d, p, q, col=amber):
        d.line([p, q], fill=col, width=3)
        import math
        a = math.atan2(q[1] - p[1], q[0] - p[0])
        for s in (-0.45, 0.45):
            d.line([q, (q[0] - 14 * math.cos(a + s), q[1] - 14 * math.sin(a + s))], fill=col, width=3)
    def draw(d, im):
        d.text((W // 2, 34), "unify 20 a b []     (logos_whyml/Logos.mlw)", font=F(24, True), fill=amber, anchor="mm")
        d.text((250, 90), "a", font=F(24, True), fill=dim, anchor="mm")
        d.text((750, 90), "b", font=F(24, True), fill=dim, anchor="mm")
        box(d, 250, 140, "Pair", 130); box(d, 150, 250, "Var 0"); box(d, 350, 250, "Atom 7")
        arrow(d, (225, 166), (170, 224)); arrow(d, (275, 166), (330, 224))
        box(d, 750, 140, "Pair", 130); box(d, 650, 250, "Atom 3"); box(d, 850, 250, "Var 1")
        arrow(d, (725, 166), (670, 224)); arrow(d, (775, 166), (830, 224))
        d.line([(320, 140), (680, 140)], fill=dim, width=2)
        d.text((500, 120), "match", font=F(18), fill=dim, anchor="mm")
        # steps
        d.text((60, 330), "step 1   Var 0 meets Atom 3", font=F(22, True), fill=amber)
        d.text((60, 364), "         occurs check passes -> bind 0 := Atom 3", font=F(19), fill=dim)
        d.text((60, 410), "step 2   Atom 7 meets Var 1", font=F(22, True), fill=amber)
        d.text((60, 444), "         occurs check passes -> bind 1 := Atom 7", font=F(19), fill=dim)
        d.rounded_rectangle([40, 500, W - 40, 600], 10, outline=amber, width=3)
        d.text((60, 512), "result  Some s", font=F(22, True), fill=amber)
        d.text((60, 552), "s = [ {key=1; value=Atom 7} ; {key=0; value=Atom 3} ]", font=F(23, True), fill=amber)
    crt(draw, (W, H), amber, (14, 8, 0), "unify_amber.png")

if __name__ == "__main__":
    os.makedirs(OUT, exist_ok=True)
    banner(); terminal(); mainframe(); unify_diagram()
