"""The order of execution on the chain of three stores: which samples a hold uses in one macro step, what this
passes between the two end stores, which are not partners (the blocks of the half step; the numerical
dissipation of the half step), and what it returns to each store of its own motion (the reaction).

Everything drawn is computed below for the zero-order holds at h = 0.1 and compared with the leading-order
statements of the paper:
  (b) [X - U]_13 and [X - U]_31 in units of h^2/2:  -1 = not passed, +1 = passed twice;
      [Delta_R]_13 and [Delta_J]_13 in units of H omega^2 / 2;
  (c) diag(X - U) in units of h^2/2:  +1 per partner whose reaction is missing, -1 per partner whose
      reaction arrives twice.
Run:  uv run --no-project --with numpy --with scipy --with matplotlib python fig_order.py
"""
import numpy as np
from matplotlib.patches import Rectangle
from scipy.linalg import expm, logm

from style import (DASH, FS, FSS, FULL, G3, INK, NOTE, OCHRE, R_STORE, RUST, TEAL, arrow, canvas, comm_point, link,
                   panel, plt, sample, save, step_bar, store)

# ------------------------------------------------------------------ the numbers
H, r = 0.1, 0.1
A = np.array([[-r, -1.0, 0.0], [1.0, 0.0, -1.0], [0.0, 1.0, -r]])
U = expm(H * A)


def hold(stage):
    """zero-order hold with the given stages (partner weights only)"""
    n = len(A)
    F = np.diag(np.exp(H * np.diag(A)))
    G = np.zeros((n, n))
    for i in range(n):
        for k in range(n):
            if i != k and A[i, k] != 0:
                a = A[i, i]
                G[i, k] = A[i, k] * ((np.exp(H * a) - 1) / a if a != 0 else H)
    N = np.where(np.array(stage)[None, :] < np.array(stage)[:, None], G, 0.0)
    return np.linalg.solve(np.eye(n) - N, F + (G - N))


ROWS = [  # name, order, stages of stores 1, 2, 3, colour
    ("Jacobi scheme", "all stores at\none stage", (1, 1, 1), RUST),
    ("middle store first", "stages 2, 1, 2", (2, 1, 2), OCHRE),
    ("from end to end", "stages 1, 2, 3", (1, 2, 3), TEAL),
]
NUM = []
for name, _, stage, _ in ROWS:
    X = hold(stage)
    E = (X - U) / (H * H / 2)
    D = np.real(logm(X)) / H - A
    dR, dJ = -(D + D.T) / 2, (D - D.T) / 2
    e13, e31 = int(round(E[0, 2])), int(round(E[2, 0]))
    diag = [int(round(v)) for v in np.diag(E)]
    NUM.append(dict(e13=e13, e31=e31, diag=diag, dR=dR[0, 2] / (H / 2), dJ=dJ[0, 2] / (H / 2)))
    print(f"{name:19s} [X-U]_13, _31 / (h^2/2) = {E[0, 2]:+.3f} {E[2, 0]:+.3f}   diag = {np.round(np.diag(E), 3)}"
          f"   [Delta_R]_13, [Delta_J]_13 / (H/2) = {dR[0, 2] / (H / 2):+.3f} {dJ[0, 2] / (H / 2):+.3f}")
assert [(n["e13"], n["e31"]) for n in NUM] == [(-1, -1), (1, 1), (-1, 1)]
assert [n["diag"] for n in NUM] == [[1, 2, 1], [-1, 2, -1], [1, 0, -1]]

# ------------------------------------------------------------------ the drawing
FH = 3.98
fig = plt.figure(figsize=(FULL, FH))
a = canvas(fig, 0, 0, FULL, FH)
YC = (3.03, 2.00, 0.97)
DY, BH = 0.31, 0.15
TK, TK1 = 1.52, 2.62
XB = (3.10, 3.50, 3.90)          # stores, exchange column
XC = (5.25, 5.63, 6.01)          # stores, reaction column
UNIT, BW = 0.115, 0.075

panel(a, 1.05, FH - 0.02, "a", "samples used in\none macro step", linespacing=1.15)
panel(a, 2.95, FH - 0.02, "b", "exchange between\nstores 1 and 3", linespacing=1.15)
panel(a, 4.95, FH - 0.02, "c", "reaction to a\nstore's own motion", linespacing=1.15)

comm_point(a, TK, YC[2] - DY - 0.13, YC[0] + DY + 0.13, "$t_k$")
comm_point(a, TK1, YC[2] - DY - 0.13, YC[0] + DY + 0.13, "$t_{k+1}$")


def sample_arrow(x, y_from, y_to, new):
    s = 1 if y_to > y_from else -1
    arrow(a, (x, y_from + s * (BH / 2 + 0.005)), (x, y_to - s * (BH / 2 + 0.005)), lw=1.7 if new else 0.7,
          ms=7.5 if new else 6)


for (name, order, stage, col), y, num in zip(ROWS, YC, NUM):
    # ---- row label
    a.plot([0.0, 0.26], [y + 0.20, y + 0.20], color=col, lw=2.4, solid_capstyle="butt")
    a.text(0.0, y + 0.07, name, ha="left", va="center", fontsize=FSS)
    a.text(0.0, y - 0.02, order, ha="left", va="top", fontsize=FSS, color=NOTE, linespacing=1.1)
    # ---- (a) lanes of the three stores, their stages and the samples they use
    lane = {i: y + (1 - i) * DY for i in (0, 1, 2)}
    for i in (0, 1, 2):
        store(a, TK - 0.25, lane[i], i + 1)
        step_bar(a, TK + 0.02, TK1 - 0.02, lane[i], BH, f"stage {stage[i]}")
        sample(a, TK, lane[i], color=col, ms=3.6)
        sample(a, TK1, lane[i], color=col, ms=3.6)
    for i, k in ((0, 1), (1, 0), (1, 2), (2, 1)):        # store i uses a sample of its partner k
        new = stage[k] < stage[i]
        off = 0.11 if i < k else 0.24
        sample_arrow(TK1 - off if new else TK + off, lane[k], lane[i], new)
    # ---- (b) what passes between stores 1 and 3 within the step
    link(a, (XB[0], y), (XB[1], y))
    link(a, (XB[1], y), (XB[2], y))
    for x, lab in zip(XB, "123"):
        store(a, x, y, lab)
    for sgn, p, q, yo in ((num["e13"], XB[2], XB[0], +1), (num["e31"], XB[0], XB[2], -1)):   # into 1, into 3
        twice = sgn > 0
        arrow(a, (p, y + yo * (R_STORE + 0.035)), (q, y + yo * (R_STORE + 0.035)), rad=0.42,
              lw=1.7 if twice else 0.8, ls="-" if twice else DASH, ms=7.5 if twice else 6)
    same = num["e13"] == num["e31"]
    part = "energy of the\npair changed" if same else "energy\nmisplaced"
    amount = (r"$%s\frac{1}{2}H\omega^2$" % ("+" if num["dR"] > 0 else "-")) if same else r"$\pm\frac{1}{2}H\omega^2$"
    a.text(XB[2] + 0.24, y + 0.05, part, ha="left", va="center", fontsize=FSS, linespacing=1.1,
           color=INK)
    a.text(XB[2] + 0.24, y - 0.215, amount, ha="left", va="center", fontsize=FS)
    # ---- (c) what each store keeps or receives twice of its own motion
    link(a, (XC[0], y), (XC[1], y))
    link(a, (XC[1], y), (XC[2], y))
    for x, lab, v in zip(XC, "123", num["diag"]):
        store(a, x, y, lab)
        if v > 0:
            a.add_patch(Rectangle((x - BW / 2, y + R_STORE + 0.035), BW, v * UNIT, fc=INK, ec=INK, lw=0.6, zorder=4))
            a.text(x + BW / 2 + 0.035, y + R_STORE + 0.035 + v * UNIT / 2, f"$+{v}$", ha="left", va="center",
                   fontsize=FSS)
        elif v < 0:
            a.add_patch(Rectangle((x - BW / 2, y - R_STORE - 0.035 + v * UNIT), BW, -v * UNIT, fc=G3, ec=INK, lw=0.6,
                                  zorder=4))
            a.text(x + BW / 2 + 0.035, y - R_STORE - 0.035 + v * UNIT / 2, f"$-{-v}$", ha="left", va="center",
                   fontsize=FSS)
        else:
            a.text(x, y + R_STORE + 0.09, "$0$", ha="center", va="center", fontsize=FSS)

# ------------------------------------------------------------------ keys
Y1, Y2 = 0.215, 0.065
KW = dict(ha="left", va="center", fontsize=FSS)
arrow(a, (1.05, Y1), (1.30, Y1), lw=0.7, ms=6)
a.text(1.36, Y1, "sample of $t_k$", **KW)
arrow(a, (1.05, Y2), (1.30, Y2), lw=1.7, ms=7.5)
a.text(1.36, Y2, "new sample, of $t_{k+1}$", **KW)
arrow(a, (2.95, Y1), (3.20, Y1), lw=0.8, ms=6, ls=DASH)
a.text(3.26, Y1, "not passed", **KW)
arrow(a, (2.95, Y2), (3.20, Y2), lw=1.7, ms=7.5)
a.text(3.26, Y2, r"passed twice (once: $\frac{1}{2}h^2$)", **KW)
a.add_patch(Rectangle((4.95, Y1 - 0.045), BW, 0.09, fc=INK, ec=INK, lw=0.6))
a.text(5.08, Y1, r"missing (units of $\frac{1}{2}h^2$)", **KW)
a.add_patch(Rectangle((4.95, Y2 - 0.045), BW, 0.09, fc=G3, ec=INK, lw=0.6))
a.text(5.08, Y2, "received twice", **KW)
save(fig, "order")
