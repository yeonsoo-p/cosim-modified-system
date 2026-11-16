"""The bound on the one-step error on the chain of three stores in a Jacobi scheme (example "the chain of three
stores").

Plotted against the macro step h: the bound alpha_* on the one-step error alpha (what store 1 is not shown:
the state of store 3, which the monolithic system passes to it through two links, entry U_13, about h^2/2);
the smallest alpha of a stable Jacobi scheme with local gains (circles; the values are printed by
../numbers/optimal_schemes.py, rounded to four decimals); and the two zero-order holds (Jacobi scheme;
sequential scheme from end to end).
System: A = [[-r,-1,0],[1,0,-1],[0,1,-r]], r = 0.1 (omega = 1).
Run:  uv run --no-project --with numpy --with scipy --with matplotlib python fig_visibility.py
"""
import math

import numpy as np
from matplotlib.patches import Circle
from scipy.linalg import expm

from style import (DASH, FS, FSS, FULL, G2, INK, LW_BOUND, LW_DATA, NOTE, R_STORE, RUST, TEAL, arrow, canvas,
                   h_ticks, link, log_decades, panel, plot_axes, plt, save, store)

R = (0.1, 0.0, 0.1)
A = np.array([[-R[0], -1.0, 0.0], [1.0, -R[1], -1.0], [0.0, 1.0, -R[2]]])


def phi1(z):
    return 1.0 if abs(z) < 1e-12 else (math.exp(z) - 1.0) / z


def zoh_jacobi(h):
    X = np.diag([math.exp(-r * h) for r in R])
    for i in range(3):
        for j in range(3):
            if i != j:
                X[i, j] = A[i, j] * h * phi1(-R[i] * h)
    return X


def zoh_seq(h):
    """zero-order hold, stores executed in the order 1, 2, 3"""
    E = [math.exp(-r * h) for r in R]
    m = [[A[i, j] * h * phi1(-R[i] * h) for j in range(3)] for i in range(3)]
    X = np.zeros((3, 3))
    X[0] = [E[0], m[0][1], 0.0]
    X[1] = m[1][0] * X[0] + np.array([0.0, E[1], m[1][2]])
    X[2] = m[2][1] * X[1] + np.array([0.0, 0.0, E[2]])
    return X


def alpha(X, U):
    return np.linalg.norm(X @ np.linalg.inv(U) - np.eye(3), 2)


def bound(U):
    """the bound alpha_* on alpha for the end stores: max |Pi_i U v| / |U v| over the states not shown to i"""
    return max(abs(U[0, 2]) / np.linalg.norm(U[:, 2]), abs(U[2, 0]) / np.linalg.norm(U[:, 0]))


TABLE_H = [0.1, 0.2, 0.3, 0.5]
BEST = [0.0050, 0.0200, 0.0447, 0.1214]     # smallest alpha of a stable Jacobi scheme, ../numbers/optimal_schemes.py

FH = 2.62
FW = 3.60
fig = plt.figure(figsize=(FW, FH))
bx = plot_axes(fig, 0.72, 0.44, 2.72, 1.98)

# ================================================================= (b) one-step error against the macro step
hs = np.geomspace(0.05, 1.0, 60)
fl = np.array([bound(expm(h * A)) for h in hs])
aj = np.array([alpha(zoh_jacobi(h), expm(h * A)) for h in hs])
ag = np.array([alpha(zoh_seq(h), expm(h * A)) for h in hs])
bx.fill_between(hs, 1e-4, fl, color=G2, lw=0, zorder=0)
bx.plot(hs, fl, color=INK, lw=LW_BOUND, zorder=3)
bx.plot(hs, aj, color=RUST, lw=LW_DATA, zorder=3)
bx.plot(hs, ag, color=TEAL, lw=LW_DATA, zorder=3, ls=(0, (5, 1.6)), dash_capstyle="butt")
bx.plot(TABLE_H, BEST, "o", ms=4.6, mfc="white", mec=RUST, mew=1.0, zorder=5)
bx.set_xscale("log")
bx.set_yscale("log")
bx.set_xlim(0.05, 1.0)
bx.set_ylim(1e-3, 1.5)
h_ticks(bx, [0.05, 0.1, 0.2, 0.5, 1.0])
log_decades(bx, -3, 0)
bx.set_xlabel(r"macro step, $h=\omega H$")
bx.set_ylabel(r"one-step error, $\alpha$")
KW = dict(fontsize=FSS, linespacing=1.1)
bx.text(0.95, 0.0092, "below the bound:\nexcluded for every\nJacobi scheme",
        ha="right", va="center", **KW)
bx.annotate("stable schemes with local\ngains, smallest " + r"$\alpha$" + " found", (TABLE_H[0], BEST[0]),
            xytext=(0.27, 0.00185), ha="center", va="center", color=RUST,
            arrowprops=dict(arrowstyle="-", lw=0.5, color=RUST, shrinkA=2, shrinkB=4), **KW)
bx.text(0.056, 1.25, "zero-order holds:", ha="left", va="center", **KW)
bx.text(0.056, 0.62, r"Jacobi scheme (unstable for $h>0.05$)", ha="left", va="center", color=RUST, **KW)
bx.text(0.056, 0.31, "sequential scheme,\nfrom end to end", ha="left", va="center", color=TEAL, **KW)

save(fig, "visibility")
print("h      alpha_*    zoh Jacobi  zoh seq   ratioJ ratioS  h^2/2   circles")
for h in TABLE_H + [0.05, 1.0]:
    U = expm(h * A)
    f, a1, a2 = bound(U), alpha(zoh_jacobi(h), U), alpha(zoh_seq(h), U)
    b = dict(zip(TABLE_H, BEST)).get(h)
    print(f"{h:<5} {f:9.5f} {a1:9.5f} {a2:9.5f} {a1 / f:6.3f} {a2 / f:6.3f} {h * h / 2:8.5f}  "
          f"rhoJ={max(abs(np.linalg.eigvals(zoh_jacobi(h)))):.4f} rhoS={max(abs(np.linalg.eigvals(zoh_seq(h)))):.4f}"
          + (f"  best/bound={b / f:.4f}" if b else ""))
for h in (0.05, 0.051, 0.06):
    print(f"Jacobi zero-order hold, h = {h}: spectral radius - 1 = {max(abs(np.linalg.eigvals(zoh_jacobi(h)))) - 1:+.2e}")
