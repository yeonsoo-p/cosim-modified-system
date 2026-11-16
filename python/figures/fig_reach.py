"""Each held sample shows a subsystem one more link (section "The half step with more held samples").

(a) what the end store of a chain is shown with l = 1, 2, 3 held samples;
(b) the bound f_1 of the end store of a lossless chain of six stores with unit rates (Jacobi scheme),
    computed from the definition of the states not shown:  f_1 = max |e_1^T U v| over unit v with v_1 = 0 and
    e_2^T U^{-q} v = 0 for q = 0..l-1, against its leading value gamma_l h^(l+1).
Run:  uv run --no-project --with numpy --with scipy --with matplotlib python fig_reach.py
"""
import numpy as np
from scipy.linalg import expm, null_space

from style import (DASH, FS, FSS, FULL, G2, INK, LW_DATA, NOTE, R_STORE, SOFT, canvas, h_ticks, link, log_decades,
                   panel, plot_axes, plt, save, store)

GAMMA = {1: 1 / 2, 2: 5 / 12, 3: 3 / 8, 4: 251 / 720}      # gamma_l^0, the error constants of the explicit Adams methods


def chain(n):
    A = np.zeros((n, n))
    for k in range(n - 1):
        A[k, k + 1], A[k + 1, k] = -1.0, 1.0
    return A


def bound(h, ell, n=6):
    A = chain(n)
    U = expm(h * A)
    Ui = np.linalg.inv(U)
    rows = [np.eye(n)[0]]
    P = np.eye(n)
    for _ in range(ell):
        rows.append(P[1])            # e_2^T U^{-r}
        P = P @ Ui
    V = null_space(np.array(rows))
    return np.linalg.norm(U[0] @ V)


hs = np.geomspace(0.05, 0.3, 9)
F = {ell: np.array([bound(h, ell) for h in hs]) for ell in (1, 2, 3, 4)}
for ell in F:
    print(f"l = {ell}: f_1 / (gamma_l h^(l+1)) at h = 0.05, 0.1, 0.3:",
          " ".join(f"{bound(h, ell) / (GAMMA[ell] * h ** (ell + 1)):.4f}" for h in (0.05, 0.1, 0.3)),
          "| with 8 stores at h = 0.1:", f"{bound(0.1, ell, 8) / (GAMMA[ell] * 0.1 ** (ell + 1)):.4f}")

FH = 2.40
fig = plt.figure(figsize=(FULL, FH))
# ------------------------------------------------------------- (a) what the end store is shown
a = canvas(fig, 0, 0, 3.55, FH)
panel(a, 0.0, FH - 0.02, "a", "what store 1 is shown")
XS = [0.95 + 0.47 * k for k in range(6)]
YR = {1: 1.62, 2: 1.05, 3: 0.48}
for ell, y in YR.items():
    a.text(0.0, y, f"{ell} held\nsample" + ("s" if ell > 1 else ""), va="center", ha="left", fontsize=FSS,
           linespacing=1.1)
    for k, (p, q) in enumerate(zip(XS[:-1], XS[1:])):
        link(a, (p, y), (q, y), ls="-" if k < ell else DASH)
    for k, x in enumerate(XS):
        shown, first = k <= ell, k == ell + 1
        store(a, x, y, k + 1, fc="white" if shown else (INK if first else G2), color="white" if first else INK)
    xa, xb = XS[0] - 0.17, XS[ell] + 0.17
    a.plot([xa, xb, xb, xa, xa], [y - 0.17, y - 0.17, y + 0.17, y + 0.17, y - 0.17], color=SOFT, lw=0.7)
    a.text(XS[ell + 1], y - 0.15, r"$\gamma_{%d}^0h^{%d}$" % (ell, ell + 1), ha="center", va="top", fontsize=FS)
a.text(XS[0] - 0.17, YR[1] + 0.21, "shown to store 1", ha="left", va="bottom", fontsize=FSS, color=NOTE)
a.text(XS[2], YR[1] + 0.21, "nearest store that is not shown", ha="left", va="bottom", fontsize=FSS)
a.text(0.0, 0.03, r"response of store 1 to it in one macro step: $\gamma_\ell^0 h^{\ell+1}$", ha="left", va="bottom",
       fontsize=FSS, color=NOTE)

# ------------------------------------------------------------- (b) the bound against the macro step
ax = plot_axes(fig, 4.38, 0.44, 1.52, 1.62)
for ell in (1, 2, 3, 4):
    ax.loglog(hs, F[ell], color=INK, lw=LW_DATA, zorder=3)
    ax.loglog(hs[::2], GAMMA[ell] * hs[::2] ** (ell + 1), ls="none", marker="o", ms=3.8, mfc="white", mec=INK,
              mew=0.9, zorder=4)
    ax.text(0.325, F[ell][-1], r"$\ell=%d$" % ell, fontsize=FSS, va="center", ha="left")
ax.set_xlim(0.05, 0.3)
ax.set_ylim(5e-8, 0.1)
ax.set_xlabel(r"macro step, $h=\omega H$")
ax.set_ylabel(r"bound of store 1, $f_1$")
h_ticks(ax, [0.05, 0.1, 0.2, 0.3])
log_decades(ax, -7, -1)
ax.plot([0.056], [0.045], ls="none", marker="o", ms=3.8, mfc="white", mec=INK, mew=0.9)
ax.text(0.062, 0.045, r"$\gamma_\ell^0\,h^{\ell+1}$", fontsize=FSS, va="center", ha="left")
fig.text(3.72 / FULL, (FH - 0.02) / FH, "(b) one order per held sample", fontsize=FS, va="top", ha="left")
save(fig, "reach")
