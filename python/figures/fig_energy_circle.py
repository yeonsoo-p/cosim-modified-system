"""The two parts of the difference in the example "zero-order hold on an undamped pair" (Jacobi scheme).

The state (x_1, x_2) in energy coordinates, read as the complex number x_1 + i x_2, starts on the circle of
constant energy.  The monolithic system turns it by the angle h per macro step.  The hold moves it along
the tangent, X = I + h J, to (1 + i h)^k.  The modified system is the continuous-time system whose flow
passes through these communication points: a spiral.  Closed forms of the example:
  numerical dissipation      radial:   the energy is multiplied by 1 + h^2 per step,
  numerical interconnection  angular:  the hold lags by h - arctan h per step.
Drawn for h = 1 (legibility).  Printed at the text width.
Run:  uv run --no-project --with numpy --with scipy --with matplotlib python fig_energy_circle.py
"""
import cmath
import math

import numpy as np
from matplotlib.patches import Arc

from style import (DASH, DOTS, FAINT, FS, FSS, G1, INK, LW_AUX, FULL, NOTE, RUST, SOFT, arrow, plt, save)

h = 1.0
NSTEP = 2
growth = math.sqrt(1 + h * h)
ang = math.atan(h)
lam = complex(math.log(growth), ang)        # H times the eigenvalue of the modified system on x_1 + i x_2

XL, YL = (-3.30, 4.05), (-1.16, 2.36)
NL = chr(10)
W = FULL
fig = plt.figure(figsize=(W, W * (YL[1] - YL[0]) / (XL[1] - XL[0])))
ax = fig.add_axes([0, 0, 1, 1])
ax.set_aspect("equal")
ax.axis("off")
LEAD = dict(arrowstyle="-", lw=0.5, color=INK, shrinkA=3, shrinkB=3)

# energy coordinates and the circle of constant energy
tt = np.linspace(0, 2 * math.pi, 400)
ax.fill(np.cos(tt), np.sin(tt), color=G1, lw=0, zorder=0)
ax.plot(np.cos(tt), np.sin(tt), color=INK, lw=0.8, zorder=2)
arrow(ax, (-1.0, 0), (1.42, 0), color=SOFT, lw=LW_AUX, ms=5, z=1)
arrow(ax, (0, -1.0), (0, 1.42), color=SOFT, lw=LW_AUX, ms=5, z=1)
ax.text(1.47, 0.0, r"$x_1$", fontsize=FSS, ha="left", va="center", color=NOTE)
ax.text(-0.05, 1.40, r"$x_2$", fontsize=FSS, ha="right", va="center", color=NOTE)
for k in range(1, NSTEP + 1):               # circles through the communication points of the hold
    r = growth ** k
    t2 = np.linspace(k * ang - 0.50, k * ang + (0.55 if k == 1 else 0.30), 80)
    ax.plot(r * np.cos(t2), r * np.sin(t2), color=FAINT, lw=0.6, zorder=1)

# monolithic system: along the circle (ink)
t = np.linspace(0, NSTEP * h, 300)
ax.plot(np.cos(t), np.sin(t), color=INK, lw=2.4, zorder=3)
for k in range(NSTEP + 1):
    z = cmath.exp(1j * k * h)
    ax.plot([z.real], [z.imag], "o", ms=5.5, color=INK, zorder=7, mec="white", mew=0.7)
for k, (dx, dy) in zip((1, 2), ((-0.19, -0.05), (0.06, -0.15))):
    z = cmath.exp(1j * k * h)
    ax.text(z.real + dx, z.imag + dy, r"$t_%d$" % k, fontsize=FSS, ha="center", va="center", color=INK)
ax.text(1.05, -0.07, r"$t_0$", fontsize=FSS, ha="left", va="top")

# the hold in a Jacobi scheme (rust): tangent moves, communication points, modified system through them
s = np.linspace(0, NSTEP, 400)
zz = np.exp(lam * s)
ax.plot(zz.real, zz.imag, color=RUST, lw=1.2, ls=DASH, zorder=4, dash_capstyle="butt")
for k in range(NSTEP):
    z0, z1 = (1 + 1j * h) ** k, (1 + 1j * h) ** (k + 1)
    ax.plot([z0.real, z1.real], [z0.imag, z1.imag], color=RUST, lw=0.6, zorder=3)
for k, (dx, dy) in zip((1, 2), ((0.15, 0.02), (0.02, 0.15))):
    z = (1 + 1j * h) ** k
    ax.plot([z.real], [z.imag], "o", ms=5.5, mfc="white", mec=RUST, mew=1.1, zorder=7)
    ax.text(z.real + dx, z.imag + dy, r"$t_%d$" % k, fontsize=FSS, ha="center", va="center", color=RUST)

# the two parts of the difference after the first step
z1 = 1 + 1j * h
u1 = z1 / abs(z1)
r1 = cmath.exp(1j * h)
ax.plot([0, u1.real], [0, u1.imag], color=SOFT, lw=0.5, ls=DOTS, zorder=1)
ax.plot([0, 1.30 * r1.real], [0, 1.30 * r1.imag], color=SOFT, lw=0.5, ls=DOTS, zorder=1)
ax.plot([u1.real, z1.real], [u1.imag, z1.imag], color=INK, lw=3.6, zorder=5, solid_capstyle="butt")   # radial excess
RL = 1.21
t3 = np.linspace(ang, h, 40)
ax.plot(RL * np.cos(t3), RL * np.sin(t3), color=SOFT, lw=3.6, zorder=5, solid_capstyle="butt")        # lag
ax.add_patch(Arc((0, 0), 0.50, 0.50, theta1=0, theta2=math.degrees(h), color=INK, lw=0.6))
ax.text(0.27, 0.10, r"$h$", fontsize=FSS, ha="left", va="center")
ax.plot([0], [0], "o", ms=2.2, color=INK)

# labels
KW = dict(fontsize=FS, va="center", linespacing=1.15)
zb = 0.5 * (u1 + z1)
ax.plot([zb.real + 0.03, 1.24], [zb.imag - 0.09, -0.30], color=INK, lw=0.5, zorder=6)
ax.text(1.24, -0.36, "numerical dissipation, here negative:" + NL + "the communication points leave" + NL
        + "the circle of constant energy", fontsize=FS, ha="left", va="top", linespacing=1.15)
mid = RL * cmath.exp(1j * (0.25 * ang + 0.75 * h))
ax.annotate("numerical interconnection:" + NL + "the hold lags in angle" + NL + "by " + r"$h-\arctan h$" + " per step",
            (mid.real, mid.imag), xytext=(-1.32, 1.50), ha="center", arrowprops=LEAD, **KW)
zr = cmath.exp(1j * 1.62)
ax.annotate("monolithic system: stays on" + NL + "the circle of constant energy", (zr.real, zr.imag),
            xytext=(-3.27, 0.62), ha="left", arrowprops=LEAD, **KW)
zc = (1 + 1j * h) ** NSTEP
ax.annotate("zero-order hold, Jacobi scheme:" + NL + "its communication points", (zc.real, zc.imag), xytext=(-0.62, 2.10),
            ha="right", arrowprops=dict(LEAD, color=RUST), color=RUST, **KW)
zm = np.exp(lam * 1.5)
ax.annotate("modified system: the flow" + NL + "through the communication" + NL + "points", (zm.real, zm.imag),
            xytext=(1.75, 1.52), ha="left", arrowprops=dict(LEAD, color=RUST), color=RUST, **KW)
for k in (1, 2):                              # energy on the circles through the communication points
    r, a1 = growth ** k, k * ang - 0.50
    ax.text(r * math.cos(a1) + 0.07, r * math.sin(a1) - 0.03,
            r"energy $\times\,(1+h^2)$" if k == 1 else r"$\times\,(1+h^2)^2$", fontsize=FSS, ha="left", va="center",
            color=NOTE)
ax.text(XL[0] + 0.03, YL[0] + 0.05, r"drawn for $h=\omega H=1$", fontsize=FSS, ha="left", va="bottom", color=NOTE)

ax.set_xlim(*XL)
ax.set_ylim(*YL)
save(fig, "energy_circle")
print("h", h, "energy factor per step", growth ** 2, "lag per step", h - ang)
