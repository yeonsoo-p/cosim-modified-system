"""The half macro step: one macro step, the output of a partner, its old sample and its new sample.
The old sample is the mean over the step minus half the increment, the new sample the mean plus half the
increment; held over the step, each differs from the signal by a triangle of the area H^2 ydot / 2.
Run:  uv run --no-project --with numpy --with scipy --with matplotlib python fig_halfstep.py
"""
from matplotlib.patches import Polygon

from style import DASH, DOTS, FS, FSS, FULL, G2, INK, NOTE, RUST, TEAL, canvas, plt, save

FW, FH = 0.80 * FULL, 2.05
fig = plt.figure(figsize=(FW, FH))
a = canvas(fig, 0, 0, FW, FH)

X0, X1 = 1.30, 3.55            # t_k, t_{k+1}
Y0, Y1 = 0.72, 1.52            # value of the output at t_k, t_{k+1}
XM, YM = 0.5 * (X0 + X1), 0.5 * (Y0 + Y1)
SL = (Y1 - Y0) / (X1 - X0)

# the two triangles
a.add_patch(Polygon([(X0, Y0), (X1, Y0), (X1, Y1)], closed=True, fc=G2, ec="none", zorder=1))
a.add_patch(Polygon([(X0, Y0), (X0, Y1), (X1, Y1)], closed=True, fc="none", ec=TEAL, lw=0.0, hatch="////",
                    zorder=1, alpha=0.55))
# axis and communication points
a.plot([X0 - 0.75, X1 + 0.55], [0.34, 0.34], color=INK, lw=0.6, zorder=2)
for x, lab in ((X0, r"$t_k$"), (XM, r"$t_k+\frac{1}{2}H$"), (X1, r"$t_{k+1}$")):
    a.plot([x, x], [0.34, Y1 + 0.16] if x != XM else [0.34, YM], color=NOTE, lw=0.5, ls=DOTS, zorder=2)
    a.text(x, 0.27, lab, ha="center", va="top", fontsize=FSS)
# the signal
a.plot([X0 - 0.35, X1 + 0.40], [Y0 - 0.35 * SL, Y1 + 0.40 * SL], color=INK, lw=1.3, zorder=4)
a.text(X1 + 0.44, Y1 + 0.40 * SL, "output $y_k$\nof the partner", ha="left", va="center", fontsize=FSS,
       linespacing=1.1)
# old and new sample, held over the step
a.plot([X0, X1], [Y0, Y0], color=RUST, lw=1.3, zorder=5)
a.plot([X0, X1], [Y1, Y1], color=TEAL, lw=1.3, ls=DASH, zorder=5)
a.plot([X0], [Y0], "o", ms=4.2, mfc=RUST, mec=RUST, zorder=6)
a.plot([X1], [Y1], "o", ms=4.2, mfc=TEAL, mec=TEAL, zorder=6)
a.plot([XM], [YM], "o", ms=3.6, mfc="white", mec=INK, mew=0.9, zorder=6)
a.text(X0 - 0.10, Y0 + 0.17, "old sample:\nhalf a step late", ha="right", va="center", fontsize=FSS, color=RUST,
       linespacing=1.1)
a.text(X0 - 0.10, Y1 + 0.02, "new sample:\nhalf a step early", ha="right", va="center", fontsize=FSS, color=TEAL,
       linespacing=1.1)
a.annotate("mean over\nthe step", (XM, YM), xytext=(X1 + 0.14, YM - 0.02), ha="left", va="center", fontsize=FSS,
           linespacing=1.1, arrowprops=dict(arrowstyle="-", lw=0.5, color=INK, shrinkA=1, shrinkB=3))
a.text(X0 + 0.66 * (X1 - X0), Y0 + 0.07, r"missing: $\frac{1}{2}H^2\dot y_k$", ha="center", va="bottom",
       fontsize=FSS)
a.text(X0 + 0.36 * (X1 - X0), Y1 - 0.10, r"in excess: $\frac{1}{2}H^2\dot y_k$", ha="center", va="top",
       fontsize=FSS)
save(fig, "halfstep")
