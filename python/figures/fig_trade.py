"""The trade between injection and added damping on the chain of three stores at h = 0.1: the schemes of the
example on the order of execution, read as sentences.

Axes, in units of the bound alpha_* on the one-step error: the energy injected over a step, (s_+ - 1)/alpha_*,
and the damping added over a step, (1 - s_-)/alpha_*. The dashed line is the forced amount of the theorem on
the amount, injection plus added damping = 2 alpha_* (mu + iota = H omega^2), which holds to leading order in
the macro step where the middle store does not run between the end stores. Marks: for each order of execution
the scheme with local gains that has the smallest one-step error (circle), and the one with the smallest
one-step error among those that inject no energy over a step (square).

The positions of the marks are the values printed by ../numbers/optimal_schemes.py, rounded to three
decimals: global optima of convex programmes in the Jacobi scheme, smallest values found by a local search
with the middle store first. From end to end the minimiser is not unique, and
the mark is the energy-conserving sweep with the dissipation of the chain, exp(-HR/2) X exp(-HR/2), computed by
../numbers/order_of_execution.py: (0.0066, 0.0066), one-step error 1.001 alpha_*.
Run:  uv run --no-project --with numpy --with scipy --with matplotlib python fig_trade.py
"""
from style import (DASH, DOTS, FS, FSS, G2, INK, LW_BOUND, MEDIUM, NOTE, OCHRE, RUST, TEAL, plot_axes, plt, save)

# (s_+ - 1)/alpha_*, (1 - s_-)/alpha_*
BEST = {"jacobi": (0.995, 1.000), "middle": (0.993, 0.989), "end": (0.0066, 0.0066)}
NOINJ = {"jacobi": (0.000, 1.759), "middle": (0.000, 1.963)}
COL = {"jacobi": RUST, "middle": OCHRE, "end": TEAL}

FW, FH = MEDIUM, 2.96
fig = plt.figure(figsize=(FW, FH))
AX0, AY0, AS = 0.62, 0.46, 2.30
ax = plot_axes(fig, AX0, AY0, AS, AS)
LIM = 2.3
ax.fill([0, 2, 0], [0, 0, 2], fc=G2, ec="none", zorder=0)
ax.plot([2, 0], [0, 2], color=INK, lw=LW_BOUND, ls=DASH, zorder=3)
ax.plot([0, LIM], [0, 0], color=NOTE, lw=0.5, ls=DOTS, zorder=1)
ax.plot([0, 0], [0, LIM], color=NOTE, lw=0.5, ls=DOTS, zorder=1)
KW = dict(fontsize=FSS, linespacing=1.12)
ax.text(0.13, 0.66, "not reached,\nto leading order,\nif the middle store\ndoes not run between\nthe end stores", ha="left", va="center",
        zorder=4, **KW)
ax.text(1.12, 1.30, "injection plus\nadded damping " + r"$=2\alpha_*$", ha="left", va="bottom", zorder=4, **KW)

ax.plot(*BEST["jacobi"], marker="o", ms=8.0, mfc="white", mec=RUST, mew=1.2, zorder=7)
ax.plot(*BEST["middle"], marker="o", ms=4.6, mfc=OCHRE, mec=OCHRE, zorder=8)
ax.plot(*BEST["end"], marker="o", ms=5.4, mfc=TEAL, mec=TEAL, zorder=8, clip_on=False)
ax.plot(*NOINJ["jacobi"], marker="s", ms=5.0, mfc=RUST, mec=INK, mew=0.6, zorder=8, clip_on=False)
ax.plot(*NOINJ["middle"], marker="s", ms=5.0, mfc=OCHRE, mec=INK, mew=0.6, zorder=8, clip_on=False)
ax.set_xlim(-0.08, LIM)
ax.set_ylim(-0.08, LIM)
ax.set_aspect("equal")
ax.set_xticks([0, 1, 2])
ax.set_yticks([0, 1, 2])
ax.set_xlabel(r"energy injected over a step, in units of $\alpha_*$")
ax.set_ylabel(r"damping added over a step, in units of $\alpha_*$")

# the three statements, to the right of the axes, each tied to its marks
W, H = fig.get_size_inches()
XT = AX0 + AS + 0.42


def data_to_fig(x, y):
    """position of the data point (x, y) of ax in inches on the figure"""
    return AX0 + AS * (x + 0.08) / (LIM + 0.08), AY0 + AS * (y + 0.08) / (LIM + 0.08)


aw = fig.add_axes([0, 0, 1, 1])
aw.set_xlim(0, W)
aw.set_ylim(0, H)
aw.axis("off")
aw.patch.set_alpha(0.0)
ITEMS = [
    (2.52, "without injection",
     "the smallest one-step error costs\n" + r"$1.8\,\alpha_*$ and $2.0\,\alpha_*$ of added damping",
     [NOINJ["jacobi"], NOINJ["middle"]]),
    (1.66, "smallest one-step error",
     "Jacobi scheme and middle store first:\n" + r"the scheme injects $\alpha_*$ and adds $\alpha_*$",
     [BEST["jacobi"]]),
    (0.80, "from end to end",
     "the energy-conserving sweep\ndoes neither",
     [BEST["end"]]),
]
for y, head, body, pts in ITEMS:
    aw.text(XT, y, head, fontsize=FS, ha="left", va="center")
    aw.text(XT, y - 0.15, body, fontsize=FSS, ha="left", va="top", color=NOTE, linespacing=1.12)
    for pt in pts:
        px, py = data_to_fig(*pt)
        aw.plot([px + 0.06, XT - 0.06], [py, y], color=INK, lw=0.5, zorder=2)
# the two colours, once
aw.plot([XT + 0.05], [0.28], marker="o", ms=5.0, mfc=RUST, mec=RUST)
aw.text(XT + 0.15, 0.28, "Jacobi", fontsize=FSS, va="center", color=RUST)
aw.plot([XT + 0.72], [0.28], marker="o", ms=5.0, mfc=OCHRE, mec=OCHRE)
aw.text(XT + 0.82, 0.28, "middle store first", fontsize=FSS, va="center", color=OCHRE)
save(fig, "trade")
