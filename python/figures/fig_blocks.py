"""What the coefficients of a scheme reach: the blocks of X - U for three subsystems i, k, j, of which
i and j are not partners and k is their common partner.

Diagonal blocks: reached by the coefficient of the own state only. Blocks between partners: reached by the
coefficients of the samples, except on the states behind the port of the partner. Blocks between subsystems
that are not partners: reached by no coefficient. The three limits of the paper are read from the three kinds.
Run:  uv run --no-project --with numpy --with scipy --with matplotlib python fig_blocks.py
"""
from matplotlib.patches import Rectangle

from style import (FS, FSS, FULL, G1, G2, G3, INK, LW_THIN, NOTE, canvas, link, plt, save, store)

FH = 2.62
fig = plt.figure(figsize=(FULL, FH))
a = canvas(fig, 0, 0, FULL, FH)

# ---------------------------------------------------------------- the coupling graph
YG = FH - 0.42
XG = (0.22, 0.62, 1.02)
for x, lab in zip(XG, ("$i$", "$k$", "$j$")):
    store(a, x, YG, lab, r=0.115)
link(a, (XG[0], YG), (XG[1], YG), r=0.115)
link(a, (XG[1], YG), (XG[2], YG), r=0.115)
a.text(0.62, YG - 0.22, "$i$ and $j$ are\nnot partners", ha="center", va="top", fontsize=FSS, color=NOTE,
       linespacing=1.1)

# ---------------------------------------------------------------- the block pattern of X - U
S = 0.56                                   # side of a block
X0, Y0 = 1.40, 0.30                        # lower left corner of the pattern
names = ("$i$", "$k$", "$j$")
STRIP = 0.16                               # the part of a partner block behind the port


def corner(r, c):
    return X0 + c * S, Y0 + (2 - r) * S


for r in range(3):
    for c in range(3):
        x, y = corner(r, c)
        if r == c:                                           # own state
            a.add_patch(Rectangle((x, y), S, S, fc=G1, ec=INK, lw=LW_THIN, zorder=2))
            a.text(x + S / 2, y + S / 2, "$F_%s$" % names[r].strip("$"), ha="center", va="center", fontsize=FS,
                   zorder=3)
        elif abs(r - c) == 1:                                # partners
            a.add_patch(Rectangle((x, y), S, S, fc="white", ec=INK, lw=LW_THIN, zorder=2))
            a.add_patch(Rectangle((x + S - STRIP, y), STRIP, S, fc=G3, ec="none", lw=0.0, zorder=3))
            a.plot([x + S - STRIP, x + S - STRIP], [y, y + S], color=INK, lw=0.5, zorder=4)
            a.text(x + (S - STRIP) / 2, y + S / 2,
                   "$G_{%s%s}C_%s$" % (names[r].strip("$"), names[c].strip("$"), names[c].strip("$")),
                   ha="center", va="center", fontsize=FSS, zorder=5)
        else:                                                # not partners
            a.add_patch(Rectangle((x, y), S, S, fc=INK, ec=INK, lw=LW_THIN, zorder=2))
for k, nm in enumerate(names):
    a.text(X0 + (k + 0.5) * S, Y0 + 3 * S + 0.05, nm, ha="center", va="bottom", fontsize=FS)
    a.text(X0 - 0.07, Y0 + (2.5 - k) * S, nm, ha="right", va="center", fontsize=FS)
a.text(X0 + 1.5 * S, Y0 + 3 * S + 0.25, "from the state of", ha="center", va="bottom", fontsize=FSS, color=NOTE)
a.text(X0 - 0.27, Y0 + 1.5 * S, "to the state of", ha="center", va="center", fontsize=FSS, color=NOTE,
       rotation=90)
a.text(X0 + 1.5 * S, Y0 - 0.06, "the blocks of $X-U$", ha="center", va="top", fontsize=FSS, color=NOTE)

# ---------------------------------------------------------------- what reaches each kind of block
XT = X0 + 3 * S + 0.36
rows = [
    (corner(0, 2), (S, S / 2), "(a) between subsystems that are not partners",
     "no coefficient reaches it:\nit limits the accuracy, and its symmetric part\ntrades energy against damping"),
    (corner(1, 2), (S - STRIP / 2, S / 2), "(b) behind the port of a partner",
     "no coefficient of the receiver reaches it: it adds\nto the error that cannot be avoided; its part in the\n"
     "numerical dissipation is cancelled by the partner"),
    (corner(2, 2), (S, S / 2), "(c) within a subsystem",
     "only the coefficient of the own state reaches it,\nnot the weights on the samples of the partners:\nthe reaction"),
]
YT = [Y0 + 3 * S + 0.02, Y0 + 1.5 * S + 0.26, Y0 + 0.40]
for (cx, off, head, body), yt in zip(rows, YT):
    px, py = cx[0] + off[0], cx[1] + off[1]
    a.plot([px, XT - 0.06], [py, yt - 0.06], color=INK, lw=0.5, zorder=6)
    a.plot([px], [py], "o", ms=2.6, mfc="white" if head.startswith("(a)") else INK, mec=INK, mew=0.6,
           zorder=7)
    a.text(XT, yt, head, ha="left", va="top", fontsize=FS)
    a.text(XT, yt - 0.165, body, ha="left", va="top", fontsize=FSS, color=NOTE, linespacing=1.12)

# small key under the graph
KX, KY = 0.06, 0.78
a.add_patch(Rectangle((KX, KY), 0.16, 0.16, fc="white", ec=INK, lw=LW_THIN))
a.text(KX + 0.23, KY + 0.08, "reached by the\ncoefficients of\nthe samples", ha="left", va="center", fontsize=FSS,
       color=NOTE, linespacing=1.1)
save(fig, "blocks")
