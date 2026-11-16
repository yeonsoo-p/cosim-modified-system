"""The networks of the examples, in one row: (a) undamped pair, (b) chain of three stores, (c) star with three
leaves. Each panel shows the partition into subsystems, the signals exchanged at the ports and the coupling
graph. The two-mass oscillator is drawn in the figure of the four choices of port (fig_ports.py).
Run:  uv run --no-project --with numpy --with scipy --with matplotlib python fig_models.py
"""
from matplotlib.patches import Circle

from style import (FSS, FULL, G2, INK, LW_THIN, NOTE, SOFT, arrow, canvas, damper, hport, hwall, link, mass,
                   panel, plt, port, region, rod, save, signal, spring, store, vspring, wall)

PH, VGAP = 1.98, 0.12
WA, WB, WC, HGAP1 = 1.75, 2.50, 1.85, 0.10
PW, HGAP = 3.05, 0.20
fig = plt.figure(figsize=(FULL, PH))
Y1 = 0.0
ax = {
    "a": canvas(fig, 0, Y1, WA, PH), "b": canvas(fig, WA + HGAP1, Y1, WB, PH),
    "c": canvas(fig, WA + WB + 2 * HGAP1, Y1, WC, PH),
}

YM = 1.335                 # axis of the mechanical sketch
R0, R1 = 1.135, 1.70       # vertical extent of the subsystem regions
P0, P1 = 1.05, 1.78        # vertical extent of a port
YV, YF = 0.90, 0.76        # the two exchanged signals
YT = 0.52                  # the words "coupling graph"
YG = 0.31                  # the coupling graph
YN = 0.14                  # notes under the graph
DX = 0.24                  # half length of a signal arrow
RS = 0.07                  # radius of a state


def words(a, x, y, text, ha="center", va="top", color=NOTE):
    a.text(x, y, text, ha=ha, va=va, fontsize=FSS, color=color, linespacing=1.1)


# ================================================================ row 1: networks of scalar stores
# ---------------------------------------------------------------- (a) undamped pair
a = ax["a"]
panel(a, 0.0, PH - 0.02, "a", "undamped pair")
XP = 0.88
region(a, 0.05, R0, XP - 0.08, R1, "store 1")
region(a, XP + 0.08, R0, 1.70, R1, "store 2")
mass(a, 0.44, YM, "mass")
rod(a, 0.65, XP, YM)
spring(a, XP, 1.56, YM)
wall(a, 1.56, YM, side="right")
port(a, XP, P0, P1)
signal(a, XP - DX, XP + DX, YV, "velocity")
signal(a, XP + DX, XP - DX, YF, "force")
words(a, 0.0, YT, "coupling graph", ha="left", va="center")
store(a, 0.44, YG, 1)
store(a, 1.26, YG, 2)
link(a, (0.44, YG), (1.26, YG))
words(a, 0.85, YG + 0.03, r"rate $\omega$", va="bottom")
words(a, 0.44, YN, "momentum")
words(a, 1.26, YN, "elongation")

# ---------------------------------------------------------------- (b) chain of three stores
a = ax["b"]
panel(a, 0.0, PH - 0.02, "b", "chain of three stores")
XA, XB = 0.92, 1.58
region(a, 0.04, R0, XA - 0.07, R1, "store 1")
region(a, XA + 0.07, R0, XB - 0.07, R1, "store 2")
region(a, XB + 0.07, R0, 2.46, R1, "store 3")
wall(a, 0.11, YM, side="left")
damper(a, 0.11, 0.36, YM)
mass(a, 0.59, YM, "mass 1", w=0.46)
rod(a, 0.82, XA, YM)
spring(a, XA, XB, YM)
rod(a, XB, 1.68, YM)
mass(a, 1.91, YM, "mass 2", w=0.46)
damper(a, 2.14, 2.39, YM)
wall(a, 2.39, YM, side="right")
port(a, XA, P0, P1)
port(a, XB, P0, P1)
signal(a, XA - DX, XA + DX, YV, "velocity")
signal(a, XB + DX, XB - DX, YV, "velocity")
signal(a, XA + DX + 0.02, XA - DX, YF)
signal(a, XB - DX - 0.02, XB + DX, YF)
a.text((XA + XB) / 2, YF, "force", ha="center", va="center", fontsize=FSS,
       bbox=dict(fc="white", ec="none", pad=1.5), zorder=8)
words(a, 0.0, YT, "coupling graph", ha="left", va="center")
XG = (0.59, (XA + XB) / 2, 1.91)
for x, lab in zip(XG, (1, 2, 3)):
    store(a, x, YG, lab)
link(a, (XG[0], YG), (XG[1], YG))
link(a, (XG[1], YG), (XG[2], YG))
words(a, WB, YT, "stores 1 and 3 are not partners", ha="right", va="center")
words(a, XG[1], YN, r"rates $\omega$; dissipation rate $r$ in stores 1 and 3")

# ---------------------------------------------------------------- (c) star with three leaves
a = ax["c"]
panel(a, 0.0, PH - 0.02, "c", "star with three leaves")
XC = 0.925
XA, XB = XC - 0.30, XC + 0.30
YP = 1.07
region(a, 0.04, R0, XA - 0.07, R1, "leaf")
region(a, XA + 0.07, R0, XB - 0.07, R1, "hub")
region(a, XB + 0.07, R0, 1.81, R1, "leaf")
region(a, XC - 0.24, 0.60, XC + 0.24, YP - 0.065)
wall(a, 0.11, YM, side="left")
spring(a, 0.11, XA, YM, n=4)
rod(a, XA, XC - 0.19, YM)
mass(a, XC, YM, "mass", w=0.38)
rod(a, XC + 0.19, XB, YM)
spring(a, XB, 1.74, YM, n=4)
wall(a, 1.74, YM, side="right")
a.plot([XC, XC], [YP, YM - 0.125], color=INK, lw=0.9, zorder=2, solid_capstyle="butt")
vspring(a, XC, 0.70, YP)
hwall(a, XC, 0.70)
port(a, XA, P0, P1)
port(a, XB, P0, P1)
hport(a, XC - 0.22, XC + 0.22, YP)
words(a, XC + 0.29, 0.83, "leaf", ha="left", va="center")
words(a, XC - 0.29, 0.83, "each port:\nvelocity out,\nforce in", ha="right", va="center")
words(a, 0.0, YT, "coupling graph", ha="left", va="center")
hub = (0.27, 0.27)
for pnt in ((0.07, 0.27), (0.47, 0.27)):
    link(a, hub, pnt, r=RS)
    store(a, pnt[0], pnt[1], "", r=RS)
link(a, hub, (0.27, 0.07), r=RS)
store(a, 0.27, 0.07, "", r=RS)
store(a, hub[0], hub[1], "", r=RS, fc=INK)
words(a, 0.61, 0.19, "the hub runs between\nat most two of the three\npairs of its partners", ha="left", va="center")

save(fig, "models")
