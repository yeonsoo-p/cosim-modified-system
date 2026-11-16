"""The two-mass oscillator in four choices of port, in the format of the figure of the networks.

(a) velocity and force: subsystem 1 holds the joining spring; (b) two displacements: each subsystem holds a
copy of the joining spring, whose far end follows the held displacement of the other mass; (c) force and
displacement: subsystem 2 holds the joining spring; (d) two forces: a master holds the joining spring and
computes its force from the two displacements. Each panel: the partition with its ports, the exchanged
signals, and the states of the two subsystems. A state that the port shows is white, one that it does not show
is grey. In (b) to (d) an arrow leads from the state that a port shows to the state that its sample drives; a
dashed arrow is the old sample of the receiver's own displacement that a held force contains.
Beside each title stand the rates at which the in-phase and the out-of-phase mode grow under a zero-order hold,
divided by H, to leading order; they are computed by ../numbers/two_mass_ports.py.
Run:  uv run --no-project --with numpy --with scipy --with matplotlib python fig_ports.py
"""
from matplotlib.patches import Circle, FancyArrowPatch, FancyBboxPatch

from style import (BOX_EDGE, FSS, FULL, G2, INK, LW_THIN, NOTE, SOFT, canvas, link, mass, panel, plt, port, region,
                   rod, save, signal, spring, store, wall)

PH, VGAP = 1.98, 0.12
PW, HGAP = 3.05, 0.20
fig = plt.figure(figsize=(FULL, 2 * PH + VGAP))
ax = {"a": canvas(fig, 0, PH + VGAP, PW, PH), "b": canvas(fig, PW + HGAP, PH + VGAP, PW, PH),
      "c": canvas(fig, 0, 0, PW, PH), "d": canvas(fig, PW + HGAP, 0, PW, PH)}

YM = 1.335                 # axis of the mechanical sketch
R0, R1 = 1.135, 1.70       # vertical extent of the subsystem regions
P0, P1 = 1.05, 1.78        # vertical extent of a port
YV, YF = 0.90, 0.76        # the two exchanged signals
YT = 0.60                  # the words above the states
YG = 0.34                  # the states
YN = 0.06                  # notes under the states
DX = 0.24                  # half length of a signal arrow
RS = 0.07                  # radius of a state


def words(a, x, y, text, ha="center", va="center", color=NOTE):
    a.text(x, y, text, ha=ha, va=va, fontsize=FSS, color=color, linespacing=1.1)


def growth(a, jacobi, sequential):
    """rates at which the in-phase and the out-of-phase mode grow, divided by H, to leading order"""
    a.text(PW - 0.02, PH - 0.01, "Jacobi: " + jacobi + "\nsequential: " + sequential, ha="right", va="top",
           fontsize=FSS, color=NOTE, linespacing=1.25)


def held_end(a, x):
    a.add_patch(Circle((x, YM), 0.035, fc="white", ec=INK, lw=LW_THIN, zorder=5))


def drive(a, p, q, rad, dashed=False):
    """arrow from the state at p to the state at q, ending at the edge of q"""
    a.add_patch(FancyArrowPatch(p, q, arrowstyle="-|>", mutation_scale=6.5, color=INK, lw=0.9,
                                connectionstyle=f"arc3,rad={rad}", zorder=5, shrinkA=5.2, shrinkB=5.2,
                                linestyle=(0, (3, 2)) if dashed else "-"))


def states(a, sub1, sub2, own1=False, own2=False):
    """two subsystems with a momentum (not shown, grey) and a displacement (shown, white) each"""
    (p1, x1), (x2, p2) = sub1, sub2
    region(a, p1 - 0.17, YG - 0.13, x1 + 0.17, YG + 0.13)
    region(a, x2 - 0.17, YG - 0.13, p2 + 0.17, YG + 0.13)
    link(a, (p1, YG), (x1, YG), r=RS, color=SOFT, lw=0.6)
    link(a, (x2, YG), (p2, YG), r=RS, color=SOFT, lw=0.6)
    drive(a, (x1, YG), (p2, YG), -0.2)
    drive(a, (x2, YG), (p1, YG), -0.2)
    if own1:
        drive(a, (x1, YG), (p1, YG), 0.75, dashed=True)
    if own2:
        drive(a, (x2, YG), (p2, YG), 0.75, dashed=True)
    for x, shown in ((p1, False), (x1, True), (x2, True), (p2, False)):
        store(a, x, YG, "", r=RS, fc="white" if shown else G2)


# ---------------------------------------------------------------- (a) velocity and force
a = ax["a"]
panel(a, 0.0, PH - 0.02, "a", "velocity and force")
growth(a, r"0, +$\frac{1}{2}$", r"0, 0")
XP = 1.93
region(a, 0.06, R0, XP - 0.08, R1, "subsystem 1")
region(a, XP + 0.08, R0, 2.99, R1, "subsystem 2")
wall(a, 0.15, YM, side="left")
spring(a, 0.15, 0.58, YM, n=3)
mass(a, 0.79, YM, "mass")
spring(a, 1.00, XP, YM)
rod(a, XP, 2.12, YM)
mass(a, 2.33, YM, "mass")
spring(a, 2.54, 2.90, YM, n=3)
wall(a, 2.90, YM, side="right")
port(a, XP, P0, P1)
signal(a, XP + DX, XP - DX, YV, "velocity")
signal(a, XP - DX, XP + DX, YF, "force")
words(a, 0.0, YT, "states of the two subsystems", ha="left")
XS = (0.365, 0.79, 1.465, 2.33, 2.72)      # ground spring, mass, joining spring | mass, ground spring
for x0, x1 in ((XS[0] - 0.17, XS[2] + 0.17), (XS[3] - 0.17, XS[4] + 0.17)):
    region(a, x0, YG - 0.13, x1, YG + 0.13)
for p, q, col in ((0, 1, SOFT), (1, 2, SOFT), (2, 3, INK), (3, 4, SOFT)):
    link(a, (XS[p], YG), (XS[q], YG), r=RS, color=col, lw=0.9 if col == INK else 0.6)
for k, x in enumerate(XS):
    store(a, x, YG, "", r=RS, fc="white" if k in (2, 3) else G2)
store(a, 0.30, YN + 0.03, "", r=RS)
words(a, 0.42, YN + 0.03, "state shown at the port", ha="left")
store(a, 1.80, YN + 0.03, "", r=RS, fc=G2)
words(a, 1.92, YN + 0.03, "not shown to the partner", ha="left")

# ---------------------------------------------------------------- (b) two displacements
a = ax["b"]
panel(a, 0.0, PH - 0.02, "b", "two displacements")
growth(a, r"$-$$\frac{1}{4}$, +$\frac{1}{4}$", r"0, 0")
XP = 1.525
region(a, 0.06, R0, XP - 0.10, R1, "subsystem 1")
region(a, XP + 0.10, R0, 2.99, R1, "subsystem 2")
wall(a, 0.15, YM, side="left")
spring(a, 0.15, 0.46, YM, n=3)
mass(a, 0.65, YM, "mass", w=0.38)
spring(a, 0.84, 1.29, YM, n=4)
held_end(a, 1.325)
held_end(a, 1.725)
spring(a, 1.76, 2.21, YM, n=4)
mass(a, 2.40, YM, "mass", w=0.38)
spring(a, 2.59, 2.90, YM, n=3)
wall(a, 2.90, YM, side="right")
port(a, XP, P0, P1)
signal(a, XP - DX, XP + DX, YV, "displacement")
signal(a, XP + DX, XP - DX, YF, "displacement")
words(a, 0.0, YT, "states: momentum and displacement of each mass", ha="left")
states(a, (0.55, 1.00), (2.05, 2.50))
words(a, PW / 2, YN, "each subsystem holds a copy of the joining spring")

# ---------------------------------------------------------------- (c) force and displacement
a = ax["c"]
panel(a, 0.0, PH - 0.02, "c", "force and displacement")
growth(a, r"$-$$\frac{1}{8}$, +$\frac{3}{8}$", r"+$\frac{1}{8}$, +$\frac{1}{8}$")
XP = 1.12
region(a, 0.06, R0, XP - 0.08, R1, "subsystem 1")
region(a, XP + 0.08, R0, 2.99, R1, "subsystem 2")
wall(a, 0.15, YM, side="left")
spring(a, 0.15, 0.50, YM, n=3)
mass(a, 0.71, YM, "mass")
rod(a, 0.92, XP, YM)
spring(a, XP, 2.12, YM)
mass(a, 2.33, YM, "mass")
spring(a, 2.54, 2.90, YM, n=3)
wall(a, 2.90, YM, side="right")
port(a, XP, P0, P1)
signal(a, XP - DX, XP + DX, YV, "displacement")
signal(a, XP + DX, XP - DX, YF, "force")
words(a, 0.0, YT, "states", ha="left")
states(a, (0.40, 0.85), (2.05, 2.50), own1=True)
words(a, PW / 2, YN, "dashed: the force contains the old displacement of mass 1")

# ---------------------------------------------------------------- (d) two forces
a = ax["d"]
panel(a, 0.0, PH - 0.02, "d", "two forces")
growth(a, r"0, +$\frac{1}{2}$", r"+$\frac{1}{4}$, +$\frac{1}{4}$")
XA, XB = 1.08, 1.97
region(a, 0.06, R0, XA - 0.08, R1, "subsystem 1")
a.add_patch(FancyBboxPatch((XA + 0.08, R0), XB - XA - 0.16, R1 - R0, boxstyle="round,pad=0,rounding_size=0.04",
                           fc="none", ec=BOX_EDGE, lw=0.7, linestyle=(0, (3, 2)), zorder=0))
words(a, (XA + XB) / 2, R1 - 0.035, "master", va="top")
region(a, XB + 0.08, R0, 2.99, R1, "subsystem 2")
wall(a, 0.15, YM, side="left")
spring(a, 0.15, 0.48, YM, n=3)
mass(a, 0.69, YM, "mass")
rod(a, 0.90, XA, YM)
spring(a, XA, XB, YM)
rod(a, XB, 2.15, YM)
mass(a, 2.36, YM, "mass")
spring(a, 2.57, 2.90, YM, n=3)
wall(a, 2.90, YM, side="right")
port(a, XA, P0, P1)
port(a, XB, P0, P1)
signal(a, XA - DX, XA + DX, YV, "displacement")
signal(a, XB + DX, XB - DX, YV, "displacement")
signal(a, XA + DX + 0.1, XA - DX, YF)
signal(a, XB - DX - 0.1, XB + DX, YF)
a.text((XA + XB) / 2, YF, "force", ha="center", va="center", fontsize=FSS,
       bbox=dict(fc="white", ec="none", pad=1.5), zorder=8)
words(a, 0.0, YT, "states; the master holds none", ha="left")
states(a, (0.40, 0.85), (2.20, 2.65), own1=True, own2=True)
words(a, PW / 2, YN, "dashed: each force contains the receiver's old displacement")

save(fig, "ports")
