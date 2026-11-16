"""One visual language for all figures of the paper. Every figure script imports this module and writes its
PDF into the folder `out` beside the scripts (see `save`).

PRINTED SIZE.  Every figure is drawn at the size at which it is printed and is to be included at its
natural size (no scaling): FULL = the text width, 6.30 in; NARROW = 0.62 of it; MEDIUM = 0.85 of it.
All drawings use inches as their unit (see `canvas`), so that a store, a link, a spring or an arrow has
the same size in every figure.

TYPE.  Computer Modern (cmr10, mathtext cm), as the body of the paper.  Two sizes only:
  FS  = 9 pt  panel labels with their titles, axis labels
  FSS = 8 pt  everything else (tick labels, annotations, notes, labels in drawings)
Nothing is smaller than 8 pt.

COLOUR.  Fixed meanings, the same in every figure:
  INK    text, axes, the monolithic system, and what is proved for every scheme (bounds)
  RUST   a Jacobi scheme
  TEAL   a sequential scheme (executed from end to end where two orders are compared)
  OCHRE  the sequential scheme with the middle store first (only where two sequential orders are compared)
  greys  auxiliary geometry; NOTE for secondary text; G2 for a region that a bound excludes;
         BOX / BOX_EDGE for the extent of a subsystem and for the duration of a macro step
There is no highlight colour.  A highlight is made with weight: heavy or filled ink (the nearest store
that is not shown, a branch point, a new sample, an amount passed twice).  What a hold does not convey
or does not pass is dashed.  Where the two parts of the difference are drawn as geometry (energy circle),
the numerical dissipation is heavy ink and the numerical interconnection heavy mid grey.

RECURRING ELEMENTS (helpers below).
  store       white circle, ink edge, its number inside
  link        ink line between two stores
  subsystem   light grey rounded region behind its elements, label in NOTE at its top
  port        dashed ink line across the cut
  signal      ink arrow, labelled at its tail (the side whose output it is)
  macro step  light grey bar between two dotted lines at the communication points t_k, t_{k+1}
  sample      filled dot

PANELS AND AXES.  Panel labels "(a) title" in FS at the top left of the panel.  Axes: left and bottom
spine only, ticks outward, no grid.  Axis labels read "quantity, symbol".  Logarithmic axes: powers of ten
on the vertical axis, decimals for the macro step h.  Curves are labelled directly; a legend only where
direct labels do not fit, and then without a frame.
"""
import os

import matplotlib

matplotlib.use("agg")
import matplotlib.pyplot as plt  # noqa: E402
import numpy as np  # noqa: E402
from matplotlib.patches import Circle, FancyArrowPatch, FancyBboxPatch  # noqa: E402

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "out")

# ------------------------------------------------------------------------------ palette
INK = "#1F2A44"
RUST, TEAL, OCHRE = "#B4532A", "#2F6F8F", "#A39218"
NOTE = "#5B6577"                      # secondary text
SOFT, FAINT = "#7D8696", "#C9CED6"    # auxiliary lines
G1, G2, G3 = "#F1F2F4", "#DDE0E5", "#BFC4CC"
BOX, BOX_EDGE = G1, G3

# ------------------------------------------------------------------------------ sizes
TEXTWIDTH = 6.30
FULL, MEDIUM, NARROW = TEXTWIDTH, 0.85 * TEXTWIDTH, 0.62 * TEXTWIDTH
FS, FSS = 9, 8
LW_DATA, LW_BOUND, LW_THIN, LW_AUX = 1.2, 1.6, 0.9, 0.6
R_STORE = 0.105                       # radius of a store, inches
DASH = (0, (4, 2.2))                  # "not conveyed", modified system
DOTS = (0, (1, 2))                    # communication points, construction lines

plt.rcParams.update({
    "font.family": ["cmr10", "STIXGeneral"], "mathtext.fontset": "cm",
    "axes.formatter.use_mathtext": True, "axes.unicode_minus": False,
    "font.size": FSS, "axes.labelsize": FS, "xtick.labelsize": FSS, "ytick.labelsize": FSS,
    "legend.fontsize": FSS, "axes.linewidth": 0.6, "xtick.major.width": 0.6, "ytick.major.width": 0.6,
    "xtick.minor.width": 0.4, "ytick.minor.width": 0.4, "xtick.major.size": 3, "ytick.major.size": 3,
    "xtick.direction": "out", "ytick.direction": "out", "pdf.fonttype": 42,
    "axes.edgecolor": INK, "axes.labelcolor": INK, "xtick.color": INK, "ytick.color": INK,
    "text.color": INK, "savefig.dpi": 220, "lines.solid_capstyle": "round",
})


def save(fig, name):
    """write the figure as out/<name>.pdf, at its natural size"""
    os.makedirs(OUT, exist_ok=True)
    fig.savefig(os.path.join(OUT, f"{name}.pdf"))
    w, h = fig.get_size_inches()
    plt.close(fig)
    print(f"written out/{name}.pdf  ({w:.2f} in x {h:.2f} in)")


# ------------------------------------------------------------------------------ axes
def canvas(fig, x0, y0, w, h):
    """a drawing area without frame; position and data units are inches, origin at its lower left"""
    W, H = fig.get_size_inches()
    ax = fig.add_axes([x0 / W, y0 / H, w / W, h / H])
    ax.set_xlim(0, w)
    ax.set_ylim(0, h)
    ax.axis("off")
    return ax


def plot_axes(fig, x0, y0, w, h):
    """a data plot; position in inches; left and bottom spine only"""
    W, H = fig.get_size_inches()
    ax = fig.add_axes([x0 / W, y0 / H, w / W, h / H])
    for s in ("top", "right"):
        ax.spines[s].set_visible(False)
    return ax


def panel(ax, x, y, tag, title="", **kw):
    """panel label '(a) title' with its upper left corner at (x, y) in the units of ax"""
    ax.text(x, y, f"({tag})" + (" " + title if title else ""), fontsize=FS, ha="left", va="top", color=INK, **kw)


def log_decades(ax, lo, hi, axis="y"):
    """ticks at the powers of ten lo..hi (exponents), labelled as powers of ten"""
    ticks = [10.0 ** k for k in range(lo, hi + 1)]
    labels = ["$1$" if k == 0 else r"$10^{%d}$" % k for k in range(lo, hi + 1)]
    if axis == "y":
        ax.set_yticks(ticks)
        ax.set_yticklabels(labels)
    else:
        ax.set_xticks(ticks)
        ax.set_xticklabels(labels)
    ax.minorticks_off()


def h_ticks(ax, values):
    """decimal ticks for the macro step h on a logarithmic horizontal axis"""
    ax.set_xticks(values)
    ax.set_xticklabels([("%g" % v) for v in values])
    ax.xaxis.set_minor_locator(matplotlib.ticker.NullLocator())


# ------------------------------------------------------------------------------ network elements
def store(ax, x, y, label="", fc="white", r=R_STORE, color=INK, z=6, lw=LW_THIN, ls="-"):
    ax.add_patch(Circle((x, y), r, fc=fc, ec=INK, lw=lw, zorder=z, ls=ls))
    if label != "":
        ax.text(x, y - 0.004, str(label), ha="center", va="center", fontsize=FSS, zorder=z + 1, color=color)


def link(ax, p, q, r=R_STORE, lw=LW_THIN, color=INK, ls="-", z=5):
    p, q = np.array(p, float), np.array(q, float)
    d = (q - p) / np.linalg.norm(q - p)
    a, b = p + r * d, q - r * d
    ax.plot([a[0], b[0]], [a[1], b[1]], color=color, lw=lw, ls=ls, zorder=z, solid_capstyle="butt")


def arrow(ax, p, q, color=INK, lw=LW_THIN, style="-|>", ms=7, z=5, rad=0.0, ls="-"):
    ax.add_patch(FancyArrowPatch(p, q, arrowstyle=style, mutation_scale=ms, color=color, lw=lw,
                                 connectionstyle=f"arc3,rad={rad}", zorder=z, linestyle=ls,
                                 shrinkA=0, shrinkB=0))


# ------------------------------------------------------------------------------ subsystems, ports, mechanics
def region(ax, x0, y0, x1, y1, label="", fs=FSS):
    """the extent of a subsystem, behind its elements; the label sits inside at the top"""
    ax.add_patch(FancyBboxPatch((x0, y0), x1 - x0, y1 - y0, boxstyle="round,pad=0,rounding_size=0.04",
                                fc=BOX, ec=BOX_EDGE, lw=0.7, zorder=0))
    if label:
        ax.text((x0 + x1) / 2, y1 - 0.035, label, ha="center", va="top", fontsize=fs, color=NOTE, zorder=1)


def mass(ax, x, y, label="", w=0.42, h=0.25):
    ax.add_patch(FancyBboxPatch((x - w / 2, y - h / 2), w, h, boxstyle="round,pad=0,rounding_size=0.02",
                                fc="white", ec=INK, lw=LW_THIN, zorder=3))
    if label:
        ax.text(x, y - 0.004, label, ha="center", va="center", fontsize=FSS, zorder=4)


def rod(ax, x0, x1, y):
    ax.plot([x0, x1], [y, y], color=INK, lw=LW_THIN, zorder=2, solid_capstyle="butt")


def spring(ax, x0, x1, y, n=5, amp=0.05, lead=0.06):
    xs, ys = [x0, x0 + lead], [y, y]
    body = (x1 - x0) - 2 * lead
    for i in range(2 * n):
        xs.append(x0 + lead + body * (i + 0.5) / (2 * n))
        ys.append(y + amp * (1 if i % 2 == 0 else -1))
    xs += [x1 - lead, x1]
    ys += [y, y]
    ax.plot(xs, ys, color=INK, lw=LW_THIN, solid_joinstyle="miter", solid_capstyle="butt", zorder=2)


def vspring(ax, x, y0, y1, n=3, amp=0.05, lead=0.05):
    ys, xs = [y0, y0 + lead], [x, x]
    body = (y1 - y0) - 2 * lead
    for i in range(2 * n):
        ys.append(y0 + lead + body * (i + 0.5) / (2 * n))
        xs.append(x + amp * (1 if i % 2 == 0 else -1))
    ys += [y1 - lead, y1]
    xs += [x, x]
    ax.plot(xs, ys, color=INK, lw=LW_THIN, solid_joinstyle="miter", solid_capstyle="butt", zorder=2)


def damper(ax, x0, x1, y, w=0.11, h=0.085):
    xm = (x0 + x1) / 2
    kw = dict(color=INK, lw=LW_THIN, zorder=2, solid_capstyle="butt")
    ax.plot([x0, xm - w / 4], [y, y], **kw)
    ax.plot([xm - w / 4, xm - w / 4], [y - h / 2, y + h / 2], **kw)                                  # piston
    ax.plot([xm - w / 2, xm + w / 2, xm + w / 2, xm - w / 2],
            [y + h / 2 + 0.015, y + h / 2 + 0.015, y - h / 2 - 0.015, y - h / 2 - 0.015], **kw)      # cylinder
    ax.plot([xm + w / 2, x1], [y, y], **kw)


def wall(ax, x, y, h=0.3, side="left"):
    """a fixed wall; side = the side on which the hatching lies"""
    ax.plot([x, x], [y - h / 2, y + h / 2], color=INK, lw=1.0, zorder=2, solid_capstyle="butt")
    s = -1 if side == "left" else 1
    for yy in np.linspace(y - h / 2 + 0.03, y + h / 2 - 0.01, 5):
        ax.plot([x, x + s * 0.045], [yy, yy - 0.045], color=INK, lw=0.6, zorder=2)


def hwall(ax, x, y, w=0.3):
    ax.plot([x - w / 2, x + w / 2], [y, y], color=INK, lw=1.0, zorder=2, solid_capstyle="butt")
    for xx in np.linspace(x - w / 2 + 0.04, x + w / 2 - 0.01, 5):
        ax.plot([xx, xx - 0.045], [y, y - 0.045], color=INK, lw=0.6, zorder=2)


def port(ax, x, y0, y1):
    ax.plot([x, x], [y0, y1], color=INK, lw=1.1, dashes=(4, 2.5), zorder=4, solid_capstyle="butt",
            dash_capstyle="butt")


def hport(ax, x0, x1, y):
    ax.plot([x0, x1], [y, y], color=INK, lw=1.1, dashes=(4, 2.5), zorder=4, dash_capstyle="butt")


def signal(ax, x0, x1, y, label="", gap=0.04):
    """an exchanged signal from x0 to x1, labelled at its tail"""
    arrow(ax, (x0, y), (x1, y), ms=6.5)
    if label:
        right = x1 > x0
        ax.text(x0 - gap if right else x0 + gap, y, label, ha="right" if right else "left", va="center",
                fontsize=FSS)


# ------------------------------------------------------------------------------ time
def step_bar(ax, x0, x1, y, h=0.17, label="", fc=BOX):
    """one macro step of one subsystem: a bar from x0 to x1 centred at height y"""
    ax.add_patch(FancyBboxPatch((x0, y - h / 2), x1 - x0, h, boxstyle="round,pad=0,rounding_size=0.02",
                                fc=fc, ec=BOX_EDGE, lw=0.7, zorder=2))
    if label:
        ax.text((x0 + x1) / 2, y - 0.004, label, ha="center", va="center", fontsize=FSS, zorder=3)


def comm_point(ax, x, y0, y1, label="", dy=0.03):
    """a communication point: dotted line from y0 to y1, its label below"""
    ax.plot([x, x], [y0, y1], color=SOFT, lw=0.6, ls=DOTS, zorder=1)
    if label:
        ax.text(x, y0 - dy, label, ha="center", va="top", fontsize=FSS)


def sample(ax, x, y, color=INK, ms=4.0, open_=False, z=7):
    ax.plot([x], [y], marker="o", ms=ms, mfc="white" if open_ else color, mec=color, mew=0.9, zorder=z,
            clip_on=False)
