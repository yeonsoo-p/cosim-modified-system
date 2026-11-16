"""The two ways in which a zero-order hold loses stability, on the chain of three stores, in one plane.

Plotted is 1/theta for the oscillatory pair of eigenvalues theta of the shifted system E x' = A x (upper half
plane). The co-simulation is stable while Re(1/theta) < 0, and 1/theta = 0 is the eigenvalue -1 of the
one-step map (E singular). Jacobi scheme: 1/theta moves to the right and crosses the imaginary axis at
h = 0.05 (a mode loses its damping). Sequential scheme: 1/theta moves down the line Re = const to the origin,
which it reaches at h = 1.415, and leaves along the real axis.
Run:  uv run --no-project --with numpy --with scipy --with matplotlib python fig_stability.py
"""
import numpy as np

from chain3 import A3, ORDERS, theta
from style import DOTS, FS, FSS, G1, INK, LW_DATA, NOTE, RUST, TEAL, arrow, plot_axes, plt, save

FW, FH = 3.60, 2.86
fig = plt.figure(figsize=(FW, FH))
ax = plot_axes(fig, 0.62, 0.44, 2.80, 2.26)
XL, XR, YB, YT = -0.16, 0.50, -0.10, 0.80
ax.axvspan(0.0, XR, fc=G1, ec="none", zorder=0)
ax.axvline(0.0, color=INK, lw=0.9, zorder=2)
ax.axhline(0.0, color=NOTE, lw=0.5, ls=DOTS, zorder=1)


def inv_theta(name, h):
    th = theta(A3, ORDERS[name], h)
    th = th[np.isfinite(th)]
    z = 1.0 / th
    k = np.argmax(z.imag)                      # 1/theta of the eigenvalue of the lower half plane lies above
    return z, z[k]


# Jacobi scheme: the pair
hj = np.linspace(0.0, 0.95, 400)
zj = np.array([inv_theta("jacobi", h)[1] for h in hj])
ax.plot(zj.real, zj.imag, color=RUST, lw=LW_DATA, zorder=4)
for h, lab, dy in ((0.05, "0.05", 0.045), (0.2, "0.2", 0.045), (0.5, "0.5", 0.045), (0.9, "0.9", 0.045)):
    z = inv_theta("jacobi", h)[1]
    ax.plot(z.real, z.imag, "o", ms=3.6, mfc=RUST if h != 0.05 else "white", mec=RUST, mew=0.9, zorder=6)
    ax.text(z.real + (0.03 if h == 0.05 else 0.0), z.imag + dy, f"${lab}$", fontsize=FSS, ha="center",
            va="bottom", color=RUST)
# sequential scheme: the pair comes down the line Re = const, meets on the real axis and splits; one of the
# two real eigenvalues passes the origin (E singular), the other moves into the stable half plane
def is_pair(h):
    return abs(inv_theta("end", h)[1].imag) > 1e-9


lo, hi = 1.40, 1.42
for _ in range(60):
    mid = 0.5 * (lo + hi)
    lo, hi = (mid, hi) if is_pair(mid) else (lo, mid)
H_MEET = lo
hs = np.linspace(0.0, H_MEET, 1500)
zs = np.array([inv_theta("end", h)[1] for h in hs])
zs[-1] = zs[-1].real
ax.plot(zs.real, zs.imag, color=TEAL, lw=LW_DATA, zorder=5, solid_capstyle="butt")
H_END = 1.47
right, left = [zs[-1].real], [zs[-1].real]
for h in np.linspace(hi, H_END, 300):
    z = inv_theta("end", h)[0]
    z = np.sort(z[(np.abs(z.imag) < 1e-9) & (z.real > -1.0)].real)
    left.append(z[0])
    right.append(z[-1])
for br in (right, left):
    br = [v for v in br if -0.135 <= v <= 0.18]      # both arrows end inside the frame
    ax.plot(br[:-1], np.zeros(len(br) - 1), color=TEAL, lw=LW_DATA, zorder=5, solid_capstyle="butt")
    arrow(ax, (br[-8], 0.0), (br[-1], 0.0), color=TEAL, lw=LW_DATA, ms=7, z=5)
print("sequential pair meets the real axis at h = %.5f, at 1/theta = %.4f; branches at h = %.2f: %.3f, %.3f"
      % (H_MEET, zs[-1].real, H_END, left[-1], right[-1]))
for h, lab in ((0.5, "0.5"), (1.0, "1"), (1.3, "1.3")):
    z = inv_theta("end", h)[1]
    ax.plot(z.real, z.imag, "o", ms=3.6, mfc=TEAL, mec=TEAL, zorder=6)
    ax.text(z.real - 0.022, z.imag, f"${lab}$", fontsize=FSS, ha="right", va="center", color=TEAL)
z0 = inv_theta("end", 0.0)[1]
ax.plot(z0.real, z0.imag, "o", ms=3.8, mfc="white", mec=INK, mew=0.9, zorder=7)
ax.text(z0.real - 0.022, z0.imag + 0.01, "$h=0$", fontsize=FSS, ha="right", va="center", color=NOTE)
ax.plot(0, 0, "o", ms=4.4, mfc=TEAL, mec=INK, mew=0.6, zorder=8)
KW = dict(fontsize=FSS, linespacing=1.1)
ax.text(0.21, 0.62, "Jacobi scheme: moves right\nby $h/2$ and crosses the axis\nat $h=0.05$, a mode loses\nits damping", color=RUST,
        ha="left", va="top", **KW)
ax.annotate("every sequential order: the pair\nmeets on the real axis, and one\neigenvalue passes the origin\nat $h=1.415$: $E$ is singular", (0, 0), xytext=(0.07, 0.36),
            color=TEAL, ha="left", va="top",
            arrowprops=dict(arrowstyle="-", lw=0.5, color=TEAL, shrinkA=2, shrinkB=4), **KW)
ax.text(-0.012, YB + 0.02, "stable", fontsize=FSS, color=NOTE, ha="right", va="bottom")
ax.text(0.012, YB + 0.02, "unstable", fontsize=FSS, color=NOTE, ha="left", va="bottom")
ax.set_xlim(XL, XR)
ax.set_ylim(YB, YT)
ax.set_xticks([0, 0.2, 0.4])
ax.set_yticks([0, 0.35, 0.7])
ax.set_xlabel(r"real part of $\omega/\theta$")
ax.set_ylabel(r"imaginary part of $\omega/\theta$")
save(fig, "stability")
print("Jacobi: Re(1/theta) at h = 0, 0.05, 0.2:", [round(inv_theta('jacobi', h)[1].real, 4) for h in (0.0, 0.05, 0.2)])
print("sequential: 1/theta at h = 0, 1, 1.41:", [np.round(inv_theta('end', h)[1], 4) for h in (0.0, 1.0, 1.41)])
