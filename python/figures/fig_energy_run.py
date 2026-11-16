"""Injection is not growth (section "Energy stored and energy created"): energy at the communication points on
the lossless chain of three, h = 0.1.  Zero-order holds in a Jacobi scheme and in the two sequential orders,
and the energy-conserving sweep (angles theta_k = h).  Plotted: ||X^k||^2, the largest energy after k macro
steps over all initial states of unit energy; the monolithic system is lossless and stays at 1.
Run:  uv run --no-project --with numpy --with scipy --with matplotlib python fig_energy_run.py
"""
import numpy as np
from scipy.linalg import expm

from style import FSS, INK, LW_BOUND, LW_DATA, NARROW, OCHRE, RUST, TEAL, plot_axes, plt, save

h = 0.1
A = np.array([[0.0, -1.0, 0.0], [1.0, 0.0, -1.0], [0.0, 1.0, 0.0]])
U = expm(h * A)
c = abs(U[0, 2]) / np.linalg.norm(U[:, 2])          # the bound alpha_* on the one-step error


def E(i):
    """store i advances exactly on the held samples of its partners"""
    M = np.zeros((3, 3))
    M[i] = A[i]
    return expm(h * M)


def seq(order):
    X = np.eye(3)
    for i in order:
        X = E(i) @ X
    return X


def rot(k, phi):
    Z = np.zeros((3, 3))
    Z[k + 1, k], Z[k, k + 1] = 1.0, -1.0
    return expm(phi * Z)


schemes = {
    "jacobi": (np.eye(3) + h * A, RUST),
    "middle": (seq((1, 0, 2)), OCHRE),
    "end": (seq((0, 1, 2)), TEAL),
    "sweep": (rot(1, h) @ rot(0, h), INK),
}
T = 40.0
K = int(round(T / h))
t = h * np.arange(K + 1)
FH = 2.45
fig = plt.figure(figsize=(NARROW, FH))
ax = plot_axes(fig, 0.56, 0.44, NARROW - 0.56 - 0.10, FH - 0.44 - 0.08)
inj, top = {}, {}
for name, (X, col) in schemes.items():
    P, g = np.eye(3), [1.0]
    for _ in range(K):
        P = X @ P
        g.append(np.linalg.norm(P, 2) ** 2)
    inj[name] = (np.linalg.norm(X @ np.linalg.inv(U), 2) - 1) / c
    top[name] = max(g)
    ax.plot(t, g, color=col, lw=LW_BOUND if name == "sweep" else LW_DATA, zorder=4 if name == "sweep" else 3)
    print(f"{name:7s} (s+ - 1)/c = {inj[name]:5.2f}   largest energy gain up to omega t = {T:g}: {top[name]:.5g}"
          f"   spectral radius {max(abs(np.linalg.eigvals(X))):.6f}")
ax.set_ylim(0.955, 1.36)
ax.set_xlim(0, T)
ax.set_yticks([1.0, 1.1, 1.2, 1.3])
ax.set_xlabel(r"time, $\omega t$")
ax.set_ylabel(r"largest energy gain, $\|X^k\|^2$")
KW = dict(fontsize=FSS, linespacing=1.1)
ax.text(3.4, 1.355, "Jacobi scheme:\n" + r"$s_+-1=%.1f\,\alpha_*$, grows" % inj["jacobi"], color=RUST, va="top", ha="left", **KW)
ax.text(39.6, 1.238, r"middle store first: $s_+-1=%.1f\,\alpha_*$, bounded" % inj["middle"], color=OCHRE, ha="right",
        va="center", **KW)
ax.text(39.6, 1.196, r"from end to end: $s_+-1=%.1f\,\alpha_*$, bounded" % inj["end"], color=TEAL, ha="right",
        va="center", **KW)
ax.text(39.6, 0.989, "monolithic system; energy-conserving sweep", color=INK, ha="right", va="top", **KW)
save(fig, "energy_run")
print("c =", c)
