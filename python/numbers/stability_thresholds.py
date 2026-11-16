"""The two ways in which the zero-order hold loses stability on the chain of three stores.

Paper: section "Modes and stability" (the thresholds h = 0.05 and h = 1.415 in the text and in the caption of
the figure of the two ways of losing stability) and the marks of that figure.

The zero-order hold is the implicit midpoint rule for the shifted system E x' = A x. The one-step map is the
Cayley transform of the pencil (A, E):  X v = xi v  <=>  A v = theta E v,  1/theta = H/2 + H/(xi - 1).
  * A mode loses its damping: theta crosses the imaginary axis. In a Jacobi scheme X = I + H phi A and
    1/theta = 1/lambda^ + H/2 for the eigenvalues lambda^ of phi A, so that the threshold is H = -2 Re(1/lambda^).
  * E becomes singular: an eigenvalue of X passes through -1.
Run:  uv run --no-project --with numpy --with scipy python stability_thresholds.py
"""
import itertools

import numpy as np
from scipy.linalg import eig

from cosim import chain3, check, first_above_one, head, hold, phi, shifted_E, show, spectral_radius, summary

A = chain3()                # r = 0.1 omega, omega = 1, h = omega H
S = [1, 1, 1]
JACOBI = (0, 0, 0)
SEQUENTIAL = sorted(set(itertools.permutations(range(3))) | {(1, 0, 1), (0, 1, 0)})    # no two partners at one stage


def inv_theta(stage, h):
    """1/theta for the oscillatory eigenvalue of the shifted system (the one drawn in the figure)"""
    th = eig(A, shifted_E(A, S, stage, h), right=False)
    z = 1.0 / th[np.isfinite(th)]
    return z[np.argmax(z.imag)]


head('Section "Modes and stability": the Cayley transform on the chain of three stores')
worst = 0.0
for stage in (JACOBI, (0, 1, 2), (1, 0, 1)):
    for h in (0.1, 0.7):
        xi = np.linalg.eigvals(hold(A, S, stage, h))
        th = eig(A, shifted_E(A, S, stage, h), right=False)
        worst = max(worst, max(min(abs(1 / t - (h / 2 + h / (x - 1))) for x in xi) for t in th))
check("1/theta = H/2 + H/(xi - 1) for the eigenvalues xi of X and theta of (A, E)", worst < 1e-10, f"{worst:.1e}")

head("Jacobi scheme: a mode loses its damping")


def gap(h):
    lam = np.linalg.eigvals(phi(A, S, h) @ A)
    lam = lam[np.abs(lam.imag) > 1e-9]
    return h + 2 * np.real(1 / lam).min()


lo, hi = 0.01, 0.2
for _ in range(60):
    mid = 0.5 * (lo + hi)
    lo, hi = (mid, hi) if gap(mid) < 0 else (lo, mid)
show("threshold h = -2 Re(1/lambda^)", "0.05", hi, digits=4)
show("first h with spectral radius above one", "0.05", first_above_one(lambda h: spectral_radius(hold(A, S, JACOBI, h)), 0.005, 1.0),
     digits=4)

head("Sequential schemes: E becomes singular")
for stage in SEQUENTIAL:
    det = lambda h: np.linalg.det(shifted_E(A, S, stage, h))
    lo, hi = 1.0, 2.0
    for _ in range(60):
        mid = 0.5 * (lo + hi)
        lo, hi = (mid, hi) if det(mid) * det(1.0) > 0 else (lo, mid)
    show(f"stages {stage}: det E = 0 at h =", "1.415", hi)
    h1 = first_above_one(lambda h: spectral_radius(hold(A, S, stage, h)), 0.005, 3.0)
    show(f"stages {stage}: first h with spectral radius above one", "1.415", h1)
    xi = np.linalg.eigvals(hold(A, S, stage, hi))
    check(f"stages {stage}: X has the eigenvalue -1 there", min(abs(xi + 1)) < 1e-6)

head("Figure of the two ways of losing stability: the marks, omega/theta of the oscillatory mode")
print("  Jacobi scheme (moves right by h/2):")
for h in (0.0, 0.05, 0.2, 0.5, 0.9):
    z = inv_theta(JACOBI, h)
    print(f"    h = {h:<4}:  {z.real:+.4f} {z.imag:+.4f} i")
check("Jacobi scheme: the real part is -r/4 + h/2 = -0.025 + h/2",
      all(abs(inv_theta(JACOBI, h).real - (-0.025 + h / 2)) < 1e-9 for h in (0.0, 0.05, 0.2, 0.5, 0.9)))
print("  sequential scheme from end to end (the pair moves down the line of constant real part):")
for h in (0.0, 0.5, 1.0, 1.3):
    z = inv_theta((0, 1, 2), h)
    print(f"    h = {h:<4}:  {z.real:+.4f} {z.imag:+.4f} i")
lo, hi = 1.40, 1.42
for _ in range(60):
    mid = 0.5 * (lo + hi)
    lo, hi = (mid, hi) if abs(inv_theta((0, 1, 2), mid).imag) > 1e-9 else (lo, mid)
print(f"    the pair meets on the real axis at h = {lo:.4f}, at omega/theta = {inv_theta((0, 1, 2), lo).real:+.4f},")
print("    and one of the two real eigenvalues passes the origin at the threshold above")
summary()
