"""The zero-order hold on an undamped pair of scalar stores.

Paper: example "zero-order hold on an undamped pair" (section "The two parts of the difference") with the
figure of the energy circle, and the sentences on two stores in the sections "Modes and stability" (frequency
of the leapfrog method, threshold H omega = 2) and "Energy stored and energy created".

Two stores exchange energy at the rate omega: A = omega J, J = [[0, -1], [1, 0]]; h = omega H.
  Jacobi scheme:      X = I + h J, and the principal logarithm gives
                      H Delta_J = -(h - arctan h) J,   H Delta_R = -(1/2) ln(1 + h^2) I;
                      the hold lags by the angle h - arctan h and multiplies the energy by 1 + h^2 per step.
  sequential scheme:  the symplectic Euler method; it conserves x1^2 + x2^2 -/+ h x1 x2 and is stable for h < 2.
Run:  uv run --no-project --with numpy --with scipy python undamped_pair.py
"""
import numpy as np

from cosim import check, head, hold, modified, show, spectral_radius, summary

J = np.array([[0.0, -1.0], [1.0, 0.0]])

head('Example "zero-order hold on an undamped pair": Jacobi scheme (omega = 1)')
for h in (1.0, 0.1):
    X = hold(J, [1, 1], (0, 0), h)
    D = h * (modified(X, h) - J)                      # H times the difference
    dJ, dR = 0.5 * (D - D.T), -0.5 * (D + D.T)
    check(f"h = {h}: X = I + h J", np.allclose(X, np.eye(2) + h * J, atol=1e-14))
    check(f"h = {h}: H Delta_J = -(h - arctan h) J", np.allclose(dJ, -(h - np.arctan(h)) * J, atol=1e-13),
          f"lag in angle per step {h - np.arctan(h):.6f}")
    check(f"h = {h}: H Delta_R = -(1/2) ln(1 + h^2) I", np.allclose(dR, -0.5 * np.log(1 + h * h) * np.eye(2), atol=1e-13),
          f"energy factor per step {np.linalg.norm(X, 2) ** 2:.6f} = 1 + h^2")
print("  the figure of the energy circle is drawn for h = 1: energy factor 2 and lag 1 - pi/4 = "
      f"{1 - np.pi / 4:.4f} per step")
h = 1e-2
D = modified(hold(J, [1, 1], (0, 0), h), h) - J
print(f"  orders in the macro step, at h = {h}: |Delta_R| / h = {np.linalg.norm(D + D.T, 2) / 2 / h:.4f} (first order),"
      f" |Delta_J| / h^2 = {np.linalg.norm(D - D.T, 2) / 2 / h ** 2:.4f} (second order)")

head('Sections "Modes and stability" and "Energy stored and energy created": two stores in a sequential scheme')
for h in (0.1, 1.0):
    for name, stage, sign in (("store 1 first", (0, 1), -1.0), ("store 2 first", (1, 0), +1.0)):
        X = hold(J, [1, 1], stage, h)
        Q = np.array([[1.0, 0.5 * sign * h], [0.5 * sign * h, 1.0]])       # x1^2 + x2^2 -/+ h x1 x2
        check(f"h = {h}, {name}: x1^2 + x2^2 {'-' if sign < 0 else '+'} h x1 x2 is conserved",
              np.allclose(X.T @ Q @ X, Q, atol=1e-13))
for h in (0.1, 1.0, 1.9):
    ang = abs(np.angle(np.linalg.eigvals(hold(J, [1, 1], (0, 1), h))[0]))      # H times the frequency of the hold
    check(f"h = {h}: the frequency is that of the leapfrog method, sin(H w~/2) = H w/2", abs(np.sin(ang / 2) - h / 2) < 1e-13)
rho = lambda h: spectral_radius(hold(J, [1, 1], (0, 1), h))
lo, hi = 1.5, 2.5
for _ in range(60):
    mid = 0.5 * (lo + hi)
    lo, hi = (lo, mid) if rho(mid) > 1 + 1e-9 else (mid, hi)
show("the sequential hold of two stores is stable up to h =", "2", hi, digits=3)
X = hold(J, [1, 1], (0, 0), 0.1)
show("Jacobi scheme: the energy is multiplied per step by 1 + h^2; at h = 0.1", "1.01", np.linalg.det(X), digits=6)
summary()
