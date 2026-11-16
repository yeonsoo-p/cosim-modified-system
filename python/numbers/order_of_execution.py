"""Energy and damping: what the order of execution decides.

Paper: section "Energy and damping: the order of execution" without the optimisation of its example (for that
see optimal_schemes.py), and the values drawn in the figure of the order of execution:
  1. the figure of the order of execution: what the zero-order holds pass between the end stores of the chain
     of three and return to each store, and the numerical dissipation between the end stores;
  2. section "The coupling graph": the least trace of a positive semidefinite numerical dissipation with the
     forced entries on a star with three leaves (3, 1.5 and 1), and the energy-conserving sweep (one-step
     error 1.001 alpha_*; with the dissipation of the chain: nu = 0 and an injection of 0.033 h^3 per step),
     which is also the mark "from end to end" of the figure of the trade;
  3. section "Energy stored and energy created" and the figure of the energy over a run: the sequential holds
     on the lossless chain of three at h = 0.1 (injection alpha_* and 2 alpha_*, the bound 1.15 on the energy,
     the threshold h = sqrt 2).
Run:  uv run --no-project --with numpy --with scipy python order_of_execution.py
"""
import numpy as np
from scipy.linalg import expm
from scipy.optimize import minimize

from cosim import (alpha_star, chain3, check, first_above_one, head, hold, lossless_chain, modified, one_step, show,
                   signs, spectral_radius, summary)

S3 = [1, 1, 1]
ORDERS = (("Jacobi scheme", (0, 0, 0)), ("middle store first", (1, 0, 1)), ("from end to end", (0, 1, 2)))

# ------------------------------------------------------------------ 1. the figure of the order of execution
head("Figure of the order of execution: zero-order holds on the chain of three stores at h = 0.1")
A, h = chain3(), 0.1
U = expm(h * A)
PAPER = {"Jacobi scheme": ((-1, -1), (1, 2, 1), "+1", "0"), "middle store first": ((1, 1), (-1, 2, -1), "-1", "0"),
         "from end to end": ((-1, 1), (1, 0, -1), "0", "-1")}
for name, stage in ORDERS:
    X = hold(A, S3, stage, h)
    E = (X - U) / (0.5 * h * h)
    D = modified(X, h) - A
    dR, dJ = -0.5 * (D + D.T), 0.5 * (D - D.T)
    (p13, p31), pd, pR, pJ = PAPER[name]
    print(f"  {name}")
    show("    passed from store 3 to store 1, [X - U]_13 in units of h^2/2", f"{p13:+d}", E[0, 2], digits=1)
    show("    passed from store 1 to store 3, [X - U]_31 in units of h^2/2", f"{p31:+d}", E[2, 0], digits=1)
    for i in range(3):
        show(f"    reaction, diagonal entry {i + 1} of X - U in units of h^2/2", f"{pd[i]:+d}", E[i, i], digits=1)
    show("    [Delta_R]_13 in units of H w^2/2", pR, dR[0, 2] / (0.5 * h), digits=1)
    show("    [Delta_J]_13 in units of H w^2/2", pJ, dJ[0, 2] / (0.5 * h), digits=1)
    if stage != (0, 0, 0):
        check("    total numerical damping of a sequential hold: nu = 0 exactly", abs(one_step(X, U)["H_nu"]) < 1e-13)

# ------------------------------------------------------------------ 2. the coupling graph
head('Section "The coupling graph": star with three leaves and unit rates')
# hub: a mass (state 0); leaves: three springs (states 1, 2, 3)
STAR = np.zeros((4, 4))
STAR[0, 1:], STAR[1:, 0] = -1.0, 1.0


def forced_block(stage, H=1e-3):
    """[Delta_R]_ij / H between the leaves, which are pairwise not partners: no coefficient reaches these
    entries, so that to leading order they are those of the zero-order hold. Rounded to multiples of 1/2."""
    D = modified(hold(STAR, [1, 1, 1, 1], stage, H), H) - STAR
    dR = -0.5 * (D + D.T)[1:, 1:] / H
    off = np.round(2 * dR) / 2
    np.fill_diagonal(off, 0.0)
    return off, np.abs(dR - np.diag(np.diag(dR)) - off).max()


def predicted_block(stage):
    """-(1/2) tau_k A_ik A_kj with tau_k = (varsigma_ik + varsigma_jk)/2 for the hub k"""
    sg = signs([1, 1, 1, 1], stage)
    off = np.zeros((3, 3))
    for i in range(1, 4):
        for j in range(1, 4):
            if i != j:
                off[i - 1, j - 1] = -0.5 * 0.5 * (sg[i, 0] + sg[j, 0]) * STAR[i, 0] * STAR[0, j]
    return off


def least_trace(off, starts=20):
    """least trace of a positive semidefinite matrix with the given off-diagonal entries: M = L L^T,
    minimise ||L||_F^2 subject to the off-diagonal entries of L L^T"""
    rng = np.random.default_rng(0)
    iu = np.triu_indices(3, 1)
    cons = dict(type="eq", fun=lambda v: (v.reshape(3, 3) @ v.reshape(3, 3).T)[iu] - off[iu])
    best = np.inf
    for _ in range(starts):
        res = minimize(lambda v: v @ v, rng.normal(size=9), constraints=[cons], method="SLSQP",
                       options=dict(ftol=1e-14, maxiter=500))
        if res.success and np.abs(cons["fun"](res.x)).max() < 1e-9:
            best = min(best, res.fun)
    return best


for name, stage, paper in (("Jacobi scheme", (0, 0, 0, 0), "3"), ("hub last", (1, 0, 0, 0), "3"),
                           ("hub first", (0, 1, 1, 1), "1.5"), ("one leaf before the hub", (1, 0, 2, 2), "1"),
                           ("two leaves before the hub", (1, 0, 0, 2), "1")):
    off, dev = forced_block(stage)
    check(f"{name}: forced entries between the leaves as in the formula", np.allclose(off, predicted_block(stage))
          and dev < 1e-2, "[Delta_R]_12, _13, _23 / H = " + ", ".join(f"{off[i, j]:+.1f}" for i, j in ((0, 1), (0, 2), (1, 2))))
    show(f"{name}: least trace, divided by H", paper, least_trace(off), digits=3)

head('Section "The coupling graph": the energy-conserving sweep on the chain of three at h = 0.1')


def rotation(n, k, angle):
    Z = np.zeros((n, n))
    Z[k + 1, k], Z[k, k + 1] = 1.0, -1.0
    return expm(angle * Z)


def sweep(hh, damped):
    """the product of plane rotations with the angles H w, executed from store 1 to store 3; damped: the map
    exp(-H R/2) X exp(-H R/2) for the chain with the dissipation rate r"""
    X = rotation(3, 1, hh) @ rotation(3, 0, hh)
    if damped:
        Rm = -0.5 * (chain3() + chain3().T)
        X = expm(-0.5 * hh * Rm) @ X @ expm(-0.5 * hh * Rm)
    return X


A0 = lossless_chain(3)
X = sweep(h, False)
check("lossless chain: the sweep is orthogonal (it conserves the energy)", np.allclose(X.T @ X, np.eye(3), atol=1e-14))
show("lossless chain: one-step error in units of the bound alpha_* of that chain", "1.001",
     one_step(X, expm(h * A0))["alpha"] / alpha_star(A0, S3, h)[0])
Xd, a_star = sweep(h, True), alpha_star(A, S3, h)[0]
p = one_step(Xd, U)
check("damped chain: total numerical damping nu = 0 exactly", abs(p["H_nu"]) < 1e-13, f"H nu = {p['H_nu']:.1e}")
show("damped chain: energy injected per step, (s_+ - 1)/h^3", "0.033", (p["s_plus"] - 1) / h ** 3)
vals = [(one_step(sweep(x, True), expm(x * A))["s_plus"] - 1) / x ** 3 for x in (0.2, 0.05, 0.025)]
print("    a remainder of third order: (s_+ - 1)/h^3 = " + ", ".join(f"{v:.4f}" for v in vals) + " at h = 0.2, 0.05, 0.025")
print("  mark 'from end to end' of the figure of the trade (the damped sweep), in units of alpha_*:")
show("    one-step error", "1.001", p["alpha"] / a_star)
show("    energy injected over a step", "0.0066", (p["s_plus"] - 1) / a_star)
show("    damping added over a step", "0.0066", (1 - p["s_minus"]) / a_star)

# ------------------------------------------------------------------ 3. energy stored and energy created
head('Section "Energy stored and energy created": the lossless chain of three at h = 0.1')
U0 = expm(h * A0)
a0 = alpha_star(A0, S3, h)[0]
steps = int(round(40.0 / h))                              # the run of the figure of the energy, w t <= 40
bound = (1 + h / np.sqrt(2)) / (1 - h / np.sqrt(2))
show("bound on the energy, (1 + h/sqrt 2)/(1 - h/sqrt 2)", "1.15", bound)
for name, stage, paper in (("from end to end", (0, 1, 2), "1.0"), ("middle store first", (1, 0, 1), "2.0"),
                           ("Jacobi scheme", (0, 0, 0), "2.0")):
    X = hold(A0, S3, stage, h)
    show(f"{name}: energy injected per step, (s_+ - 1)/alpha_*", paper, (one_step(X, U0)["s_plus"] - 1) / a0)
    P, top = np.eye(3), 1.0
    for _ in range(steps):
        P = X @ P
        top = max(top, np.linalg.norm(P, 2) ** 2)
    if stage == (0, 0, 0):
        check(f"{name}: the energy grows", top > 100 and spectral_radius(X) > 1,
              f"largest energy up to w t = 40: {top:.0f}, spectral radius {spectral_radius(X):.5f}")
        continue
    Aseq = signs(S3, stage) * A0                          # symmetric: no two partners share a stage
    Q = np.eye(3) - 0.5 * h * Aseq
    show(f"{name}: ||A_seq|| / (sqrt 2 w)", "1", np.linalg.norm(Aseq, 2) / np.sqrt(2), digits=10)
    check(f"{name}: the modified energy is conserved, X^T Q X = Q", np.allclose(X.T @ Q @ X, Q, atol=1e-13))
    check(f"{name}: the energy stays within the bound", top <= bound + 1e-12, f"largest energy up to w t = 40: {top:.4f}")
    show(f"{name}: stable up to h = sqrt 2 =", "1.414", first_above_one(lambda x: spectral_radius(hold(A0, S3, stage, x)),
                                                                        0.05, 3.0, tol=1e-9))
P, top = np.eye(3), 1.0
for _ in range(steps):
    P = sweep(h, False) @ P
    top = max(top, np.linalg.norm(P, 2) ** 2)
check("energy-conserving sweep: the energy stays at its initial value", abs(top - 1) < 1e-10)
summary()
