"""The least values over all schemes with one held sample, to leading order in the macro step.

Paper: the lemma "the reach of the coefficients" and what follows from it: the proposition "least one-step
error" (the star with three leaves), the example "the chain of three stores" (alpha_* is the least one-step
error in every order), the theorem "the amount" and the star with m leaves in the section "The coupling graph",
the example "the chain of three, by order of execution" (without injection), the remark after the proposition
"the reaction" (partner weights only; the ring of four), the largest energy over a run in the section "Energy
stored and energy created", the least error over a run (the display after the theorem "order barrier"), and the
proposition "more held samples" (two samples on the chain of four, three on the chain of five; there X - U is
-H^(l+1) (D_l + Z) to leading order, with Z free on the stores fewer than l + 1 links away).

To leading order X - U = H^2 (P + Z) with P = A_varsigma A / 2 and Z free in the reach of the coefficients:
for scalar stores, the diagonal and the entries between partners. Each least value is a convex programme over
Z; the paper proves the closed forms, and this script recomputes them from the programmes. All networks here are
scalar stores with unit rates (the chain of three has r = 0.1).
Run:  uv run --no-project --with numpy --with scipy --with cvxpy python least_values.py
"""
import cvxpy as cp
import numpy as np
from scipy.linalg import expm, sqrtm

from cosim import chain3, check, head, hold, lossless_chain, show, signs, summary


def star(m):
    """hub (state 0) and m leaves, unit rates"""
    A = np.zeros((m + 1, m + 1))
    for l in range(1, m + 1):
        A[l, 0], A[0, l] = 1.0, -1.0
    return A


def ring(n):
    A = np.zeros((n, n))
    for i in range(n):
        A[i, (i + 1) % n], A[(i + 1) % n, i] = -1.0, 1.0
    return A


def half_step(A, stage):
    """P = A_varsigma A / 2 for scalar stores"""
    n = len(A)
    S = signs([1] * n, stage)
    As = np.where(np.eye(n) > 0, 0.0, S * A)
    return 0.5 * As @ A


def reach(A, own=True):
    m = (np.abs(A) > 0) & ~np.eye(len(A), dtype=bool)
    m = m | m.T
    return m | np.eye(len(A), dtype=bool) if own else m


def program(P, mask, kind):
    n = len(P)
    Z = cp.Variable((n, n))
    cons = [Z[i, j] == 0 for i in range(n) for j in range(n) if not mask[i, j]]
    M = P + Z
    S = (M + M.T) / 2
    if kind == "norm":                      # least one-step error over H^2
        obj = cp.sigma_max(M)
    elif kind == "norm, no injection":      # the same among schemes that inject no energy
        obj = cp.sigma_max(M)
        cons.append(S << 0)
    elif kind == "spread":                  # least mu + iota over H
        obj = cp.lambda_max(S) - cp.lambda_min(S)
    elif kind == "injection":               # least iota over H
        obj = cp.lambda_max(S)
    pr = cp.Problem(cp.Minimize(obj), cons)
    pr.solve()
    return pr.value, Z.value


ORDERS3 = {"Jacobi": (0, 0, 0), "middle store first": (1, 0, 1), "end to end": (0, 1, 2)}
A = chain3()

head('Example "the chain of three stores" and example "the chain of three, by order of execution"')
for name, st in ORDERS3.items():
    P = half_step(A, st)
    e, _ = program(P, reach(A), "norm")
    g, _ = program(P, reach(A), "norm, no injection")
    show(f"{name}: least one-step error, in units of alpha_* = h^2/2", "1", e / 0.5, 3)
    show(f"{name}: the same without injection, in units of alpha_*", "1" if name == "end to end" else "2", g / 0.5, 3)
for name, st in ORDERS3.items():
    s, _ = program(half_step(A, st), reach(A), "spread")
    pair = 0 if name == "end to end" else 1
    check(f"{name}: least spread = |sum_k tau_k A_1k A_k3| (pair value)", abs(s - pair) < 1e-5,
          f"{s:.6f}")

head('Section "The coupling graph": the star with m leaves (least mu + iota in units of H)')
STAR_ORDERS = {"Jacobi": (0, 0, 0, 0), "hub first": (0, 1, 1, 1), "hub last": (1, 0, 0, 0),
               "one leaf before the hub": (1, 0, 2, 2), "two leaves before the hub": (1, 0, 0, 2)}
for name, st in STAR_ORDERS.items():
    s, _ = program(half_step(star(3), st), reach(star(3)), "spread")
    show(f"three leaves, {name}", "1.5" if "before" not in name else "1", s, 1)
for m in (4, 5, 6):
    s, _ = program(half_step(star(m), (0,) * (m + 1)), reach(star(m)), "spread")
    check(f"{m} leaves, Jacobi: least spread m/2", abs(s - m / 2) < 1e-5, f"{s:.6f}")

head('Proposition "least one-step error": the star with three leaves in a Jacobi scheme')
P = half_step(star(3), (0, 0, 0, 0))
e, _ = program(P, reach(star(3)), "norm")
rows = max(np.linalg.norm(P[l, [k for k in (1, 2, 3) if k != l]]) for l in (1, 2, 3))
show("least one-step error, in units of H^2 omega^2", "0.75", e, 2)
show("in units of alpha_* (the largest response of a leaf)", "1.06", e / rows, 2)

head('Remark after the proposition "the reaction": partner weights only, Jacobi, least iota in units of H')
for name, An in (("chain of three", A), ("star with three leaves", star(3)), ("ring of four", ring(4))):
    P = half_step(An, (0,) * len(An))
    i_least, _ = program(P, reach(An, own=False), "injection")
    single = max(np.diag((P + P.T) / 2))
    print(f"  {name:<24s} least injection {i_least:.4f}   bound of single subsystems {single:.4f}")
    if name == "ring of four":
        show("ring of four: least injection over the bound of single subsystems", "2", i_least / single, 0)
    else:
        check(f"{name}: the bound of single subsystems is reached", abs(i_least - single) < 1e-5)

head('Section "Energy stored and energy created": largest energy over a run, lossless chain of three, h = 0.1')
L, h = lossless_chain(3), 0.1
for name, st in (("end to end", (0, 1, 2)), ("middle store first", (1, 0, 1))):
    X = hold(L, [1, 1, 1], st, h)
    S = signs([1, 1, 1], st)
    As = np.where(np.eye(3) > 0, 0.0, S * L)
    Q = np.eye(3) - 0.25 * h * (As + As.T)
    kappa = np.linalg.eigvalsh(Q)[-1] / np.linalg.eigvalsh(Q)[0]
    Xk, best = np.eye(3), 0.0
    for _ in range(200000):
        Xk = X @ Xk
        best = max(best, np.linalg.norm(Xk, 2) ** 2)
    show(f"{name}: largest energy over 2e5 steps", "1.15", best, 2)
    if name == "middle store first":
        Qh = np.real(sqrtm(Q))
        a = Qh @ np.array([1.0, 0.0, 1.0])
        V = np.linalg.eigh(Q)[1]
        check("middle store first: the extreme eigenvectors of Q lie in the turned plane",
              max(abs(V[:, 0] @ a), abs(V[:, 2] @ a)) < 1e-12, f"kappa(Q) = {kappa:.5f}, reached {best:.5f}")
check("2 cos theta = 2 - 2 h^2 is not an integer at h = 0.1", abs((2 - 2 * h * h) - round(2 - 2 * h * h)) > 1e-9)

head('Display after the theorem "order barrier": least error over a run of length T = 1/(2||A||), in units of H')
T = 1.0 / (2 * np.linalg.norm(A, 2))
ts = np.linspace(T / 40, T, 40)


def Phi(t, M, q=200):
    s = (np.arange(q) + 0.5) * t / q
    return sum(expm((t - si) * A) @ M @ expm(si * A) for si in s) * (t / q)


mask = reach(A)
free = [(p, q) for p in range(3) for q in range(3) if mask[p, q]]
basis = {}
for (p, q) in free:
    E = np.zeros((3, 3))
    E[p, q] = 1.0
    basis[(p, q)] = [Phi(t, E) for t in ts]
for name, st in ORDERS3.items():
    P = half_step(A, st)
    base = [Phi(t, P) for t in ts]
    z, r = cp.Variable(len(free)), cp.Variable()
    terms = [base[k] + sum(z[m] * basis[f][k] for m, f in enumerate(free)) for k in range(len(ts))]
    cp.Problem(cp.Minimize(r), [cp.sigma_max(M) <= r for M in terms]).solve()
    zoh = max(np.linalg.norm(M, 2) for M in base)
    show(f"{name}: least error over the run", "0.16", r.value, 2)
    print(f"      zero-order hold (Z = 0): {zoh:.4f}")
    check(f"{name}: the zero-order hold lies between 0.33 and 0.35 after rounding", 0.325 <= zoh < 0.355)


def gamma(l, sigma):
    """gamma_l^sigma = int_0^1 binom(s + l - 1 - sigma, l) ds"""
    s = (np.arange(4000) + 0.5) / 4000
    return float(np.mean(np.prod([(s + l - 1 - sigma - m) / (m + 1) for m in range(l)], axis=0)))


def defect(A, stage, l):
    """D_l with the rows sum_j gamma_l^sigma_ij A_ij (A^l)_j for scalar stores; a sample is new if its
    sender runs at an earlier stage"""
    n, Al = len(A), np.linalg.matrix_power(A, l)
    D = np.zeros((n, n))
    for i in range(n):
        for j in range(n):
            if j != i and A[i, j] != 0:
                D[i] += gamma(l, 1 if stage[j] < stage[i] else 0) * A[i, j] * Al[j]
    return D


def shown(n, l):
    """on a chain a store is shown the stores fewer than l + 1 links away"""
    return np.abs(np.subtract.outer(np.arange(n), np.arange(n))) <= l


head('Proposition "more held samples": least mu + iota in units of H^l omega^(l+1) on chains')
A4 = lossless_chain(4)
for name, st in (("Jacobi", (0, 0, 0, 0)), ("middle stores first", (1, 0, 0, 1)), ("end to end", (0, 1, 2, 3))):
    s, _ = program(defect(A4, st, 2), shown(4, 2), "spread")
    show(f"two samples, chain of four, {name}", "0.5" if name == "end to end" else "0", s, 1)
A5 = lossless_chain(5)
for name, st in (("Jacobi", (0, 0, 0, 0, 0)), ("both ends last", (1, 0, 0, 0, 1)),
                 ("end to end", (0, 1, 2, 3, 4)), ("from the other end", (4, 3, 2, 1, 0))):
    D = defect(A5, st, 3)
    s, _ = program(D, shown(5, 3), "spread")
    entry = abs(D[0, 4] + D[4, 0]) / 2
    check(f"three samples, chain of five, {name}: trades, least spread 2 |entry|",
          entry > 0.04 and abs(s - 2 * entry) < 1e-4, f"{s:.5f}")
summary()
