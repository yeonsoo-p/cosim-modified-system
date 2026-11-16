"""The schemes with the smallest one-step error on the chain of three stores.

Paper: example "the chain of three, by order of execution" (six values at h = 0.1), the marks of the figure of
the trade between injection and added damping, and, for the Jacobi scheme, the sentence of the example "the
chain of three stores" that stable schemes with local gains come within a relative 1e-5 of the bound alpha_*,
with the circles of the figure of the bound.

The class. A scheme with one held sample on scalar stores, x_i+ = F_i x_i + sum_j g_ij yhat_j, has the
one-step map X = (I - G_new)^(-1) (F + G_old), with the coefficients of the new samples in G_new and the others
in G_old; for a scalar store a local gain realises every F_i > 0 and every g_ij. For fixed G_new the map X is
affine in F and G_old, so that the one-step error alpha = ||X U^(-1) - I|| is a convex function of them.

What is a global optimum and what is not.
  * Jacobi scheme: G_new = 0, one convex programme: the values are GLOBAL OPTIMA.
  * Sequential orders: the coefficients of the new samples (two numbers) are varied by the Nelder-Mead method
    from four starting points, with the convex programme for the remaining coefficients at each of them. The
    values are the smallest found by this LOCAL SEARCH: upper bounds of the minima.

  * Circles of the figure of the bound: stable Jacobi schemes at the bound; where the minimiser that the
    solver returns is unstable, a second convex programme selects a stable scheme within a relative 1e-5.

The run takes about one minute.
Run:  uv run --no-project --with numpy --with scipy --with cvxpy python optimal_schemes.py
"""
import warnings

import cvxpy as cp
import numpy as np
from scipy.linalg import expm
from scipy.optimize import minimize

from cosim import alpha_star, chain3, check, head, show, spectral_radius, summary

warnings.filterwarnings("ignore")
ORDERS = (("jacobi", None), ("middle", (1, 0, 2)), ("end", (0, 1, 2)))     # order of execution of the stores
LINKS = ((0, 1), (1, 0), (1, 2), (2, 1))       # (i, j): store i receives a sample of its partner j


class Problem:
    """the schemes with one held sample on the chain of three stores in one order of execution"""

    def __init__(self, A, H, order):
        self.A, self.H = A, H
        self.U = expm(H * A)
        self.Uinv = np.linalg.inv(self.U)
        pos = None if order is None else {s: k for k, s in enumerate(order)}
        self.new = [(i, j) for i, j in LINKS if pos is not None and pos[j] < pos[i]]
        self.old = [(i, j) for i, j in LINKS if (i, j) not in self.new]
        self.start = None

    def start_of_hold(self):
        """the coefficients of the new samples in the zero-order hold"""
        a = np.diag(self.A)
        g = np.where(np.abs(a) > 0, np.expm1(self.H * a) / np.where(np.abs(a) > 0, a, 1.0), self.H)
        return np.array([self.A[i, j] * g[i] for i, j in self.new])

    def inner(self, outer, no_injection=False):
        """the convex programme for F and the coefficients of the old samples, for given coefficients of the
        new samples: smallest alpha, optionally among the schemes with s_+ <= 1. Returns (alpha, X)."""
        n = 3
        Gn = np.zeros((n, n))
        for (i, j), g in zip(self.new, outer):
            Gn[i, j] = g
        M = np.linalg.inv(np.eye(n) - Gn)
        cols = []
        for i, j in [(i, i) for i in range(n)] + self.old:
            E = np.zeros((n, n))
            E[i, j] = 1.0
            cols.append(E.ravel())
        T = np.array(cols).T
        z = cp.Variable(T.shape[1])
        D = M @ cp.reshape(T @ z, (n, n), order="C") @ self.Uinv
        cons = [cp.sigma_max(D) <= 1.0] if no_injection else []
        prob = cp.Problem(cp.Minimize(cp.sigma_max(D - np.eye(n)) / self.H ** 2), cons)
        try:
            prob.solve(solver=cp.CLARABEL)
        except Exception:
            return np.inf, None
        if z.value is None:
            return np.inf, None
        X = M @ (T @ z.value).reshape(n, n)
        return np.linalg.norm(X @ self.Uinv - np.eye(n), 2), X

    def least_trace(self, bound):
        """Jacobi scheme: among the schemes with alpha <= bound, the one with the least trace of X (a convex
        programme; it selects a strongly damped scheme among the many with nearly the smallest alpha)"""
        n = 3
        cols = []
        for i, j in [(i, i) for i in range(n)] + self.old:
            E = np.zeros((n, n))
            E[i, j] = 1.0
            cols.append(E.ravel())
        T = np.array(cols).T
        z = cp.Variable(T.shape[1])
        Xv = cp.reshape(T @ z, (n, n), order="C")
        prob = cp.Problem(cp.Minimize(cp.trace(Xv)),
                          [cp.sigma_max(Xv @ self.Uinv - np.eye(n)) / self.H ** 2 <= bound / self.H ** 2])
        prob.solve(solver=cp.CLARABEL)
        X = (T @ z.value).reshape(n, n)
        return np.linalg.norm(X @ self.Uinv - np.eye(n), 2), X

    def best(self, no_injection=False, starts=4, seed=0):
        """smallest alpha: one convex programme in a Jacobi scheme, a local search otherwise"""
        if not self.new:
            return self.inner(np.zeros(0), no_injection)
        rng = np.random.default_rng(seed)
        x0 = self.start_of_hold() if self.start is None else self.start
        best = (np.inf, None, None)
        for s in range(starts):
            x = x0 if s == 0 else x0 * (1 + 0.3 * rng.normal(size=x0.shape)) + 0.1 * self.H * rng.normal(size=x0.shape)
            res = minimize(lambda v: self.inner(v, no_injection)[0] / self.H ** 2, x, method="Nelder-Mead",
                           options=dict(xatol=1e-7, fatol=1e-9, maxiter=250 * len(x0)))
            val, X = self.inner(res.x, no_injection)
            if val < best[0]:
                best = (val, X, res.x)
        if not no_injection and best[2] is not None:
            self.start = best[2]                # the search without injection starts from this scheme
        return best[0], best[1]


def describe(X, U, a):
    """one-step error, energy injected and damping added over a step, in units of alpha_*"""
    D = X @ np.linalg.inv(U)
    s = np.linalg.svd(D, compute_uv=False)
    return dict(alpha=np.linalg.norm(D - np.eye(3), 2) / a, injected=(s[0] - 1) / a, damping=(1 - s[-1]) / a,
                rho=spectral_radius(X), positive=bool((np.diag(X) > 0).all()))


if __name__ == "__main__":
    A, h = chain3(), 0.1
    U = expm(h * A)
    a = alpha_star(A, [1, 1, 1], h)[0]
    least, noinj = {}, {}
    for key, order in ORDERS:
        P = Problem(A, h, order)
        least[key] = describe(P.best()[1], U, a)
        noinj[key] = describe(P.best(no_injection=True)[1], U, a)

    head('Example "the chain of three, by order of execution": smallest one-step error, in units of alpha_*')
    show("alpha_* at h = 0.1", "0.0050", a)
    show("Jacobi scheme (global optimum)", "1.000", least["jacobi"]["alpha"])
    show("middle store first (local search)", "0.993", least["middle"]["alpha"])
    show("from end to end (local search)", "1.000", least["end"]["alpha"])
    print("  among the schemes that inject no energy over a step, s_+ <= 1:")
    show("Jacobi scheme (global optimum)", "1.759", noinj["jacobi"]["alpha"])
    show("middle store first (local search)", "1.963", noinj["middle"]["alpha"])
    show("from end to end (local search)", "1.000", noinj["end"]["alpha"])
    show("avoiding injection costs the factor: Jacobi scheme", "1.8", noinj["jacobi"]["alpha"] / least["jacobi"]["alpha"])
    show("avoiding injection costs the factor: middle store first", "2.0",
         noinj["middle"]["alpha"] / least["middle"]["alpha"])
    check("all six schemes are stable and have F_i > 0",
          all(d["rho"] < 1 and d["positive"] for d in list(least.values()) + list(noinj.values())),
          "spectral radii " + ", ".join(f"{d['rho']:.4f}" for d in list(least.values()) + list(noinj.values())))

    head("Figure of the trade: the marks (energy injected, damping added), in units of alpha_*")
    show("circle, Jacobi scheme: injected", "0.995", least["jacobi"]["injected"])
    show("circle, Jacobi scheme: added damping", "1.000", least["jacobi"]["damping"])
    show("circle, middle store first: injected", "0.993", least["middle"]["injected"])
    show("circle, middle store first: added damping", "0.989", least["middle"]["damping"])
    show("square, Jacobi scheme: injected", "0.000", noinj["jacobi"]["injected"])
    show("square, Jacobi scheme: added damping", "1.759", noinj["jacobi"]["damping"])
    show("square, middle store first: injected", "0.000", noinj["middle"]["injected"])
    show("square, middle store first: added damping", "1.963", noinj["middle"]["damping"])
    print("  distance of the squares from the dashed line, injection plus added damping = 2 alpha_*, in per cent:")
    show("Jacobi scheme", "12", 100 * (2 - noinj["jacobi"]["injected"] - noinj["jacobi"]["damping"]) / 2)
    show("middle store first", "2", 100 * (2 - noinj["middle"]["injected"] - noinj["middle"]["damping"]) / 2)
    print("  from end to end the minimiser is not unique (the search returns the scheme with injected = "
          f"{least['end']['injected']:+.4f},")
    print(f"  added damping = {least['end']['damping']:+.4f}); the mark of the figure is the energy-conserving sweep, "
          "see order_of_execution.py")

    head('Example "the chain of three stores" and the circles of the figure of the bound: the Jacobi scheme '
         "with the smallest one-step error")
    print("  The minimiser of the convex programme is not unique, and the one that the solver returns need not be")
    print("  stable. Where it is not, a second convex programme selects, among the Jacobi schemes with")
    print("  alpha <= (1 + 1e-5) alpha_*, the one with the least trace of X.")
    for hh, circle in ((0.1, "0.0050"), (0.2, "0.0200"), (0.3, "0.0447"), (0.5, "0.1214")):
        P = Problem(A, hh, None)
        a_h = alpha_star(A, [1, 1, 1], hh)[0]
        al, X = P.best()
        how = "minimiser returned"
        if spectral_radius(X) >= 1:
            al, X = P.least_trace((1 + 1e-5) * a_h)
            how = "least trace"
        show(f"h = {hh}: smallest alpha of a stable scheme (circle of the figure)", circle, al)
        check(f"h = {hh}: the scheme is stable and has F_i > 0 ({how})",
              spectral_radius(X) < 1 and (np.diag(X) > 0).all(),
              f"alpha/alpha_* - 1 = {al / a_h - 1:.1e}, spectral radius {spectral_radius(X):.4f}")
        if hh == 0.1:
            check("h = 0.1: within a relative 1e-5 of the bound alpha_*", abs(al / a_h - 1) < 1e-5, f"{al / a_h - 1:.1e}")
    summary()
