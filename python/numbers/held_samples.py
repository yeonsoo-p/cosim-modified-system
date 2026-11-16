"""More held samples: the constants of the half step, the bound of the end store of a chain, an exact rule.

Paper: section "The half step with more held samples" (the constants gamma, the figure of the lossless chain
of six stores, the exact rule on the lossless chain of three) and the numerical constants in the proof of the
bound over a run (appendix).

  gamma_l^sigma = int_0^1 binom(s + l - 1 - sigma, l) ds:  the mean of a signal over the macro step differs
  from the mean of the polynomial through its l samples by gamma_l^sigma H^l times its l-th derivative
  (sigma = 0: old samples, the explicit Adams methods; sigma = 1: with the new sample, the implicit ones).

  f_1: the largest response of store 1, in one step of the monolithic system, to a state of unit norm that it
  is not shown; with l held samples in a Jacobi scheme the states not shown satisfy v_1 = 0 and
  e_2^T U^(-q) v = 0 for q = 0, ..., l - 1.
Run:  uv run --no-project --with numpy --with scipy python held_samples.py
"""
from fractions import Fraction

import numpy as np
from scipy.linalg import expm, null_space

from cosim import check, head, lossless_chain, show, summary


def gamma(l, sigma):
    """int_0^1 binom(s + l - 1 - sigma, l) ds, exactly"""
    coef = [Fraction(1)]                                  # prod_{q=0}^{l-1} (s - sigma + q), lowest power first
    for q in range(l):
        c = Fraction(q - sigma)
        new = [Fraction(0)] * (len(coef) + 1)
        for k, v in enumerate(coef):
            new[k + 1] += v
            new[k] += v * c
        coef = new
    fact = Fraction(1)
    for q in range(1, l + 1):
        fact *= q
    return sum(v / (k + 1) for k, v in enumerate(coef)) / fact


def f_end(h, l, n=6):
    """the bound f_1 of the end store of a lossless chain of n stores with unit rates, l held samples"""
    U = expm(h * lossless_chain(n))
    Ui = np.linalg.inv(U)
    rows, P = [np.eye(n)[0]], np.eye(n)
    for _ in range(l):
        rows.append(P[1])                                 # e_2^T U^(-q)
        P = P @ Ui
    V = null_space(np.array(rows))
    return np.linalg.norm(U[0] @ V) if V.size else 0.0


head('Section "The half step with more held samples": the constants gamma')
for sigma, paper in ((0, ("1/2", "5/12", "3/8")), (1, ("-1/2", "-1/12", "-1/24"))):
    got = [gamma(l, sigma) for l in (1, 2, 3)]
    check(f"sigma = {sigma}: gamma_1, gamma_2, gamma_3 = " + ", ".join(paper), [str(g) for g in got] == list(paper),
          "computed " + ", ".join(str(g) for g in got) + f"; gamma_4 = {gamma(4, sigma)}")

head("Figure of the lossless chain of six stores: f_1 against gamma_l h^(l+1), Jacobi scheme")
A6 = lossless_chain(6)
for l in (1, 2, 3, 4):
    g = float(gamma(l, 0))
    ratios = [f_end(h, l) / (g * h ** (l + 1)) for h in (0.05, 0.1, 0.3)]
    print(f"  l = {l}: f_1 / (gamma_l h^(l+1)) = " + ", ".join(f"{x:.4f}" for x in ratios) + " at h = 0.05, 0.1, 0.3;"
          f"  |[A^(l+1)]_(1,l+2)| = {abs(np.linalg.matrix_power(A6, l + 1)[0, l + 1]):.0f}")
    check(f"l = {l}: f_1 = gamma_l h^(l+1) to leading order", abs(ratios[0] - 1) < 0.002 and abs(ratios[0] - 1) < abs(ratios[1] - 1))

head("Lossless chain of three, two held samples: the rule of an end store is exact")
A3 = lossless_chain(3)
for h in (0.1, 0.7):
    U = expm(h * A3)
    Ui = np.linalg.inv(U)
    e1, e2 = np.eye(3)[0], np.eye(3)[1]
    shown = np.array([e1, e2, e2 @ Ui])                   # own state, sample of t_k, sample of t_(k-1)
    # rule x_1^(k+1) = F_1 x_1^k + g0 y_2^k + g1 y_2^(k-1) with F_1 = 1: least defect over g0, g1
    g, *_ = np.linalg.lstsq(shown[1:].T, U[0] - e1, rcond=None)
    defect = np.linalg.norm(U[0] - e1 - g @ shown[1:])
    check(f"h = {h}: no state is hidden from store 1 (the three maps are independent)", np.linalg.matrix_rank(shown) == 3)
    check(f"h = {h}: the rule with F_1 = 1 has no defect", defect < 1e-13, f"defect {defect:.1e}")
    show(f"h = {h}: coefficient of the past sample minus tan(h/sqrt 2)/sqrt 2", "0", g[1] - np.tan(h / np.sqrt(2)) / np.sqrt(2),
         digits=12)

head("Appendix, proof of the bound over a run: the numerical constants")
e = np.exp(0.5)
check("exp(1/2) - 1 < 0.65", e - 1 < 0.65, f"{e - 1:.4f}")
check("2 - exp(1/2) > 0.35", 2 - e > 0.35, f"{2 - e:.4f}")
check("1 + exp(1/2) < 2.65", 1 + e < 2.65, f"{1 + e:.4f}")
check("1 + exp(1/2)/4 < 1.42", 1 + e / 4 < 1.42, f"{1 + e / 4:.4f}")
show("the constant of the order barrier, 2 x 2.65", "5.3", 2 * 2.65)
summary()
