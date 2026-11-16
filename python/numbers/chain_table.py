"""Common schemes on the chain of three stores at h = 0.1.

Paper: every entry of the table "Schemes on the chain of three stores", the running text of the section
"Common schemes on the chain of three", the numbers of the example "the chain of three stores" that concern
the zero-order holds, the Jacobi scheme with the spectrum of the monolithic system (end of the section
"Convergence over a run"), and the order of the scheme with the derivative of the partner output (section
"Where the reaction can be taken from").

The chain: A = [[-r, -w, 0], [w, 0, -w], [0, w, -r]], r = 0.1 w, w = 1, h = w H.
Columns of the table: one-step error alpha and energy injected over a step s_+ - 1, both in units of the bound
alpha_*; shift of the decay rate of the oscillatory and of the non-oscillatory mode, in units of H w^2
(positive: the co-simulation is damped more than the monolithic system); error over the run,
max_k ||X^k - U^k|| for k H <= 50/w.
Rows: the zero-order hold with partner weights only; the zero-order hold with the gains K_i of the reaction,
realised as local gains; linear extrapolation of two held samples (X is the map of its underlying one-step
method); the first-order input with the derivative of the partner output. The last two in a Jacobi scheme.
Run:  uv run --no-project --with numpy --with scipy python chain_table.py
"""
import numpy as np
from scipy.linalg import expm

from cosim import (alpha_star, chain3, check, decay_shifts, first_above_one, head, hold, one_step, reaction_gains,
                   run_error, show, spectral_radius, summary)

A, S, h = chain3(), [1, 1, 1], 0.1
U = expm(h * A)
a_star = alpha_star(A, S, h)[0]
ORDERS = (("Jacobi", (0, 0, 0)), ("end to end", (0, 1, 2)), ("middle store first", (1, 0, 1)))
STEPS = int(round(50.0 / h))


def phi1(z):
    """(exp(z) - 1)/z"""
    return np.where(np.abs(z) > 1e-8, np.expm1(z) / np.where(np.abs(z) > 1e-8, z, 1.0), 1.0)


def phi2(z):
    """(exp(z) - 1 - z)/z^2"""
    return np.where(np.abs(z) > 1e-8, (phi1(z) - 1.0) / np.where(np.abs(z) > 1e-8, z, 1.0), 0.5)


def with_gains(stage, hh=h):
    return hold(A, S, stage, hh, reaction_gains(A, S, stage, hh))


def derivative_scheme(hh=h):
    """Jacobi scheme with the input u_i(t) = sum_k L_ik (y_k + (t - t_k) y_k'), where y_k' is the rate of the
    partner output in the monolithic system at t_k"""
    a = np.diag(A)
    Ac = A - np.diag(a)
    return np.diag(np.exp(hh * a)) + hh * phi1(hh * a)[:, None] * Ac + hh * hh * phi2(hh * a)[:, None] * (Ac @ A)


def linear_extrapolation(hh=h):
    """Jacobi scheme with two held samples: every store integrates itself exactly on the straight line through
    the samples of t_k and t_(k-1). Returns the coefficients (M0, M1) of x^(k+1) = M0 x^k + M1 x^(k-1) and the
    map X of the underlying one-step method: X^2 = M0 X + M1, with the three principal eigenvalues."""
    a = np.diag(A)
    Ac = A - np.diag(a)
    p1, p2 = hh * phi1(hh * a), hh * hh * phi2(hh * a)       # int_0^H exp((H - s) a) ds, the same with the factor s
    M0 = np.diag(np.exp(hh * a)) + (p1 + p2 / hh)[:, None] * Ac
    M1 = -(p2 / hh)[:, None] * Ac
    w, V = np.linalg.eig(np.block([[M0, M1], [np.eye(3), np.zeros((3, 3))]]))
    k = np.argsort(-np.abs(w))[:3]                           # the other three eigenvalues are parasitic
    W = V[:3, k]
    X = (W @ np.diag(w[k]) @ np.linalg.inv(W)).real
    return M0, M1, X, np.sort(np.abs(w))[:3]


def row(name, X, paper):
    """paper: the entries of the row as printed (alpha, s_+ - 1, shift oscillatory, shift non-oscillatory, run)"""
    p = one_step(X, U)
    shifts = decay_shifts(A, X, h)
    osc = [s for l, s in shifts if l.imag > 1e-9][0] / h
    non = [s for l, s in shifts if abs(l.imag) <= 1e-9][0] / h
    print(f"  {name}")
    show("    one-step error, alpha/alpha_*", paper[0], p["alpha"] / a_star)
    show("    energy injected, (s_+ - 1)/alpha_*", paper[1], (p["s_plus"] - 1) / a_star)
    if paper[2] is None:
        big = max((osc, non), key=abs)
        show("    largest shift of a decay rate", paper[3], big)
    else:
        show("    shift of the decay rate, oscillatory mode", paper[2], osc, digits=3)
        show("    shift of the decay rate, non-oscillatory mode", paper[3], non, digits=3)
    show("    error over the run", paper[4], run_error(X, U, STEPS))
    return p, osc, non


head('Example "the chain of three stores"')
show("[A^2]_13 in units of w^2", "1", (A @ A)[0, 2], digits=6)
show("alpha_* at h = 0.1", "0.0050", a_star)
show("alpha_* in units of h^2/2 (leading order)", "1.0", a_star / (0.5 * h * h))
ratios = [one_step(hold(A, S, st, h), U)["alpha"] / a_star for _, st in ORDERS]
print("  one-step error of the zero-order holds (Jacobi, end to end, middle store first), in units of alpha_*: "
      + ", ".join(f"{x:.3f}" for x in ratios))
show("  the smallest of the three", "2.0", min(ratios))
show("  the largest of the three", "2.2", max(ratios))

head('Table "Schemes on the chain of three stores" at h = 0.1 (alpha_* = 0.0050)')
print("zero-order hold, partner weights only")
PAPER = {"Jacobi": ("2.07", "+2.07", "-0.995", "0", "12.2"), "end to end": ("2.00", "+1.00", "0", "0", "0.120"),
         "middle store first": ("2.17", "+2.01", "0", "0", "0.072")}
res = {}
for name, st in ORDERS:
    res[name] = row(name, hold(A, S, st, h), PAPER[name])
print("zero-order hold with the gains K_i")
PAPER = {"Jacobi": ("1.01", "+1.01", "-0.252", "+0.500", "0.254"),
         "end to end": ("1.01", "+0.08", "-0.001", "+0.001", "0.061"),
         "middle store first": ("1.01", "+1.00", "+0.250", "-0.500", "0.250")}
gres = {}
for name, st in ORDERS:
    gres[name] = row(name, with_gains(st), PAPER[name])
print("prediction, Jacobi scheme")
M0, M1, Xl, parasitic = linear_extrapolation()
row("linear extrapolation", Xl, ("0.24", "+0.005", None, "-0.002", "0.092"))
check("    X is the underlying one-step method: X^2 = M0 X + M1", np.allclose(Xl @ Xl, M0 @ Xl + M1, atol=1e-12),
      "moduli of the parasitic eigenvalues " + ", ".join(f"{x:.3f}" for x in parasitic))
xs, worst = [np.eye(3), U], 0.0                              # the recursion itself, from exact starting values
for k in range(2, STEPS + 1):
    xs.append(M0 @ xs[-1] + M1 @ xs[-2])
    worst = max(worst, np.linalg.norm(xs[-1] - np.linalg.matrix_power(U, k), 2))
print(f"      for comparison, the two-step recursion itself, started on the exact values x^0, x^1: error over the run {worst:.4f}")
row("derivative of partner output", derivative_scheme(), ("0.09", "+0.004", "-0.002", "0", "0.036"))

head('Section "Common schemes on the chain of three": the running text')
rate = -max(np.linalg.eigvals(A), key=lambda z: z.imag).real             # decay rate r/2 of the oscillatory mode
show("Jacobi hold: decay rate lost by the oscillatory mode, in units of its decay rate r/2 (\"twice\")", "2.0",
     -res["Jacobi"][1] * h / rate)
check("the sequential holds keep the decay rates of the monolithic system exactly",
      all(abs(v) < 1e-10 for name in ("end to end", "middle store first") for v in res[name][1:]))
check("the Jacobi hold is unstable, the two sequential holds are stable",
      spectral_radius(hold(A, S, (0, 0, 0), h)) > 1 and all(spectral_radius(hold(A, S, st, h)) < 1 for _, st in ORDERS[1:]),
      "spectral radii " + ", ".join(f"{spectral_radius(hold(A, S, st, h)):.5f}" for _, st in ORDERS))
show("gains, Jacobi: part of the lost decay rate that remains (\"a quarter\")", "0.25", gres["Jacobi"][1] / res["Jacobi"][1])
show("gains, Jacobi: unstable for h above (leading order: H w^2 = 2 r)", "0.2",
     first_above_one(lambda x: spectral_radius(with_gains((0, 0, 0), x)), 0.005, 2.5), digits=2)
show("gains, middle store first: unstable for h above", "0.2",
     first_above_one(lambda x: spectral_radius(with_gains((1, 0, 1), x)), 0.005, 2.5), digits=3)
show("hold with partner weights only, middle store first: unstable for h above", "1.415",
     first_above_one(lambda x: spectral_radius(hold(A, S, (1, 0, 1), x)), 0.005, 2.5))
show("gains, Jacobi and middle store first: the scheme injects, in units of alpha_*", "1.0",
     (gres["Jacobi"][0]["s_plus"] - 1) / a_star)
show("gains, Jacobi: a decay rate is shifted by, in units of H w^2", "0.5", gres["Jacobi"][2])
show("gains, end to end: the scheme injects, in units of alpha_*", "0.08", (gres["end to end"][0]["s_plus"] - 1) / a_star)
show("gains, end to end: largest shift of a decay rate, in units of H w^2", "0.001",
     max(abs(gres["end to end"][1]), abs(gres["end to end"][2])))

head('Section "Convergence over a run": a Jacobi scheme with exactly the spectrum of the monolithic system')
# X = [[f1, -g, 0], [g, f2, -g], [0, g, f1]] has the eigenvalue f1 and those of [[f1, -sqrt2 g], [sqrt2 g, f2]]
lam = max(np.linalg.eigvals(A), key=lambda z: z.imag)
f1 = np.exp(-0.1 * h)                                        # exp(-r h), the non-oscillatory mode
f2 = 2 * np.exp(h * lam.real) * np.cos(h * lam.imag) - f1    # trace of the oscillatory pair
g = np.sqrt((np.exp(2 * h * lam.real) - f1 * f2) / 2)        # its determinant
Xs = np.array([[f1, -g, 0.0], [g, f2, -g], [0.0, g, f1]])
check("a Jacobi scheme with F_i > 0 has the eigenvalues of U",
      np.allclose(np.sort_complex(np.linalg.eigvals(Xs)), np.sort_complex(np.linalg.eigvals(U)), atol=1e-13) and f1 > 0 < f2,
      f"F = ({f1:.4f}, {f2:.4f}, {f1:.4f})")
print(f"  its one-step error is {one_step(Xs, U)['alpha'] / a_star:.3f} alpha_*: the error lies in the mode shapes")

head('Section "Where the reaction can be taken from": the derivative of the partner output')
vals = [np.linalg.norm(derivative_scheme(x) - expm(x * A), 2) / x ** 3 for x in (0.1, 0.05, 0.025)]
check("Jacobi scheme with the first-order input: X - U = O(H^3)", max(vals) / min(vals) < 1.05,
      "||X - U|| / h^3 = " + ", ".join(f"{v:.4f}" for v in vals) + " at h = 0.1, 0.05, 0.025")
summary()
