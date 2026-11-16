"""The two-mass oscillator in four choices of port.

Paper: example "one oscillator, four choices of port" (all its numbers), the growth rates printed in the figure
of the four choices of port, and the value f_1 = 0.50 H^2 quoted in the example "the chain of three stores".

Two unit masses are attached to the ground by unit springs and joined by a unit spring; the in-phase mode has
the frequency 1 and the out-of-phase mode the frequency sqrt 3. The four partitions:
  (a) velocity and force:      subsystem 1 holds the joining spring; power-conjugate ports, energy coordinates
                               (x1, v1, e | x2, v2) with the elongation e of the joining spring;
  (b) two displacements:       each subsystem holds a copy of the joining spring, whose far end follows the
                               held displacement of the other mass; states (x1, v1 | x2, v2);
  (c) force and displacement:  subsystem 2 holds the joining spring; the force that subsystem 1 is given
                               contains the old sample of its own displacement;
  (d) two forces:              a master holds the joining spring; both forces contain the receiver's old
                               displacement.
In every partition each subsystem integrates itself exactly on the held samples (zero-order hold).
Run:  uv run --no-project --with numpy --with scipy python two_mass_ports.py
"""
from fractions import Fraction

import numpy as np
from scipy.linalg import eig, expm

from cosim import (alpha_star, check, head, hold, one_step, owners, reaction_gains, show, spectral_radius, step_map,
                   summary, two_mass_velocity_force)

# ------------------------------------------------------------------ the four partitions
APC, SIZES_PC = two_mass_velocity_force()
HELD_PC = np.zeros((5, 5))
HELD_PC[2, 4], HELD_PC[4, 2] = 1.0, -1.0                 # e' contains v2; v2' contains the force -e
A4 = np.array([[0, 1, 0, 0], [-2, 0, 1, 0], [0, 0, 0, 1], [1, 0, -2, 0]], float)      # (x1, v1 | x2, v2)
HELD_DD = np.zeros((4, 4))
HELD_DD[1, 2], HELD_DD[3, 0] = 1.0, 1.0                  # each mass is pulled by the held displacement of the other
HELD_FD = HELD_DD.copy()
HELD_FD[1, 0] = -1.0                                     # the force on mass 1 contains its own old displacement
HELD_FF = HELD_FD.copy()
HELD_FF[3, 2] = -1.0                                     # and so does the force on mass 2
PARTITIONS = (("(a) velocity and force", APC, HELD_PC, SIZES_PC), ("(b) two displacements", A4, HELD_DD, [2, 2]),
              ("(c) force and displacement", A4, HELD_FD, [2, 2]), ("(d) two forces", A4, HELD_FF, [2, 2]))
ORDERS = (("Jacobi", (0, 0)), ("1 then 2", (0, 1)), ("2 then 1", (1, 0)))
# rates of the in-phase and of the out-of-phase mode, divided by H, as printed in the figure: Jacobi, sequential
FIGURE = {"(a) velocity and force": (("0", "1/2"), ("0", "0")), "(b) two displacements": (("-1/4", "1/4"), ("0", "0")),
          "(c) force and displacement": (("-1/8", "3/8"), ("1/8", "1/8")), "(d) two forces": (("0", "1/2"), ("1/4", "1/4"))}


def modes(A):
    """the modes with positive frequency, in-phase first: (eigenvalue, right and left eigenvector)"""
    lam, VL, VR = eig(A, left=True, right=True)
    return sorted(((lam[m], VR[:, m], VL[:, m]) for m in range(len(lam)) if lam[m].imag > 1e-9), key=lambda t: t[0].imag)


def leading_rates(A, held, sizes, stage):
    """growth of a mode to leading order: Re(lambda~ - lambda)/H = Re((1/2) lambda w* A_s v / w* v), where A_s is
    the held part with every entry signed +1 for a new sample and -1 for an old one"""
    ow = owners(sizes)
    st = np.asarray(stage)[ow]
    new = (ow[:, None] != ow[None, :]) & (st[None, :] < st[:, None])
    As = np.where(new, 1.0, -1.0) * held
    return [float((0.5 * lam * (w.conj() @ As @ v) / (w.conj() @ v)).real) for lam, v, w in modes(A)]


def actual_rates(A, X, H, steps=1):
    """Re(lambda~ - lambda)/H from the eigenvalues of the map X over `steps` macro steps"""
    mu = np.log(np.linalg.eigvals(X).astype(complex)) / (steps * H)
    return [float((mu[np.argmin(abs(mu - lam))] - lam).real / H) for lam, _, _ in modes(A)]


# ------------------------------------------------------------------ the figure
head("Figure of the four choices of port: growth of the in-phase and of the out-of-phase mode, divided by H")
H = 0.05
worst = 0.0
for name, A, held, sizes in PARTITIONS:
    print(f"  {name}")
    for oname, stage in ORDERS:
        paper = FIGURE[name][0 if oname == "Jacobi" else 1]
        lead = leading_rates(A, held, sizes, stage)
        act = actual_rates(A, step_map(A - held, held, sizes, stage, H), H)
        for mode, p, l, a in zip(("in-phase", "out-of-phase"), paper, lead, act):
            check(f"    {oname:9s} {mode:13s} leading order {p:>5s}", abs(l - float(Fraction(p))) < 1e-12,
                  f"computed {l:+.6f}; from the eigenvalues of X at H = 0.05: {a:+.5f}")
            if float(Fraction(p)) != 0:
                worst = max(worst, abs(a / float(Fraction(p)) - 1))
            else:
                check(f"    {oname:9s} {mode:13s} no growth at H = 0.05", abs(a) < 1e-4, f"{a:+.1e}")
check("the eigenvalues of X at H = 0.05 give the nonzero values to within 0.3 per cent", 100 * worst < 0.3,
      f"largest deviation {100 * worst:.2f} per cent")

# ------------------------------------------------------------------ the example: velocity and force
head('Example "one oscillator, four choices of port": velocity and force at the port, H = 0.1')
H = 0.1
U = expm(H * APC)
a_star, per_sub = alpha_star(APC, SIZES_PC, H)
lam = sorted(abs(np.linalg.eigvals(APC).imag))
show("frequency of the out-of-phase mode, squared", "3", lam[-1] ** 2, digits=8)
show("alpha_* (in units of 1e-3)", "4.99", 1e3 * a_star)
print("    (the bounds of the two subsystems: " + ", ".join(f"{1e3 * v:.4f}e-3" for v in per_sub) + ")")
show("alpha_* in units of H^2/2", "1.0", a_star / (0.5 * H * H))
blocks = lambda X: (np.linalg.norm((X - U)[:3, :3], 2) / a_star, np.linalg.norm((X - U)[3:, 3:], 2) / a_star)
res = {}
for oname, stage in ORDERS:
    X0 = hold(APC, SIZES_PC, stage, H)
    X1 = hold(APC, SIZES_PC, stage, H, reaction_gains(APC, SIZES_PC, stage, H))
    res[oname] = (one_step(X0, U), one_step(X1, U), blocks(X0), blocks(X1), spectral_radius(X0), spectral_radius(X1))
print("  partner weights only")
for oname, _ in ORDERS:
    for i in (0, 1):
        show(f"    {oname}: diagonal block {i + 1} of X - U, in units of alpha_*", "1.00", res[oname][2][i])
show("    Jacobi: total numerical damping H nu, in units of H^2", "-1", res["Jacobi"][0]["H_nu"] / H ** 2, digits=1)
for oname in ("1 then 2", "2 then 1"):
    check(f"    {oname}: the total damping is exact, nu = 0", abs(res[oname][0]["H_nu"]) < 1e-13)
print("  with the gains K_i (-H/2 for a partner that has not yet run, +H/2 for one that has), as local gains")
show("    Jacobi: diagonal blocks of X - U, in units of alpha_*", "0.02", max(res["Jacobi"][3]))
show("    Jacobi: total numerical damping H nu, in units of H^2 (restored)", "0", res["Jacobi"][1]["H_nu"] / H ** 2, digits=1)
show("    Jacobi: one-step error without the gains, in units of alpha_*", "1.42", res["Jacobi"][0]["alpha"] / a_star)
show("    Jacobi: one-step error with the gains (the bound)", "1.00", res["Jacobi"][1]["alpha"] / a_star)
for oname in ("1 then 2", "2 then 1"):
    show(f"    {oname}: one-step error without the gains", "1.45", res[oname][0]["alpha"] / a_star)
    show(f"    {oname}: one-step error with the gains", "1.04", res[oname][1]["alpha"] / a_star)
print("  spectral radius")
show("    Jacobi, zero-order hold", "1.005", res["Jacobi"][4])
show("    Jacobi, with the gains", "1.002", res["Jacobi"][5])
for oname in ("1 then 2", "2 then 1"):
    show(f"    {oname}, zero-order hold", "1", res[oname][4], digits=10)
rho = sorted(res[o][5] for o in ("1 then 2", "2 then 1"))
show("    sequential orders with the gains, the smaller", "1.001", rho[0])
show("    sequential orders with the gains, the larger", "1.002", rho[1])

# ------------------------------------------------------------------ the example: the other partitions
head('Example "one oscillator, four choices of port": the partitions with a displacement or a force at the port')
lead = {name: [leading_rates(A, held, sizes, st) for _, st in ORDERS] for name, A, held, sizes in PARTITIONS}
b, c, d = (lead[k] for k in ("(b) two displacements", "(c) force and displacement", "(d) two forces"))
check("each subsystem that receives a held force adds 1/8 to both rates",
      all(abs(c[o][m] - b[o][m] - 0.125) < 1e-12 and abs(d[o][m] - c[o][m] - 0.125) < 1e-12 for o in range(3) for m in range(2)))
check("two displacements, Jacobi: the two rates sum to zero", abs(sum(b[0])) < 1e-12)
check("Jacobi schemes: two displacements have the smallest growth rate",
      max(b[0]) < min(max(lead[k][0]) for k in lead if not k.startswith("(b)")),
      "largest rates " + ", ".join(f"{max(lead[k][0]):.3f}" for k in lead))
Q = np.array([[2, 0, -1, 0], [0, 1, 0, 0], [-1, 0, 2, 0], [0, 0, 0, 1]], float)       # energy of the whole oscillator
for oname, stage in ORDERS[1:]:
    X = step_map(A4 - HELD_DD, HELD_DD, [2, 2], stage, 0.1)
    check(f"two displacements, {oname}: the energy of the oscillator is conserved exactly",
          np.allclose(X.T @ Q @ X, Q, atol=1e-13))
print("  reversing the order in every second macro step (rates per step from the map of two steps, H = 0.05):")
H = 0.05
for name, A, held, sizes in PARTITIONS:
    X2 = step_map(A - held, held, sizes, (1, 0), H) @ step_map(A - held, held, sizes, (0, 1), H)
    act = actual_rates(A, X2, H, steps=2)
    grows = name[:3] in ("(c)", "(d)")
    check(f"    {name}: a mode {'still grows' if grows else 'does not grow'}", (max(act) > 0.1) == grows,
          "rates " + ", ".join(f"{a:+.4f}" for a in act))

# ------------------------------------------------------------------ the value quoted in the example of the chain
head('Example "the chain of three stores": force and displacement at the port')
print("  subsystem 1 (x1, v1) is shown the force, that is, the displacement x2, and not the velocity v2")
for H in (0.1, 0.05):
    f1 = np.linalg.norm(expm(H * A4)[:2, 3])             # response of subsystem 1 to a unit velocity v2
    show(f"  f_1 / H^2 at H = {H}", "0.50", f1 / H ** 2)
summary()
