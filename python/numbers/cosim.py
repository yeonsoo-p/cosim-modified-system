"""Shared functions of the scripts that recompute the numbers of the paper.

A network is a matrix A (the monolithic system x' = A x) with a partition of its states into subsystems,
given by the list `sizes` of their dimensions. A scheme is described by its one-step map X; the monolithic
system advances by U = exp(H A) over a macro step H. The order of execution is a tuple `stage` with the stage
of every subsystem: subsystem i uses the new sample of a partner k exactly if stage[k] < stage[i].

    hold            one-step map of the zero-order hold (optionally with local gains)
    step_map        the same for a general split of A into an integrated and a held part
    reaction_gains  the gains K_i of the reaction, as the block-diagonal matrix of the B_i K_i B_i^T
    phi, shifted_E  the matrices phi and E of the zero-order hold (the shifted system E x' = A x)
    alpha_star      the bound alpha_* on the one-step error of a Jacobi scheme with one held sample
    one_step        one-step error, extreme singular values and H nu of the relative one-step map
    modified        the modified system, (1/H) Log X
    decay_shifts    shifts of the decay rates of the modes
    run_error       max_k ||X^k - U^k|| over a run
    show, summary   print a computed value beside the value printed in the paper
"""
import numpy as np
from scipy.linalg import expm, logm, null_space


# ------------------------------------------------------------------------------ networks of the paper
def chain3(r=0.1, w=1.0):
    """the chain of three stores: two masses joined by a spring; momenta and elongation as states"""
    return np.array([[-r, -w, 0.0], [w, 0.0, -w], [0.0, w, -r]])


def lossless_chain(n, w=1.0):
    """lossless chain of n scalar stores with the rate w on every link"""
    A = np.zeros((n, n))
    for k in range(n - 1):
        A[k, k + 1], A[k + 1, k] = -w, w
    return A


def two_mass_velocity_force():
    """two unit masses, attached to the ground and joined by unit springs, in energy coordinates:
    (x1, v1, e | x2, v2) with the elongation e = x2 - x1 of the joining spring in subsystem 1.
    Subsystem 1 shows the force of the joining spring (the state e), subsystem 2 its velocity v2."""
    A = np.array([[0, 1, 0, 0, 0], [-1, 0, 1, 0, 0], [0, -1, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, -1, -1, 0]], float)
    return A, [3, 2]


# ------------------------------------------------------------------------------ schemes
def owners(sizes):
    """index of the subsystem of every state"""
    return np.repeat(np.arange(len(sizes)), sizes)


def signs(sizes, stage):
    """varsigma for every pair of states: +1 if the subsystem of the column runs at an earlier stage"""
    st = np.asarray(stage)[owners(sizes)]
    return np.where(st[None, :] < st[:, None], 1.0, -1.0)


def step_map(A_live, A_held, sizes, stage, H):
    """One-step map of the scheme in which every subsystem integrates x' = A_live x exactly over the macro
    step, driven by A_held x with x held at a sample: the new sample where the entry of A_held couples two
    subsystems and the source runs at an earlier stage, the old sample otherwise.
    X = (I - N)^(-1) (F + M) with N on the new and M on the old samples."""
    n = len(A_live)
    ow = owners(sizes)
    Z = np.zeros((2 * n, 2 * n))
    Z[:n, :n] = A_live
    Z[:n, n:] = np.eye(n)
    Ex = expm(H * Z)
    F, Phi = Ex[:n, :n], Ex[:n, n:]                 # exp(H A_live) and its integral over the step
    GC = Phi @ A_held
    st = np.asarray(stage)[ow]
    newer = (ow[:, None] != ow[None, :]) & (st[None, :] < st[:, None])
    N = np.where(newer, GC, 0.0)
    return np.linalg.solve(np.eye(n) - N, F + GC - N)


def hold(A, sizes, stage, H, gain=None):
    """Zero-order hold: every subsystem integrates itself exactly on the held samples of its partners.
    gain: a block-diagonal matrix added to the subsystems (local gains), or None."""
    ow = owners(sizes)
    same = ow[:, None] == ow[None, :]
    live = np.where(same, A, 0.0) + (0.0 if gain is None else gain)
    return step_map(live, np.where(same, 0.0, A), sizes, stage, H)


def reaction_gains(A, sizes, stage, H):
    """B_i K_i B_i^T = (H/2) sum_k varsigma_ik A_ki^T A_ki as a block-diagonal matrix (power-conjugate ports)"""
    n = len(A)
    idx = np.concatenate([[0], np.cumsum(sizes)])
    K = np.zeros((n, n))
    for i in range(len(sizes)):
        for k in range(len(sizes)):
            Aki = A[idx[k]:idx[k + 1], idx[i]:idx[i + 1]]
            if k != i and np.any(Aki):
                sig = 1.0 if stage[k] < stage[i] else -1.0
                K[idx[i]:idx[i + 1], idx[i]:idx[i + 1]] += 0.5 * H * sig * Aki.T @ Aki
    return K


def phi(A, sizes, H):
    """phi = diag(phi_i), phi_i = int_0^1 exp(s H A_i) ds"""
    n = len(A)
    ow = owners(sizes)
    Z = np.zeros((2 * n, 2 * n))
    Z[:n, :n] = H * np.where(ow[:, None] == ow[None, :], A, 0.0)
    Z[:n, n:] = np.eye(n)
    return expm(Z)[:n, n:]


def shifted_E(A, sizes, stage, H):
    """E = Psi_0 - (H/2) A_varsigma of the zero-order hold, Psi_0 = phi^(-1) + (H/2) A_d: the co-simulation is
    the implicit midpoint rule for the shifted system E x' = A x"""
    ow = owners(sizes)
    same = ow[:, None] == ow[None, :]
    return (np.linalg.inv(phi(A, sizes, H)) + 0.5 * H * np.where(same, A, 0.0)
            - 0.5 * H * np.where(same, 0.0, signs(sizes, stage) * A))


# ------------------------------------------------------------------------------ quantities
def alpha_star(A, sizes, H):
    """The bound alpha_* on the one-step error of a Jacobi scheme with one held sample: the largest, over
    the subsystems i, of max |Pi_i U v| / |U v| over the states v that subsystem i is not shown (Pi_i v = 0
    and C_j v = 0 for its partners j). The output of a partner j is read from the block A_ij: the states of
    j on which the block acts. Returns the largest value and the list of the values per subsystem."""
    n = len(A)
    idx = np.concatenate([[0], np.cumsum(sizes)])
    U = expm(H * A)
    out = []
    for i in range(len(sizes)):
        rows = [np.eye(n)[idx[i]:idx[i + 1]]]
        for j in range(len(sizes)):
            blk = A[idx[i]:idx[i + 1], idx[j]:idx[j + 1]]
            if j != i and np.any(blk):
                _, s, Vt = np.linalg.svd(blk)
                C = np.zeros((int(np.sum(s > 1e-12)), n))
                C[:, idx[j]:idx[j + 1]] = Vt[:C.shape[0]]
                rows.append(C)
        V = null_space(np.vstack(rows))
        if V.shape[1] == 0:
            out.append(0.0)
            continue
        M, Nm = U[idx[i]:idx[i + 1]] @ V, U @ V
        out.append(float(np.sqrt(max(np.linalg.eigvals(np.linalg.solve(Nm.T @ Nm, M.T @ M)).real))))
    return max(out), out


def one_step(X, U):
    """quantities of the relative one-step map X U^(-1)"""
    D = X @ np.linalg.inv(U)
    s = np.linalg.svd(D, compute_uv=False)
    return dict(alpha=np.linalg.norm(D - np.eye(len(U)), 2), s_plus=s[0], s_minus=s[-1],
                H_nu=-np.log(abs(np.linalg.det(D))))


def modified(X, H):
    """the modified system (1/H) Log X"""
    return logm(X).real / H


def spectral_radius(X):
    return float(max(abs(np.linalg.eigvals(X))))


def decay_shifts(A, X, H):
    """For every mode of A with nonnegative imaginary part: (eigenvalue of A, shift of its decay rate), where
    the shift is positive if the co-simulation is damped more than the monolithic system."""
    lam, mu = np.linalg.eigvals(A), list(np.linalg.eigvals(modified(X, H)))
    out = []
    for l in sorted(lam, key=lambda z: -z.imag):
        m = min(mu, key=lambda z: abs(z - l))
        mu.remove(m)
        if l.imag > -1e-9:
            out.append((l, -(m.real - l.real)))
    return out


def run_error(X, U, steps):
    """max_k ||X^k - U^k|| for 1 <= k <= steps"""
    P, V, worst = np.eye(len(U)), np.eye(len(U)), 0.0
    for _ in range(steps):
        P, V = X @ P, U @ V
        worst = max(worst, np.linalg.norm(P - V, 2))
    return worst


def first_above_one(rho, lo, hi, samples=2000, tol=1e-12):
    """smallest macro step in [lo, hi] at which the function rho exceeds 1 (scan, then bisection)"""
    hs = np.linspace(lo, hi, samples)
    prev = hs[0]
    for h in hs:
        if rho(h) > 1 + tol:
            a, b = prev, h
            for _ in range(60):
                mid = 0.5 * (a + b)
                a, b = (a, mid) if rho(mid) > 1 + tol else (mid, b)
            return b
        prev = h
    return None


# ------------------------------------------------------------------------------ output
_CHECKS = []


def head(text):
    print("\n" + text)
    print("-" * len(text))


def show(text, paper, value, digits=None):
    """Print a computed value beside the value printed in the paper and compare the two after rounding to
    the digits printed there (digits: number of decimals; read from the string `paper` if not given)."""
    if digits is None:
        digits = len(paper.split(".")[1]) if "." in paper else 0
    ok = abs(round(float(value), digits) - float(paper)) < 0.5 * 10.0 ** (-digits) * 1e-6 + 1e-12
    _CHECKS.append((text, ok))
    more = max(digits + 2, 4)
    print(f"  {text:<66s} paper {paper:>8s}   computed {value:+.{more}f}   {'agrees' if ok else 'DIFFERS'}")
    return ok


def check(text, ok, detail=""):
    """print a statement that is either true or false"""
    _CHECKS.append((text, bool(ok)))
    print(f"  {text:<66s} {'holds' if ok else 'FAILS'}" + (f"   ({detail})" if detail else ""))
    return ok


def summary():
    bad = [t for t, ok in _CHECKS if not ok]
    print()
    if bad:
        print(f"{len(bad)} of {len(_CHECKS)} comparisons differ from the paper:")
        for t in bad:
            print("   " + t)
    else:
        print(f"All {len(_CHECKS)} comparisons agree with the paper to the digits printed there.")
