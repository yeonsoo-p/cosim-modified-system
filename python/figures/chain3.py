"""The chain of three stores of the paper (two masses joined by a spring; the two momenta and the spring
elongation as states) for the figure of the two ways of losing stability: the matrix E of the zero-order hold
and the eigenvalues theta of the shifted system E x' = A x, for scalar stores."""
import numpy as np
from scipy.linalg import eig

W, R = 1.0, 0.1                     # coupling rate omega, dissipation rate r = 0.1 omega
A3 = np.array([[-R, -W, 0.0], [W, 0.0, -W], [0.0, W, -R]])
ORDERS = {"jacobi": (0, 0, 0), "end": (0, 1, 2), "middle": (1, 0, 1)}      # stages of stores 1, 2, 3


def split(A):
    """the part within the stores and the coupling"""
    Ad = np.diag(np.diag(A))
    return Ad, A - Ad


def signs(stage):
    """varsigma_ik = +1 if k runs at an earlier stage than i, and -1 otherwise"""
    st = np.asarray(stage)
    return np.where(st[None, :] < st[:, None], 1.0, -1.0)


def Emat(A, stage, H):
    """E = Psi_0 - (H/2) A_varsigma, with Psi_0 = (H A_d / 2) coth(H A_d / 2)"""
    Ad, Ac = split(A)
    x = 0.5 * H * np.diag(Ad)
    psi = np.where(np.abs(x) > 1e-12, x / np.tanh(np.where(np.abs(x) > 1e-12, x, 1.0)), 1.0)
    return np.diag(psi) - 0.5 * H * signs(stage) * Ac


def theta(A, stage, H):
    """eigenvalues of the shifted system E x' = A x"""
    return eig(A, Emat(A, stage, H), right=False)
