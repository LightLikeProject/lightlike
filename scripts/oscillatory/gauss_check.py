"""Numerical check (not a proof) of the Gaussian model integral in
Lightlike/Oscillatory/Gaussian.lean.

For a complex symmetric n x n matrix A with Re A positive definite,
    G(A) = int_{R^n} exp(-<A x, x>/2) dx
satisfies (Lean: integral_gauss_sq_mul_det)
    G(A)^2 det A = (2 pi)^n,
and the induction step (Lean: integral_gauss_succ)
    G(A) = (pi / (A_00 / 2))^(1/2) G(S),   S = Schur complement of A_00.
and, with the branch fixed (Lean: integral_gauss_eq_invSqrtDet),
    G(A) = (2 pi)^(n/2) prod_k lambda_k^(-1/2),
over the eigenvalues lambda_k of A (all with Re > 0), principal roots.

G(A) is computed by the tensor-product trapezoidal rule on [-L, L]^n, which converges
exponentially for Gaussians (aliasing error ~ exp(-Re(1/lambda) (2 pi/h)^2 / 2)), independently of
the Lean proof. Checks, on six instances (n = 1, 2, 3, real and complex, diagonal and not):
 1. Re A is positive definite and A is symmetric (sanity of the instance);
 2. |G^2 det A / (2 pi)^n - 1| < 1e-9;
 3. the recursion of integral_gauss_succ, with S computed from A, matches to 1e-9;
 4. G matches (2 pi)^(n/2) prod lambda_k^(-1/2) to 1e-9.
Controls, which must FAIL:
 (a) wrong input: B = A + K with K real antisymmetric has the same quadratic form, so
     G(B) = G(A), but G(B)^2 det B != (2 pi)^n (the symmetry hypothesis is needed);
 (b) wrong branch: (2 pi)^(n/2) (det A)^(-1/2) with the principal root of det A. On the n = 3
     instance whose eigenvalue arguments sum to more than pi it has the wrong sign, so the
     branch is the eigenvalue product, not the principal root of the determinant (Lean:
     cpow_det_diagonal_wrong_branch, for A = (1 + 2i) I_3).
The script exits with code 0 only if every check passes and both controls fail.

Usage: .venv/bin/python -I scripts/oscillatory/gauss_check.py
"""
import sys

import numpy as np

TOL = 1e-9


def rotation3(a, b, c):
    """A real orthogonal 3 x 3 matrix from three angles."""
    ca, sa, cb, sb, cc, sc = np.cos(a), np.sin(a), np.cos(b), np.sin(b), np.cos(c), np.sin(c)
    rz = np.array([[ca, -sa, 0], [sa, ca, 0], [0, 0, 1]])
    ry = np.array([[cb, 0, sb], [0, 1, 0], [-sb, 0, cb]])
    rx = np.array([[1, 0, 0], [0, cc, -sc], [0, sc, cc]])
    return rz @ ry @ rx


def instances():
    """(name, A, K) with A complex symmetric and K real antisymmetric (control (a))."""
    yield "n = 1, A = 1", np.array([[1.0 + 0j]]), None
    yield "n = 1, A = 2 - 3i", np.array([[2 - 3j]]), None
    yield ("n = 2, A = [[1, i], [i, 2]], det 3", np.array([[1, 1j], [1j, 2]]),
           np.array([[0, 1.0], [-1.0, 0]]))
    q2 = np.array([[np.cos(0.7), -np.sin(0.7)], [np.sin(0.7), np.cos(0.7)]])
    yield ("n = 2, A = Q diag(1 + i, 2 - 2i) Q^T", q2 @ np.diag([1 + 1j, 2 - 2j]) @ q2.T,
           np.array([[0, 0.5], [-0.5, 0]]))
    q3 = rotation3(0.4, -0.9, 1.3)
    yield ("n = 3, A = Q diag(1 + 2i, 1 + 2.5i, 1 + 3i) Q^T (arguments sum to 3.55 > pi)",
           q3 @ np.diag([1 + 2j, 1 + 2.5j, 1 + 3j]) @ q3.T,
           np.array([[0, 1.0, -0.5], [-1.0, 0, 2.0], [0.5, -2.0, 0]]))
    q3b = rotation3(-1.1, 0.3, 0.8)
    yield ("n = 3, A = Q diag(1, 2 - i, 0.5 + 0.2i) Q^T + 0.1 i (all ones)",
           q3b @ np.diag([1, 2 - 1j, 0.5 + 0.2j]) @ q3b.T + 0.1j * np.ones((3, 3)), None)


def gauss_integral(A, L=10.0, h=0.125):
    """Tensor-product trapezoidal rule for int exp(-<A x, x>/2) over [-L, L]^n."""
    n = A.shape[0]
    t = np.arange(-L, L + h / 2, h)
    grids = np.meshgrid(*([t] * n), indexing="ij")
    X = np.stack([g.ravel() for g in grids], axis=1)
    q = np.einsum("ki,ij,kj->k", X, A, X)
    return np.sum(np.exp(-q / 2)) * h**n


def schur0(A):
    return A[1:, 1:] - np.outer(A[1:, 0], A[0, 1:]) / A[0, 0]


def recursion(A):
    """G(A) from the recursion of integral_gauss_succ, with G(empty) = 1."""
    if A.shape[0] == 0:
        return 1.0 + 0j
    return np.sqrt(np.pi / (A[0, 0] / 2)) * recursion(schur0(A))


def main():
    ok = True
    for name, A, K in instances():
        n = A.shape[0]
        sym = np.allclose(A, A.T)
        repd = bool(np.all(np.linalg.eigvalsh((A.real + A.real.T) / 2) > 0))
        G = gauss_integral(A)
        lam = np.linalg.eigvals(A)
        sq = abs(G**2 * np.linalg.det(A) / (2 * np.pi) ** n - 1)
        rec = abs(recursion(A) / G - 1)
        eig = (2 * np.pi) ** (n / 2) * np.prod(lam ** -0.5)
        eig_err = abs(eig / G - 1)
        print(f"{name}\n  symmetric: {sym}; Re A positive definite: {repd}")
        print(f"  G = {G:.12g}")
        print(f"  |G^2 det A / (2 pi)^n - 1| = {sq:.2e}; recursion: {rec:.2e};"
              f" eigenvalue branch: {eig_err:.2e}")
        good = sym and repd and sq < TOL and rec < TOL and eig_err < TOL
        if K is not None:
            B = A + K
            GB = gauss_integral(B)
            same = abs(GB / G - 1) < TOL
            wrong = abs(GB**2 * np.linalg.det(B) / (2 * np.pi) ** n - 1)
            fails_a = same and wrong > 1e-3
            print(f"  control (a), B = A + K antisymmetric: G(B) = G(A): {same};"
                  f" |G(B)^2 det B / (2 pi)^n - 1| = {wrong:.3g}; fails as it must: {fails_a}")
            good = good and fails_a
        if n == 3 and np.sum(np.angle(lam)) > np.pi:
            principal = (2 * np.pi) ** (n / 2) * np.linalg.det(A) ** -0.5
            ratio = principal / G
            fails_b = abs(ratio + 1) < TOL
            print(f"  control (b), principal root of det A: ratio to G = {ratio:.6g};"
                  f" wrong sign as it must be: {fails_b}")
            good = good and fails_b
        ok = ok and good
    print("OK" if ok else "FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
