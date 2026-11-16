"""Numerical certificate (not a proof) that the 6 x 6 node blocks H^{X_a X_a} of the Hessian of the
Lorentzian vertex action are nondegenerate at the critical configurations considered, and a
cross-check of the sign structure of the real part (numpy only, fixed seed).

The block is built from BDFHP (arXiv:0907.2440, Appendix A, eqs. (58)-(61), p. 32-33) in the form
established by `Lightlike/Asymptotics/Lorentzian/HessianNode.lean` (`hessXX_block`), which for the
generators J = i sigma / 2, K = sigma / 2 is 1/4 of (61) at the ends where the node is the source of
the edge and has, at the ends where it is the target, the sign s_e = -1 and the triple-product term
(`scripts/asymptotics/lorentzian_hessian_paper61_check.py` documents the comparison with (61)):
    Q(alpha, beta) = sum_e k_e [ -1/2 (a,a)_e + i s_e (a,b)_e + s_e m_e.(a x b)
                                 - (1/2 + i s_e gamma) (b,b)_e ],   (u,v)_e = u.v - (m_e.u)(m_e.v),
so the symmetric matrix H (Q = v^T H v, v = (alpha, beta)) has the blocks
    H_aa = -1/2 sum k P_e,  H_bb = -sum (1/2 + i s gamma) k P_e,  H_ab = 1/2 sum k s (i P_e + C_e),
with C_e[i][j] = sum_c m_e[c] eps[c][i][j]. The vectors m_e are the unit vectors of the closure
sum_e k_e m_e = 0 (BDFHP eq. (25)); p = gamma k.

Configurations: the four ends of a node of the regular 4-simplex (m_e the vertices of a regular
tetrahedron, equal k), with all ends source ends, and with one target end (a node a > 0 of the
simplex); random closed configurations with 4 and 5 ends, seeded; degenerate controls with all
normals parallel (m, -m).

Printed for each configuration: the condition number (the evidence of nondegeneracy: a determinant
alone depends on the scale of the entries), the relative determinant |det H| / prod |diag|, the smallest
|eigenvalue| and the largest eigenvalue of Re H^RR. Failure (exit 1): |det| < 1e-8 times
the product of the magnitudes of the diagonal entries for a configuration expected to be
nondegenerate; Re H^RR not negative definite for non-parallel normals; Re H^RR negative definite
for all-parallel normals (then it has a zero eigenvalue along the axis). This is a check of the
closed form at sample points, not a proof for all boundary data.
Usage: python3 -I scripts/asymptotics/lorentzian_hessian_xx_certificate.py
"""
import sys

import numpy as np

EPS = np.zeros((3, 3, 3))
for (c, i, j), v in {(0, 1, 2): 1, (1, 2, 0): 1, (2, 0, 1): 1, (0, 2, 1): -1, (2, 1, 0): -1, (1, 0, 2): -1}.items():
    EPS[c, i, j] = v


def block(m, k, s, gamma):
    """The complex symmetric 6 x 6 matrix H (alpha first, then beta)."""
    H = np.zeros((6, 6), complex)
    for me, ke, se in zip(m, k, s):
        P = np.eye(3) - np.outer(me, me)
        C = np.einsum('c,cij->ij', me, EPS)
        H[:3, :3] += -0.5 * ke * P
        H[3:, 3:] += -(0.5 + 1j * se * gamma) * ke * P
        cr = 0.5 * ke * se * (1j * P + C)
        H[:3, 3:] += cr
        H[3:, :3] += cr.T
    return H


def report(name, m, k, s, gamma, expect_nondegenerate=True):
    H = block(m, k, s, gamma)
    ev = np.linalg.eigvals(H)
    sv = np.linalg.svd(H, compute_uv=False)
    det = abs(np.linalg.det(H))
    diag = np.prod(np.abs(np.diag(H)))
    rr = np.linalg.eigvalsh(H[:3, :3].real)  # Re H^RR, real symmetric
    parallel = max(np.linalg.norm(np.cross(m[0], me)) for me in m) < 1e-9
    ok = True
    if expect_nondegenerate and not parallel:
        ok = det >= 1e-8 * diag and rr.max() < -1e-12
    if parallel:
        ok = abs(rr.max()) < 1e-12 and rr.min() < -1e-12      # one zero eigenvalue along the axis
    cond = sv.max() / sv.min() if sv.min() > 0 else float('inf')
    print(f"{name} (gamma={gamma}): cond={cond:.3e}, |det|/prod|diag|={(det / diag if diag > 0 else float('nan')):.3e} (test >= 1e-8), "
          f"min|eig|={np.abs(ev).min():.3e}, max eig Re H^RR={rr.max():.4e}, "
          f"normals parallel: {parallel}: {'ok' if ok else 'FAIL'}")
    return ok


def closed_vectors(rng, n):
    while True:
        m = rng.normal(size=(n, 3))
        m /= np.linalg.norm(m, axis=1)[:, None]
        kk = np.linalg.svd(m.T)[2][-1]
        if np.all(kk > 0) or np.all(kk < 0):
            return m, np.abs(kk)


def main():
    rng = np.random.default_rng(271828)
    ok = True
    tet = np.array([[1, 1, 1], [1, -1, -1], [-1, 1, -1], [-1, -1, 1]], float) / np.sqrt(3)
    k = np.ones(4)
    for gamma in (0.1, 0.5, 1.0, 4.0):
        ok &= report("regular tetrahedron, 4 source ends", tet, k, np.ones(4), gamma)
        ok &= report("regular tetrahedron, 3 source + 1 target", tet, k, np.array([1, 1, 1, -1.0]), gamma)
        ok &= report("regular tetrahedron, 2 source + 2 target", tet, k, np.array([1, 1, -1, -1.0]), gamma)
    for n in (4, 5):
        m, kk = closed_vectors(rng, n)
        for gamma in (0.5, 4.0):
            s = np.ones(n)
            s[-1] = -1
            ok &= report(f"random closed {n} ends, one target", m, kk, s, gamma)
    # controls: all normals parallel (collinear closure m, -m): the rotation block is degenerate
    m = np.array([[0, 0, 1.0], [0, 0, -1.0]])
    ok &= report("degenerate control (parallel normals)", m, np.ones(2), np.ones(2), 0.5)
    # control: the sign pattern matters (a wrong block would change the determinant)
    d1 = abs(np.linalg.det(block(tet, k, np.array([1, 1, 1, -1.0]), 0.5)))
    d2 = abs(np.linalg.det(block(tet, k, np.ones(4), 0.5)))
    good = abs(d1 - d2) > 1e-6 * max(d1, d2)
    print(f"control: the target sign changes |det| ({d1:.3g} vs {d2:.3g}): {'detected' if good else 'NOT detected'}")
    ok &= good
    print("OK" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
