"""Numerical check (not a proof) of the Spin(4) = SU(2) x SU(2) representations in
Lightlike/Spin4/Rep.lean, built independently of the Lean construction: from the textbook
angular-momentum matrices instead of symmetrised tensor powers.

Spin j (doubled n = 2j): J_z = diag(j, j-1, ..., -j), J_+ |j m> = sqrt(j(j+1) - m(m+1)) |j m+1>
(Condon-Shortley), J_x = (J_+ + J_-)/2, J_y = (J_+ - J_-)/(2i). The group element
g = exp(-i t u.sigma/2) of SU(2) acts by D^j(g) = exp(-i t u.J). The representation (j+, j-) of
Spin(4) is D^{j+}(g+) kron D^{j-}(g-).

Checks (numpy, float64; ranks with relative tolerance 1e-9), doubled spins n, m = 0..N:
 1. unitarity and dimension (n+1)(m+1);
 2. irreducibility (Schur): the matrices commuting with three random group elements form a
    space of dimension 1;
 3. faithful labels: for (n, m) != (n', m') of the same dimension, no nonzero X satisfies
    X rho(g) = rho'(g) X for three random g; for equal labels the space has dimension 1;
 4. the character of (1/2, 1/2) on the torus (diag(e^{ia}, e^{-ia}), diag(e^{ib}, e^{-ib})) is
    2cos(a+b) + 2cos(a-b), the trace of the SO(4) rotation x -> p x q^{-1} of R^4 = H;
 5. the centre: (-1, -1) acts as (-1)^(n+m).
Control: restricted to the diagonal SU(2), pairs (g, g), the commutant has dimension
min(n, m) + 1 (Clebsch-Gordan: j+ (x) j- = |j+ - j-| + ... + (j+ + j-), multiplicity-free), which
is > 1 when n, m >= 1. The script checks that value. With --diagonal it instead runs check 2 on
the diagonal model, which must FAIL (exit code 1).

Usage: .venv/bin/python -I scripts/spin4/spin4_check.py [N] [--diagonal]
"""
import itertools
import sys

import numpy as np

ARGS = [a for a in sys.argv[1:] if not a.startswith("--")]
N = int(ARGS[0]) if ARGS else 4
DIAGONAL = "--diagonal" in sys.argv
TOL = 1e-9
rng = np.random.default_rng(20261105)


def spin_matrices(n):
    """J_x, J_y, J_z for spin n/2, basis m = n/2, ..., -n/2."""
    j = n / 2
    ms = np.array([j - k for k in range(n + 1)])
    jz = np.diag(ms).astype(complex)
    jp = np.zeros((n + 1, n + 1), dtype=complex)
    for k in range(1, n + 1):          # J_+ maps m = ms[k] to m + 1 = ms[k-1]
        m = ms[k]
        jp[k - 1, k] = np.sqrt(j * (j + 1) - m * (m + 1))
    jm = jp.conj().T
    return (jp + jm) / 2, (jp - jm) / 2j, jz


def expm_herm(h, t):
    """exp(-i t h) for Hermitian h."""
    w, v = np.linalg.eigh(h)
    return v @ np.diag(np.exp(-1j * t * w)) @ v.conj().T


def D(n, g):
    """Spin-n/2 matrix of the SU(2) element g = (t, u) = exp(-i t u.sigma/2)."""
    t, u = g
    jx, jy, jz = spin_matrices(n)
    return expm_herm(u[0] * jx + u[1] * jy + u[2] * jz, t)


def random_su2():
    u = rng.normal(size=3)
    return (rng.uniform(0, 4 * np.pi), u / np.linalg.norm(u))


def rho(n, m, g):
    return np.kron(D(n, g[0]), D(m, g[1]))


def hom_dim(mats_a, mats_b):
    """dim {X : X A_k = B_k X for all k} (X is d_b x d_a)."""
    da, db = mats_a[0].shape[0], mats_b[0].shape[0]
    rows = [np.kron(np.eye(db), a.T) - np.kron(b, np.eye(da)) for a, b in zip(mats_a, mats_b)]
    big = np.vstack(rows)
    s = np.linalg.svd(big, compute_uv=False)
    rank = int(np.sum(s > TOL * s[0])) if s[0] > 0 else 0
    return da * db - rank


failures = []


def check(cond, msg):
    if not cond:
        failures.append(msg)


labels = [(n, m) for n in range(N + 1) for m in range(N + 1)]
samples = [(random_su2(), random_su2()) for _ in range(3)]

if DIAGONAL:
    print("--diagonal: irreducibility test on the diagonal model (g, g); expected to FAIL")
    for n, m in labels:
        mats = [rho(n, m, (g[0], g[0])) for g in samples]
        c = hom_dim(mats, mats)
        check(c == 1, f"diagonal ({n},{m}): commutant dimension {c}, not 1")
else:
    for n, m in labels:
        mats = [rho(n, m, g) for g in samples]
        d = mats[0].shape[0]
        check(d == (n + 1) * (m + 1), f"({n},{m}): dimension {d}")
        for a in mats:
            # einsum, not `@`: complex matmul of size 25 raises spurious floating-point flags with
            # some numpy/Accelerate builds on macOS (the product itself is finite)
            aah = np.einsum("ij,kj->ik", a, a.conj())
            check(np.allclose(aah, np.eye(d), atol=1e-10), f"({n},{m}): not unitary")
        c = hom_dim(mats, mats)
        check(c == 1, f"({n},{m}): commutant dimension {c}, expected 1")
        # control: the diagonal SU(2)
        diag = [rho(n, m, (g[0], g[0])) for g in samples]
        cd = hom_dim(diag, diag)
        check(cd == min(n, m) + 1, f"diagonal ({n},{m}): commutant {cd}, expected {min(n, m) + 1}")
        # centre
        minus = (2 * np.pi, np.array([0.0, 0.0, 1.0]))
        z = rho(n, m, (minus, minus))
        check(np.allclose(z, (-1) ** (n + m) * np.eye(d), atol=1e-10), f"({n},{m}): centre")
    # faithful labels
    pairs = 0
    for (n, m), (n2, m2) in itertools.product(labels, labels):
        if (n + 1) * (m + 1) != (n2 + 1) * (m2 + 1):
            continue
        h = hom_dim([rho(n, m, g) for g in samples], [rho(n2, m2, g) for g in samples])
        check(h == (1 if (n, m) == (n2, m2) else 0), f"Hom(({n},{m}),({n2},{m2})) = {h}")
        pairs += 1
    # character of (1/2, 1/2)
    for _ in range(20):
        a, b = rng.uniform(-np.pi, np.pi, size=2)
        ga = (-2 * a, np.array([0.0, 0.0, 1.0]))      # diag(e^{ia}, e^{-ia})
        gb = (-2 * b, np.array([0.0, 0.0, 1.0]))
        tr = np.trace(rho(1, 1, (ga, gb)))
        check(abs(tr - (2 * np.cos(a + b) + 2 * np.cos(a - b))) < 1e-10, "(1/2,1/2) character")
    print(f"labels (n, m) with n, m <= {N}: {len(labels)}; equal-dimension pairs: {pairs}")
    print("checks: dimension, unitarity, commutant = 1, diagonal commutant = min(n,m)+1, centre,")
    print("        Hom between distinct labels = 0, character of (1/2,1/2)")

if failures:
    print(f"FAIL: {len(failures)} failures; first: {failures[:3]}")
    sys.exit(1)
print("OK")
