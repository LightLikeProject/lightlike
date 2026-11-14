"""Numerical check (not a proof) of the 4-valent intertwiner results in
Lightlike/Recoupling/Intertwiner.lean, in physical (not doubled) units, with SymPy's exact
3j and 6j symbols.

  iota^{(k)}_{m1 m2 m3 m4} = sqrt(2k+1) sum_mu (-1)^(k-mu) (j1 j2 k; m1 m2 mu)(k j3 j4; -mu m3 m4)
  (Martin-Dussaud, arXiv:1902.08439, eqs. (44)-(45)).

1. Orthonormality: sum_m iota^{(k)} iota^{(k')} = delta_{kk'} for admissible k.
2. Change of channel: <iota^{(12)k}(j1 j2 j3 j4) | iota^{(13)l}(j1 j3 j2 j4)>
     = (-1)^(j2+j3+k+l) sqrt((2k+1)(2l+1)) {j1 j2 k; j4 j3 l}.
3. Control (wrong input): the phase (-1)^(j1+j4+k+l) must fail somewhere.
4. Reference values used by the Lean trust checks (Lightlike/Recoupling/Tests.lean).
5. Orthogonality at fixed spins, the reference values of the trust checks for sixJSym_orth_all
   (Intertwiner.lean) and sum_threeJ_mul_threeJ (ThreeJ.lean), exact:
     sum_x (2x+1)(2q+1) {1 1/2 x; 1 1/2 q}{1 1/2 x; 1 1/2 r} = delta_qr for q, r in {1/2, 3/2};
     sum_{m1 m2} (1/2 1/2 J; m1 m2 0)(1/2 1/2 J'; m1 m2 0) = delta_JJ' / (2J+1) for J, J' in {0, 1}.
   Control (wrong input): without the weight (2x+1) the q = r = 1/2 sum is 5/18, not 1.
6. Dimensions of the 4-valent SU(2) intertwiner spaces, from the weights (exact): 0 for the
   doubled spins (4, 4, 4, 16) (triangle condition; the sum 28 is even), 4 for (3, 3, 3, 3), 3 for
   (4, 4, 4, 8); with the EPRL labels for gamma = 1/2, 1/3 the injectivity criterion of
   eprlIntertwiner_injective_iff (Lightlike/Spin4/Fusion.lean) holds at the first two and fails at
   the third.
   Control (wrong model): parity alone (sum 2j+ even) would call (4, 4, 4, 16) non-injective.
7. Clebsch-Gordan on the diagonal SU(2) by characters (exact), the reference values of the trust
   checks for spin4_diag_clebschGordan (Lightlike/Spin4/ClebschGordan.lean): at diag(x, 1/x),
     chi_n(x) chi_m(x) = sum_{k <= min(n, m)} chi_{n+m-2k}(x)   (doubled spins n, m <= 8),
   and for n = m = 1 both sides are x^2 + 2 + x^-2 = 2 cos 2theta + 2.
   Control (wrong input): off the diagonal, at (g+, g-) = (-1, 1), the trace of (n/2, m/2) is
   (-1)^n (n+1)(m+1) but the blocks give (-1)^(n+m) (n+1)(m+1): -4 against 4 for n = m = 1.
8. The double cover Spin(4) = SU(2) x SU(2) -> SO(4), x -> p x conj(q) on the quaternions in the
   basis 1, i, j, k (exact integer arithmetic), the reference values of the trust checks for toSO4
   (Lightlike/Spin4/SO4.lean): (-1, -1) -> Id, (1, -1) -> -Id, (-1, 1) -> -Id, and (i, 1) maps 1 ->
   i and
   j -> k. Over the 64 pairs from the quaternion group {+-1, +-i, +-j, +-k} the kernel is exactly
   {(1, 1), (-1, -1)}, and every image is an orthogonal matrix of determinant 1.
   Control (wrong model): "the kernel is {(1, 1)}" fails, since 2 pairs map to Id, not 1.
9. Completeness: the vector representation of Spin(4) is (1/2, 1/2) (exact), the reference
   values of the trust checks for spin4Rep_complete (Lightlike/Spin4/Completeness.lean): its traces
   at
   (1, -1) and (-1, 1) are -4 and -4; of the doubled labels (n, m) with (n+1)(m+1) = 4, namely
   (0, 3), (1, 1), (3, 0), only (1, 1) has these traces, and on the torus (e^{ia}, e^{ib}) its
   character is chi_1(a) chi_1(b).
   Control (wrong labels): (3, 0) and (0, 3) have different torus characters.
10. Turaev-Viro at level r = 4 (q = e^{i pi/4}, [2] = sqrt 2), the reference values of the
   trust checks in Lightlike/TuraevViro/Tests.lean, with the q-Racah formula of
   Lightlike/TuraevViro/QSixJ.lean in
   doubled spins and the convention 1/0 = 0 (exact): {1 1 0; 1 1 0} = -sqrt(2)/2,
   {1 1 2; 1 1 0} = {1 2 1; 1 2 1} = sqrt(2)/2, {0 0 0; 1 1 1}^2 = sqrt(2)/2; orthogonality
   holds at (B, A, E, F, q) = (1, 2, 1, 2, 1) and (1, 1, 1, 1, 0), Biedenharn-Elliott at
   a = ... = f = 1, p = q = r = 0. A 30-digit scan finds no failure among all 3^5
   orthogonality and 3^9 Biedenharn-Elliott instances at r = 4 (numerical evidence).
   Control (wrong model): with the integer dimensions x + 1, orthogonality at (1, 2, 1, 2, 1)
   gives 1 against that model's 1/2, and Biedenharn-Elliott gives sqrt 2 against sqrt(2)/2.
11. Turaev-Viro of S^3 at r = 3 (exact), the reference value of turaevViro3_sphere: on the
   boundary of the 4-simplex (5 vertices, 10 edges, 10 triangles, 5 tetrahedra), summing over
   all 2^10 colourings with the normalisation of Lightlike/TuraevViro/Model.lean,
   Z = W^(-5) sum = 2^(-5) * 16 = 1/2 = 1/W for W = [1]^2 + [2]^2 = 2. That this
   normalisation is the textbook one, TV(S^3) = 1/W, is a convention match, not a theorem.
   Control (wrong model): with the integer dimensions J + 1, W = 5 and Z = 721/3125, not 1/5.
Spins 0..3/2, virtual spins 0..3.
"""
import itertools
import sys
from collections import Counter
from sympy import Rational as R, S, sqrt, simplify
from sympy.physics.wigner import wigner_3j, wigner_6j


def projs(j):
    return [-j + n for n in range(int(2 * j) + 1)]


def adm(a, b, c):
    return (a + b + c) == int(a + b + c) and abs(a - b) <= c <= a + b


def iota(j1, j2, j3, j4, k, m1, m2, m3, m4):
    if not (adm(j1, j2, k) and adm(k, j3, j4)):
        return S(0)
    tot = S(0)
    for mu in projs(k):
        tot += (-1) ** int(k - mu) * wigner_3j(j1, j2, k, m1, m2, mu) * wigner_3j(k, j3, j4, -mu, m3, m4)
    return sqrt(2 * k + 1) * tot


def inner(j, k, jp, kp, perm):
    tot = S(0)
    for m in itertools.product(*(projs(x) for x in j)):
        if sum(m) != 0:
            continue
        a = iota(*j, k, *m)
        if a != 0:
            tot += a * iota(*jp, kp, *[m[p] for p in perm])
    return tot


spins = [R(n, 2) for n in range(4)]
virt = [R(n, 2) for n in range(7)]
orth_bad = orth_n = ch_bad = ch_n = ctrl_fail = 0
for j in itertools.product(spins, repeat=4):
    for k in virt:
        for kp in virt:
            v = inner(j, k, j, kp, (0, 1, 2, 3))
            want = 1 if (k == kp and adm(j[0], j[1], k) and adm(k, j[2], j[3])) else 0
            orth_n += 1
            orth_bad += simplify(v - want) != 0
        for l in virt:
            jp = (j[0], j[2], j[1], j[3])
            v = inner(j, k, jp, l, (0, 2, 1, 3))
            sj = wigner_6j(j[0], j[1], k, j[3], j[2], l) if (
                adm(j[0], j[1], k) and adm(j[0], j[2], l) and adm(j[3], j[1], l) and adm(j[3], j[2], k)) else 0
            e = j[1] + j[2] + k + l
            if e != int(e):
                continue
            ch_n += 1
            ch_bad += simplify(v - (-1) ** int(e) * sqrt((2 * k + 1) * (2 * l + 1)) * sj) != 0
            e2 = j[0] + j[3] + k + l
            if e2 == int(e2) and simplify(v - (-1) ** int(e2) * sqrt((2 * k + 1) * (2 * l + 1)) * sj) != 0:
                ctrl_fail += 1
h = R(1, 2)
print(f"orthonormality: {orth_n} cases, {orth_bad} mismatches")
print(f"change of channel: {ch_n} cases, {ch_bad} mismatches")
print(f"control (wrong phase (-1)^(j1+j4+k+l)): fails in {ctrl_fail} cases (expected > 0)")
print("iota^(0)_{1/2,-1/2,1/2,-1/2}(1/2,1/2,1/2,1/2) =", iota(h, h, h, h, 0, h, -h, h, -h))
print("<(12)0|(13)0>, <(12)0|(13)1> for four spins 1/2:",
      inner((h, h, h, h), 0, (h, h, h, h), 0, (0, 2, 1, 3)),
      inner((h, h, h, h), 0, (h, h, h, h), 1, (0, 2, 1, 3)))

# 5. orthogonality at fixed spins (exact)
def sixj(a, b, c, d, e, f):
    # 0 for an inadmissible triad, as in Physlib's sixJSym (SymPy raises instead)
    if adm(a, b, c) and adm(a, e, f) and adm(d, b, f) and adm(d, e, c):
        return wigner_6j(a, b, c, d, e, f)
    return S(0)


def six_orth(q, r, weight=True):
    tot = S(0)
    for n in range(4):  # x = 0, 1/2, 1, 3/2: the range of the Lean sum, B + A + 1 = 4 doubled values
        x = R(n, 2)
        w = (2 * x + 1) if weight else 1
        tot += w * (2 * q + 1) * sixj(1, h, x, 1, h, q) * sixj(1, h, x, 1, h, r)
    return simplify(tot)


def three_orth(J, Jp):
    return simplify(sum(wigner_3j(h, h, J, m1, m2, 0) * wigner_3j(h, h, Jp, m1, m2, 0)
                        for m1 in projs(h) for m2 in projs(h)))


six_vals = {(q, r): six_orth(q, r) for q in (h, 3 * h) for r in (h, 3 * h)}
six_ok = all(v == (1 if q == r else 0) for (q, r), v in six_vals.items())
six_ctrl = six_orth(h, h, weight=False)
three_vals = {(J, Jp): three_orth(J, Jp) for J in (0, 1) for Jp in (0, 1)}
three_ok = all(v == (R(1, 2 * J + 1) if J == Jp else 0) for (J, Jp), v in three_vals.items())
print("6j values {1 1/2 1/2; 1 1/2 3/2}, {1 1/2 3/2; 1 1/2 3/2}:",
      wigner_6j(1, h, h, 1, h, 3 * h), wigner_6j(1, h, 3 * h, 1, h, 3 * h))
print("6j orthogonality, (q, r) -> sum:", {f"({q}, {r})": v for (q, r), v in six_vals.items()},
      "; without (2x+1):", six_ctrl)
print("3j orthogonality, (J, J') -> sum:", {f"({J}, {Jp})": v for (J, Jp), v in three_vals.items()})
print("3j values (1/2 1/2 1; +-1/2 -+1/2 0), (1/2 1/2 0; 1/2 -1/2 0), (1/2 1/2 0; -1/2 1/2 0):",
      wigner_3j(h, h, 1, h, -h, 0), wigner_3j(h, h, 1, -h, h, 0),
      wigner_3j(h, h, 0, h, -h, 0), wigner_3j(h, h, 0, -h, h, 0))

# 6. dimensions of the 4-valent SU(2) intertwiner spaces from the weights (exact), the reference
#    values of the trust checks for eprlIntertwiner_injective_iff (Lightlike/Spin4/Fusion.lean)
def weights(Js):
    """Multiplicities of the doubled weights of V_{J1} x ... x V_{Jk} (doubled spins J)."""
    mult = {0: 1}
    for J in Js:
        new = {}
        for w, c in mult.items():
            for m in range(-J, J + 1, 2):
                new[w + m] = new.get(w + m, 0) + c
        mult = new
    return mult


def inv_dim(Js):
    """dim of the SU(2) invariants: multiplicity of weight 0 minus that of weight 1 (doubled 2)."""
    mult = weights(Js)
    return mult.get(0, 0) - mult.get(2, 0)


def eprl_labels(gamma, J):
    """Doubled EPRL labels (2j+, 2j-) = ((1 + gamma) J / 2, (1 - gamma) J / 2)."""
    return (1 + gamma) * J / 2, (1 - gamma) * J / 2


cases = {(4, 4, 4, 16): R(1, 2), (3, 3, 3, 3): R(1, 3), (4, 4, 4, 8): R(1, 2)}
fus = {}
for Js, g in cases.items():
    ns = [eprl_labels(g, J)[0] for J in Js]
    fus[Js] = (inv_dim(Js), sum(Js), sum(ns))
# the criterion: injective iff sum 2j+ even or no SU(2) intertwiners; the control drops the second
crit = {Js: (n % 2 == 0) or d == 0 for Js, (d, _, n) in fus.items()}
parity_only = {Js: n % 2 == 0 for Js, (d, _, n) in fus.items()}
print("4-valent SU(2) intertwiners, doubled J -> (dim, sum J, sum 2j+):",
      {str(k): v for k, v in fus.items()})
print("injective by the criterion:", {str(k): v for k, v in crit.items()},
      "; parity only (control, must differ at (4, 4, 4, 16)):", {str(k): v for k, v in parity_only.items()})
fus_ok = fus[(4, 4, 4, 16)] == (0, 28, 21) and fus[(3, 3, 3, 3)] == (4, 12, 8)
fus_ok = fus_ok and fus[(4, 4, 4, 8)] == (3, 20, 15)
fus_ok = fus_ok and eprl_labels(R(1, 2), 16) == (12, 4) and crit[(4, 4, 4, 16)] and not parity_only[(4, 4, 4, 16)]
fus_ok = fus_ok and crit[(3, 3, 3, 3)] and not crit[(4, 4, 4, 8)]
ok = orth_bad == 0 and ch_bad == 0 and ctrl_fail > 0
ok = ok and six_ok and six_ctrl == R(5, 18) and three_ok
ok = ok and wigner_6j(1, h, h, 1, h, 3 * h) == R(-1, 3) and wigner_6j(1, h, 3 * h, 1, h, 3 * h) == R(-1, 12)
ok = ok and simplify(wigner_3j(h, h, 1, h, -h, 0) - 1 / sqrt(6)) == 0
ok = ok and simplify(wigner_3j(h, h, 1, -h, h, 0) - 1 / sqrt(6)) == 0
ok = ok and simplify(wigner_3j(h, h, 0, -h, h, 0) + 1 / sqrt(2)) == 0

# 7. Clebsch-Gordan on the diagonal SU(2) by characters (exact), the reference values of the trust
# checks for spin4_diag_clebschGordan (Lightlike/Spin4/ClebschGordan.lean). A character at diag(x,
# 1/x) is
# stored as {power of x: multiplicity}; doubled spins throughout.


def chi(n):
    return Counter({n - 2 * k: 1 for k in range(n + 1)})


def chi_pair(n, m):
    """Trace of (n/2, m/2) at (g, g): chi_n(x) chi_m(x)."""
    c = Counter()
    for a, u in chi(n).items():
        for b, v in chi(m).items():
            c[a + b] += u * v
    return c


def chi_blocks(n, m):
    """Trace of the blocks of cgMat n m at g: sum_{k <= min(n, m)} chi_{n+m-2k}(x)."""
    c = Counter()
    for k in range(min(n, m) + 1):
        c.update(chi(n + m - 2 * k))
    return c


def at_minus_one(c):
    return sum(v * (-1) ** (p % 2) for p, v in c.items())


grid = [(n, m) for n in range(9) for m in range(9)]
cg_bad = sum(1 for n, m in grid if chi_pair(n, m) != chi_blocks(n, m))
# Control (wrong input): off the diagonal, at (g+, g-) = (-1, 1) the trace of (n/2, m/2) is
# (-1)^n (n+1)(m+1); the blocks at -1 give (-1)^(n+m) (n+1)(m+1). They differ whenever m is odd.
off = {(n, m): ((-1) ** n * (n + 1) * (m + 1), at_minus_one(chi_blocks(n, m))) for n, m in grid}
off_fail = sum(1 for a, b in off.values() if a != b)
print(f"characters on the diagonal, doubled n, m <= 8: {len(grid)} cases, {cg_bad} mismatches")
print("(1/2, 1/2) at diag(x, 1/x), powers of x -> multiplicity:", dict(sorted(chi_blocks(1, 1).items())),
      "(= 2 cos 2theta + 2)")
print(f"control (off the diagonal, (-1, 1)): (1, 1) -> {off[(1, 1)]}; fails in {off_fail} cases "
      f"(expected {sum(1 for n, m in grid if m % 2 == 1)})")
cg_ok = cg_bad == 0 and dict(chi_blocks(1, 1)) == {2: 1, 0: 2, -2: 1} and off[(1, 1)] == (-4, 4)
cg_ok = cg_ok and off_fail == sum(1 for n, m in grid if m % 2 == 1)

# 8. The double cover Spin(4) -> SO(4), x -> p x conj(q) (exact), the reference values of the trust
# checks for toSO4 (Lightlike/Spin4/SO4.lean). Quaternions are tuples (re, i, j, k) of integers.


def qmul(a, b):
    a0, a1, a2, a3 = a
    b0, b1, b2, b3 = b
    return (a0 * b0 - a1 * b1 - a2 * b2 - a3 * b3, a0 * b1 + a1 * b0 + a2 * b3 - a3 * b2,
            a0 * b2 - a1 * b3 + a2 * b0 + a3 * b1, a0 * b3 + a1 * b2 - a2 * b1 + a3 * b0)


def qconj(a):
    return (a[0], -a[1], -a[2], -a[3])


QBASIS = [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]


def so4_matrix(p, q):
    """Matrix of x -> p x conj(q) in the basis 1, i, j, k (column c is the image of basis vector c)."""
    cols = [qmul(qmul(p, e), qconj(q)) for e in QBASIS]
    return tuple(tuple(cols[c][r] for c in range(4)) for r in range(4))


def mat_mul(A, B):
    return tuple(tuple(sum(A[r][k] * B[k][c] for k in range(4)) for c in range(4)) for r in range(4))


def det4(A):
    from sympy import Matrix
    return Matrix(A).det()


ID4 = tuple(tuple(int(r == c) for c in range(4)) for r in range(4))
NEG4 = tuple(tuple(-x for x in row) for row in ID4)
ONE, NEG, QI = (1, 0, 0, 0), (-1, 0, 0, 0), (0, 1, 0, 0)
Q8 = [tuple(s * x for x in e) for e in QBASIS for s in (1, -1)]
pairs = [(p, q) for p in Q8 for q in Q8]
kernel = [(p, q) for p, q in pairs if so4_matrix(p, q) == ID4]
in_so4 = all(mat_mul(tuple(zip(*M)), M) == ID4 and det4(M) == 1
             for M in (so4_matrix(p, q) for p, q in pairs))
i_left = so4_matrix(QI, ONE)
i_vals = (tuple(i_left[r][0] for r in range(4)), tuple(i_left[r][2] for r in range(4)))
print("toSO4: (-1,-1) -> Id", so4_matrix(NEG, NEG) == ID4, "; (1,-1) -> -Id", so4_matrix(ONE, NEG) == NEG4,
      "; (-1,1) -> -Id", so4_matrix(NEG, ONE) == NEG4, "; (i,1): 1 ->", i_vals[0], "j ->", i_vals[1])
print(f"kernel over Q8 x Q8 (64 pairs): {kernel}; all images in SO(4): {in_so4}")
print(f"control (wrong model, kernel = {{(1, 1)}}): {len(kernel)} pairs map to Id, not 1")
so4_ok = (so4_matrix(NEG, NEG) == ID4 and so4_matrix(ONE, NEG) == NEG4 and so4_matrix(NEG, ONE) == NEG4
          and i_vals == ((0, 1, 0, 0), (0, 0, 0, 1)) and in_so4
          and sorted(kernel) == sorted([(ONE, ONE), (NEG, NEG)]) and len(kernel) != 1)
ok = ok and fus_ok and cg_ok and so4_ok


# 9. Completeness: the vector representation of Spin(4) is (1/2, 1/2) (exact), the reference values of
# the trust checks for spin4Rep_complete (Lightlike/Spin4/Completeness.lean). The rep (n/2, m/2) has
# dimension
# (n+1)(m+1) and traces (-1)^m (n+1)(m+1) at (1, -1), (-1)^n (n+1)(m+1) at (-1, 1); on the torus
# (e^{ia}, e^{ib}) its character is chi_n(a) chi_m(b) with chi_n(t) = sum_k cos((n - 2k) t).
from sympy import symbols, sin, cos, expand

ta, tb = symbols('a b', real=True)


def trace4(M):
    return sum(M[r][r] for r in range(4))


def chi_su2(n, t):
    return sum(cos((n - 2 * k) * t) for k in range(n + 1))


def torus(t):
    return (cos(t), sin(t), 0, 0)


vec_minus = (trace4(so4_matrix(ONE, NEG)), trace4(so4_matrix(NEG, ONE)))
dim4 = [(n, m) for n in range(4) for m in range(4) if (n + 1) * (m + 1) == 4]
forced = [(n, m) for n, m in dim4 if ((-1) ** m * (n + 1) * (m + 1), (-1) ** n * (n + 1) * (m + 1)) == vec_minus]
vec_char = expand(trace4(so4_matrix(torus(ta), torus(tb))))
char_ok = expand(vec_char - expand(chi_su2(1, ta) * chi_su2(1, tb))) == 0
wrong_char = [expand(vec_char - expand(chi_su2(n, ta) * chi_su2(m, tb))) != 0 for n, m in ((3, 0), (0, 3))]
print(f"vector rep: dim 4, traces at (1,-1), (-1,1): {vec_minus}; labels of dim 4: {dim4}; "
      f"forced by the traces: {forced}")
print(f"torus character tr = {vec_char} = chi_1(a) chi_1(b): {char_ok}; "
      f"control (wrong labels (3,0), (0,3)) differ: {wrong_char}")
comp_ok = vec_minus == (-4, -4) and forced == [(1, 1)] and char_ok and all(wrong_char)

ok = ok and comp_ok


# 10. Turaev-Viro at level r = 4 (q = e^{i pi/4}, [2] = sqrt 2), the reference values of the trust
# checks for qOrthogonality and qBiedenharnElliott (Lightlike/TuraevViro/TuraevViro.lean). The
# quantum 6j symbol
# is the one of Lightlike/TuraevViro/QSixJ.lean, with Lean's convention 1/0 = 0, doubled spins 0, 1,
# 2.
from sympy import pi, Integer
import mpmath


def qnum(r, n):
    return sin(n * pi / r) / sin(pi / r)


def qfact(r, n):
    p = Integer(1)
    for k in range(n):
        p *= qnum(r, k + 1)
    return simplify(p)


def inv0(x):
    return Integer(0) if x == 0 else 1 / x


def inv_qfact(r, u):
    return inv0(qfact(r, u)) if u >= 0 else Integer(0)


def qadm(r, a, b, c):
    # doubled spins: Lean's Tri (Lightlike/PonzanoRegge/Pentagon.lean) asks for an even sum, which
    # the
    # physical-spin adm above does not test for integer arguments
    return ((a + b + c) % 2 == 0 and abs(a - b) <= c <= a + b
            and a + b + c <= 2 * (r - 2))


def qdelta(r, a, b, c):
    s = (a + b + c) // 2
    return sqrt(qfact(r, s - a) * qfact(r, s - b) * qfact(r, s - c) * inv0(qfact(r, s + 1)))


def qsixj(r, j1, j2, j3, j4, j5, j6):
    if not (qadm(r, j1, j2, j3) and qadm(r, j1, j5, j6) and qadm(r, j4, j2, j6) and qadm(r, j4, j5, j3)):
        return Integer(0)
    al = [(j1 + j2 + j3) // 2, (j1 + j5 + j6) // 2, (j4 + j2 + j6) // 2, (j4 + j5 + j3) // 2]
    be = [(j1 + j2 + j4 + j5) // 2, (j2 + j3 + j5 + j6) // 2, (j3 + j1 + j6 + j4) // 2]
    tot = Integer(0)
    for z in range(j1 + j2 + j3 + j4 + j5 + j6 + 1):
        t = (-1) ** z * qfact(r, z + 1)
        for x in al:
            t *= inv_qfact(r, z - x)
        for y in be:
            t *= inv_qfact(r, y - z)
        tot += t
    return simplify(qdelta(r, j1, j2, j3) * qdelta(r, j1, j5, j6) * qdelta(r, j4, j2, j6)
                    * qdelta(r, j4, j5, j3) * tot)


Q4 = {js: qsixj(4, *js) for js in itertools.product(range(3), repeat=6)}
s2 = sqrt(2)


def orth4(B, A, E, F, q, dim):
    return simplify(sum(dim(x) * Q4[(B, A, x, E, F, q)] ** 2 for x in range(3)))


def be4(a, b, c, d, e, f, p, q, r, dim):
    return simplify(sum((-1) ** ((a + b + c + d + e + f + p + q + r + x) // 2) * dim(x)
                        * Q4[(a, b, x, c, d, p)] * Q4[(c, d, x, e, f, q)] * Q4[(e, f, x, b, a, r)]
                        for x in range(3)))


qdim4, cldim = (lambda x: simplify(qnum(4, x + 1))), (lambda x: x + 1)
vals4 = [Q4[(1, 1, 0, 1, 1, 0)], Q4[(1, 1, 2, 1, 1, 0)], Q4[(1, 2, 1, 1, 2, 1)], simplify(Q4[(0, 0, 0, 1, 1, 1)] ** 2)]
inst4 = [orth4(1, 2, 1, 2, 1, qdim4), orth4(1, 1, 1, 1, 0, qdim4), be4(1, 1, 1, 1, 1, 1, 0, 0, 0, qdim4),
         simplify(Q4[(0, 0, 0, 1, 1, 1)] ** 2)]
ctrl4 = [orth4(1, 2, 1, 2, 1, cldim), be4(1, 1, 1, 1, 1, 1, 0, 0, 0, cldim)]
# full scan, numerical (mpmath, 30 digits): all 3^5 orthogonality and 3^9 BE instances
mpmath.mp.dps = 30
QN = {k: mpmath.mpf(str(v.evalf(40))) for k, v in Q4.items()}
dN = [mpmath.mpf(str(qdim4(x).evalf(40))) for x in range(3)]
orth_bad4 = sum(1 for B, A, E, F, q in itertools.product(range(3), repeat=5)
                if abs(sum(dN[x] * QN[(B, A, x, E, F, q)] ** 2 for x in range(3))
                       - ((1 / dN[q]) if qadm(4, A, E, q) and qadm(4, B, q, F) else 0)) > mpmath.mpf(10) ** -20)
be_bad4 = sum(1 for a, b, c, d, e, f, p, q, r in itertools.product(range(3), repeat=9)
              if abs(sum((-1) ** ((a + b + c + d + e + f + p + q + r + x) // 2) * dN[x]
                         * QN[(a, b, x, c, d, p)] * QN[(c, d, x, e, f, q)] * QN[(e, f, x, b, a, r)] for x in range(3))
                     - QN[(p, q, r, e, a, d)] * QN[(p, q, r, f, b, c)]) > mpmath.mpf(10) ** -20)
print("r = 4: [1], [2], [3], [4] =", [simplify(qnum(4, n)) for n in range(1, 5)],
      "; {110;110}, {112;110}, {121;121}, {000;111}^2 =", vals4)
print("r = 4 instances: orth (1,2,1,2,1), orth (1,1,1,1,0), BE (1^6, 0^3), BE right side =", inst4,
      "; numerical scan (not a proof): orthogonality failures", orth_bad4, "of 243, BE failures", be_bad4, "of 19683")
print("control (wrong model, integer dimensions x + 1): orth (1,2,1,2,1) =", ctrl4[0], "(that model predicts 1/2),",
      "BE (1^6, 0^3) =", ctrl4[1], "(not sqrt(2)/2)")
tv4_ok = (vals4 == [-s2 / 2, s2 / 2, s2 / 2, s2 / 2] and inst4 == [s2 / 2, 1, s2 / 2, s2 / 2]
          and orth_bad4 == 0 and be_bad4 == 0 and ctrl4 == [1, s2])

ok = ok and tv4_ok


# 11. Turaev-Viro of S^3 = boundary of the 4-simplex at r = 3 (exact), the reference value of the trust
# check turaevViro3_sphere. Normalisation as in Lightlike/TuraevViro/Model.lean (stated, a PROXY
# match of the
# textbook convention): Z = W^(-#vertices) sum_colourings prod_edges [J+1](-1)^J prod_triangles
# (-1)^(sum/2) prod_tets {6j}, W = sum_J [J+1]^2; the textbook value is TV(S^3) = 1/W.
# Each tetrahedron a < b < c < d contributes {c_cd c_bd c_bc; c_ab c_ac c_ad} (Model.tetAmp_eq).
V5 = range(5)
EDGES5 = list(itertools.combinations(V5, 2))
TRIS5 = list(itertools.combinations(V5, 3))
TETS5 = list(itertools.combinations(V5, 4))
Q3 = {js: qsixj(3, *js) for js in itertools.product(range(2), repeat=6)}


def tv_sphere(dim):
    W = sum(dim(J) ** 2 for J in range(2))
    tot, nonzero = Integer(0), 0
    for cols in itertools.product(range(2), repeat=10):
        c = dict(zip(EDGES5, cols))
        w = Integer(1)
        for e in EDGES5:
            w *= dim(c[e]) * (-1) ** c[e]
        for x, y, z in TRIS5:
            w *= (-1) ** ((c[(x, y)] + c[(x, z)] + c[(y, z)]) // 2)
        for a, b, cc, d in TETS5:
            w *= Q3[(c[(cc, d)], c[(b, d)], c[(b, cc)], c[(a, b)], c[(a, cc)], c[(a, d)])]
        w = simplify(w)
        tot += w
        nonzero += w != 0
    return simplify(W), simplify(tot), nonzero, simplify(tot / W ** 5)


tv3 = tv_sphere(lambda J: simplify(qnum(3, J + 1)))
cl3 = tv_sphere(lambda J: J + 1)
print(f"r = 3, S^3 = boundary of the 4-simplex: W = {tv3[0]}, sum = {tv3[1]} ({tv3[2]} nonzero colourings), "
      f"Z = {tv3[3]} (= 1/W)")
print(f"control (wrong model, integer dimensions J + 1): W = {cl3[0]}, sum = {cl3[1]}, Z = {cl3[3]} (not 1/W = 1/5)")
tv3_ok = tv3 == (2, 16, 16, R(1, 2)) and cl3[0] == 5 and cl3[1] == 721 and cl3[3] == R(721, 3125)

ok = ok and tv3_ok
print("OK" if ok else "FAIL")
sys.exit(0 if ok else 1)
