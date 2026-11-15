"""Numerical cross-check of Lorentzian Regge calculus (Lightlike/Regge/Lorentzian/).

Numerical evidence, not proof. The formulas below transcribe the Lean definitions: Sorkin's
complex angle (`sorkinAngle`: `boostPart - (pi/2) * lightRays * i`), the dihedral angle
`lorDihedral4` (Sorkin's angle of `(G_s, G_u, M)` at a spacelike triangle, `arccos(-M/sqrt(G_s G_u))`
at a timelike one), `triHL`, `causalZ`, `lorArea = sqrt|triHL|/4`, `lorAreaPartial`, and the action
`lorReggeAction` with its boundary term. Signature (-,+,+,+), variables the signed squared edge
lengths L. Derivatives are central differences at 80 significant digits (mpmath).

Checks, each with a wrong-input control that must FAIL:
  1. Flat ring (M12's `flatRing`, Lean `Lightlike/Regge/Lorentzian/Tests.lean`) in the frames `frameT` and
     `frameS`: the dihedral angles at {0,1,2} are the Lean values and sum to 2*pi (timelike) and
     -2*pi*i (spacelike), so the deficit vanishes.
     Control: M12's Euclidean formula arccos(+M/sqrt(G_s G_u)) gives the deficit pi.
  2. Area derivative: d lorArea / dL_e = lorAreaPartial at spacelike and timelike triangles.
     Control: dropping the sign `triSign` is wrong at every timelike triangle.
  3. Lorentzian Schlaefli identity (`lorSchlaefli4`): for random Lorentzian 4-simplices with no
     null triangle or tetrahedron, sum_t A_t d(theta_t) = 0 along random directions. Also
     checks that `lorDihedral4` does not depend on the labelling of the triangle and the two
     tetrahedra.
     Control: the Euclidean sign at timelike triangles breaks the identity.
  4. Lorentzian Regge equations (`hasDerivAt_lorReggeAction`): on M12's subdivided 4-simplex
     `cone5` with randomly perturbed (non-flat) squared lengths of both causal types,
     dS/dtau = sum_int dA_t eps_t + sum_bdry dA_t (pi Z_t - sum theta).
     Control: letting the causal factor follow a sign flip of the area derivative (no triSign) breaks it.
  5. Flat solution (`IsGeometric4.lorReggeAction_stationary`, Lean `cone5_lorStationary`): at the
     flat cone5 in `frameC`, the derivative of the action along each interior edge vanishes and
     all ten interior deficits are zero.
     Control: the same derivative at perturbed lengths is not zero.
"""
import itertools
import random
import sys

import mpmath as mp

mp.mp.dps = 80
H = mp.mpf(10) ** -25          # finite-difference step
TOL = mp.mpf(10) ** -30        # agreement tolerance
FAIL = mp.mpf(10) ** -6        # a control must differ by at least this much
PI = mp.pi
I = mp.mpc(0, 1)

results = []


def record(name, ok):
    results.append((name, ok))
    print(("PASS " if ok else "FAIL ") + name)


# ---------- Lean definitions, transcribed ----------

def key(a, b):
    return frozenset((a, b))


def sqL(L, a, b):
    return mp.mpf(0) if a == b else L[key(a, b)]


def ipL(L, o, a, b):
    return (sqL(L, o, a) + sqL(L, o, b) - sqL(L, a, b)) / 2


def det(M):
    return mp.det(mp.matrix(M))


def gram(L, p, rows, cols):
    return det([[ipL(L, p, a, b) for b in cols] for a in rows])


def gram2L(L, p, q, r):
    return gram(L, p, (q, r), (q, r))


def gram3L(L, p, q, r, s):
    return gram(L, p, (q, r, s), (q, r, s))


def mixedL(L, p, q, r, s, u):
    return gram(L, p, (q, r, s), (q, r, u))


def gram4L(L, p, q, r, s, u):
    return gram(L, p, (q, r, s, u), (q, r, s, u))


def boostPart(aa, bb, ab):
    if aa * bb > 0:
        return mp.acosh(ab / mp.sqrt(aa * bb)) if ab > 0 else -mp.acosh(-ab / mp.sqrt(aa * bb))
    if aa * bb < 0:
        return mp.asinh(ab / mp.sqrt(-(aa * bb)))
    return mp.mpf(0)


def lightRays(aa, bb, ab):
    if aa * bb > 0:
        return 0 if aa * ab > 0 else 2
    return 1 if aa * bb < 0 else 0


def sorkinAngle(aa, bb, ab):
    return boostPart(aa, bb, ab) - PI / 2 * lightRays(aa, bb, ab) * I


def lorDihedral4(L, p, q, r, s, u, euclid_sign=False):
    G = gram2L(L, p, q, r)
    Gs, Gu, M = gram3L(L, p, q, r, s), gram3L(L, p, q, r, u), mixedL(L, p, q, r, s, u)
    if G > 0:
        return sorkinAngle(Gs, Gu, M)
    if G < 0:
        sgn = 1 if euclid_sign else -1
        return mp.mpc(mp.acos(sgn * M / mp.sqrt(Gs * Gu)))
    return mp.mpc(0)


def dihedralAt(L, sigma, t, **kw):
    p, q, r = sorted(t)
    s, u = sorted(set(sigma) - set(t))
    return lorDihedral4(L, p, q, r, s, u, **kw)


def edges_of(t):
    return [key(a, b) for a, b in itertools.combinations(sorted(t), 2)]


def triHL(L, t):
    Ls = [L[e] for e in edges_of(t)]
    return sum(Ls) ** 2 - 2 * sum(x ** 2 for x in Ls)


def causalZ(L, t):
    return -I if triHL(L, t) > 0 else mp.mpc(1)


def lorArea(L, t):
    return mp.sqrt(abs(triHL(L, t))) / 4


def lorAreaPartial(L, t, e, signed=True):
    h = triHL(L, t)
    sgn = (1 if h > 0 else -1) if signed else 1
    return sgn * (sum(L[f] for f in edges_of(t)) - 2 * L[e]) / (4 * mp.sqrt(abs(h)))


def lorAreaDeriv(L, v, t, **kw):
    return sum(v[e] * lorAreaPartial(L, t, e, **kw) for e in edges_of(t))


class Complex4:
    def __init__(self, simps):
        self.simps = [tuple(sorted(s)) for s in simps]
        self.tris = sorted({t for s in self.simps for t in itertools.combinations(s, 3)})
        tets = {}
        for s in self.simps:
            for t in itertools.combinations(s, 4):
                tets[t] = tets.get(t, 0) + 1
        self.tets = sorted(tets)
        bdry_tets = [t for t, n in tets.items() if n == 1]
        self.bdry_tris = [t for t in self.tris if any(set(t) <= set(b) for b in bdry_tets)]
        self.int_tris = [t for t in self.tris if t not in self.bdry_tris]
        self.edges = sorted({key(a, b) for t in self.tris for a, b in itertools.combinations(t, 2)},
                            key=sorted)
        self.int_edges = [e for e in self.edges
                          if not any(e <= set(t) for t in self.bdry_tris)]

    def star(self, t):
        return [s for s in self.simps if set(t) <= set(s)]


def angleSum(K, L, t, **kw):
    return sum(dihedralAt(L, s, t, **kw) for s in K.star(t))


def lorReggeAction(K, L):
    S = sum(lorArea(L, t) * (2 * PI * causalZ(L, t) - angleSum(K, L, t)) for t in K.int_tris)
    return S + sum(lorArea(L, t) * (PI * causalZ(L, t) - angleSum(K, L, t)) for t in K.bdry_tris)


def line(L, v, tau):
    return {e: L[e] + tau * v[e] for e in L}


def ddtau(f):
    return (f(H) - f(-H)) / (2 * H)


def minkowski_lengths(X):
    def eta(y, z):
        return -y[0] * z[0] + y[1] * z[1] + y[2] * z[2] + y[3] * z[3]
    L = {}
    for a, b in itertools.combinations(range(len(X)), 2):
        d = [mp.mpf(X[b][k]) - mp.mpf(X[a][k]) for k in range(4)]
        L[key(a, b)] = eta(d, d)
    return L


def non_null(K, L, margin=mp.mpf(10) ** -3):
    return (all(abs(triHL(L, t)) > margin for t in K.tris)
            and all(abs(gram3L(L, *t)) > margin for t in K.tets))


rng = random.Random(20261110)

# ---------- 1. flat ring, two frames ----------

ring = Complex4([(0, 1, 2, 3, 4), (0, 1, 2, 4, 5), (0, 1, 2, 5, 3)])
posT = [(0, 0, 0, 0), (2, 0, 0, 0), (0, 1, 0, 0), (2, 0, 1, 0), (2, 0, 0, 1), (2, 0, -1, -1)]
posS = [(0, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (2, 1, 0, 0), (0, 1, 0, 1), (-2, 1, 0, -1)]
LT, LS = minkowski_lengths(posT), minkowski_lengths(posS)
t012 = (0, 1, 2)
assert ring.int_tris == [t012]
angT = [dihedralAt(LT, s, t012) for s in ring.star(t012)]
angS = [dihedralAt(LS, s, t012) for s in ring.star(t012)]
expT = [PI / 2, 3 * PI / 4, 3 * PI / 4]
expS = [-I * PI / 2, mp.asinh(-1 / mp.sqrt(3)) - I * PI / 2, mp.acosh(4 / mp.sqrt(12)) - I * PI]
record("1a flat ring, frameT: Lean dihedral values pi/2, 3pi/4, 3pi/4",
       all(abs(a - b) < TOL for a, b in zip(angT, expT)))
record("1b flat ring, frameS: Lean dihedral values -i pi/2, arsinh(-1/sqrt3) - i pi/2, "
       "arcosh(4/sqrt12) - i pi",
       all(abs(a - b) < TOL for a, b in zip(angS, expS)))
defT = 2 * PI * causalZ(LT, t012) - sum(angT)
defS = 2 * PI * causalZ(LS, t012) - sum(angS)
record("1c flat ring: deficit 0 at a timelike and at a spacelike triangle",
       abs(defT) < TOL and abs(defS) < TOL and causalZ(LT, t012) == 1 and causalZ(LS, t012) == -I)
defE = 2 * PI - angleSum(ring, LT, t012, euclid_sign=True)
record("1d control: Euclidean angle formula on Lorentzian data gives deficit pi (must be wrong)",
       abs(defE - PI) < TOL and abs(defE) > FAIL)

# ---------- 2. area derivative ----------

def random_point(scale=3):
    return [mp.mpf(rng.uniform(-scale, scale)) for _ in range(4)]


ok2, ctrl2, n_sp, n_tl = True, True, 0, 0
for _ in range(40):
    L = minkowski_lengths([random_point() for _ in range(3)])
    t = (0, 1, 2)
    h = triHL(L, t)
    if abs(h) < mp.mpf(10) ** -3:
        continue
    for e in edges_of(t):
        v = {f: mp.mpf(1 if f == e else 0) for f in L}
        num = ddtau(lambda tau: lorArea(line(L, v, tau), t))
        ok2 &= abs(num - lorAreaPartial(L, t, e)) < TOL
        if h < 0:
            ctrl2 &= abs(num - lorAreaPartial(L, t, e, signed=False)) > FAIL
    n_sp += h > 0
    n_tl += h < 0
record(f"2a dA/dL_e = lorAreaPartial ({n_sp} spacelike, {n_tl} timelike triangles)",
       ok2 and n_sp > 0 and n_tl > 0)
record("2b control: without triSign the area derivative is wrong at every timelike triangle",
       ctrl2 and n_tl > 0)

# ---------- 3. Lorentzian Schlaefli ----------

simplex = Complex4([(0, 1, 2, 3, 4)])
ok3, ok3lab, ctrl3, n_simplices, types = True, True, True, 0, set()
while n_simplices < 12:
    L = minkowski_lengths([random_point() for _ in range(5)])
    if not non_null(simplex, L) or not gram4L(L, 0, 1, 2, 3, 4) < 0:
        continue
    n_simplices += 1
    sig = (0, 1, 2, 3, 4)
    for t in simplex.tris:
        types.add(triHL(L, t) > 0)
        # labelling independence of lorDihedral4
        p, q, r = t
        s, u = sorted(set(sig) - set(t))
        ref = lorDihedral4(L, p, q, r, s, u)
        for (a, b, c) in itertools.permutations(t):
            for (d, f) in ((s, u), (u, s)):
                ok3lab &= abs(lorDihedral4(L, a, b, c, d, f) - ref) < TOL
    has_timelike = any(triHL(L, t) < 0 for t in simplex.tris)
    for _ in range(3):
        v = {e: mp.mpf(rng.uniform(-1, 1)) for e in L}
        val = ddtau(lambda tau: sum(lorArea(L, t) * dihedralAt(line(L, v, tau), sig, t)
                                    for t in simplex.tris))
        ok3 &= abs(val) < TOL
        if has_timelike:
            bad = ddtau(lambda tau: sum(lorArea(L, t) *
                                        dihedralAt(line(L, v, tau), sig, t, euclid_sign=True)
                                        for t in simplex.tris))
            ctrl3 &= abs(bad) > FAIL
record(f"3a Lorentzian Schlaefli: sum_t A_t d(theta_t) = 0 on {n_simplices} random 4-simplices "
       f"(triangle types seen: {sorted('spacelike' if x else 'timelike' for x in types)})",
       ok3 and types == {True, False})
record("3b lorDihedral4 is independent of the labelling (12 labellings per triangle)", ok3lab)
record("3c control: Euclidean sign at timelike triangles breaks Schlaefli", ctrl3)

# ---------- 4. Regge equations on a perturbed cone5 ----------

cone = Complex4([tuple(sorted(set(range(6)) - {k})) for k in range(5)])
assert len(cone.int_tris) == 10 and len(cone.int_edges) == 5
posC = [(0, 0, 0, 0), (10, 0, 0, 0), (0, 5, 0, 0), (0, 0, 5, 0), (0, 0, 0, 15), (2, 1, 1, 3)]
LC = minkowski_lengths(posC)


def regge_rhs(K, L, v, **kw):
    lhs_int = sum(lorAreaDeriv(L, v, t, **kw) * (2 * PI * causalZ(L, t) - angleSum(K, L, t))
                  for t in K.int_tris)
    return lhs_int + sum(lorAreaDeriv(L, v, t, **kw) * (PI * causalZ(L, t) - angleSum(K, L, t))
                         for t in K.bdry_tris)


ok4, ctrl4, n4 = True, True, 0
while n4 < 4:
    Lp = {e: x + mp.mpf(rng.uniform(-0.5, 0.5)) for e, x in LC.items()}
    if not non_null(cone, Lp) or not all(gram4L(Lp, *s) < 0 for s in cone.simps):
        continue
    n4 += 1
    for _ in range(2):
        v = {e: mp.mpf(rng.uniform(-1, 1)) for e in Lp}
        num = ddtau(lambda tau: lorReggeAction(cone, line(Lp, v, tau)))
        ok4 &= abs(num - regge_rhs(cone, Lp, v)) < TOL
        ctrl4 &= abs(num - regge_rhs(cone, Lp, v, signed=False)) > FAIL
record(f"4a dS = sum dA_t eps_t + boundary term on {n4} perturbed (non-flat) cone5 geometries",
       ok4)
record("4b control: the area derivative without triSign does not give dS", ctrl4)

# ---------- 5. flat cone5 solves the Lorentzian Regge equations ----------

record("5a flat cone5 in frameC: no null triangle or tetrahedron, all 4-simplices Lorentzian",
       non_null(cone, LC) and all(gram4L(LC, *s) < 0 for s in cone.simps))
int_types = sorted(triHL(LC, t) > 0 for t in cone.int_tris)
record("5b flat cone5: 5 spacelike and 5 timelike interior triangles, all deficits 0",
       int_types.count(True) == 5 and int_types.count(False) == 5 and
       all(abs(2 * PI * causalZ(LC, t) - angleSum(cone, LC, t)) < TOL for t in cone.int_tris))
ok5, ctrl5 = True, True
for e in cone.int_edges:
    v = {f: mp.mpf(1 if f == e else 0) for f in LC}
    ok5 &= abs(ddtau(lambda tau: lorReggeAction(cone, line(LC, v, tau)))) < TOL
    Lp = {f: x + mp.mpf(rng.uniform(-0.3, 0.3)) for f, x in LC.items()}
    ctrl5 &= abs(ddtau(lambda tau: lorReggeAction(cone, line(Lp, v, tau)))) > FAIL
record("5c flat cone5: dS/dL_e = 0 at all five interior edges", ok5)
record("5d control: at perturbed lengths dS/dL_e is not 0", ctrl5)

n_fail = sum(1 for _, ok in results if not ok)
print(f"{len(results) - n_fail}/{len(results)} checks passed")
sys.exit(1 if n_fail else 0)
