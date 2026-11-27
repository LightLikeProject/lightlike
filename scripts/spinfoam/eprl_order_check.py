"""Numerical check, wrong-input control: the positional node basis change `nodeT` without the sign `nodeEta` makes the EPRL state sum at
gamma = 1 depend on the vertex order.

Numerical evidence, not proof. Doubled spins throughout.

Model of the sorted-basis state sum `Lightlike.SpinFoam.EPRLStateSum.amplitudeI 1 K cut` (Lightlike/SpinFoam/EPRLStateSum/IntrinsicVertex.lean)
in which the node basis change is built as if the channel tensor of the sorted legs and that of the cyclic legs were equal, i.e. WITHOUT the
sign `nodeEta` of `fourJ_swap₁₂`, `fourJ_swap₃₄`, `fourJ_swapPairs`. The Lean `amplitudeI` carries `nodeEta`; it is the basis-free contraction
(`simpEIAux_eq_contract5`) and independent of the vertex order (`amplitudeI_one_relabel`), see scripts/spinfoam/eprl_free_gluing_check.py. The
model here is the wrong input that the check must tell apart from it. On the boundary `sphere6` of the 5-simplex on the vertices 0 < 1 < ... < 5:

* a triangle colouring `col <= cut`, face amplitude `J + 1` (`faceAmp_one`), edge amplitude 1;
* a sorted label `z_t` on every tetrahedron, `z_t <= leg_0 + leg_1` (`tetBoxI`);
* the vertex of the 4-simplex `s` with sorted vertices `s_0 < ... < s_4` and spins
  `J p q = col(s - {s_p, s_q})`:
  `vertexI = sum_x prod_a nodeT(J, a, z_a, x_a) * fifteenJSimplex(J, x)` with
  `nodeT = sum_m nodeI(z, m) nodeP(x, m)` (no `nodeEta`), `nodeI` the recoupling matrix of the sorted legs
  `a.succAbove 0..3`, `nodeP` the one of the cyclic legs `a+1..a+4` (`fourRecoupling`), and
  `fifteenJSimplex` as in scripts/spinfoam/vertex_check.py.

The cutoff `bone(u, w)` allows spin 1 (doubled) on the four triangles containing the edge
`{u, w}` and 0 elsewhere. A permutation `pi` of the vertices maps `sphere6` to itself and
`bone(0, 1)` to `bone(pi 0, pi 1)`, so independence of the vertex order would force
`A(u, w) = A(0, 1)` for all pairs. The script prints `A(u, w)` for all 15 pairs; for this wrong input they are `5` or `-3`.

Wrong-input control: the same sum with the positional labels glued directly (nodeT replaced by
the identity, i.e. `EPRL.amplitude` of Lightlike/SpinFoam/EPRL.lean) must differ from the intrinsic one somewhere.

Run: .venv/bin/python -I scripts/spinfoam/eprl_order_check.py   (prints the table and "OK")
"""
import itertools
import math
import sys
from fractions import Fraction
from functools import lru_cache

sys.path.insert(0, __import__('os').path.dirname(__file__))
from vertex_check import amp_closed, fifteen_simplex  # noqa: E402


def tri(a, b, c):
    return (a + b + c) % 2 == 0 and abs(a - b) <= c <= a + b


@lru_cache(maxsize=None)
def delta(a, b, c):
    """Triangle coefficient, doubled spins: sqrt((a+b-c)/2! (a-b+c)/2! (-a+b+c)/2! / ((a+b+c)/2+1)!)."""
    return Fraction(math.factorial((a + b - c) // 2) * math.factorial((a - b + c) // 2)
                    * math.factorial((-a + b + c) // 2), math.factorial((a + b + c) // 2 + 1))


@lru_cache(maxsize=None)
def sixj(j1, j2, j3, j4, j5, j6):
    """Racah's formula for {j1 j2 j3; j4 j5 j6}, doubled spins."""
    tr = [(j1, j2, j3), (j1, j5, j6), (j4, j2, j6), (j4, j5, j3)]
    if not all(tri(*t) for t in tr):
        return 0.0
    pre = 1.0
    for t in tr:
        pre *= math.sqrt(float(delta(*t)))
    a = [sum(t) // 2 for t in tr]
    b = [(j1 + j2 + j4 + j5) // 2, (j2 + j3 + j5 + j6) // 2, (j3 + j1 + j6 + j4) // 2]
    s = 0
    for t in range(max(a), min(b) + 1):
        den = 1
        for x in a:
            den *= math.factorial(t - x)
        for y in b:
            den *= math.factorial(y - t)
        s += Fraction((-1) ** t * math.factorial(t + 1), den)
    return pre * float(s)


def four_recoupling(j1, j2, j3, j4, k, l):
    """`fourRecoupling` of Lightlike/Recoupling/Intertwiner.lean."""
    return ((-1) ** ((j2 + j3 + k + l) // 2) * math.sqrt((k + 1) * (l + 1))
            * sixj(j1, j2, k, j4, j3, l))


def succ_above(a, k):
    return k if k < a else k + 1


SIMPBOX = [(1, 3), (2, 4), (3, 0), (4, 1), (0, 2)]   # simpBox J a = range(J a b + J a c + 1)


def node_i(J, a, z, m):
    sa = [succ_above(a, k) for k in range(4)]
    return four_recoupling(*[J[a][b] for b in sa], z, m)


def node_p(J, a, x, m):
    cyc = [(a + d) % 5 for d in (1, 2, 3, 4)]
    return four_recoupling(*[J[a][b] for b in cyc], x, m)


def node_t(J, a, z, x):
    b, c = SIMPBOX[a]
    return sum(node_i(J, a, z, m) * node_p(J, a, x, m) for m in range(J[a][b] + J[a][c] + 1))


def fifteen(J, x):
    j = {(p, q): J[p][q] for p in range(5) for q in range(p + 1, 5)}
    return fifteen_simplex(j, list(x))


@lru_cache(maxsize=None)
def vertex(Jt, z, intrinsic=True):
    J = [list(r) for r in Jt]
    if not intrinsic:
        return fifteen(J, z)
    boxes = [range(J[a][(a + 1) % 5] + J[a][(a + 2) % 5] + 1) for a in range(5)]
    tot = 0.0
    for x in itertools.product(*boxes):
        c = 1.0
        for a in range(5):
            c *= node_t(J, a, z[a], x[a])
            if c == 0.0:
                break
        if c != 0.0:
            tot += c * fifteen(J, x)
    return tot


V6 = range(6)
SIMPS = [tuple(v for v in V6 if v != p) for p in V6]
TETS = [tuple(sorted(t)) for t in itertools.combinations(V6, 4)]
TRIS = [tuple(sorted(t)) for t in itertools.combinations(V6, 3)]


def amplitude(cut, intrinsic=True):
    free = [f for f in TRIS if cut[f] > 0]
    total = 0.0
    for vals in itertools.product(*[range(cut[f] + 1) for f in free]):
        col = {f: 0 for f in TRIS}
        col.update(dict(zip(free, vals)))
        face = 1.0
        for f in TRIS:
            face *= col[f] + 1
        legs = {t: [col[tuple(v for v in t if v != t[k])] for k in range(4)] for t in TETS}
        boxes = [range(legs[t][0] + legs[t][1] + 1) for t in TETS]
        inner = 0.0
        for zs in itertools.product(*boxes):
            zt = dict(zip(TETS, zs))
            w = 1.0
            for s in SIMPS:
                J = tuple(tuple(col[tuple(v for v in s if v not in (s[p], s[q]))] if p != q else 0
                                for q in range(5)) for p in range(5))
                z = tuple(zt[tuple(v for v in s if v != s[a])] for a in range(5))
                w *= vertex(J, z, intrinsic)
                if w == 0.0:
                    break
            inner += w
        total += face * inner
    return total


@lru_cache(maxsize=None)
def ooguri_vertex(Jt, Kt):
    """`ampP` (the Ooguri vertex amplitude `simpW` of Lightlike/SpinFoam/Vertex.lean) at positions."""
    J = {frozenset((p, q)): Jt[p][q] for p in range(5) for q in range(5) if p != q}
    return amp_closed(J, list(Kt))


def ooguri_amplitude(cut):
    """Pure Ooguri amplitude `Ooguri.amplitudeGF` of `sphere6` with the triangle cutoff `cut`
    (the virtual spins of the tetrahedra run over all values their legs allow)."""
    free = [f for f in TRIS if cut[f] > 0]
    total = 0.0
    for vals in itertools.product(*[range(cut[f] + 1) for f in free]):
        col = {f: 0 for f in TRIS}
        col.update(dict(zip(free, vals)))
        face = 1.0
        for f in TRIS:
            face *= col[f] + 1
        legs = {t: sum(col[tuple(v for v in t if v != t[k])] for k in range(4)) for t in TETS}
        boxes = [range(legs[t] + 1) for t in TETS]
        inner = 0.0
        for zs in itertools.product(*boxes):
            zt = dict(zip(TETS, zs))
            w = 1.0
            for s in SIMPS:
                J = tuple(tuple(col[tuple(v for v in s if v not in (s[p], s[q]))] if p != q else 0
                                for q in range(5)) for p in range(5))
                K = tuple(zt[tuple(v for v in s if v != s[a])] for a in range(5))
                w *= ooguri_vertex(J, K)
                if w == 0.0:
                    break
            inner += w
        total += face * inner
    return total


def bone(u, w):
    return {f: (1 if u in f and w in f else 0) for f in TRIS}


def main():
    table = {}
    for u, w in itertools.combinations(V6, 2):
        table[(u, w)] = amplitude(bone(u, w))
        print(f"A({u},{w}) = {table[(u, w)]:+.6f}")
    ooo = {k: ooguri_amplitude(bone(*k)) for k in table}
    print("pure Ooguri amplitude (control 1):", {k: round(v, 6) for k, v in ooo.items()})
    print("pure Ooguri |A| values:", sorted(set(round(abs(v), 9) for v in ooo.values())))
    vals = sorted(set(round(v, 9) for v in table.values()))
    print("distinct values:", vals)
    dep = len(vals) > 1
    print("vertex order dependence:", "YES" if dep else "NO")
    pos = {k: amplitude(bone(*k), intrinsic=False) for k in [(0, 1), (0, 2), (1, 3)]}
    print("positional (wrong-input control):", {k: round(v, 6) for k, v in pos.items()})
    ctrl = any(abs(pos[k] - table[k]) > 1e-9 for k in pos)
    print("control differs:", ctrl)
    print("OK" if ctrl else "FAILED")
    return 0 if ctrl else 1


if __name__ == "__main__":
    sys.exit(main())
