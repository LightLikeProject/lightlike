"""Numerical check (not a proof): a forcing gauge set stays forcing along Pachner moves in 4D.

Question: if T forces every triangle of the closed 4-manifold triangulation K (a tetrahedron with
three triangles in the set forces the fourth), does the set that the gauge-rule theorems produce
after a move (Lean: IsGauge.move24, isGauge_move15, amplitudeGF_move33_gauge) force every triangle
of the new complex? Start: the boundary of the 5-simplex with T = the ten triangles through a vertex.

Forward moves: 3-3 (T unchanged), 2-4 (T plus the triangle {p, q, a}, a in the old tetrahedron),
1-5 (T plus {v, a_0, a_j}, j = 1..4). Inverse moves 4-2 and 5-1: the gauge set is given on the
complex before the move and loses the triangles that the forward move adds.
Controls: with one triangle removed from the starting T, the closure forces fewer than all
triangles, so the check can fail; a wrong rule (2-4 without adding a triangle) must be caught.
Exit 0 when no preserved-forcing failure occurs and the controls fail as they should.
"""
import itertools
import random
import sys
from collections import Counter

fs = frozenset


def faces(K, k):
    return {fs(c) for s in K for c in itertools.combinations(sorted(s), k)}


def closure(K, T):
    tets, Z, ch = faces(K, 4), set(T), True
    while ch:
        ch = False
        for t in tets:
            miss = [f for f in map(fs, itertools.combinations(sorted(t), 3)) if f not in Z]
            if len(miss) == 1:
                Z.add(miss[0])
                ch = True
    return Z


def forces(K, T):
    return faces(K, 3) <= closure(K, T)


def m15(K, T, v, rng):
    s = rng.choice(sorted(K, key=sorted))
    a = sorted(s)
    K2 = (K - {s}) | {fs(set(c) | {v}) for c in itertools.combinations(a, 4)}
    return K2, set(T) | {fs({v, a[0], x}) for x in a[1:]}


def m24(K, T, rng, add=True):
    cand = [t for t in faces(K, 4) if sum(t <= s for s in K) == 2]
    rng.shuffle(cand)
    edges = faces(K, 2)
    for t in cand:
        p, q = [next(iter(s - t)) for s in K if t <= s]
        if fs({p, q}) in edges:
            continue
        K2 = (K - {t | {p}, t | {q}}) | {fs({p, q} | (t - {x})) for x in t}
        return K2, set(T) | ({fs({p, q, rng.choice(sorted(t))})} if add else set())
    return None


def m33(K, T, rng):
    tris = sorted(faces(K, 3), key=sorted)
    rng.shuffle(tris)
    for sg in tris:
        st = [s for s in K if sg <= s]
        if sg in T or len(st) != 3:
            continue
        tau = fs().union(*[s - sg for s in st])
        if len(tau) != 3 or tau in faces(K, 3):
            continue
        new = [fs((sg | tau) - {a}) for a in sg]
        if any(n in K for n in new):
            continue
        return (K - set(st)) | set(new), set(T)
    return None


def collapsible(K, T):
    """The vertices, edges of K and the triangles T collapse to a point (IsGauge's collapsibility)."""
    cx = faces(K, 1) | faces(K, 2) | set(T)
    ch = True
    while ch and len(cx) > 1:
        ch = False
        for f in sorted(cx, key=lambda x: (-len(x), sorted(x))):
            cof = [g for g in cx if f < g and len(g) == len(f) + 1]
            if len(cof) == 1 and not any(f < g for g in cx if len(g) > len(f) + 1):
                cx -= {f, cof[0]}
                ch = True
                break
    return len(cx) == 1


def inverse_moves(K, T):
    """All 4-2 and 5-1 moves of (K, T) whose triangles to remove lie in T and leave a gauge set:
    yield (name, K', T')."""
    for e in faces(K, 2):
        st = [s for s in K if e <= s]
        if len(st) == 4:
            tet = fs().union(*[s - e for s in st])
            if len(tet) == 4 and all(len(s - e) == 3 for s in st):
                p, q = sorted(e)
                K2 = (K - set(st)) | {tet | {p}, tet | {q}}
                for a in tet:
                    f = fs({p, q, a})
                    if f in T and collapsible(K2, T - {f}):
                        yield "42", K2, T - {f}
    for v in {x for s in K for x in s}:
        st = [s for s in K if v in s]
        if len(st) == 5:
            link = fs().union(*[s - {v} for s in st])
            if len(link) == 5 and all(len(s - {v}) == 4 for s in st):
                for a0 in link:
                    fl = {fs({v, a0, x}) for x in link - {a0}}
                    if fl <= T and collapsible((K - set(st)) | {link}, T - fl):
                        yield "51", (K - set(st)) | {link}, T - fl


def start():
    K = {fs(c) for c in itertools.combinations(range(6), 5)}
    return K, {fs(t) for t in itertools.combinations(range(6), 3) if 5 in t}


def main():
    K0, T0 = start()
    assert forces(K0, T0)
    fail = Counter()
    ok = Counter()
    # control 1: removing one triangle of T stops it forcing, for every choice
    assert all(not forces(K0, T0 - {f}) for f in T0), "control: a triangle removed must break forcing"
    for sd in range(60):
        rng = random.Random(sd)
        K, T, nv = K0, T0, 6
        for _ in range(40):
            r = rng.choice(["15", "24", "33", "33"])
            if r == "15":
                K, T = m15(K, T, nv, rng)
                nv += 1
            else:
                o = (m24 if r == "24" else m33)(K, T, rng)
                if not o:
                    continue
                K, T = o
            (ok if forces(K, T) else fail)[r] += 1
            for name, K2, T2 in inverse_moves(K, T):
                (ok if forces(K2, T2) else fail)[name] += 1
    # control 2: the 2-4 move without the added triangle must lose forcing sometimes
    wrong = Counter()
    for sd in range(60):
        rng = random.Random(sd)
        K, T, nv = K0, T0, 6
        for _ in range(3):
            K, T = m15(K, T, nv, rng)
            nv += 1
        o = m24(K, T, rng, add=False)
        if o:
            wrong[forces(*o)] += 1
    print("inverse moves (4-2, 5-1) that lose forcing are a finding, not a failure")
    print("forcing kept:", dict(ok), "forcing lost:", dict(fail), "wrong rule (no added triangle):", dict(wrong))
    needed = ["15", "24", "33", "42", "51"]
    if any(ok[x] == 0 for x in needed):
        print("a move type never occurred")
        return 1
    if wrong[False] == 0:
        print("control failed: the wrong 2-4 rule keeps forcing")
        return 1
    return 1 if any(fail[x] for x in ('15', '24', '33')) else 0


if __name__ == "__main__":
    sys.exit(main())
