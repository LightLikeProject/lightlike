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


def direct_forcing_gauge(K, rng, tries=20):
    """A forcing gauge set found directly: a random minimal forcing set of the right size
    E - V + 1 that is collapsible (None if none is found)."""
    tris = sorted(faces(K, 3), key=sorted)
    target = len(faces(K, 2)) - len(faces(K, 1)) + 1
    for _ in range(tries):
        rng.shuffle(tris)
        T = set(tris)
        for f in tris:
            if forces(K, T - {f}):
                T.discard(f)
        if len(T) == target and collapsible(K, T):
            return T
    return None


# A pinned counterexample (found by random search over forcing sets of random complexes reachable
# from the boundary of the 5-simplex): a collapsible forcing gauge set T of size E - V + 1 on a closed
# 4-manifold triangulation with 48 simplices, and a 3-3 move (sigma = {1,4,5}, tau = {0,6,9}) after which
# the same T no longer forces: forcing is not preserved by 3-3 for every forcing gauge set.
CEX_K = [[0, 1, 2, 4, 7], [0, 1, 2, 4, 9], [0, 1, 2, 5, 8], [0, 1, 2, 5, 9], [0, 1, 2, 7, 8], [0, 1, 3, 5, 6], [0, 1, 3, 5, 8], [0, 1, 3, 6, 7], [0, 1, 3, 7, 10], [0, 1, 3, 8, 10], [0, 1, 4, 5, 6], [0, 1, 4, 5, 9], [0, 1, 4, 6, 7], [0, 1, 7, 8, 11], [0, 1, 7, 10, 11], [0, 1, 8, 10, 11], [0, 2, 3, 4, 5], [0, 2, 3, 4, 7], [0, 2, 3, 5, 7], [0, 2, 4, 5, 9], [0, 2, 5, 7, 8], [0, 3, 4, 5, 6], [0, 3, 4, 6, 7], [0, 3, 5, 7, 10], [0, 3, 5, 8, 10], [0, 5, 7, 8, 10], [0, 7, 8, 10, 11], [1, 2, 3, 6, 7], [1, 2, 3, 6, 8], [1, 2, 3, 7, 8], [1, 2, 4, 6, 7], [1, 2, 4, 6, 9], [1, 2, 5, 6, 8], [1, 2, 5, 6, 9], [1, 3, 5, 6, 8], [1, 3, 7, 8, 10], [1, 4, 5, 6, 9], [1, 7, 8, 10, 11], [2, 3, 4, 5, 6], [2, 3, 4, 6, 12], [2, 3, 4, 7, 12], [2, 3, 5, 6, 8], [2, 3, 5, 7, 8], [2, 3, 6, 7, 12], [2, 4, 5, 6, 9], [2, 4, 6, 7, 12], [3, 4, 6, 7, 12], [3, 5, 7, 8, 10]]
CEX_T = [[0, 1, 4], [0, 1, 5], [0, 1, 7], [0, 1, 8], [0, 2, 3], [0, 2, 5], [0, 2, 9], [0, 3, 6], [0, 3, 7], [0, 4, 6], [0, 6, 7], [0, 7, 11], [0, 10, 11], [1, 2, 6], [1, 2, 9], [1, 3, 5], [1, 3, 6], [1, 3, 10], [1, 4, 9], [1, 5, 9], [1, 6, 9], [1, 8, 11], [1, 10, 11], [2, 3, 4], [2, 3, 6], [2, 3, 8], [2, 4, 12], [2, 5, 6], [2, 5, 7], [2, 6, 8], [2, 7, 8], [3, 4, 5], [3, 4, 6], [3, 4, 7], [3, 5, 10], [3, 7, 8], [3, 7, 10], [3, 7, 12], [3, 8, 10], [4, 5, 9], [4, 6, 12], [5, 6, 8], [6, 7, 12], [7, 10, 11], [8, 10, 11]]
CEX_SIGMA, CEX_TAU = fs({1, 4, 5}), fs({0, 6, 9})


def sigma_not_needed(K, T, sigma):
    """True if the closure of T under the tetrahedra that do not contain the triangle `sigma` of a
    3-3 move reaches every triangle except `sigma`: no forcing step needs `sigma`. This is
    sufficient for T to force after the move (the new triangle tau is then forced by a new
    tetrahedron), and in all sampled cases it was also necessary."""
    tets = {t for t in faces(K, 4) if not sigma <= t}
    Z, ch = set(T), True
    while ch:
        ch = False
        for t in tets:
            miss = [f for f in map(fs, itertools.combinations(sorted(t), 3)) if f not in Z]
            if len(miss) == 1:
                Z.add(miss[0])
                ch = True
    return faces(K, 3) - {sigma} <= Z


def counterexample_33():
    """True if the pinned counterexample is valid: T forces on K, sigma not in T, the move is a 3-3 move
    of K, and T does not force after it."""
    K = {fs(s) for s in CEX_K}
    T = {fs(t) for t in CEX_T}
    st = [s for s in K if CEX_SIGMA <= s]
    new = [fs((CEX_SIGMA | CEX_TAU) - {a}) for a in CEX_SIGMA]
    legal = (len(st) == 3 and fs().union(*[s - CEX_SIGMA for s in st]) == CEX_TAU
             and CEX_TAU not in faces(K, 3) and not any(n in K for n in new) and CEX_SIGMA not in T)
    K2 = (K - set(st)) | set(new)
    return (legal and forces(K, T) and collapsible(K, T) and not forces(K2, T)
            and not sigma_not_needed(K, T, CEX_SIGMA))


def local_lemma_33():
    """Exhaustive check of the local lemma behind the characterization of 3-3 (computer-assisted proof).

    The six vertices of a 3-3 move are s0,s1,s2 (sigma) and c0,c1,c2 (tau). Of the 20 triangles,
    sigma and tau are the two that change; the other 18 are 'mixed' (m: two s and one c; n: two c and
    one s). The 9 tetrahedra with two s and two c lie in the complex before and after the move; before
    the move there are also the three tetrahedra sigma + c, after it the three tau + s.

    Lemma. Let W be a set of mixed triangles that is closed under the 9 common tetrahedra and contains
    all three m-triangles of some c (a 'full m-row') and all three n-triangles of some s (a 'full
    n-row'). Then the closure of W under the tetrahedra before the move, and under those after it,
    adds no mixed triangle: it adds only sigma, respectively tau.
    Returns the number of such W checked, and the number where the lemma fails (must be 0).
    """
    S, C = (0, 1, 2), (3, 4, 5)
    tri = lambda *x: fs(x)
    mixed = [t for t in map(fs, itertools.combinations(range(6), 3)) if t not in (fs(S), fs(C))]
    idx = {t: i for i, t in enumerate(mixed)}
    sg, tau = fs(S), fs(C)
    all_tets = [fs(c) for c in itertools.combinations(range(6), 4)]
    common = [t for t in all_tets if len(t & fs(S)) == 2]
    pre = [t for t in all_tets if len(t & fs(S)) == 3]
    post = [t for t in all_tets if len(t & fs(S)) == 1]

    def rule(t):
        return [fs(x) for x in itertools.combinations(sorted(t), 3)]

    def close(Z, tets):
        Z, ch = set(Z), True
        while ch:
            ch = False
            for t in tets:
                miss = [f for f in rule(t) if f not in Z]
                if len(miss) == 1:
                    Z.add(miss[0])
                    ch = True
        return Z

    rows_m = [[tri(S[i], S[j], c) for i, j in ((0, 1), (0, 2), (1, 2))] for c in C]
    rows_n = [[tri(C[i], C[j], x) for i, j in ((0, 1), (0, 2), (1, 2))] for x in S]
    checked = bad = 0
    for mask in range(1 << 18):
        W = {mixed[i] for i in range(18) if mask >> i & 1}
        if not (any(all(f in W for f in r) for r in rows_m) and any(all(f in W for f in r) for r in rows_n)):
            continue
        if close(W, common) != W:
            continue
        checked += 1
        if close(W, common + pre) - {sg} != W or close(W, common + post) - {tau} != W:
            bad += 1
    return checked, bad


def moves33(K):
    """All 3-3 moves of K: (sigma, tau, K after the move)."""
    tris = faces(K, 3)
    for sg in sorted(tris, key=sorted):
        st = [s for s in K if sg <= s]
        if len(st) != 3:
            continue
        tau = fs().union(*[s - sg for s in st])
        new = [fs((sg | tau) - {a}) for a in sg]
        if len(tau) == 3 and tau not in tris and not any(n in K for n in new):
            yield sg, tau, (K - set(st)) | set(new)


def minimal_forcing(K, rng):
    """A random minimal set of triangles that forces every triangle of K."""
    L = sorted(faces(K, 3), key=sorted)
    rng.shuffle(L)
    T = set(L)
    for f in L:
        if forces(K, T - {f}):
            T.discard(f)
    return T


def sampled_equivalence(seeds=25):
    """For random minimal forcing sets T (not nec. gauge sets) on random complexes and every 3-3 move
    with sigma not in T: T forces after the move iff `sigma_not_needed`. Returns the counts."""
    cnt = Counter()
    for sd in range(seeds):
        rng = random.Random(1000 + sd)
        K, T, nv = start()[0], None, 6
        for _ in range(rng.randrange(3, 20)):
            r = rng.choice(["15", "24", "33"])
            if r == "15":
                K, _ = m15(K, set(), nv, rng)
                nv += 1
            else:
                o = (m24 if r == "24" else m33)(K, set(), rng)
                if o:
                    K = o[0]
        for _ in range(2):
            T = minimal_forcing(K, rng)
            for sg, tau, K2 in moves33(K):
                if sg not in T:
                    cnt[(sigma_not_needed(K, T, sg), forces(K2, T))] += 1
    return cnt


def start():
    K = {fs(c) for c in itertools.combinations(range(6), 5)}
    return K, {fs(t) for t in itertools.combinations(range(6), 3) if 5 in t}


def main():
    K0, T0 = start()
    assert forces(K0, T0)
    fail = Counter()
    direct, seen = Counter(), set()
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
                good = forces(K2, T2)
                (ok if good else fail)[name] += 1
                if not good and sum(direct.values()) < 15 and fs(K2) not in seen:
                    seen.add(fs(K2))
                    direct[direct_forcing_gauge(K2, rng) is not None] += 1
    # a pinned counterexample: 3-3 does not preserve forcing for every forcing gauge set
    if not counterexample_33():
        print("the pinned 3-3 counterexample no longer holds")
        return 1
    print("pinned counterexample: a collapsible forcing set on a 48-simplex 4-sphere loses forcing under 3-3")
    checked, badl = local_lemma_33()
    print("local lemma for 3-3: patterns checked", checked, "failures", badl)
    if badl or not checked:
        return 1
    eq = sampled_equivalence()
    print("3-3 with T unchanged, (sigma not needed, T forces after the move):", dict(eq))
    if eq[(True, False)] or eq[(False, True)] or not eq[(True, True)]:
        print("the sufficient condition and forcing after 3-3 disagree")
        return 1
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
    print("complexes where the transported set fails, a forcing gauge set found directly:", dict(direct))
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
