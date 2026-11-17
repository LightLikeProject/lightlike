"""Numerical check (not a proof): the gauge set carried along from the boundary of the 5-simplex by
forward Pachner moves is robust.

A set T of triangles is *robust* for a complex K if it forces every triangle of K with any one
tetrahedron removed (`Lightlike.SpinFoam.Robust`). The 1-5 case of "robust sets stay robust" is proved
in Lean (`robust_move15`); for the 3-3 move it is false in general (the pinned counterexample below, also proved in Lean:
`robust_not_kept_by_move33`), and for the 2-4 move a random search found a counterexample, while a robust set keeps forcing under both (`forces_move24_of_robust`,
`forces_move33_of_robust`). Here, for random 4-spheres
reached from the boundary of the 5-simplex by `STEPS` forward moves (1-5, 2-4, 3-3, with the gauge set
carried along as in `forcechain.py`), for each seed:

1. the carried set is robust after every move (counted per move kind);
2. every tetrahedron of the final complex is checked separately (counted);
3. at every 3-3 location with the moved triangle not in T, the closure of T under the tetrahedra
   without that triangle is complete (the condition of the 3-3 characterization).

Controls: the pinned counterexample of `forcechain.py` (a collapsible forcing set that loses forcing
under a 3-3 move) is not robust; a set with one triangle removed from the carried set is not robust.
Observed totals (longer runs of the same code, not reproduced here): 1,104,480 of 1,104,480
tetrahedra, 38,176 of 38,176 3-3 locations, 822 of 822 consecutive moves. This is numerical evidence,
not a proof, and it concerns the carried set only: it is not evidence for existence of forcing gauge
sets in general.
Exit code 0 when every count above holds and the controls fail as they should.
"""
import itertools
import os
import random
import sys
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import forcechain as F

fs = frozenset
STEPS = 12


def closure_tets(T, tets):
    Z, ch = set(T), True
    while ch:
        ch = False
        for t in tets:
            miss = [f for f in map(fs, itertools.combinations(sorted(t), 3)) if f not in Z]
            if len(miss) == 1:
                Z.add(miss[0])
                ch = True
    return Z


def closed4(K):
    """Every tetrahedron of K lies in exactly two 4-simplices (a closed 4-manifold triangulation)."""
    cnt = Counter(fs(c) for x in K for c in itertools.combinations(sorted(x), 4))
    return set(cnt.values()) == {2}


def robust(K, T):
    tets, tris = F.faces(K, 4), F.faces(K, 3)
    return all(tris <= closure_tets(T, tets - {t}) for t in tets)


# A pinned counterexample to "robust sets stay robust under the 3-3 move": a 4-sphere with 20
# simplices on 8 vertices, a set T of 23 triangles that is robust for K, and the 3-3 move
# sigma = {3, 6, 7} -> tau = {0, 2, 4} (sigma not in T) after which T is not robust: removing the common
# tetrahedron {0, 2, 3, 6} breaks forcing (found by random search, seed 6434 of the search in the
# pull request; the pair {0, 2, 3, 6}, {0, 3, 6, 7} breaks forcing already in K).
CEX_K = [[0, 1, 2, 3, 5], [0, 1, 2, 3, 6], [0, 1, 2, 5, 7], [0, 1, 2, 6, 7], [0, 1, 3, 4, 5], [0, 1, 3, 4, 6], [0, 1, 4, 5, 6], [0, 1, 5, 6, 7], [0, 2, 3, 5, 7], [0, 2, 3, 6, 7], [0, 3, 4, 5, 7], [0, 3, 4, 6, 7], [0, 4, 5, 6, 7], [1, 2, 3, 4, 5], [1, 2, 3, 4, 6], [1, 2, 4, 5, 6], [1, 2, 5, 6, 7], [2, 3, 4, 5, 7], [2, 3, 4, 6, 7], [2, 4, 5, 6, 7]]
CEX_T = [[0, 1, 3], [0, 1, 4], [0, 1, 7], [0, 2, 5], [0, 2, 6], [0, 3, 4], [0, 3, 5], [0, 3, 7], [0, 4, 5], [0, 4, 6], [0, 5, 6], [0, 6, 7], [1, 2, 4], [1, 2, 7], [1, 3, 5], [1, 3, 6], [1, 4, 5], [1, 6, 7], [2, 3, 6], [2, 3, 7], [2, 4, 7], [3, 4, 6], [5, 6, 7]]
CEX_SIGMA, CEX_TAU = fs({3, 6, 7}), fs({0, 2, 4})


def counterexample_robust_33():
    """K is a 4-sphere, T is robust for K, sigma is not in T, and T is not robust after the move."""
    K = {fs(s) for s in CEX_K}
    T = {fs(t) for t in CEX_T}
    st = [s for s in K if CEX_SIGMA <= s]
    new = [fs((CEX_SIGMA | CEX_TAU) - {a}) for a in CEX_SIGMA]
    legal = (len(st) == 3 and fs().union(*[s - CEX_SIGMA for s in st]) == CEX_TAU
             and CEX_SIGMA not in T and closed4(K))
    K2 = (K - set(st)) | set(new)
    return legal and closed4(K2) and robust(K, T) and not robust(K2, T)


def main(nseeds=12):
    c = Counter()
    for sd in range(nseeds):
        rng = random.Random(sd)
        K, T, nv = F.start()[0], F.start()[1], 6
        for _ in range(STEPS):
            r = rng.choice(["15", "24", "33"])
            if r == "15":
                K, T = F.m15(K, T, nv, rng)
                nv += 1
            else:
                o = (F.m24 if r == "24" else F.m33)(K, T, rng)
                if not o:
                    continue
                K, T = o
            c[(r, "robust after the move", robust(K, T))] += 1
        tets, tris = F.faces(K, 4), F.faces(K, 3)
        for t in tets:
            c[("final complex", "tetrahedron checked", tris <= closure_tets(T, tets - {t}))] += 1
        for sg, tau, K2 in F.moves33(K):
            if sg in T:
                continue
            A = closure_tets(T, {t for t in tets if not sg <= t})
            c[("3-3 location", "closure without the moved triangle complete", (tris - {sg}) <= A)] += 1
        if sd == 0:
            c[("control", "one triangle removed from T is not robust",
               not robust(K, T - {sorted(T, key=sorted)[0]}))] += 1
    c[("control", "pinned counterexample: robust for K, not robust after the 3-3 move",
       counterexample_robust_33())] += 1
    K = {fs(x) for x in F.CEX_K}
    T = {fs(x) for x in F.CEX_T}
    c[("control", "the pinned counterexample of forcechain.py is not robust", not robust(K, T))] += 1
    for k in sorted(c, key=str):
        print(k, c[k])
    ok = all(k[2] for k in c)
    print("OK" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
