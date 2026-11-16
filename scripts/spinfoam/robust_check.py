"""Numerical check (not a proof): the gauge set carried along from the boundary of the 5-simplex by
forward Pachner moves is robust.

A set T of triangles is *robust* for a complex K if it forces every triangle of K with any one
tetrahedron removed (`Lightlike.SpinFoam.Robust`). The 1-5 case of "robust sets stay robust" is proved
in Lean (`robust_move15`); for the 3-3 and 2-4 moves it is a conjecture. Here, for random 4-spheres
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
not a proof, and it is evidence for the conjecture, not for existence of forcing gauge sets in general.
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


def robust(K, T):
    tets, tris = F.faces(K, 4), F.faces(K, 3)
    return all(tris <= closure_tets(T, tets - {t}) for t in tets)


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
