"""Numerical check (not a proof): the cut-off state sum of a gauge set that obeys the gauge rule but
does not force every triangle has no limit.

Complex and gauge set: those of `gauge_manifold_check.py` (a closed triangulation of the 4-sphere with
24 4-simplices; a collapsible gauge set T of 25 triangles that forces only 38 of the 62 triangles, so 24
triangles stay free). With the doubled spins of the free triangles at most C, the admissible colourings
are few (1, 3, 7, 12, 19, ... for C = 1, 2, 4, 6, 8, ...), every tetrahedron has a single virtual spin, and
the state sum factorises over the closed-form vertex amplitudes of `vertex_check.py`.

Result (exact 3j symbols, double-precision contraction; the rounding error of the contraction has
not been bounded): the state sum at doubled cutoff
C = 2, 4, ..., 34 is
3.5, 2.43, -3.40, -6.00, 1.28, 11.64, 10.81, -3.80, -16.10, -9.06, 12.39, 23.59, 8.57, -18.14, -25.31,
-1.53, 28.20: it changes sign (9 times in these values) and its size grows. Numerically, then, the
cutoff sums do not settle for this gauge set. This is an observation, not a proof (no limit statement
is proved), and the floating-point sums of the first version of this script, which used `vertex_check`'s
float 3j symbols, are wrong above C = 18 (the Racah sum loses all digits).
Checks (default CMAX = 24): C = 1 gives 1 and C = 2 gives 3.5 (as in `gauge_manifold_check.py`), the
sequence changes sign at least three times, and its largest absolute value for C >= 12 exceeds the
largest for C <= 8. Run with an argument to go higher: `python3 gauge_cutoff_limit.py 40`.
"""
import itertools
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import exact3j
import gauge_manifold_check as G
import vertex_check as vc

vc.threej = exact3j.threej_exact  # exact Racah sums; the float version loses all digits above spin ~10
vc.fourj.cache_clear()

CMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 24


def main():
    simp = [tuple(s) for s in G.SIMP]
    V, E, Tr, Te = (G.faces(simp, k) for k in (1, 2, 3, 4))
    T = {frozenset(t) for t in G.T0}
    assert T <= Tr and len(T) == len(E) - len(V) + 1 and G.collapsible(V | E | T)
    U = sorted(Tr - G.closure(simp, T), key=sorted)
    tetl = [G.legs(t) for t in Te]
    idx = {u: i for i, u in enumerate(U)}
    seq = {}
    for C in [1] + list(range(2, CMAX + 1, 2)):
        sols = []

        def val(g, asg):
            return asg.get(idx[g]) if g in idx else 0

        def en(i, asg):
            for tt in tetl:
                v = [val(g, asg) for g in tt]
                if None not in v and not any(G.tri(v[0], v[1], k) and G.tri(k, v[2], v[3])
                                             for k in range(2 * C + 1)):
                    return
            if i == len(U):
                sols.append(dict(asg))
                return
            for x in range(C + 1):
                asg[i] = x
                en(i + 1, asg)
                del asg[i]
        en(0, {})
        tot = 0.0
        for s in sols:
            col = {g: 0 for g in Tr}
            for u, i in idx.items():
                col[u] = s[i]
            w = 1.0
            for g in Tr:
                w *= col[g] + 1
            for sm in simp:
                Jd = {frozenset((a, b)): col[frozenset(sm) - {sm[a], sm[b]}]
                      for a, b in itertools.combinations(range(5), 2)}
                ks = []
                for i in range(5):
                    wv = [x for x in range(5) if x != i]
                    sp = [Jd[frozenset((i, q))] for q in (wv[0], wv[2], wv[1], wv[3])]
                    ks.append([k for k in range(2 * C + 1)
                               if G.tri(sp[0], sp[1], k) and G.tri(k, sp[2], sp[3])])
                w *= sum(vc.amp_closed(Jd, list(K)) for K in itertools.product(*ks))
            tot += w
        seq[C] = tot
        print('doubled cutoff', C, ': colourings', len(sols), ', state sum', round(tot, 6), flush=True)
    evens = [seq[C] for C in range(2, CMAX + 1, 2)]
    flips = sum(1 for a, b in zip(evens, evens[1:]) if a * b < 0)
    small = max(abs(seq[C]) for C in range(2, 9, 2))
    large = max(abs(seq[C]) for C in range(12, CMAX + 1, 2))
    ok = abs(seq[1] - 1) < 1e-9 and abs(seq[2] - 3.5) < 1e-9 and flips >= 3 and large > small
    print('sign changes', flips, '; max |sum| for C <= 8:', round(small, 3), '; for C >= 12:',
          round(large, 3))
    print('OK' if ok else 'FAIL')
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
