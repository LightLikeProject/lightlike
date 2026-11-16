"""Numerical check (not a proof) of the oscillation frequency of the Lorentzian vertex amplitude
against the published numerics: eq. (53) of Barrett, Dowdall, Fairbairn, Hellmann, Pereira
(arXiv:0907.2440, Sec. 6.4 p. 30) says that for the Regge state of a Lorentzian 4-simplex the
amplitude oscillates as exp(+-i lambda gamma sum_{a<b} k_ab Theta_ab); Table 6 of Dona, Fanizza,
Sarno, Speziale (arXiv:1903.12624, Phys. Rev. D 100 (2019) 106003, p. 26) fits the rescaled amplitude
lambda^12 A_v of the Lorentzian Regge data of its Table 1 (four spins 5 lambda on one tetrahedron,
six spins 2 lambda) by |N| cos(Omega lambda + phi) for gamma = 0.1, 1.2, 7, 8 with
Omega = 0.963e-2, 0.116, 0.674, 0.770.

Construction (a symmetric Lorentzian 4-simplex, all five tetrahedra spacelike): a regular tetrahedron
T of edge a in the hyperplane t = 0, and an apex at (h, 0, 0, 0) above its centre. The four triangles
of T have area 5, the six triangles with the apex have area 2 (this fixes a and h; the small
root h is used). The dihedral (boost) angles are Theta_ab = arccosh |n_a . n_b| for the unit normals of
the tetrahedra. The Regge sum is sum_{a<b} k_ab Theta_ab with the sign + on the four thin angles
(the hinges of area 5) and - on the six others, the type 4-1 signs of Table 5 of the source. We check
that Omega / gamma = sum k Theta = 0.09629 matches the four published frequencies to the digits
published, and that the wrong sign pattern (all +) does not.
What this checks, and what it does not: only the FREQUENCY of the oscillation (the coefficient of
lambda in the phase). The amplitude |N| and the global phase are not compared. The source states that
it did not reproduce the global phase from the analytic formula (its footnote 17, p. 25), and |N|
needs the normalisation constants c_ab, Omega_ab of the vertex and det H; neither is attempted.
This is numerical evidence for the statement of eq. (53), not a proof.
Sources (keys of docs/tasks/sources.yaml): bdfhp-2010 (eq. (53)), dona-fanizza-sarno-speziale-2019
(Table 6, p. 26; Table 1, p. 8, for the spins).
Usage: python3 -I scripts/asymptotics/lorentzian_regge_frequency_check.py
"""
import sys
from itertools import combinations

import numpy as np
from scipy.optimize import brentq

ETA = np.diag([-1.0, 1, 1, 1])
PUBLISHED = {0.1: 0.963e-2, 1.2: 0.116, 7.0: 0.674, 8.0: 0.770}   # Table 6, coefficient of lambda
PUB_DIGITS = {0.1: 3, 1.2: 3, 7.0: 3, 8.0: 3}                      # significant digits published


def mdot(u, v):
    return u @ ETA @ v


def build(a, h):
    T = np.array([[1, 1, 1], [1, -1, -1], [-1, 1, -1], [-1, -1, 1]], float) * a / (2 * np.sqrt(2))
    return [np.array([0, *t]) for t in T] + [np.array([h, 0, 0, 0])]


def tri_area(P, ids):
    u, v = P[ids[1]] - P[ids[0]], P[ids[2]] - P[ids[0]]
    return 0.5 * np.sqrt(abs(mdot(u, u) * mdot(v, v) - mdot(u, v) ** 2))


def regge_sum(area_t=5.0, area_apex=2.0):
    a = np.sqrt(4 * area_t / np.sqrt(3))
    f = lambda h: tri_area(build(a, h), (0, 1, 4)) - area_apex
    hs = np.linspace(0.0, 0.9, 91)
    h = next(brentq(f, hs[i], hs[i + 1]) for i in range(90) if f(hs[i]) * f(hs[i + 1]) < 0)
    P = build(a, h)
    N = []
    for k in range(5):
        o = [P[b] for b in range(5) if b != k]
        M = np.array([x - o[0] for x in o[1:]])
        n = np.linalg.svd(M @ ETA)[2][-1]
        N.append(n / np.sqrt(abs(mdot(n, n))))
        assert mdot(N[-1], N[-1]) < 0, "tetrahedron not spacelike"
    plus = minus = 0.0
    for (i, j) in combinations(range(5), 2):
        tri = tuple(sorted(set(range(5)) - {i, j}))
        ar = tri_area(P, tri)
        th = np.arccosh(abs(mdot(N[i], N[j])))
        if abs(ar - area_t) < 1e-6:
            plus += ar * th          # thin angles: hinges of area 5
        else:
            minus += ar * th
    return plus - minus, plus + minus, h


def main():
    s, s_all, h = regge_sum()
    print(f"apex height h = {h:.6f}; sum k Theta (type 4-1 signs) = {s:.6f}; with all + signs: {s_all:.4f}")
    ok = True
    for g, om in PUBLISHED.items():
        pred = g * s
        rel = abs(pred - om) / om
        good = rel < 6e-3          # the published digits: 3 significant (5e-3 relative at worst)
        print(f"  gamma = {g}: predicted Omega = gamma * sum = {pred:.5f}, Table 6: {om}; relative difference {rel:.1e}: "
              f"{'ok' if good else 'FAIL'}")
        ok = ok and good
    bad = [abs(g * s_all - om) / om > 1.0 for g, om in PUBLISHED.items()]
    print(f"control: the all-plus sign pattern is off by more than 100% for every gamma: {'detected' if all(bad) else 'NOT detected'}")
    s2, _, _ = regge_sum(5.0, 1.8)
    c2 = abs(s2 - s) / s > 0.1
    print(f"control: other area ratio (5 : 1.8) gives sum = {s2:.5f}, not {s:.5f}: {'detected' if c2 else 'NOT detected'}")
    ok = ok and all(bad) and c2
    print("OK" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
