"""Exact (sympy) check of the 3D wrong-model control of the linearized Regge coefficient.

For the Kuhn star, each of the 36 incidences (sigma, h) contributes `-(qf H hv) / (2 |hv|^2) * dth_h(rf dd)` to the
hinge density, where `hv` is the hinge vector, `dth_h` the linear form of the first variation of the dihedral angle times the
hinge length, and `rf dd` the second-order squared-length increments (Lightlike/Regge/Linear3/SaintVenantCore.lean).
With the weights 1/|hv|^2 the sum is the Saint-Venant density `-1/4 svPair`; with the weights replaced by 1 (no volume
weights) it is a different density.  For the test field h = cos(2 pi y0) E12 (E12 symmetric with 1 at (1,2) and (2,1)):
  correct density  = -2 pi^2 cos^2(2 pi y0),  cube integral -pi^2      (= the integral of the Fierz-Pauli density),
  wrong density    = -14/3 pi^2 cos^2(2 pi y0), cube integral -7 pi^2/3.
The Lean statements are in Lightlike/Regge/Linear3/EtaCoefficientTests.lean; this script is exact-arithmetic evidence for them."""
import sympy as sp
from sympy import pi, cos, Rational as R

kv = [(0, 0, 0), (1, 0, 0), (1, 1, 0), (1, 1, 1)]
perms = [(0, 1, 2), (0, 2, 1), (1, 0, 2), (1, 2, 0), (2, 0, 1), (2, 1, 0)]
hP = [0, 0, 0, 1, 1, 2]; hQ = [1, 2, 3, 2, 3, 3]; hR = [2, 1, 1, 0, 0, 0]; hS = [3, 3, 2, 3, 2, 1]
dth = [
    lambda x: -x[4] / 4 + x[5] / 2,
    lambda x: x[0] / 2 - x[3] / 2 - x[2] - x[4] / 2 + x[5],
    lambda x: x[0] / 2 - R(3, 4) * x[3] - R(3, 4) * x[2] + R(3, 2) * x[5],
    lambda x: x[0] / 2 - x[3] / 2 - x[2] / 2 + x[5] / 2,
    lambda x: x[0] / 2 - x[1] / 2 - x[3] - x[2] / 2 + x[5],
    lambda x: -x[1] / 4 + x[5] / 2,
]
y0 = sp.Symbol("y0")
c = cos(2 * pi * y0)
H = lambda i, j: c if {i, j} == {1, 2} else 0
def dd(k, l, i, j): return -(2 * pi) ** 2 * c if (k, l) == (0, 0) and {i, j} == {1, 2} else 0
def kpos(s, h, a): return [R(kv[a][perms[s][i]]) - R(kv[hP[h]][perms[s][i]] + kv[hQ[h]][perms[s][i]], 2) for i in range(3)]
def ddq(S, T, X): return sum(S[k] * T[l] * dd(k, l, i, j) * X[i] * X[j] for k in range(3) for l in range(3) for i in range(3) for j in range(3))
def rf(S, X): return ddq(S, S, X) / 2 + ddq(X, X, X) / 24
def qf(X): return sum(X[i] * H(i, j) * X[j] for i in range(3) for j in range(3))
def density(weighted):
    tot = 0
    for s in range(6):
        for h in range(6):
            p = [kpos(s, h, a) for a in range(4)]
            x = []
            for (a, b) in [(hP[h], hQ[h]), (hP[h], hR[h]), (hQ[h], hR[h]), (hP[h], hS[h]), (hQ[h], hS[h]), (hR[h], hS[h])]:
                mid = [(p[a][i] + p[b][i]) / 2 for i in range(3)]
                D = [p[b][i] - p[a][i] for i in range(3)]
                x.append(rf(mid, D))
            hv = [R(kv[hQ[h]][perms[s][i]] - kv[hP[h]][perms[s][i]]) for i in range(3)]
            hb = sum(v ** 2 for v in hv)
            tot += -qf(hv) / (2 * (hb if weighted else 1)) * dth[h](x)
    return sp.simplify(tot)
right, wrong = density(True), density(False)
I = lambda f: sp.simplify(sp.integrate(f, (y0, 0, 1)))
assert sp.simplify(right + 2 * pi ** 2 * c ** 2) == 0 and I(right) == -pi ** 2
assert sp.simplify(wrong + R(14, 3) * pi ** 2 * c ** 2) == 0 and I(wrong) == -R(7, 3) * pi ** 2
assert I(wrong) != I(right)
print("OK: correct density integrates to -pi^2, the density without volume weights to -7 pi^2/3 (different)")
