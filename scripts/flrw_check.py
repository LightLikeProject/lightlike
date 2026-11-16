"""Cross-check for the FLRW chart of Lightlike/Cosmology/FLRW.lean (CO1).

Conventions of Lightlike/Spacetime/Curvature.lean:
  Gamma^i_{jk} = 1/2 g^{il} (d_j g_{lk} + d_k g_{lj} - d_l g_{jk})
  R^r_{s m n} = d_m Gamma^r_{n s} - d_n Gamma^r_{m s} + Gamma^r_{m l} Gamma^l_{n s} - Gamma^r_{n l} Gamma^l_{m s}
  R_{s n} = R^r_{s r n},  G = Ric - (1/2) R g

Metric (signature -+++): -dt^2 + a(t)^2 dx^2 / (1 + k |x|^2 / 4)^2, any real k.

Checks (numerical evidence, not proof; the values to reproduce are Carroll, Lecture Notes on
General Relativity (1997), eqs. (8.29), (8.33) to (8.36)):
  1. R_00 = -3 a''/a, R_0i = 0, R_ij = (a''/a + 2 a'^2/a^2 + 2k/a^2) g_ij.
  2. G_00 = 3 (a'^2 + k)/a^2, G_ij = -(2 a''/a + a'^2/a^2 + k/a^2) g_ij.
  3. G + Lam g = 8 pi Gn T for T = (rho + p) u u + p g gives Friedmann's first and second equations.
  4. Control: the metric with (1 - k |x|^2/4) in place of (1 + k |x|^2/4) does NOT satisfy 1 and 2.
Run: python3 -I scripts/flrw_check.py
"""
import sympy as sp

t, x, y, z, k, Lam, Gn = sp.symbols("t x y z k Lambda G", real=True)
a = sp.Function("a", positive=True)(t)
rho = sp.Function("rho")(t)
p = sp.Function("p")(t)
X = [t, x, y, z]
r2 = x**2 + y**2 + z**2


def curvature(sign):
    psi = a / (1 + sign * k * r2 / 4)
    g = sp.diag(-1, psi**2, psi**2, psi**2)
    gi = g.inv()
    G3 = [[[sum(gi[i, l] * (sp.diff(g[l, kk], X[j]) + sp.diff(g[l, j], X[kk])
                            - sp.diff(g[j, kk], X[l])) for l in range(4)) / 2
            for kk in range(4)] for j in range(4)] for i in range(4)]

    def Riem(rr, s, m, n):
        return (sp.diff(G3[rr][n][s], X[m]) - sp.diff(G3[rr][m][s], X[n])
                + sum(G3[rr][m][l] * G3[l][n][s] - G3[rr][n][l] * G3[l][m][s]
                      for l in range(4)))

    Ric = sp.Matrix(4, 4, lambda s, n: sp.simplify(sum(Riem(rr, s, rr, n) for rr in range(4))))
    R = sp.simplify(sum(gi[i, j] * Ric[i, j] for i in range(4) for j in range(4)))
    Ein = (Ric - R * g / 2).applyfunc(sp.simplify)
    return g, Ric, Ein


def expected(g):
    ad, add = sp.diff(a, t), sp.diff(a, t, 2)
    Ric = sp.zeros(4, 4)
    Ein = sp.zeros(4, 4)
    Ric[0, 0] = -3 * add / a
    Ein[0, 0] = 3 * (ad**2 + k) / a**2
    for i in range(1, 4):
        Ric[i, i] = (add / a + 2 * ad**2 / a**2 + 2 * k / a**2) * g[i, i]
        Ein[i, i] = -(2 * add / a + ad**2 / a**2 + k / a**2) * g[i, i]
    return Ric, Ein


def matches(sign):
    g, Ric, Ein = curvature(sign)
    eR, eE = expected(g)
    return (Ric - eR).applyfunc(sp.simplify) == sp.zeros(4, 4) and \
           (Ein - eE).applyfunc(sp.simplify) == sp.zeros(4, 4), g, Ein


ok, g, Ein = matches(+1)
assert ok, "checks 1 and 2 fail for the FLRW chart"
print("1, 2: Ricci and Einstein tensors of the FLRW chart agree with the closed forms")

# 3. Einstein equations with a perfect fluid at rest: u^mu = (1,0,0,0), u_mu = g_{mu 0}.
ad, add = sp.diff(a, t), sp.diff(a, t, 2)
T00 = rho
Tii = p * g[1, 1]
e00 = sp.simplify(Ein[0, 0] + Lam * g[0, 0] - 8 * sp.pi * Gn * T00)
eii = sp.simplify(Ein[1, 1] + Lam * g[1, 1] - 8 * sp.pi * Gn * Tii)
fried1 = (ad / a) ** 2 - (8 * sp.pi * Gn / 3 * rho - k / a**2 + Lam / 3)
fried2 = add / a - (-(4 * sp.pi * Gn / 3) * (rho + 3 * p) + Lam / 3)
assert sp.simplify(e00 / 3 - fried1) == 0, "00 component is not Friedmann's first equation"
# ij component = -(1/ g_ii) ... equals -(2 fried2 + fried1) after dividing by g_ii
assert sp.simplify(eii / g[1, 1] + 2 * fried2 + fried1) == 0, "ij component mismatch"
print("3: the 00 component is Friedmann's first equation; the ij component is 2*second + first")

# 4. Control: the wrong sign of k in the chart factor breaks 1 and 2.
bad, _, _ = matches(-1)
assert not bad, "control failed: the wrong-sign chart satisfies the identities"
print("4: control OK: the chart with the opposite sign of k fails the identities")
