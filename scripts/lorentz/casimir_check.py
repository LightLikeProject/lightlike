"""Numerical cross-check of the two Casimirs of the SL(2,C) principal series (milestone HA1).

The representation acts on functions on C^2 by F -> F(g^T z). Its generators on smooth functions
are dpi(X)F(z) = DF_z(X^T z) (real derivative). With K_a = sigma_a/2 and J_a = i sigma_a/2,

    C1 = sum_a dpi(K_a)^2 - dpi(J_a)^2,     C2 = -sum_a dpi(J_a) dpi(K_a).

On F homogeneous of degree (-1+i rho+k, -1+i rho-k), i.e. F(lam z) = |lam|^(2 i rho-2) (lam/|lam|)^(2k) F(z),
the literature (Ruhl 1970; Barrett et al. 2010) gives C1 = k^2 - rho^2 - 1 and C2 = k rho.

Test functions: F = N^s * z0^p * conj(z1)^q with N = |z0|^2+|z1|^2, p - q = 2k, s = i rho - 1 - (p+q)/2,
evaluated at random points. Control: the same operators on a function of a different degree must
give different values. This is numerical evidence, not proof.
"""
import random
import sys

import sympy as sp

x0, y0, x1, y1 = sp.symbols('x0 y0 x1 y1', real=True)
z = [x0 + sp.I*y0, x1 + sp.I*y1]
coords = [x0, y0, x1, y1]

def D(F, v):
    """Real directional derivative of F at the symbolic point along the complex vector field v(z)."""
    # direction in real coordinates: (Re v0, Im v0, Re v1, Im v1)
    dirs = [sp.re(v[0]), sp.im(v[0]), sp.re(v[1]), sp.im(v[1])]
    return sum(sp.diff(F, c) * d for c, d in zip(coords, dirs))

def act(X, F):
    XT = sp.Matrix(X).T
    v = XT * sp.Matrix(z)
    return D(F, [sp.expand(v[0]), sp.expand(v[1])])

s1 = [[0, 1], [1, 0]]
s2 = [[0, -sp.I], [sp.I, 0]]
s3 = [[1, 0], [0, -1]]
K = [sp.Matrix(s)/2 for s in (s1, s2, s3)]
J = [sp.I*sp.Matrix(s)/2 for s in (s1, s2, s3)]

def casimirs(F):
    C1 = sum(act(Ka, act(Ka, F)) - act(Ja, act(Ja, F)) for Ka, Ja in zip(K, J))
    C2 = -sum(act(Ja, act(Ka, F)) for Ka, Ja in zip(K, J))
    return C1, C2

def test(p, q, rho, s_shift=0):
    k = sp.Rational(p - q, 2)
    s = sp.I*rho - 1 - sp.Rational(p + q, 2) + s_shift
    N = x0**2 + y0**2 + x1**2 + y1**2
    F = sp.exp(s*sp.log(N)) * z[0]**p * sp.conjugate(z[1])**q
    C1, C2 = casimirs(F)
    pt = {c: sp.Rational(random.randint(1, 9), random.randint(1, 9)) for c in coords}
    Fv = complex(sp.N(F.subs(pt)))
    c1 = complex(sp.N(C1.subs(pt))) / Fv
    c2 = complex(sp.N(C2.subs(pt))) / Fv
    return k, c1, c2

random.seed(1)
ok = True
for (p, q, rho) in [(0, 0, sp.Rational(1, 3)), (2, 0, sp.Rational(3, 2)), (1, 0, 2), (1, 3, sp.Rational(-1, 2)), (3, 1, sp.Rational(5, 7))]:
    k, c1, c2 = test(p, q, rho)
    e1 = float(k**2 - rho**2 - 1)
    e2 = float(k*rho)
    good = abs(c1 - e1) < 1e-9 and abs(c2 - e2) < 1e-9
    ok &= good
    print(f"p={p} q={q} k={k} rho={rho}: C1={c1:.10f} (expect {e1:.10f})  C2={c2:.10f} (expect {e2:.10f})  {'OK' if good else 'FAIL'}")

# Control: wrong homogeneity degree (s shifted by 1/2) gives a different C1.
k, c1, c2 = test(2, 0, sp.Rational(3, 2), s_shift=sp.Rational(1, 2))
e1 = float(k**2 - sp.Rational(9, 4) - 1)
control = abs(c1 - e1) > 1e-3
print(f"control (wrong degree): C1={c1:.6f} vs principal-series value {e1:.6f}: {'differs (OK)' if control else 'SAME (FAIL)'}")
print("ALL OK" if ok and control else "FAILED")
sys.exit(0 if ok and control else 1)
