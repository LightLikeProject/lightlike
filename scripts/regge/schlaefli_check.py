"""Symbolic check of the polynomial form of Schläfli's identity for a Euclidean tetrahedron.

Numerical/symbolic evidence, not proof. For the tetrahedron pqrs with squared edge lengths
x_pq, ..., x_rs it checks:
  1. N'_e is symmetric under p<->q and r<->s, where for the edge pq
     N'_pq = 2 x_pq (x_pr + x_ps - x_rs) - (x_pr + x_pq - x_qr)(x_ps + x_pq - x_qs),
     so that cos(theta_pq) = N'_pq / sqrt(H_pqr H_pqs), H = 16 * (area)^2 (Heron).
  2. H_pqr H_pqs - N'_pq^2 = 576 * x_pq * V^2, with V^2 the Cayley-Menger volume (vol2), so that
     sin(theta_pq) = 24 V l_pq / sqrt(H_pqr H_pqs).
  3. Schläfli: sum_e [2 dN'_e - N'_e (dH_F1/H_F1 + dH_F2/H_F2)] = 0 for d = d/dx_f, every edge f,
     which is equivalent to sum_e l_e d(theta_e) = 0.
  4. Control: the same sum with a deliberately wrong weight (exterior angle sign flipped on one
     edge, i.e. dropping one term) is NOT zero.
"""
import itertools
import sympy as sp

V = ['p', 'q', 'r', 's']
xs = {}
for a, b in itertools.combinations(V, 2):
    xs[frozenset((a, b))] = sp.Symbol('x_' + a + b, positive=True)
def x(a, b):
    return xs[frozenset((a, b))]

def H(a, b, c):
    A, B, C = x(a, b), x(b, c), x(c, a)
    return 2 * (A * B + B * C + C * A) - (A**2 + B**2 + C**2)

def Np(p, q, r, s):
    return 2 * x(p, q) * (x(p, r) + x(p, s) - x(r, s)) - (x(p, r) + x(p, q) - x(q, r)) * (x(p, s) + x(p, q) - x(q, s))

# vol2 as in Lightlike.PR.vol2 with a=AB,b=BC,c=CA,d=CD,e=AD,f=BD and A,B,C,D = p,q,r,s
a2, b2, c2, d2, e2, f2 = x('p','q'), x('q','r'), x('r','p'), x('r','s'), x('p','s'), x('q','s')
vol2 = (a2*d2*(-a2 - d2 + b2 + e2 + c2 + f2) + b2*e2*(a2 + d2 - b2 - e2 + c2 + f2)
        + c2*f2*(a2 + d2 + b2 + e2 - c2 - f2) - a2*b2*c2 - a2*e2*f2 - d2*b2*f2 - d2*e2*c2) / 144

edges = []
for (p, q) in itertools.combinations(V, 2):
    r, s = [v for v in V if v not in (p, q)]
    edges.append((p, q, r, s))

ok = True
for (p, q, r, s) in edges:
    sym1 = sp.expand(Np(p, q, r, s) - Np(q, p, r, s))
    sym2 = sp.expand(Np(p, q, r, s) - Np(p, q, s, r))
    sin_id = sp.expand(H(p, q, r) * H(p, q, s) - Np(p, q, r, s)**2 - 576 * x(p, q) * vol2)
    print(f"edge {p}{q}: N' symmetric: {sym1 == 0 and sym2 == 0};  H1 H2 - N'^2 - 576 x V^2 = {sin_id}")
    ok &= (sym1 == 0 and sym2 == 0 and sin_id == 0)

def schlaefli_sum(f, drop=None):
    tot = 0
    for (p, q, r, s) in edges:
        if drop == (p, q):
            continue
        N = Np(p, q, r, s)
        H1, H2 = H(p, q, r), H(p, q, s)
        tot += 2 * sp.diff(N, f) - N * (sp.diff(H1, f) / H1 + sp.diff(H2, f) / H2)
    return sp.simplify(sp.together(tot))

for f in xs.values():
    val = schlaefli_sum(f)
    print(f"d/d{f}: Schläfli sum = {val}")
    ok &= (val == 0)

ctrl = schlaefli_sum(x('p', 'q'), drop=('r', 's'))
print(f"control (one edge dropped), d/dx_pq: sum is zero? {ctrl == 0}")
ok &= (ctrl != 0)
print("ALL CHECKS PASS" if ok else "CHECK FAILED")
