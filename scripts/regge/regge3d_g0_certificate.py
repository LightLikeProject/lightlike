"""Exact (SymPy) certificate for the algebraic core of the 3D convergence in a general chart.

At a point where the chart metric has Gram matrix g0 (entries g00..g22) and the second-order jet of
the squared distances is encoded by a symmetric matrix B (the chart Ricci tensor, up to the factor
A^T ric A), the 36 incidences (tetrahedron, hinge) of the Kuhn triangulation give

    T = sum over incidences of (N' - N/2 (P1'/P1 + P2'/P2)) / k,

where P1, P2, N are the two face Gram polynomials and the cross term of the incidence in the squared
lengths, ' is the epsilon-derivative along the first-order term, and k is the integer determinant
of the tetrahedron's edge vectors.  Claims, each checked in exact rational arithmetic:
  (a) T det(g0) = det(g0) tr(adj(g0) B) / 2 as a rational function (the scalar curvature is
      R det g0 = tr(adj g0 B));
  (b) the six distinct face polynomials P_i are irreducible, and each divides its numerator, so the
      fractions are polynomials q_i and (a) is a polynomial identity;
  (c) the identity is linear in B: it holds for each of the six symmetric basis matrices;
  (d) control: dropping the scalar-curvature term of the second-order jet breaks (a).
Usage: python3 scripts/regge/regge3d_g0_certificate.py     (about 1 to 3 minutes)
Numerical or computer-algebra evidence, not a proof; the Lean statement is proved separately.
"""
import itertools
import sympy as sp
from sympy import Rational as Q_
g = sp.Matrix(3, 3, lambda i, j: sp.Symbol('g%d%d' % (min(i, j), max(i, j))))
bs = sp.symbols('b00 b01 b02 b11 b12 b22')
B = sp.Matrix([[bs[0], bs[1], bs[2]], [bs[1], bs[3], bs[4]], [bs[2], bs[4], bs[5]]])
detg = g.det(); adj = g.adjugate()
rho = (adj * B).trace()           # R det g
edges = [e for e in itertools.product((0, 1), repeat=3) if any(e)]
def star(edge):
    p, q = (0, 0, 0), tuple(edge); res = set()
    for c in itertools.product(range(-1, 2), repeat=3):
        for perm in itertools.permutations(range(3)):
            v = [tuple(c)]
            for k in perm:
                w = list(v[-1]); w[k] += 1; v.append(tuple(w))
            if p in v and q in v: res.add(tuple(v))
    return list(res)
def ip(M, a, b): return (sp.Matrix(a).T * M * sp.Matrix(b))[0]
DROP_R_TERM = False   # control: drop the scalar-curvature term of the second-order jet
def mhat(a, b):   # det(g) * m_ab,  m_ab = -(1/3) Rm(y,z,y,z),  R = rho/det(g)
    yy, zz, yz = ip(g, a, a), ip(g, b, b), ip(g, a, b)
    return -(detg * (yy * ip(B, b, b) - 2 * yz * ip(B, a, b) + zz * ip(B, a, a))
             - (0 if DROP_R_TERM else rho / 2) * (yy * zz - yz ** 2)) / 3

eps = sp.Symbol('eps')
def pieces(edge_list=None):
    """T_hat = detg * T as  poly + sum_P num_P / P  (dict P -> num_P); returns (poly, dict)."""
    poly = 0; nums = {}
    for e in (edge_list or edges):
        mid = [Q_(x, 2) for x in e]
        for vs in star(e):
            pos = [tuple(v[i] - mid[i] for i in range(3)) for v in vs]
            L0, m = {}, {}
            for i, j in itertools.combinations(range(4), 2):
                d = [pos[i][t] - pos[j][t] for t in range(3)]
                L0[(i, j)] = sp.expand(ip(g, d, d)); m[(i, j)] = sp.expand(mhat(pos[i], pos[j]))
            ia, ib = vs.index((0, 0, 0)), vs.index(tuple(e))
            c, d_ = [k for k in range(4) if k not in (ia, ib)]
            def exprs(L):
                l = lambda i, j: L[(min(i, j), max(i, j))]
                ee = l(ia, ib); uu = l(ia, c); ww = l(ia, d_)
                eu = (ee + uu - l(ib, c)) / 2; ew = (ee + ww - l(ib, d_)) / 2; uw = (uu + ww - l(c, d_)) / 2
                return uu * ee - eu ** 2, ww * ee - ew ** 2, uw * ee - eu * ew
            P1, P2, N = (sp.expand(x) for x in exprs(L0))
            Le = {k: L0[k] + eps * m[k] for k in L0}
            P1d, P2d, Nd = (sp.expand(sp.diff(x, eps).subs(eps, 0)) for x in exprs(Le))
            k = abs(sp.Matrix([[vs[r][i] - vs[ia][i] for i in range(3)] for r in (ib, c, d_)]).det())
            poly += Nd / k
            nums[P1] = nums.get(P1, 0) - N * P1d / (2 * k)
            nums[P2] = nums.get(P2, 0) - N * P2d / (2 * k)
    return sp.expand(poly), {P: sp.expand(v) for P, v in nums.items()}

def check():
    poly, nums = pieces(); Ps = list(nums); gv = sorted(g.free_symbols, key=str)
    ok = len(Ps) == 6 and all(len(sp.factor_list(P)[1]) == 1 and sp.factor_list(P)[1][0][1] == 1 for P in Ps)
    print('(b) six distinct irreducible face polynomials:', ok)
    target = sp.expand(detg * rho / 2)
    for b in bs:
        sub = {x: (1 if x == b else 0) for x in bs}
        qs = []
        for P in Ps:
            q, r = sp.div(sp.Poly(sp.expand(nums[P].subs(sub)), *gv), sp.Poly(P, *gv))
            ok = ok and r.is_zero; qs.append(q.as_expr())
        res = sp.expand(poly.subs(sub) + sum(qs) - target.subs(sub))
        ok = ok and res == 0
        print('(b),(c) B = unit at %s: P_i | numerator_i, poly + sum q_i - target = %s' % (b, res))
    global DROP_R_TERM
    DROP_R_TERM = True
    poly_c, nums_c = pieces(); DROP_R_TERM = False
    sub = {x: (1 if x == bs[0] else 0) for x in bs}
    Dn = 1
    for P in Ps: Dn = sp.expand(Dn * P)
    res = sp.expand(poly_c.subs(sub) * Dn) + sum(sp.expand(nums_c[P].subs(sub) * sp.cancel(Dn / P)) for P in Ps) - sp.expand(target.subs(sub) * Dn)
    print('(d) control (R term dropped), residual of the cleared identity nonzero:', sp.expand(res) != 0)
    ok = ok and sp.expand(res) != 0
    return ok

if __name__ == '__main__':
    import sys
    sys.exit(0 if check() else 1)
