"""Symbolic check of the 4D identities behind RC5 (numerical/symbolic evidence, not proof).

For a 4-simplex with vertices p, q, r, s, u and squared edge lengths x_ij, inner products of the
edge vectors from a base point o are <i-o, j-o> = (x_oi + x_oj - x_ij)/2. For a triangle T = (p, q, r)
and the two tetrahedra T+s, T+u containing it:
  gram2(T)     = det Gram(q-p, r-p)                    (= 4 area^2)
  gram3(T, s)  = det Gram(q-p, r-p, s-p)               (= 36 vol^2)
  M(T; s, u)   = det [<a,a> <a,b> <a,d>; <b,a> <b,b> <b,d>; <c,a> <c,b> <c,d>]
                 with a = q-p, b = r-p, c = s-p, d = u-p,
and the interior dihedral angle at T is cos theta = M / sqrt(gram3(T,s) gram3(T,u)).
Checks:
  1. M and gram3 are exactly symmetric: M under permutations of p, q, r and s <-> u; gram3 under
     all permutations of its four points.
  2. Desnanot-Jacobi: gram3(T,s) gram3(T,u) - M^2 = gram2(T) gram4.
  3. Facet identity: for each tetrahedron F of the 4-simplex, the sum over its four triangles t of
     M(t; F-t, w) (w the fifth vertex) equals gram3(F).
  4. Triangle sum: sum over the ten triangles t of M(t; s, u) equals half the sum of gram3 over
     the five tetrahedra (each triangle lies in two of them). With 3 this gives Schläfli's identity
     algebraically: sum_t A_t dtheta_t = -(1/(2 sqrt gram4)) sum_t [dM_t - (M_t/2)(dG_s/G_s +
     dG_u/G_u)], and sum_t M_t dG_s/G_s + M_t dG_u/G_u = sum_F dG_F = 2 d(sum_t M_t).
  5. Schläfli, exactly at random rational points: sum_t [2 dM_t - M_t (dG_s/G_s + dG_u/G_u)] = 0
     for d = d/dx_e, every edge e.
  6. Control: dropping one triangle from the Schläfli sum gives a nonzero result.
  7. Cayley-Menger: gram2 = -CM_2/4, gram3 = CM_3/8, gram4 = -CM_4/16 (the bordered determinants
     of squared lengths), i.e. gram_k = (k!)^2 vol_k^2.
"""
import itertools
import sympy as sp

P = ['p', 'q', 'r', 's', 'u']
X = {frozenset(e): sp.Symbol('x_' + ''.join(e), positive=True) for e in itertools.combinations(P, 2)}
def x(i, j):
    return sp.Integer(0) if i == j else X[frozenset((i, j))]
def ip(o, i, j):
    return (x(o, i) + x(o, j) - x(i, j)) / 2

def gram(o, pts):
    return sp.Matrix([[ip(o, i, j) for j in pts] for i in pts]).det()

def M(T, s, u):
    p, q, r = T
    rows = [q, r, s]; cols = [q, r, u]
    return sp.Matrix([[ip(p, i, j) for j in cols] for i in rows]).det()

def g3(F):
    o = F[0]
    return gram(o, F[1:])

ok = True
T = ('p', 'q', 'r')
base = sp.expand(M(T, 's', 'u'))
for perm in itertools.permutations(T):
    ok &= sp.expand(M(perm, 's', 'u') - base) == 0
    ok &= sp.expand(M(perm, 'u', 's') - base) == 0
g = sp.expand(g3(('p', 'q', 'r', 's')))
for perm in itertools.permutations(('p', 'q', 'r', 's')):
    ok &= sp.expand(g3(perm) - g) == 0
print("1. symmetry:", ok, flush=True)

dj = sp.expand(g3(('p','q','r','s')) * g3(('p','q','r','u')) - M(T,'s','u')**2
               - gram('p', ['q','r']) * gram('p', ['q','r','s','u']))
print("2. Desnanot-Jacobi:", dj == 0, flush=True); ok &= dj == 0

tris = list(itertools.combinations(P, 3))
facets = list(itertools.combinations(P, 4))
def other(F, t):
    return [v for v in F if v not in t][0]
for F in facets:
    w = [v for v in P if v not in F][0]
    tot = sum(M(t, other(F, t), w) for t in itertools.combinations(F, 3))
    r_ = sp.expand(tot - g3(F))
    ok &= r_ == 0
print("3. facet identity:", ok, flush=True)

tot_t = sum(M(t, *[v for v in P if v not in t]) for t in tris)
tot_F = sum(g3(F) for F in facets)
r4 = sp.expand(2 * tot_t - tot_F)
print("4. triangle sum = half the facet sum:", r4 == 0, flush=True); ok &= r4 == 0

terms = []
for t in tris:
    s_, u_ = [v for v in P if v not in t]
    Mt = sp.expand(M(t, s_, u_))
    Gs, Gu = sp.expand(g3(t + (s_,))), sp.expand(g3(t + (u_,)))
    terms.append((t, Mt, Gs, Gu))
def schlaefli(e, pt, drop=None):
    tot = sp.Integer(0)
    for t, Mt, Gs, Gu in terms:
        if drop == t:
            continue
        gs, gu = Gs.subs(pt), Gu.subs(pt)
        tot += 2 * sp.diff(Mt, e).subs(pt) - Mt.subs(pt) * (sp.diff(Gs, e).subs(pt) / gs
                                                             + sp.diff(Gu, e).subs(pt) / gu)
    return tot
import random
random.seed(1)
# perturbations of the regular 4-simplex (unit squared lengths), so all volumes are nonzero
pts = [{k: 1 + sp.Rational(random.randint(-20, 20), 100) for k in X.values()} for _ in range(3)]
for pt in pts:
    for e in X.values():
        val = schlaefli(e, pt)
        ok &= val == 0
print("5. Schläfli exact at 3 random rational points, all 10 edges:", ok, flush=True)
ctrl = schlaefli(X[frozenset(('p', 'q'))], pts[0], drop=('p', 'q', 'r'))
print("6. control (one triangle dropped):", ctrl, flush=True); ok &= ctrl != 0

def cm(pts):
    n = len(pts)
    rows = [[0] + [1] * n] + [[1] + [x(a, b) for b in pts] for a in pts]
    return sp.Matrix(rows).det()
c2 = sp.expand(gram('p', ['q', 'r']) + cm(['p', 'q', 'r']) / 4)
c3 = sp.expand(g3(('p', 'q', 'r', 's')) - cm(['p', 'q', 'r', 's']) / 8)
c4 = sp.expand(gram('p', ['q', 'r', 's', 'u']) + cm(P) / 16)
print("7. Cayley-Menger relations:", c2 == 0 and c3 == 0 and c4 == 0, flush=True)
ok &= c2 == 0 and c3 == 0 and c4 == 0

reg = {k: 1 for k in X.values()}
cosreg = sp.nsimplify(M(T,'s','u').subs(reg) / sp.sqrt(g3(('p','q','r','s')).subs(reg) * g3(('p','q','r','u')).subs(reg)))
print("regular 4-simplex: cos theta =", cosreg)
print("ALL CHECKS PASS" if ok and cosreg == sp.Rational(1, 4) else "CHECK FAILED")
