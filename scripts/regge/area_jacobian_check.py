"""Symbolic check of the area Regge calculus statements for a 4-simplex.

Numerical/symbolic evidence, not proof. With squared edge lengths s (10 edges, ordered
01,02,03,04,12,13,14,23,24,34) and A_t^2 = ((a+b+c)^2 - 2(a^2+b^2+c^2))/16 for each triangle:
  1. The Jacobian of s -> A^2 at the regular simplex (s = 1) has determinant -48/8^10 != 0.
  2. At the corner simplex (s_0i = 1, s_ij = 2) it is singular, with a 2-dimensional kernel
     containing k = (0,0,0,0,0,1,-1,-1,1,0).
  3. s0 + k/2 and s0 - k/2 are different, both have positive leading minors of the Gram matrix
     (valid Euclidean simplices), and they have the same ten squared areas.
  4. Control: a different direction (e_5 only) does NOT give equal areas for +-t.
"""
import itertools
import sys
import sympy as sp

E = list(itertools.combinations(range(5), 2))
T = list(itertools.combinations(range(5), 3))
S = sp.symbols('s0:10')

def h(a, b, c):
    return ((a + b + c) ** 2 - 2 * (a * a + b * b + c * c)) / 16

Asq = [h(*[S[E.index(p)] for p in itertools.combinations(t, 2)]) for t in T]
Jac = sp.Matrix(10, 10, lambda t, e: sp.diff(Asq[t], S[e]))
ok = True

def check(name, cond):
    global ok
    print(('PASS ' if cond else 'FAIL ') + name)
    ok = ok and cond

reg = {x: 1 for x in S}
check('det Jac(regular) = -48/8^10', Jac.subs(reg).det() == sp.Rational(-48, 8 ** 10))

s0 = [1, 1, 1, 1, 2, 2, 2, 2, 2, 2]
J0 = Jac.subs(dict(zip(S, s0)))
k = sp.Matrix([0, 0, 0, 0, 0, 1, -1, -1, 1, 0])
check('det Jac(corner) = 0', J0.det() == 0)
check('Jac(corner) k = 0, kernel dim 2', J0 * k == sp.zeros(10, 1) and len(J0.nullspace()) == 2)

def gram(s):
    g = lambda i, j: s[E.index((min(i, j), max(i, j)))]
    return sp.Matrix(4, 4, lambda a, b: g(0, a + 1) if a == b else (g(0, a + 1) + g(0, b + 1) - g(a + 1, b + 1)) / 2)

def areas(s):
    return [a.subs(dict(zip(S, s))) for a in Asq]

half = sp.Rational(1, 2)
sp_ = [x + half * y for x, y in zip(s0, k)]
sm_ = [x - half * y for x, y in zip(s0, k)]
check('different lengths', sp_ != sm_)
for nm, s in (('plus', sp_), ('minus', sm_)):
    G = gram(s)
    check('Gram minors positive (%s)' % nm, all(G[:j, :j].det() > 0 for j in range(1, 5)))
check('equal squared areas', areas(sp_) == areas(sm_))
# explicit points in R^4 (Cholesky factor of the Gram matrix) realise s_plus and s_minus
r14, r42 = sp.sqrt(14), sp.sqrt(42)
def pts(sign):
    return [[0, 0, 0, 0], [1, 0, 0, 0], [0, 1, 0, 0],
            [-sign * sp.Rational(1, 4), sign * sp.Rational(1, 4), r14 / 4, 0],
            [sign * sp.Rational(1, 4), -sign * sp.Rational(1, 4), r14 / 28, r42 / 7]]
def realizes(P, s):
    return all(sp.simplify(sum((P[i][c] - P[j][c]) ** 2 for c in range(4)) - s[n]) == 0
               for n, (i, j) in enumerate(E))
check('points realise s_plus', realizes(pts(1), sp_))
check('points realise s_minus', realizes(pts(-1), sm_))
check('edge-vector determinants nonzero',
      all(sp.Matrix(P[1:]).det() != 0 for P in (pts(1), pts(-1))))
e5 = [0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
check('control: e_5 direction gives different areas',
      areas([x + half * y for x, y in zip(s0, e5)]) != areas([x - half * y for x, y in zip(s0, e5)]))
sys.exit(0 if ok else 1)
