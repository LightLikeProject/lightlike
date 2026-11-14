"""Check of the sixth-order distance expansion (numerical and symbolic evidence, not proof).

Notation (all jets of the metric g at a point x, in coordinates):
    G = g(x),  A(u) = sum_k u_k d_k g,  B(u, v) = sum_kl u_k v_l d_l d_k g,
    C(u, v, s) = sum_klp u_k v_l s_p d_p d_l d_k g,  gam = Gamma_x(w, w).
    F(w)     = w.G.w + w.A(w).w/2 + w.B(w,w).w/6 - gam.G.gam/12        (distJet)
    quint(w) = w.C(w,w,w).w/24 - w.B(w,w).gam/12 + w.B(w,gam).w/24 + gam.A(w).gam/24
    F5 = F + quint
    midJet_m(D) = D.G_m.D + D.B_m(D,D).D/24 - gam_m.G_m.gam_m/12

Claims checked:
  1. (exact, symbolic) for a random polynomial metric, F5 centred at m - eps D/2, evaluated at
     eps D, equals midJet_m(eps D) up to O(eps^6): the coefficients of eps^2 .. eps^5 vanish.
     Control: F (without quint) leaves a non-zero eps^5 coefficient.
  2. (numerical) on the round sphere (stereographic chart) and the hyperbolic plane (half-plane),
     d(x, x + eps w)^2 - F5_x(eps w) = O(eps^6), while d^2 - F_x(eps w) is only O(eps^5).
  3. (numerical) d(m - eps D/2, m + eps D/2)^2 - midJet_m(eps D) = O(eps^6) with a non-zero
     eps^6 coefficient (the order is sharp).
"""
import random
import sympy as sp
import mpmath as mp

y = sp.symbols('y0 y1')
N = 2


def jets(g):
    """Symbolic first, second and third partials of a 2x2 metric g(y)."""
    d1 = [[[sp.diff(g[i, j], y[k]) for k in range(N)] for j in range(N)] for i in range(N)]
    d2 = [[[[sp.diff(d1[i][j][k], y[l]) for l in range(N)] for k in range(N)] for j in range(N)]
          for i in range(N)]
    d3 = [[[[[sp.diff(d2[i][j][k][l], y[p]) for p in range(N)] for l in range(N)] for k in range(N)]
           for j in range(N)] for i in range(N)]
    return d1, d2, d3


def jet_forms(g, d1, d2, d3, x):
    """The jet quantities at the point x (substituted symbolically)."""
    sub = {y[0]: x[0], y[1]: x[1]}
    G = g.subs(sub)
    Gi = G.inv()
    a = [[[d1[i][j][k].subs(sub) for k in range(N)] for j in range(N)] for i in range(N)]
    b = [[[[d2[i][j][k][l].subs(sub) for l in range(N)] for k in range(N)] for j in range(N)]
         for i in range(N)]
    c = [[[[[d3[i][j][k][l][p].subs(sub) for p in range(N)] for l in range(N)] for k in range(N)]
          for j in range(N)] for i in range(N)]
    R = range(N)
    def A(u): return sp.Matrix(N, N, lambda i, j: sum(u[k] * a[i][j][k] for k in R))
    def B(u, v): return sp.Matrix(N, N, lambda i, j: sum(u[k] * v[l] * b[i][j][k][l]
                                                          for k in R for l in R))
    def C(u, v, s): return sp.Matrix(N, N, lambda i, j: sum(u[k] * v[l] * s[p] * c[i][j][k][l][p]
                                                             for k in R for l in R for p in R))
    def Gam(u, v):
        return sp.Matrix([sum(sp.Rational(1, 2) * Gi[i, l] * (a[l][j][k] + a[l][k][j] - a[j][k][l])
                              * u[j] * v[k] for j in R for k in R for l in R) for i in R])
    return G, A, B, C, Gam


def dot(p, M, q): return (sp.Matrix(p).T * M * sp.Matrix(q))[0, 0]


def F_and_quint(G, A, B, C, Gam, w):
    gam = Gam(w, w)
    F = dot(w, G, w) + dot(w, A(w), w) / 2 + dot(w, B(w, w), w) / 6 - dot(gam, G, gam) / 12
    q = (dot(w, C(w, w, w), w) / 24 - dot(w, B(w, w), gam) / 12 + dot(w, B(w, gam), w) / 24
         + dot(gam, A(w), gam) / 24)
    return F, q


def mid_jet(G, A, B, C, Gam, D):
    gam = Gam(D, D)
    return dot(D, G, D) + dot(D, B(D, D), D) / 24 - dot(gam, G, gam) / 12


# --- 1. exact midpoint cancellation for a random polynomial metric ----------------------------
random.seed(7)
def rnd(): return sp.Rational(random.randint(-9, 9), 10)
def poly():
    return sum(rnd() * y[0] ** i * y[1] ** j for i in range(5) for j in range(5) if 1 <= i + j <= 4)
g11, g12, g22 = poly(), poly() / 3, poly()
g = sp.Matrix([[2 + g11, g12], [g12, 1 + g22]])
d1, d2, d3 = jets(g)
eps = sp.Symbol('eps')
m = [sp.Rational(1, 7), sp.Rational(-1, 5)]
D = [sp.Rational(3, 4), sp.Rational(-2, 3)]
x = [m[i] - eps * D[i] / 2 for i in range(N)]
G, A, B, C, Gam = jet_forms(g, d1, d2, d3, x)
F, q = F_and_quint(G, A, B, C, Gam, [eps * Di for Di in D])
Gm, Am, Bm, Cm, Gamm = jet_forms(g, d1, d2, d3, m)
M = mid_jet(Gm, Am, Bm, Cm, Gamm, [eps * Di for Di in D])
def coeffs(expr, upto=6):
    s = sp.series(expr, eps, 0, upto + 1).removeO()
    return [sp.nsimplify(sp.simplify(s.coeff(eps, k))) for k in range(upto + 1)]
c5 = coeffs(F + q - M)
c4 = coeffs(F - M)
print("1. F5(m-eps D/2; eps D) - midJet_m(eps D), coefficients eps^0..eps^6:")
print("   ", [float(c) for c in c5])
assert all(c == 0 for c in c5[:6]), "midpoint cancellation fails"
print("   control (no quint), eps^5 coefficient:", float(c4[5]))
assert c4[5] != 0
assert all(c == 0 for c in c4[:5])

# --- 2./3. sphere and hyperbolic plane --------------------------------------------------------
mp.mp.dps = 60
sphere = sp.Matrix([[4 / (1 + y[0]**2 + y[1]**2)**2, 0], [0, 4 / (1 + y[0]**2 + y[1]**2)**2]])
hyper = sp.Matrix([[1 / y[1]**2, 0], [0, 1 / y[1]**2]])

def d_sphere(p, r):
    def emb(u):
        s = 1 + u[0]**2 + u[1]**2
        return [2 * u[0] / s, 2 * u[1] / s, (1 - u[0]**2 - u[1]**2) / s]
    P, Q = emb(p), emb(r)
    cross = [P[1]*Q[2]-P[2]*Q[1], P[2]*Q[0]-P[0]*Q[2], P[0]*Q[1]-P[1]*Q[0]]
    return mp.atan2(mp.sqrt(sum(c**2 for c in cross)), sum(P[i]*Q[i] for i in range(3)))

def d_hyper(p, r):
    return mp.acosh(1 + ((p[0]-r[0])**2 + (p[1]-r[1])**2) / (2 * p[1] * r[1]))

def slope(xs, ys):
    lx = [mp.log(v) for v in xs]; ly = [mp.log(abs(v)) for v in ys]
    n = len(xs); mx = sum(lx) / n; my = sum(ly) / n
    return sum((lx[i]-mx)*(ly[i]-my) for i in range(n)) / sum((lx[i]-mx)**2 for i in range(n))

def numeric_forms(g, x):
    d1, d2, d3 = jets(g)
    G, A, B, C, Gam = jet_forms(g, d1, d2, d3, [sp.Rational(v) for v in x])
    return G, A, B, C, Gam

eps_list = [mp.mpf(2) ** (-k) for k in range(5, 11)]
ok = True
for name, gmet, dist, x0, w0 in [("sphere", sphere, d_sphere, ("0.3", "-0.2"), ("0.6", "0.8")),
                                 ("hyperbolic", hyper, d_hyper, ("0.2", "1.3"), ("0.5", "-0.7"))]:
    G, A, B, C, Gam = numeric_forms(gmet, x0)
    wsym = sp.symbols('w0 w1')
    F, q = F_and_quint(G, A, B, C, Gam, list(wsym))
    Mj = mid_jet(G, A, B, C, Gam, list(wsym))
    fF = sp.lambdify(wsym, F, 'mpmath'); fq = sp.lambdify(wsym, q, 'mpmath')
    fM = sp.lambdify(wsym, Mj, 'mpmath')
    X = [mp.mpf(v) for v in x0]; W = [mp.mpf(v) for v in w0]
    r5, r6, rm = [], [], []
    for e in eps_list:
        w = [e * W[0], e * W[1]]
        d2v = dist(X, [X[0] + w[0], X[1] + w[1]]) ** 2
        r5.append(d2v - fF(*w)); r6.append(d2v - fF(*w) - fq(*w))
        dm = dist([X[0] - w[0] / 2, X[1] - w[1] / 2], [X[0] + w[0] / 2, X[1] + w[1] / 2]) ** 2
        rm.append(dm - fM(*w))
    s5, s6, sm = slope(eps_list, r5), slope(eps_list, r6), slope(eps_list, rm)
    c6 = rm[-1] / eps_list[-1] ** 6
    print(f"2. {name}: one-sided remainder order with F: {float(s5):.3f}, with F5: {float(s6):.3f}")
    print(f"3. {name}: midpoint remainder order {float(sm):.3f}, eps^6 coefficient ~ {float(c6):.3e}")
    ok &= abs(s5 - 5) < 0.1 and abs(s6 - 6) < 0.1 and abs(sm - 6) < 0.1 and abs(c6) > 1e-6
assert ok
print("OK")
