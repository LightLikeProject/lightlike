"""Acceptance check for RC6a step 4 (numerical evidence, not proof).

Claim: for x = m - Δ/2, y = m + Δ/2 the squared geodesic distance has the midpoint expansion
    d(x, y)^2 = g_m(Δ, Δ) + Q_m(Δ) + O(|Δ|^6),
with Q_m the quartic term of the energy of the trial curve
    γ(t) = m + (t - 1/2) Δ + η(t),  η(t) = t (1 - t) Γ_m(Δ, Δ) / 2,
which solves the geodesic equation to second order (the energy is stationary at the geodesic, so
an O(|Δ|^3) error in the curve changes the energy by O(|Δ|^6)).

Q_m is derived symbolically for a general 2D metric from its 2-jet at m, then compared with the
closed-form distances of the round sphere (stereographic coordinates) and the hyperbolic plane
(Poincaré half-plane): the remainder must scale as |Δ|^6. Control: dropping Q_m leaves an error
of order |Δ|^4.
"""
import math
import sympy as sp

# --- symbolic Q_m for a general 2D metric -----------------------------------------------------
t, eps = sp.symbols('t epsilon')
D = sp.symbols('D0 D1')
g0 = [[sp.Symbol(f'g{i}{j}') if i <= j else sp.Symbol(f'g{j}{i}') for j in range(2)] for i in range(2)]
a = {(i, j, k): sp.Symbol(f'a{min(i,j)}{max(i,j)}_{k}') for i in range(2) for j in range(2) for k in range(2)}
b = {(i, j, k, l): sp.Symbol(f'b{min(i,j)}{max(i,j)}_{min(k,l)}{max(k,l)}')
     for i in range(2) for j in range(2) for k in range(2) for l in range(2)}
def gz(z):
    """The metric at m + z, to second order: g + a z + b z z / 2."""
    return [[g0[i][j] + sum(a[(i, j, k)] * z[k] for k in range(2))
             + sum(b[(i, j, k, l)] * z[k] * z[l] for k in range(2) for l in range(2)) / 2
             for j in range(2)] for i in range(2)]
G = sp.Matrix(g0)
Ginv = G.inv()
# Christoffel symbols at m: Γ^i_jk = ½ g^{il}(a_lj,k + a_lk,j - a_jk,l)
Gam = [[[sp.Rational(1, 2) * sum(Ginv[i, l] * (a[(l, j, k)] + a[(l, k, j)] - a[(j, k, l)])
                                 for l in range(2)) for k in range(2)] for j in range(2)]
       for i in range(2)]
GDD = [sum(Gam[i][j][k] * D[j] * D[k] for j in range(2) for k in range(2)) for i in range(2)]
eta = [t * (1 - t) * GDD[i] / 2 for i in range(2)]
z = [eps * (t - sp.Rational(1, 2)) * D[i] + eps**2 * eta[i] for i in range(2)]
zd = [sp.diff(zi, t) for zi in z]
gm = gz(z)
integrand = sum(gm[i][j] * zd[i] * zd[j] for i in range(2) for j in range(2))
E = sp.integrate(sp.expand(sp.series(integrand, eps, 0, 5).removeO()), (t, 0, 1))
E = sp.expand(E)
E2 = E.coeff(eps, 2)
E3 = E.coeff(eps, 3)
Q = E.coeff(eps, 4)
assert sp.simplify(E2 - sum(g0[i][j] * D[i] * D[j] for i in range(2) for j in range(2))) == 0
assert sp.simplify(E3) == 0  # odd order vanishes about the midpoint

def jet(metric, m, h=1e-3):
    """Numerical 2-jet of a metric function at m (central differences)."""
    def gij(x, i, j): return metric(x)[i][j]
    gv = metric(m)
    av, bv = {}, {}
    for i in range(2):
        for j in range(2):
            for k in range(2):
                e = [0, 0]; e[k] = h
                av[(i, j, k)] = (gij([m[0]+e[0], m[1]+e[1]], i, j) - gij([m[0]-e[0], m[1]-e[1]], i, j)) / (2*h)
                for l in range(2):
                    f = [0, 0]; f[l] = h
                    pp = gij([m[0]+e[0]+f[0], m[1]+e[1]+f[1]], i, j)
                    pm = gij([m[0]+e[0]-f[0], m[1]+e[1]-f[1]], i, j)
                    mp = gij([m[0]-e[0]+f[0], m[1]-e[1]+f[1]], i, j)
                    mm = gij([m[0]-e[0]-f[0], m[1]-e[1]-f[1]], i, j)
                    bv[(i, j, k, l)] = (pp - pm - mp + mm) / (4*h*h)
    return gv, av, bv

def Q_num(metric, m, Dv):
    gv, av, bv = jet(metric, m)
    sub = {D[0]: Dv[0], D[1]: Dv[1]}
    for i in range(2):
        for j in range(2):
            sub[g0[i][j]] = gv[i][j]
            for k in range(2):
                sub[a[(i, j, k)]] = av[(i, j, k)]
                for l in range(2):
                    sub[b[(i, j, k, l)]] = bv[(i, j, k, l)]
    return float(Q.subs(sub)), sum(gv[i][j]*Dv[i]*Dv[j] for i in range(2) for j in range(2))

# --- test metrics with closed-form distances ---------------------------------------------------
def sphere_g(x):
    l = 2 / (1 + x[0]**2 + x[1]**2)
    return [[l*l, 0], [0, l*l]]
def sphere_d(p, q):
    def P(x):
        r2 = x[0]**2 + x[1]**2
        return (2*x[0]/(1+r2), 2*x[1]/(1+r2), (1-r2)/(1+r2))
    u, v = P(p), P(q)
    return math.acos(max(-1, min(1, sum(s*w for s, w in zip(u, v)))))
def hyp_g(x):
    return [[1/x[1]**2, 0], [0, 1/x[1]**2]]
def hyp_d(p, q):
    return math.acosh(1 + ((p[0]-q[0])**2 + (p[1]-q[1])**2) / (2*p[1]*q[1]))

ok = True
for name, g, d, m, u in [("sphere", sphere_g, sphere_d, (0.3, -0.2), (0.6, 0.8)),
                         ("hyperbolic", hyp_g, hyp_d, (0.1, 1.3), (0.8, -0.6))]:
    rows = []
    for s in (0.2, 0.1, 0.05, 0.025):
        Dv = (s*u[0], s*u[1])
        x = (m[0]-Dv[0]/2, m[1]-Dv[1]/2); y = (m[0]+Dv[0]/2, m[1]+Dv[1]/2)
        q, g2 = Q_num(g, m, Dv)
        dd = d(x, y)**2
        rows.append((s, abs(dd - g2 - q), abs(dd - g2)))
    rates = [math.log(rows[i][1]/rows[i+1][1], 2) for i in range(len(rows)-1)]
    ctrl = [math.log(rows[i][2]/rows[i+1][2], 2) for i in range(len(rows)-1)]
    print(f"{name}: remainder order {[round(r, 2) for r in rates]} (expect 6); "
          f"without Q_m {[round(r, 2) for r in ctrl]} (expect 4)")
    ok &= rates[-1] > 5.5 and ctrl[-1] < 4.5

# --- the one-sided expansion at an endpoint (the form proven in Lean) --------------------------
# d(x, x + w)^2 = g(w, w) + (1/2) ∂_w g(w, w) + (1/6) ∂_w ∂_w g(w, w) - (1/12) |Γ(w, w)|^2_g
#                 + O(|w|^5),
# all coefficients at x. Control: dropping the Γ term leaves an error of order |w|^4.
def F_num(metric, x, w, cG=-1/12):
    gv, av, bv = jet(metric, x)
    det = gv[0][0]*gv[1][1] - gv[0][1]*gv[1][0]
    gi = [[gv[1][1]/det, -gv[0][1]/det], [-gv[1][0]/det, gv[0][0]/det]]
    Gam = [[[0.5*sum(gi[i][l]*(av[(l, j, k)] + av[(l, k, j)] - av[(j, k, l)]) for l in range(2))
             for k in range(2)] for j in range(2)] for i in range(2)]
    Gww = [sum(Gam[i][j][k]*w[j]*w[k] for j in range(2) for k in range(2)) for i in range(2)]
    G2 = sum(gv[i][j]*w[i]*w[j] for i in range(2) for j in range(2))
    A3 = sum(av[(i, j, k)]*w[k]*w[i]*w[j] for i in range(2) for j in range(2) for k in range(2))
    B4 = sum(bv[(i, j, k, l)]*w[k]*w[l]*w[i]*w[j]
             for i in range(2) for j in range(2) for k in range(2) for l in range(2))
    GG = sum(gv[i][j]*Gww[i]*Gww[j] for i in range(2) for j in range(2))
    return G2 + A3/2 + B4/6 + cG*GG

for name, g, d, x0, u in [("sphere", sphere_g, sphere_d, (0.3, -0.2), (0.6, 0.8)),
                          ("hyperbolic", hyp_g, hyp_d, (0.1, 1.3), (0.8, -0.6))]:
    rows = []
    for s in (0.2, 0.1, 0.05, 0.025):
        w = (s*u[0], s*u[1])
        dd = d(x0, (x0[0]+w[0], x0[1]+w[1]))**2
        rows.append((abs(dd - F_num(g, x0, w)), abs(dd - F_num(g, x0, w, cG=0))))
    rates = [math.log(rows[i][0]/rows[i+1][0], 2) for i in range(len(rows)-1)]
    ctrl = [math.log(rows[i][1]/rows[i+1][1], 2) for i in range(len(rows)-1)]
    print(f"{name} one-sided: remainder order {[round(r, 2) for r in rates]} (expect 5); "
          f"without the Γ term {[round(r, 2) for r in ctrl]} (expect 4)")
    ok &= rates[-1] > 4.5 and ctrl[-1] < 4.5
print("ALL CHECKS PASS" if ok else "CHECK FAILED")
