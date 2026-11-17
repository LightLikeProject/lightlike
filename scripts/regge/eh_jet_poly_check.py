"""Exact-arithmetic (sympy) check of the second-order expansion of the curvature density (R/2) sqrt(det g) of the
metric g = 1 + eta h in the jet (h, dh, ddh) of a symmetric field in dimension 3:

  F1 = (1/2) (sum_ij dd_ijij - sum_ki dd_kkii),
  F2 = fpDens(dh) + div T'   (the Fierz-Pauli density plus an explicit divergence), with the field T' of
  Lightlike/Regge/Conv3/CurvaturePoly.lean (divTp).

The formulas use the Christoffel/Riemann conventions of Lightlike/Spacetime/Curvature.lean through the jet formula
`curvJ`. Wrong-input control: changing the coefficient -3/2 of divTp to -1 makes the identity fail.
Numerical-algebraic evidence for the Lean statements F1_eq and F2_eq, not a proof."""
import itertools
import sympy as sp
eta = sp.symbols("eta")
Hm = sp.Matrix(3, 3, lambda i, j: sp.Symbol(f"H{min(i,j)}{max(i,j)}"))
dhm = [[[sp.Symbol(f"d{k}_{min(i,j)}{max(i,j)}") for j in range(3)] for i in range(3)] for k in range(3)]
ddm = [[[[sp.Symbol(f"dd{min(a,b)}{max(a,b)}_{min(i,j)}{max(i,j)}") for j in range(3)] for i in range(3)] for b in range(3)] for a in range(3)]
G = sp.eye(3) + eta * Hm
Gi = sp.eye(3) - eta * Hm + eta**2 * Hm * Hm            # exact up to O(eta^3)
dg = lambda a, i, j: eta * dhm[a][i][j]
ddg = lambda a, b, i, j: eta * ddm[a][b][i][j]
chr_ = lambda i, j, k: sp.Rational(1, 2) * sum(Gi[i, l] * (dg(j, l, k) + dg(k, l, j) - dg(l, j, k)) for l in range(3))
def dchr(mu, rho, nu, sig):
    return sp.Rational(1, 2) * sum(
        (-sum(Gi[rho, i] * dg(mu, i, r) * Gi[r, l] for i in range(3) for r in range(3))) * (dg(nu, l, sig) + dg(sig, l, nu) - dg(l, nu, sig))
        + Gi[rho, l] * (ddg(mu, nu, l, sig) + ddg(mu, sig, l, nu) - ddg(mu, l, nu, sig)) for l in range(3))
def trunc(e, n=2):
    e = sp.expand(e)
    return sum(e.coeff(eta, k) * eta**k for k in range(n + 1))
Chr = [[[trunc(chr_(i, j, k)) for k in range(3)] for j in range(3)] for i in range(3)]
DC = {}
for mu, rho, nu, sig in itertools.product(range(3), repeat=4):
    DC[mu, rho, nu, sig] = trunc(dchr(mu, rho, nu, sig))
R = 0
for sig, nu in itertools.product(range(3), repeat=2):
    inner = sum(DC[rho, rho, nu, sig] - DC[nu, rho, rho, sig]
                + sum(Chr[rho][rho][l] * Chr[l][nu][sig] - Chr[rho][nu][l] * Chr[l][rho][sig] for l in range(3)) for rho in range(3))
    R += Gi[sig, nu] * inner
R = trunc(R)
sq = 1 + eta * Hm.trace() / 2 + eta**2 * (Hm.trace()**2 / 8 - (Hm * Hm).trace() / 4)   # sqrt det to O(eta^2): det = 1 + t eta + e2 eta^2
F = trunc(sp.expand(R / 2 * sq))
F1 = sp.expand(F.coeff(eta, 1)); F2 = sp.expand(2 * F.coeff(eta, 2))
assert F.coeff(eta, 0) == 0
R1 = sum(ddm[i][j][i][j] for i in range(3) for j in range(3)) - sum(ddm[k][k][i][i] for k in range(3) for i in range(3))
assert sp.expand(F1 - R1 / 2) == 0

div = [sum(dhm[m][m][n] for m in range(3)) for n in range(3)]; tr = [sum(dhm[k][i][i] for i in range(3)) for k in range(3)]
fp = (-sp.Rational(1, 4) * sum(dhm[l][m][n]**2 for l in range(3) for m in range(3) for n in range(3)) + sp.Rational(1, 2) * sum(c**2 for c in div)
      - sp.Rational(1, 2) * sum(div[n] * tr[n] for n in range(3)) + sp.Rational(1, 4) * sum(c**2 for c in tr))
Dd = sp.expand(F2 - fp)


R=range(3)
H=lambda i,j: sp.Symbol(f"H{min(i,j)}{max(i,j)}")
dh=lambda k,i,j: sp.Symbol(f"d{k}_{min(i,j)}{max(i,j)}")
dd=lambda a,b,i,j: sp.Symbol(f"dd{min(a,b)}{max(a,b)}_{min(i,j)}{max(i,j)}")
t=sum(H(i,i) for i in R)
div=0
for m in R:
    div+=sp.Rational(1,2)*(sum(dh(m,a,a) for a in R)*sum(dh(c,c,m) for c in R)+t*sum(dd(m,c,c,m) for c in R))
    div-=sp.Rational(1,2)*(sum(dh(m,a,a) for a in R)*sum(dh(m,i,i) for i in R)+t*sum(dd(m,m,i,i) for i in R))
    div-=sp.Rational(1,2)*sum(dh(m,a,b)*dh(a,b,m)+H(a,b)*dd(m,a,b,m) for a in R for b in R)
    div+=sum(dh(m,a,m)*dh(a,i,i)+H(a,m)*dd(m,a,i,i) for a in R for i in R)
    div+=sum(dh(m,a,b)*dh(m,a,b)+H(a,b)*dd(m,m,a,b) for a in R for b in R)
    div-=sp.Rational(3,2)*sum(dh(m,a,m)*dh(c,a,c)+H(a,m)*dd(m,c,a,c) for a in R for c in R)
assert sp.expand(div - Dd) == 0
wrong = div + sp.Rational(1, 2) * sum(dh(m, a, m) * dh(c, a, c) + H(a, m) * dd(m, c, a, c) for m in R for a in R for c in R)
assert sp.expand(wrong - Dd) != 0   # control: coefficient -3/2 replaced by -1
print("OK: F1 = R1/2, F2 - fpDens = div T' (exact); the control with coefficient -1 fails")
