"""Numerical cross-checks of the SL(2,R) representations of milestone HA3.

Conventions are those of `Lightlike/Lorentz/SL2R*.lean` (transpose action):

    principal series  (pi(g) f)(x) = |bx+d|^(i nu-1) sgn(bx+d)^eps f((ax+c)/(bx+d)),
    discrete series   (D(g) F)(z)  = (bz+d)^(-n) F((az+c)/(bz+d))   on L^2(H, y^(n-2) dx dy),

for g = [[a, b], [c, d]], so that g -> pi(g) is multiplicative: pi(g h) = pi(g) pi(h).

Checks:
 1. group law of both actions at random points (cocycle of the multiplier);
 2. unitarity by quadrature: L^2(R) for the principal series, L^2(H, y^(n-2) dx dy) for D_n;
 3. the Casimir Omega = H^2/4 + (EF+FE)/2 of the derived actions along
    upper(t) = [[1,t],[0,1]], lower(t) = [[1,0],[t,1]], expH(t) = diag(e^t, e^-t),
    symbolically: -(1+nu^2)/4 on the principal series, (n/2)(n/2-1) on D_n (the Lean values);
 4. the complementary series: the invariant Hermitian form on the K-types phi_m of the line
    model with exponent sigma-1 (sigma real) has lambda_(m+2)/lambda_m = (m+1+sigma)/(m+1-sigma),
    derived here from the raising and lowering operators, not assumed. (The route note writes
    (m+1-sigma)/(m+1+sigma) for the g^-1 convention, exponent -1-sigma; the two differ by
    sigma -> -sigma, and the criterion |sigma| < 1 is the same.)
 5. the partial fractions of step 10 of the route: 2 sum_(n odd) nu^2/(n^2+nu^2) =
    (pi nu/2) tanh(pi nu/2) and 1 + 2 sum_(n even >= 2) nu^2/(n^2+nu^2) = (pi nu/2) coth(pi nu/2);
 6. the spherical Plancherel formula (Mehler-Fock inversion at the origin) for
    F(cosh r) = exp(-a cosh r): F(1) = int_0^oo rho tanh(pi rho) F^(rho) d rho, with
    F^(rho) = int_1^oo F(x) P_(-1/2+i rho)(x) dx = sqrt(2/(pi a)) K_(i rho)(a); the closed form is
    itself checked by direct quadrature.

Controls (each must FAIL the corresponding identity):
 - a wrong multiplier exponent i nu (instead of i nu - 1) breaks unitarity and changes the Casimir;
 - complex nu breaks unitarity;
 - a wrong weight y^(n-1) in place of y^(n-2) breaks unitarity of D_n;
 - the unsymmetrised H^2/4 + EF is not a scalar;
 - sigma = 3/2 gives a negative ratio (no invariant inner product);
 - n = 1: (z+i)^(-1) is not in L^2(H, y^(-1) dx dy) (the integral diverges logarithmically);
 - coth in place of tanh in the spherical formula gives a different value.

This is numerical evidence, not proof.
"""
import random
import sys

import mpmath as mp
import sympy as sp
from scipy import integrate

random.seed(20261110)
mp.mp.dps = 20
ok = True


def report(name, good):
    global ok
    ok = ok and good
    print(f"{name}: {'OK' if good else 'FAIL'}")


def rand_sl2():
    while True:
        a, b, c = (random.uniform(-2, 2) for _ in range(3))
        if abs(a) > 0.3:
            return [[a, b], [c, (1 + b * c) / a]]


def mul(g, h):
    return [[g[0][0] * h[0][0] + g[0][1] * h[1][0], g[0][0] * h[0][1] + g[0][1] * h[1][1]],
            [g[1][0] * h[0][0] + g[1][1] * h[1][0], g[1][0] * h[0][1] + g[1][1] * h[1][1]]]


# ---------------------------------------------------------------- 1. group law
def mult(eps, nu, t, shift=-1):
    if t == 0:  # a single point, null for the quadrature
        return 0
    return abs(t) ** (1j * nu + shift) * (1 if t > 0 else (-1) ** eps)


def act(eps, nu, g, f, shift=-1):
    def h(x):
        den = g[0][1] * x + g[1][1]
        if den == 0:  # the pole of the Moebius map, a null set
            return 0
        return mult(eps, nu, den, shift) * f((g[0][0] * x + g[1][0]) / den)
    return h


def f0(x):
    return complex(mp.exp(-x * x)) * (1 + 2j * x)


def actC(n, g, F):
    def h(z):
        jac = g[0][1] * z + g[1][1]
        return jac ** (-n) * F((g[0][0] * z + g[1][0]) / jac)
    return h


def F0(z):
    return complex(mp.exp(-(z - 2j) ** 2 / 3)) * (z + 1j) ** -3


err_p, err_d = 0.0, 0.0
for _ in range(20):
    g, h = rand_sl2(), rand_sl2()
    eps, nu = random.choice([0, 1]), random.uniform(-3, 3)
    x = random.uniform(-3, 3)
    lhs = act(eps, nu, g, act(eps, nu, h, f0))(x)
    rhs = act(eps, nu, mul(g, h), f0)(x)
    err_p = max(err_p, abs(lhs - rhs) / max(1, abs(rhs)))
    n = random.choice([2, 3, 4])
    z = complex(random.uniform(-2, 2), random.uniform(0.2, 2))
    lhs, rhs = actC(n, g, actC(n, h, F0))(z), actC(n, mul(g, h), F0)(z)
    err_d = max(err_d, abs(lhs - rhs) / max(1, abs(rhs)))
print(f"group law: max relative error principal {err_p:.2e}, discrete {err_d:.2e}")
report("1. group law pi(gh) = pi(g) pi(h)", err_p < 1e-10 and err_d < 1e-10)


# ---------------------------------------------------------------- 2. unitarity
def norm2_line(f, pole=None):
    pts = [-mp.inf] + ([mp.mpf(pole)] if pole is not None else []) + [mp.inf]
    return float(mp.quad(lambda x: abs(f(float(x))) ** 2, pts))


g = [[1.3, 0.7], [-0.4, (1 + 0.7 * -0.4) / 1.3]]
pole = -g[1][1] / g[0][1]
base = norm2_line(f0)
vals = {
    "nu=1.7": norm2_line(act(0, 1.7, g, f0), pole),
    "eps=1": norm2_line(act(1, -0.9, g, f0), pole),
}
good = all(abs(v - base) < 1e-8 * base for v in vals.values())
print(f"unitarity principal: |f|^2 = {base:.12f}, |pi(g) f|^2 = " +
      ", ".join(f"{k}: {v:.12f}" for k, v in vals.items()))
report("2a. principal series unitary (real nu)", good)
wrong = norm2_line(act(0, 1.7, g, f0, shift=0), pole)
cplx = norm2_line(act(0, 1.7 + 0.4j, g, f0), pole)
print(f"controls: exponent i nu: {wrong:.6f}; nu = 1.7+0.4i: {cplx:.6f}  (vs {base:.6f})")
report("2b. control: wrong exponent / complex nu not unitary",
       abs(wrong - base) > 1e-3 and abs(cplx - base) > 1e-3)


def norm2_H(F, wexp):
    """int_H |F|^2 y^wexp dx dy, computed on the unit disk z = i(1+w)/(1-w) in polar coordinates."""
    def integrand(r, th):
        wd = r * complex(mp.cos(th), mp.sin(th))
        z = 1j * (1 + wd) / (1 - wd)
        jac2 = 4 / abs(1 - wd) ** 4
        return abs(F(z)) ** 2 * z.imag ** wexp * jac2 * r
    val, _ = integrate.dblquad(integrand, 0, 2 * float(mp.pi), 0, 1, epsabs=1e-12, epsrel=1e-11)
    return val


def lowest(n):
    return lambda z: (z + 1j) ** (-n)


gD = [[0.8, -0.5], [0.6, (1 - 0.5 * 0.6) / 0.8]]
for n in (2, 3):
    F = lowest(n)
    exact = float(4 * mp.pi / (4 ** n * (n - 1)))
    a0 = norm2_H(F, n - 2)
    a1 = norm2_H(actC(n, gD, F), n - 2)
    w0 = norm2_H(F, n - 1)
    w1 = norm2_H(actC(n, gD, F), n - 1)
    print(f"D_{n}: |F|^2 = {a0:.12f} (exact 4 pi/(4^n (n-1)) = {exact:.12f}),"
          f" |D(g)F|^2 = {a1:.12f}; weight y^(n-1): {w0:.6f} vs {w1:.6f}")
    report(f"2c. D_{n} unitary on L^2(H, y^(n-2) dx dy)",
           abs(a0 - exact) < 1e-9 * exact and abs(a1 - exact) < 1e-9 * exact)
    report(f"2d. control: weight y^(n-1) not invariant (n={n})", abs(w0 - w1) > 1e-3 * w0)

# n = 1: int_H |z+i|^-2 y^-1 dx dy = int_0^oo pi / (y (y+1)) dy diverges at y = 0
cut = [mp.quad(lambda y: mp.pi / (y * (y + 1)), [mp.mpf(10) ** -k, 1]) for k in (4, 8, 16)]
print("n = 1 control: int_eps^1 pi/(y(y+1)) dy for eps = 1e-4, 1e-8, 1e-16:",
      ", ".join(f"{float(c):.3f}" for c in cut))
report("2e. control: (z+i)^-1 not square-integrable for n = 1", cut[2] - cut[1] > 20)

# ---------------------------------------------------------------- 3. Casimir (symbolic)
t, x, nu_s, sig = sp.symbols('t x nu sigma')
w = sp.symbols('w')
nn = sp.symbols('n', positive=True, integer=True)
psi = sp.Function('psi')
upper = sp.Matrix([[1, t], [0, 1]])
lower = sp.Matrix([[1, 0], [t, 1]])
expH = sp.Matrix([[sp.exp(t), 0], [0, sp.exp(-t)]])


def d_line(expo, gam, expr):
    """Derived principal-series action along gam(t), at t = 0; den > 0 near t = 0."""
    den = gam[0, 1] * x + gam[1, 1]
    mob = (gam[0, 0] * x + gam[1, 0]) / den
    return sp.simplify(sp.diff(den ** expo * expr.subs(x, mob), t).subs(t, 0))


def d_disc(n, gam, expr):
    jac = gam[0, 1] * w + gam[1, 1]
    mob = (gam[0, 0] * w + gam[1, 0]) / jac
    return sp.simplify(sp.diff(jac ** (-n) * expr.subs(w, mob), t).subs(t, 0))


def casimir(d, f, symmetric=True):
    hh = d(expH, d(expH, f)) / 4
    ef = d(upper, d(lower, f))
    fe = d(lower, d(upper, f))
    return sp.simplify(hh + ((ef + fe) / 2 if symmetric else ef))


fP = psi(x)
cP = casimir(lambda gm, e: d_line(sp.I * nu_s - 1, gm, e), fP)
resP = sp.simplify(sp.expand(cP + (1 + nu_s ** 2) / 4 * fP))
print(f"principal Casimir - (-(1+nu^2)/4) psi = {resP}")
report("3a. Omega = -(1+nu^2)/4 on P^(eps, i nu)", resP == 0)
comm = sp.simplify(d_line(sp.I * nu_s - 1, upper, d_line(sp.I * nu_s - 1, lower, fP))
                   - d_line(sp.I * nu_s - 1, lower, d_line(sp.I * nu_s - 1, upper, fP))
                   - d_line(sp.I * nu_s - 1, expH, fP))
report("3b. [E, F] = H on P^(eps, i nu)", comm == 0)
cW = casimir(lambda gm, e: d_line(sp.I * nu_s, gm, e), fP)
resW = sp.simplify(sp.expand(cW + (1 + nu_s ** 2) / 4 * fP))
print(f"control (exponent i nu): Casimir + (1+nu^2)/4 psi = {sp.factor(resW)}")
report("3c. control: wrong exponent changes the Casimir", resW != 0)
cU = casimir(lambda gm, e: d_line(sp.I * nu_s - 1, gm, e), fP, symmetric=False)
resU = sp.simplify(sp.expand(cU + (1 + nu_s ** 2) / 4 * fP))
report("3d. control: H^2/4 + EF is not scalar", sp.diff(resU, x) != 0 or resU.has(sp.Derivative))

FD = psi(w)
cD = casimir(lambda gm, e: d_disc(nn, gm, e), FD)
resD = sp.simplify(sp.expand(cD - nn / 2 * (nn / 2 - 1) * FD))
print(f"discrete Casimir - (n/2)(n/2-1) F = {resD}")
report("3e. Omega = (n/2)(n/2-1) on D_n", resD == 0)
# j(j+1) normalisation: j = -s/2 with s = 1 - i nu, and j = -n/2
j = -(1 - sp.I * nu_s) / 2
report("3f. j(j+1) form: -(1+nu^2)/4 = j(j+1), j = -1/2 + i nu/2",
       sp.simplify(j * (j + 1) + (1 + nu_s ** 2) / 4) == 0)

# ---------------------------------------------------------------- 4. complementary series
# K-types of the line model with exponent sigma - 1 (ε = 0, m even):
#   phi_m(x) = (1+x^2)^((sigma-1)/2) ((1+ix)/(1-ix))^(m/2),
# rotation generator W = E - F; raising/lowering E_pm = H pm i (E+F).
expo = sig - 1


def phi(m):
    return (1 + x ** 2) ** ((sig - 1) / 2) * ((1 + sp.I * x) / (1 - sp.I * x)) ** (m // 2)


def D(gm, e):
    return d_line(expo, gm, e)


def num_ratio(expr, target, sv):
    """Values of expr/target at sample points x; constant iff expr is proportional to target."""
    q = sp.lambdify(x, (expr / target).subs(sig, sv), 'mpmath')
    return [complex(q(mp.mpf(xv))) for xv in (-1.7, -0.4, 0.3, 1.1, 2.6)]


def const(vals):
    return max(abs(v - vals[0]) for v in vals) < 1e-12 * max(1, abs(vals[0]))


ladder_ok, form_ok = True, True
for sv in (sp.Rational(3, 5), sp.Rational(3, 2), sp.Rational(37, 100)):
    for m in (-4, -2, 0, 2):
        Y = D(upper, phi(m)) + D(lower, phi(m))
        Yn = D(upper, phi(m + 2)) + D(lower, phi(m + 2))
        Wv = num_ratio(D(upper, phi(m)) - D(lower, phi(m)), phi(m), sv)
        ladder_ok = ladder_ok and const(Wv) and abs(Wv[0] + 1j * m) < 1e-12
        # E_pm = H pm i (E + F); find the raising one (phi_m -> phi_(m+2)) and its partner
        for sgn in (1, -1):
            up = num_ratio(D(expH, phi(m)) + sgn * sp.I * Y, phi(m + 2), sv)
            dn = num_ratio(D(expH, phi(m + 2)) - sgn * sp.I * Yn, phi(m), sv)
            if const(up) and const(dn):
                break
        else:
            ladder_ok = False
            continue
        # H, E+F skew-Hermitian  =>  (E_pm)^* = -E_mp  =>  lam_(m+2)/lam_m = -conj(dn)/up
        r = -dn[0].conjugate() / up[0]
        target = float((m + 1 + sv) / (m + 1 - sv))
        form_ok = form_ok and abs(r - target) < 1e-12
        print(f"   sigma={float(sv)}: lambda_{m + 2}/lambda_{m} = {r.real:+.12f}{r.imag:+.1e}i"
              f" (expect {target:+.12f})")
report("4a. W phi_m = -i m phi_m and a ladder pair E_pm maps phi_m <-> phi_(m+2)", ladder_ok)
report("4b. invariant form: ratio (m+1+sigma)/(m+1-sigma) for real sigma", form_ok)
inside = all((m + 1 + 0.6) / (m + 1 - 0.6) > 0 for m in range(-40, 41, 2))
outside = min((m + 1 + 1.5) / (m + 1 - 1.5) for m in range(-40, 41, 2))
print(f"   sigma = 0.6: all ratios positive: {inside};  sigma = 3/2: min ratio = {outside:.3f}")
report("4c. sigma = 0.6 (s = 0.3) positive; control sigma = 3/2 (s = 3/4) indefinite",
       inside and outside < 0)

# ---------------------------------------------------------------- 5. partial fractions
pf_ok = True
for nu in (0.3, 1.0, 2.7, 7.5):
    odd = 2 * mp.nsum(lambda k: nu ** 2 / ((2 * k - 1) ** 2 + nu ** 2), [1, mp.inf])
    even = 1 + 2 * mp.nsum(lambda k: nu ** 2 / ((2 * k) ** 2 + nu ** 2), [1, mp.inf])
    th = mp.pi * nu / 2 * mp.tanh(mp.pi * nu / 2)
    ch = mp.pi * nu / 2 * mp.coth(mp.pi * nu / 2)
    pf_ok = pf_ok and abs(odd - th) < 1e-12 and abs(even - ch) < 1e-12
    print(f"   nu={nu}: odd sum {float(odd):.12f} vs tanh {float(th):.12f};"
          f" even sum {float(even):.12f} vs coth {float(ch):.12f}")
report("5. odd series -> tanh, even series -> coth", pf_ok)

# ---------------------------------------------------------------- 6. spherical Plancherel
aa = mp.mpf(1)


def hat(rho):
    return mp.sqrt(2 / (mp.pi * aa)) * mp.besselk(1j * rho, aa).real


rho0 = mp.mpf('0.7')
direct = mp.quad(lambda X: mp.exp(-aa * X) * mp.legenp(-0.5 + 1j * rho0, 0, X, type=3).real,
                 [1, 5, 20, mp.inf])
print(f"   F^(0.7): direct quadrature {float(direct):.12f}, closed form {float(hat(rho0)):.12f}")
report("6a. Mehler-Fock transform of exp(-a x) = sqrt(2/(pi a)) K_(i rho)(a)",
       abs(direct - hat(rho0)) < 1e-10)
lhs = mp.exp(-aa)
rhs = mp.quad(lambda r: r * mp.tanh(mp.pi * r) * hat(r), [0, 5, 20, 60])
ctl = mp.quad(lambda r: r * mp.coth(mp.pi * r) * hat(r), [0, 5, 20, 60])
print(f"   F(1) = {float(lhs):.12f}; int rho tanh(pi rho) F^ = {float(rhs):.12f};"
      f" with coth: {float(ctl):.12f}")
report("6b. spherical Plancherel with density rho tanh(pi rho)", abs(lhs - rhs) < 1e-10)
report("6c. control: coth density gives a different value", abs(lhs - ctl) > 1e-3)

print("ALL OK" if ok else "FAILED")
sys.exit(0 if ok else 1)
