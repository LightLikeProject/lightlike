"""Numerical check (sympy + exact trapezoid rule for trigonometric polynomials) that on the 3-torus
  int -1/4 h_ij e_ikl e_jmn d_k d_m h_ln  =  int fpDens(dh),
and a wrong-input control: a non-periodic field breaks the equality. Evidence, not proof."""
import itertools, random
import numpy as np, sympy as sp

x = sp.symbols("x0 x1 x2")
def eps(i, j, k): return sp.LeviCivita(i, j, k)
def field(periodic, seed):
    rnd = random.Random(seed)
    def trig():
        t = 0
        for _ in range(3):
            n = [rnd.randint(-1, 1) for _ in range(3)]
            a, b = rnd.uniform(-1, 1), rnd.uniform(-1, 1)
            ph = 2 * sp.pi * sum(n[i] * x[i] for i in range(3))
            t += a * sp.sin(ph) + b * sp.cos(ph)
        return t
    h = [[None] * 3 for _ in range(3)]
    for i in range(3):
        for j in range(i, 3):
            f = trig()
            if not periodic:
                f += rnd.uniform(0.5, 1) * x[0] * x[1] + rnd.uniform(0.5, 1) * x[2] ** 2
            h[i][j] = h[j][i] = f
    return h
def densities(h):
    d = lambda f, k: sp.diff(f, x[k])
    sv = sum(h[i][j] * eps(i, k, l) * eps(j, m, n) * d(d(h[l][n], m), k)
             for i in range(3) for j in range(3) for k in range(3) for l in range(3) for m in range(3) for n in range(3)
             if eps(i, k, l) != 0 and eps(j, m, n) != 0)
    dh = [[[d(h[i][j], k) for j in range(3)] for i in range(3)] for k in range(3)]
    div = [sum(dh[m][m][n] for m in range(3)) for n in range(3)]
    tr = [sum(dh[k][i][i] for i in range(3)) for k in range(3)]
    fp = (-sp.Rational(1, 4) * sum(dh[l][m][n] ** 2 for l in range(3) for m in range(3) for n in range(3))
          + sp.Rational(1, 2) * sum(c ** 2 for c in div) - sp.Rational(1, 2) * sum(div[n] * tr[n] for n in range(3))
          + sp.Rational(1, 4) * sum(c ** 2 for c in tr))
    return -sp.Rational(1, 4) * sv, fp
def integral(expr):
    f = sp.lambdify(x, expr, "numpy")
    N = 8; g = (np.arange(N) + 0.5) / N
    X = np.meshgrid(g, g, g, indexing="ij")
    return float(np.mean(f(*X)))
worst = {}
for periodic in (True, False):
    errs = []
    for seed in range(4):
        a, b = densities(field(periodic, seed))
        errs.append(abs(integral(a) - integral(b)))
    worst[periodic] = max(errs)
    print("periodic" if periodic else "NOT periodic (control)", "max |int(sv) - int(fp)| =", max(errs))
assert worst[True] < 1e-10, "the two integrals must agree for periodic fields"
assert worst[False] > 1.0, "control: a non-periodic field must break the equality"
print("OK: equal for periodic fields, control fails")
