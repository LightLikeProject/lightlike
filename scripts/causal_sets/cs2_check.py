"""Numerical cross-check (not a proof) of the relation probabilities of Lightlike/CausalSets.

`p` is the probability that two independent uniform points x, y of a region of Minkowski space
(time first) satisfy x < y: y - x is future causal and nonzero. For n points the expected number of
relations is n (n - 1) p.

* Exact (SymPy): the 1+1 diamond gives 1/4 (light-cone coordinates u = t + x, v = t - x make it the
  unit square, ordered coordinatewise); the rectangle [0,1] x [0,2] (time extent 1, space extent 2)
  gives the integral of (1 - s)(s - s^2/4) over [0,1], which is 7/48.
* Myrheim-Meyer formula Gamma(D+1) Gamma(D/2) / (4 Gamma(3D/2)): 1/2 at D = 1, 1/4 at D = 2, 4/35 at
  D = 3 and 1/20 at D = 4; it equals the Beta form (d/2) B((d+3)/2, d) of the proof (d = D - 1).
* Monte Carlo (numpy, fixed seed): the 1+1 diamond sampled in (t, x) coordinates, the 1+1 rectangle,
  and the 3+1 diamond, which agree with the exact values to the statistical error.
* Wrong-input controls, each must be detected: the rectangle value is not the diamond value; a
  3+1 unit cube does not give 1/20; the formula with Gamma(D) instead of Gamma(D+1) is not 1/4.
Exit 0 when all values agree and every control is detected."""
import sys
import numpy as np
from sympy import Rational, gamma, integrate, symbols, simplify

s = symbols("s", positive=True)
fails = []

def check(name, ok):
    print(("ok   " if ok else "FAIL ") + name)
    if not ok:
        fails.append(name)

def mm(D, shift=1):
    return gamma(D + shift) * gamma(Rational(D, 2)) / (4 * gamma(Rational(3 * D, 2)))

# exact values
rect = integrate((1 - s) * (s - s**2 / 4), (s, 0, 1))
check("rectangle [0,1]x[0,2]: 7/48", simplify(rect - Rational(7, 48)) == 0)
check("Myrheim-Meyer D=2 is 1/4", simplify(mm(2) - Rational(1, 4)) == 0)
check("Myrheim-Meyer D=4 is 1/20", simplify(mm(4) - Rational(1, 20)) == 0)
unit_square = integrate((1 - s) * (2 * s - s**2), (s, 0, 1))
check("square [0,1]x[0,1] in (t,x) also gives 1/4 (coincidence of the 1+1 case)",
      simplify(unit_square - Rational(1, 4)) == 0)

# the Beta-integral form of the proof, (d/2) B((d+3)/2, d), equals the Gamma form for d = 1..8
from sympy import beta as sym_beta
for dd in range(1, 9):
    ok = simplify(gamma(Rational(dd + 3, 2)) * gamma(dd) / gamma(Rational(3 * dd + 3, 2)) * Rational(dd, 2)
                  - mm(dd + 1)) == 0
    check(f"Beta form (d/2) B((d+3)/2, d) = Myrheim-Meyer formula at D={dd + 1}", ok)
check("Myrheim-Meyer D=1 (two points of an interval) is 1/2", simplify(mm(1) - Rational(1, 2)) == 0)
check("Myrheim-Meyer D=3 is 4/35", simplify(mm(3) - Rational(4, 35)) == 0)

rng = np.random.default_rng(20240607)

def related(a, b):
    d = b - a
    sp = np.sum(d[:, 1:] ** 2, axis=1)
    return (d[:, 0] >= 0) & (sp <= d[:, 0] ** 2) & np.any(d != 0, axis=1)

def sample(kind, dim, n):
    """n uniform points of the region: 'diamond' (D = dim) or 'box' with the given side lengths."""
    out = []
    while sum(len(o) for o in out) < n:
        if kind == "diamond":
            lo = np.array([0.0] + [-0.5] * (dim - 1))
            hi = np.array([1.0] + [0.5] * (dim - 1))
            p = lo + (hi - lo) * rng.random((4 * n, dim))
            keep = np.sum(p[:, 1:] ** 2, axis=1) <= np.minimum(p[:, 0], 1 - p[:, 0]) ** 2
            out.append(p[keep])
        else:
            out.append(np.array(kind) * rng.random((n, len(kind))))
    return np.concatenate(out)[:n]

def mc(kind, dim, n=2_000_000):
    a, b = sample(kind, dim, n), sample(kind, dim, n)
    return float(np.mean(related(a, b)))

TOL = 1.5e-3
d2 = mc("diamond", 2)
check(f"Monte Carlo 1+1 diamond {d2:.4f} vs 1/4", abs(d2 - 0.25) < TOL)
r2 = mc((1.0, 2.0), 2)
check(f"Monte Carlo 1+1 rectangle {r2:.4f} vs 7/48", abs(r2 - 7 / 48) < TOL)
d3 = mc("diamond", 3)
check(f"Monte Carlo 2+1 diamond {d3:.4f} vs 4/35", abs(d3 - 4 / 35) < TOL)
d4 = mc("diamond", 4)
check(f"Monte Carlo 3+1 diamond {d4:.4f} vs 1/20", abs(d4 - 1 / 20) < TOL)

# wrong-input controls (each must be detected)
check("control: rectangle value differs from the diamond value", abs(7 / 48 - 0.25) > 0.05)
c4 = mc((1.0, 1.0, 1.0, 1.0), 4)
check(f"control: 3+1 unit cube {c4:.4f} is not 1/20", abs(c4 - 1 / 20) > 10 * TOL)
check("control: Gamma(D) instead of Gamma(D+1) is not 1/4 at D=2", simplify(mm(2, shift=0) - Rational(1, 4)) != 0)
check("control: MC detects the wrong 1+1 value 1/5", abs(d2 - 0.2) > TOL)

if fails:
    print("FAILED:", fails)
    sys.exit(1)
print("all CS2 values agree")
