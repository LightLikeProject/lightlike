"""Numerical check of the 4D Regge equations (numerical evidence, not proof).

On the boundary of the 5-simplex (six 4-simplices, a triangulated 4-sphere) with randomly perturbed
edge lengths, compare the gradient of the Regge action S = sum_t A_t delta_t, computed by central
finite differences, with Regge's formula proven in Lightlike/Regge/D4/ReggeEquations.lean:

    dS/dl_e = sum_{t contains e} (dA_t/dl_e) delta_t,   dA_t/dl_e = l_e (l_f^2 + l_g^2 - l_e^2) / (8 A_t).

Also check Schlaefli's identity on one 4-simplex: along a random direction, sum_t A_t dtheta_t = 0
while the individual terms are of order one. Controls: the gradient without the area factor
(sum_{t contains e} delta_t, the 3D form) and a Schlaefli sum with one triangle dropped do not match.
"""
import itertools
import math
import random
import sys

V = range(6)
SIMPS = [frozenset(s) for s in itertools.combinations(V, 5)]
TRIS = [frozenset(t) for t in itertools.combinations(V, 3)]
EDGES = [frozenset(e) for e in itertools.combinations(V, 2)]


def sq(l, a, b):
    return 0.0 if a == b else l[frozenset((a, b))] ** 2


def ip(l, o, a, b):
    return (sq(l, o, a) + sq(l, o, b) - sq(l, a, b)) / 2


def det3(m):
    return (m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1])
            - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
            + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0]))


def gram3(l, p, q, r, s):
    pts = [q, r, s]
    return det3([[ip(l, p, i, j) for j in pts] for i in pts])


def mixed(l, p, q, r, s, u):
    return det3([[ip(l, p, i, j) for j in (q, r, u)] for i in (q, r, s)])


def dihedral(l, t, sigma):
    p, q, r = sorted(t)
    s, u = sorted(sigma - t)
    c = mixed(l, p, q, r, s, u) / math.sqrt(gram3(l, p, q, r, s) * gram3(l, p, q, r, u))
    return math.acos(c)


def area(l, t):
    p, q, r = sorted(t)
    g2 = ip(l, p, q, q) * ip(l, p, r, r) - ip(l, p, q, r) ** 2
    return math.sqrt(g2) / 2


def deficit(l, t):
    return 2 * math.pi - sum(dihedral(l, t, s) for s in SIMPS if t <= s)


def action(l):
    return sum(area(l, t) * deficit(l, t) for t in TRIS)


def area_partial(l, t, e):
    f, g = [x for x in EDGES if x <= t and x != e]
    return l[e] * (l[f] ** 2 + l[g] ** 2 - l[e] ** 2) / (8 * area(l, t))


random.seed(7)
l = {e: 1 + random.uniform(-0.1, 0.1) for e in EDGES}
h = 1e-6
err, err_ctrl = 0.0, 0.0
for e in EDGES:
    lp, lm = dict(l), dict(l)
    lp[e] += h
    lm[e] -= h
    fd = (action(lp) - action(lm)) / (2 * h)
    formula = sum(area_partial(l, t, e) * deficit(l, t) for t in TRIS if e <= t)
    ctrl = sum(deficit(l, t) for t in TRIS if e <= t)
    err = max(err, abs(fd - formula))
    err_ctrl = max(err_ctrl, abs(fd - ctrl))
print(f"Regge's equations: max |FD - sum dA/dl delta| = {err:.2e}")
print(f"control (no area factor):  max |FD - sum delta| = {err_ctrl:.2e}")

# Schlaefli on one 4-simplex
sigma = SIMPS[0]
v = {e: random.uniform(-1, 1) for e in EDGES}
ts = [t for t in TRIS if t <= sigma]


def angle_sum(tau, drop=None):
    lt = {e: l[e] + tau * v[e] for e in EDGES}
    return sum(area(l, t) * dihedral(lt, t, sigma) for t in ts if t != drop)


terms = []
for t in ts:
    lp = {e: l[e] + h * v[e] for e in EDGES}
    lm = {e: l[e] - h * v[e] for e in EDGES}
    terms.append(area(l, t) * (dihedral(lp, t, sigma) - dihedral(lm, t, sigma)) / (2 * h))
print(f"Schlaefli: largest term |A dtheta| = {max(abs(x) for x in terms):.3f}, "
      f"sum = {sum(terms):.2e}")
drop = (angle_sum(h, ts[0]) - angle_sum(-h, ts[0])) / (2 * h)
print(f"control (one triangle dropped): sum = {drop:.3f}")
ok = err < 1e-6 and err_ctrl > 1e-2 and abs(sum(terms)) < 1e-6 and abs(drop) > 1e-2
print("ALL CHECKS PASS" if ok else "CHECK FAILED")
sys.exit(0 if ok else 1)
