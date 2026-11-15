"""Numerical check of Regge's equations dS/dl_e = deficit_e (numerical evidence, not proof).

The complex is the boundary of the 4-simplex (five tetrahedra on vertices 0..4, every edge in three
tetrahedra, no boundary). Edge lengths are random perturbations of 1. For each edge e the central
finite difference of the Regge action S = sum_e l_e (2 pi - sum_t theta_t(e)) is compared with the
deficit angle at e. Control: the individual terms l_f d(theta_f)/d(l_e) of Schläfli's sum are not
small, so the agreement is a genuine cancellation, not a numerical accident.
"""
import itertools, math, random, sys

def dihedral(pq, pr, qr, ps, qs, rs):
    # same formula as Lightlike.PR.cosDihedral / Lightlike.PR.dihedral
    ru = (pr**2 + pq**2 - qr**2) / (2 * pq)
    su = (ps**2 + pq**2 - qs**2) / (2 * pq)
    c = ((pr**2 + ps**2 - rs**2) / 2 - ru * su) / math.sqrt((pr**2 - ru**2) * (ps**2 - su**2))
    return math.acos(c)

V = range(5)
edges = [frozenset(e) for e in itertools.combinations(V, 2)]
tets = [frozenset(t) for t in itertools.combinations(V, 4)]

def angle(L, t, e):
    p, q = sorted(e)
    r, s = sorted(t - e)
    l = lambda a, b: L[frozenset((a, b))]
    return dihedral(l(p, q), l(p, r), l(q, r), l(p, s), l(q, s), l(r, s))

def deficit(L, e):
    return 2 * math.pi - sum(angle(L, t, e) for t in tets if e <= t)

def action(L):
    return sum(L[e] * deficit(L, e) for e in edges)

random.seed(1)
L = {e: 1 + 0.15 * (random.random() - 0.5) for e in edges}
h = 1e-6
worst = 0.0
for e in edges:
    Lp, Lm = dict(L), dict(L)
    Lp[e] += h; Lm[e] -= h
    dS = (action(Lp) - action(Lm)) / (2 * h)
    worst = max(worst, abs(dS - deficit(L, e)))
print(f"max |dS/dl_e - deficit_e| over 10 edges: {worst:.2e}")

# control: the terms of Schläfli's sum for one tetrahedron and one varied edge are not small
t = tets[0]
e = edges[0]
terms = []
for f in [x for x in edges if x <= t]:
    Lp, Lm = dict(L), dict(L)
    Lp[e] += h; Lm[e] -= h
    terms.append(L[f] * (angle(Lp, t, f) - angle(Lm, t, f)) / (2 * h))
print(f"Schläfli terms l_f dtheta_f/dl_e: max |term| = {max(abs(x) for x in terms):.3f}, "
      f"sum = {sum(terms):.2e}")
ok = worst < 1e-6 and max(abs(x) for x in terms) > 0.05 and abs(sum(terms)) < 1e-6
print("ALL CHECKS PASS" if ok else "CHECK FAILED")
sys.exit(0 if ok else 1)
