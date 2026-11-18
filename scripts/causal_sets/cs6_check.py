"""Numerical cross-check (not a proof) of the transitive-percolation statements of
Lightlike/CausalSets/Growth.lean.

* Enumeration: the numbers of naturally labelled posets on 1..4 elements are 1, 2, 7, 40, and the
  weights p^a q^b (a = number of maximal elements of the pasts, b = elements outside the past) sum
  to 1 for n = 2, 3 (SymPy, exact).
* Monte Carlo (numpy, fixed seed): independent links with probability p, transitive closure; the
  frequency of each 3-element poset matches the weight.
* Wrong-input controls, each must be detected: dropping the elements-outside-the-past factor q^b gives
  weights that do not sum to 1; the antichain frequency is not p^3.
Exit 0 when all agree and every control is detected."""
import itertools
import sys
import numpy as np
from sympy import symbols, simplify, Rational

p = symbols("p")
q = 1 - p
fails = []

def check(name, ok):
    print(("ok   " if ok else "FAIL ") + name)
    if not ok:
        fails.append(name)

def nat_posets(n):
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    out = []
    for bits in itertools.product([0, 1], repeat=len(pairs)):
        r = {pr for pr, b in zip(pairs, bits) if b}
        if all((i, k) in r for (i, j) in r for (j2, k) in r if j == j2):
            out.append(frozenset(r))
    return out

def weight(P, n):
    w = 1
    for j in range(n):
        D = {i for i in range(j) if (i, j) in P}
        m = [i for i in D if not any((i, k) in P for k in D)]
        w *= p ** len(m) * q ** (j - len(D))
    return w

for n, want in zip(range(1, 5), (1, 2, 7, 40)):
    check(f"number of naturally labelled posets on {n} = {len(nat_posets(n))}", len(nat_posets(n)) == want)
for n in (2, 3, 4):
    tot = simplify(sum(weight(P, n) for P in nat_posets(n)))
    check(f"weights sum to 1 for n={n}", tot == 1)

rng = np.random.default_rng(20240607)
pv = 0.3
N = 60000
counts = {}
for _ in range(N):
    links = {(i, j) for i in range(3) for j in range(i + 1, 3) if rng.random() < pv}
    closed = set(links)
    if (0, 1) in closed and (1, 2) in closed:
        closed.add((0, 2))
    counts[frozenset(closed)] = counts.get(frozenset(closed), 0) + 1
ok = True
for P in nat_posets(3):
    f = counts.get(P, 0) / N
    w = float(weight(P, 3).subs(p, pv))
    ok = ok and abs(f - w) < 0.01
check("Monte Carlo frequencies match the weights for n=3, p=0.3", ok)

# controls
nob = simplify(sum(
    __import__("math").prod(p ** len([i for i in {a for a in range(j) if (a, j) in P}
                                      if not any((i, k) in P for k in {a for a in range(j) if (a, j) in P})])
                            for j in range(3)) for P in nat_posets(3)))
check("control: weights without the q factors do not sum to 1", simplify(nob - 1) != 0)
check("control: antichain frequency is not p^3",
      abs(counts.get(frozenset(), 0) / N - pv ** 3) > 0.01)

if fails:
    print("FAILED:", fails)
    sys.exit(1)
print("all CS6 values agree")
