"""Numerical cross-check (not a proof) of the longest-chain statements of Lightlike/CausalSets.

* Exact enumeration: the sum of the length of a longest increasing subsequence over all permutations
  of n = 1..5 is 1, 3, 12, 58, 335, so E[LIS] = 2 for n = 3 (the Lean theorems `sum_longestChain_*`).
* Monte Carlo (numpy, fixed seed): the longest chain of n = 3 uniform points of the unit square
  (light-cone coordinates of the 1+1 diamond, product order) has mean 2.
* Asymptotics: the mean over many points divided by sqrt(n) approaches 2 slowly from below
  (Vershik-Kerov, Logan-Shepp), not 1.
* Wrong-input controls, each must be detected: a reversed permutation has longest chain 1, not n; the
  constant 1 in c sqrt(n) is not the value at n = 3 (sqrt(3) != 2); a non-uniform (comonotone)
  sample does not give mean 2.
Exit 0 when all agree and every control is detected."""
import itertools
import sys
import numpy as np

fails = []

def check(name, ok):
    print(("ok   " if ok else "FAIL ") + name)
    if not ok:
        fails.append(name)

def lis(p):
    n = len(p)
    best = 0
    for m in range(1 << n):
        idx = [i for i in range(n) if m >> i & 1]
        if all(p[idx[k]] < p[idx[k + 1]] for k in range(len(idx) - 1)):
            best = max(best, len(idx))
    return best

for n, want in zip(range(1, 6), (1, 3, 12, 58, 335)):
    got = sum(lis(p) for p in itertools.permutations(range(n)))
    check(f"sum of LIS over S_{n} = {got} (expected {want})", got == want)

rng = np.random.default_rng(20240607)

def longest_chain_points(pts):
    pts = sorted(pts.tolist())
    ys = [y for _, y in pts]
    tails = []
    import bisect
    for y in ys:
        k = bisect.bisect_left(tails, y)
        if k == len(tails):
            tails.append(y)
        else:
            tails[k] = y
    return len(tails)

m3 = np.mean([longest_chain_points(rng.random((3, 2))) for _ in range(40000)])
check(f"Monte Carlo n=3 mean longest chain {m3:.3f} vs 2", abs(m3 - 2) < 0.02)
n = 400
mn = np.mean([longest_chain_points(rng.random((n, 2))) for _ in range(40)]) / np.sqrt(n)
check(f"n=400: mean/sqrt(n) = {mn:.3f}, below 2 and above 1.5", 1.5 < mn < 2.0)

# controls
check("control: reversed permutation has longest chain 1", lis([3, 2, 1, 0]) == 1)
check("control: sqrt(3) is not 2", abs(np.sqrt(3) - 2) > 0.2)
bad = np.mean([longest_chain_points(np.column_stack([r, r + 0.0 * r])) for r in rng.random((4000, 3))])
check(f"control: comonotone points give mean {bad:.3f}, not 2", abs(bad - 2) > 0.5)

if fails:
    print("FAILED:", fails)
    sys.exit(1)
print("all CS3 values agree")
