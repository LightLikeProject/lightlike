"""Route C test (G3-196 attempt 3): does the x-sum of q-Biedenharn-Elliott admit a TERMWISE
recurrence in the external colour p with coefficients independent of x?  Python, mpmath, uses q6j
of scripts/tv_check.py.  Usage: python3 be_recurrence_test.py R [kmax]"""
import sys, os, random, itertools
sys.argv_saved = sys.argv[:]
sys.argv = [sys.argv[0]]
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from mpmath import mp, mpf, matrix, svd_r
import importlib.util
spec = importlib.util.spec_from_file_location('tvc', os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tv_check.py'))
src = open(spec.origin).read().split('\ndef check_classical')[0]   # only the definitions
ns = {}
exec(compile(src, 'tv_check_defs', 'exec'), ns)
q6j, qnum = ns['q6j'], ns['qnum']
mp.dps = 40
R = int(sys.argv_saved[1]) if len(sys.argv_saved) > 1 else 7
KMAX = int(sys.argv_saved[2]) if len(sys.argv_saved) > 2 else 3

def term(x, a, b, c, d, e, f, p, q, r_):
    S = a + b + c + d + e + f + p + q + r_
    if (S + x) % 2: return mpf(0)
    return (-1) ** ((S + x) // 2) * qnum(x + 1, R) * q6j(a, b, x, c, d, p, R) * q6j(c, d, x, e, f, q, R) * q6j(e, f, x, b, a, r_, R)

def rhs(a, b, c, d, e, f, p, q, r_):
    return q6j(p, q, r_, e, a, d, R) * q6j(p, q, r_, f, b, c, R)

def lhs(*t):
    return sum(term(x, *t) for x in range(0, R - 1))

random.seed(3)
M = R - 2
worst = mpf(0); n = 0
res = {}
tries = 0
while n < 400 and tries < 400000:
    tries += 1
    lo, hi = M // 3, (2 * M) // 3 + 1
    a, b, c, d, e, f = [random.randint(lo, hi) for _ in range(6)]
    q, r_ = [random.randint(0, M) for _ in range(2)]
    p0 = random.randint(0, M // 2)
    # BE check at p0 where both sides nonzero
    rr = rhs(a, b, c, d, e, f, p0, q, r_)
    if rr == 0: continue
    err = abs(lhs(a, b, c, d, e, f, p0, q, r_) - rr)
    worst = max(worst, err)
    # termwise nullity: columns p0, p0+2, ..., rows x
    for k in range(1, KMAX + 1):
        cols = []
        for j in range(k + 1):
            pj = p0 + 2 * j
            if pj > M: break
            cols.append([term(x, a, b, c, d, e, f, pj, q, r_) for x in range(0, R - 1)])
        if len(cols) < k + 1: break
        nzrows = [i for i in range(len(cols[0])) if any(abs(col[i]) > mpf(10) ** -30 for col in cols)]
        if len(nzrows) < k + 2: continue   # not discriminating
        cols = [[col[i] for i in nzrows] for col in cols]
        A = matrix(len(cols[0]), len(cols))
        for j, col in enumerate(cols):
            for i, v in enumerate(col): A[i, j] = v
        s = svd_r(A, compute_uv=False)
        smin = s[len(cols) - 1] if len(cols[0]) >= len(cols) else mpf(0)
        smax = s[0]
        null = smax > mpf(10) ** -30 and smin / smax < mpf(10) ** -25
        res.setdefault(k, [0, 0]); res[k][1] += 1; res[k][0] += int(null)
    n += 1
print(f"r={R}: BE worst |LHS-RHS| over {n} tuples: {float(worst):.2e}")
for k, (nn, tot) in sorted(res.items()):
    print(f"termwise recurrence of order {k} in p (coefficients independent of x) exists in {nn}/{tot} tuples")
