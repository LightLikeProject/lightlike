"""Numerical check (not a proof) of the Turaev-Viro ingredients, in the conventions of
Lightlike/PonzanoRegge with integers replaced by quantum integers.

q = exp(i pi / r), [n] = sin(n pi / r) / sin(pi / r). Doubled spins J = 2j in {0, ..., r-2}.
Admissible triad (a, b, c): a + b + c even, triangle inequalities, a + b + c <= 2 (r - 2).
q-6j by the q-Racah formula (Kirillov-Reshetikhin), with Delta(a,b,c)^2 = [s-a]![s-b]![s-c]!/[s+1]!;
this is `qSixJ` of Lightlike/TuraevViro/QSixJ.lean (same z-range, same signs).

Default run (`python3 scripts/tv_check.py`, needs numpy, mpmath, sympy; about 1 minute):
 A. The Lean propositions `Model.BE` and `Model.Orth` of `tvModel r`
 (Lightlike/TuraevViro/Model.lean),
    evaluated exactly as stated, r = 4..8: BE with sign (-1)^((a+b+c+d+e+f+p+q+r+x)/2) (floor
    division on naturals), weight dim x = [x+1], and ALL labels a..r in 0..r-2 (labels >= r-1 are
    sampled: both sides vanish); Orth for all B A E F q, with its `if ok .. then 1/dim q else 0`.
 B. An independent source of q-6j values: Temperley-Lieb / Jones-Wenzl evaluation of the
    tetrahedral network (Kauffman-Lins gauge, loop value -[2]), divided by sqrt|prod of the four
    thetas|. It uses no q-Racah sum and no factorial formula; compared with `qSixJ` in sign and
    value for r = 4..8, plus six printed values.
 C. Wrong-input controls, which must FAIL: flipped sign in BE, integer dimensions, a wrong q
    (formula at pi/(r+1)), the TL value in the other loop-value gauge, TL at a wrong r.
 D. r = infinity (ordinary factorials): q-Racah equals SymPy's wigner_6j (convention check).
Options: `--moves` also runs the older checks of the 2-3 move, the 1-4 move and a different
orthogonality identity (r = 3..6, slow; `--long` adds 7); `--wrong-dim` is the old control.
"""
import itertools, sys
from functools import lru_cache
from mpmath import mp, mpf, sin, pi, sqrt
from sympy import Rational
from sympy.physics.wigner import wigner_6j

mp.dps = 40
WRONG = "--wrong-dim" in sys.argv

def qnum(n, r):
    if r is None:
        return mpf(n)
    return sin(n * pi / r) / sin(pi / r)

@lru_cache(maxsize=None)
def qfact(n, r):
    out = mpf(1)
    for k in range(1, n + 1):
        out *= qnum(k, r)
    return out

def adm(a, b, c, r):
    if (a + b + c) % 2 or c > a + b or a > b + c or b > a + c:
        return False
    return r is None or a + b + c <= 2 * (r - 2)

def delta(a, b, c, r):
    s = (a + b + c) // 2
    return sqrt(qfact(s - a, r) * qfact(s - b, r) * qfact(s - c, r) / qfact(s + 1, r))

@lru_cache(maxsize=None)
def q6j(j1, j2, j3, j4, j5, j6, r):
    """{j1 j2 j3; j4 j5 j6}_q, doubled units; triads (123)(156)(426)(453)."""
    tri = [(j1, j2, j3), (j1, j5, j6), (j4, j2, j6), (j4, j5, j3)]
    if not all(adm(*t, r) for t in tri):
        return mpf(0)
    al = [sum(t) // 2 for t in tri]
    be = [(j1 + j2 + j4 + j5) // 2, (j2 + j3 + j5 + j6) // 2, (j3 + j1 + j6 + j4) // 2]
    tot = mpf(0)
    for z in range(max(al), min(be) + 1):
        den = qfact(z - al[0], r) * qfact(z - al[1], r) * qfact(z - al[2], r) * \
            qfact(z - al[3], r) * qfact(be[0] - z, r) * qfact(be[1] - z, r) * qfact(be[2] - z, r)
        tot += (-1) ** z * qfact(z + 1, r) / den
    pre = 1
    for t in tri:
        pre *= delta(*t, r)
    return pre * tot

def dim(J, r):
    return mpf(J + 1) if WRONG else qnum(J + 1, r)

def ew(J, r):
    return (-1) ** J * dim(J, r)

def ts(a, b, c):
    return (-1) ** ((a + b + c) // 2)

def tet(col, p, q_, r_, s, r):
    e = lambda u, v: col[frozenset((u, v))]
    return q6j(e(p, q_), e(q_, r_), e(r_, p), e(r_, s), e(p, s), e(q_, s), r)

def check_classical(jmax2=3):
    err = 0
    for js in itertools.product(range(jmax2 + 1), repeat=6):
        a = q6j(*js, None)
        b = wigner_6j(*[Rational(j, 2) for j in js]) if all(
            adm(*t, None) for t in [(js[0], js[1], js[2]), (js[0], js[4], js[5]),
                                    (js[3], js[1], js[5]), (js[3], js[4], js[2])]) else 0
        err = max(err, abs(a - mpf(float(b))))
    return err

def check_23(r):
    S = range(r - 1)
    E9 = ["AB", "BC", "CA", "AD", "BD", "CD", "AE", "BE", "CE"]
    err, n = mpf(0), 0
    for vals in itertools.product(S, repeat=9):
        col = {frozenset(k): v for k, v in zip(E9, vals)}
        lhs = ts(col[frozenset("AB")], col[frozenset("BC")], col[frozenset("CA")]) * \
            tet(col, "A", "B", "C", "D", r) * tet(col, "A", "B", "C", "E", r)
        rhs = mpf(0)
        for x in S:
            col[frozenset("DE")] = x
            f = lambda u, v: col[frozenset((u, v))]
            rhs += ew(x, r) * ts(f("A", "D"), f("D", "E"), f("E", "A")) * \
                ts(f("B", "D"), f("D", "E"), f("E", "B")) * ts(f("C", "D"), f("D", "E"), f("E", "C")) * \
                tet(col, "A", "B", "D", "E", r) * tet(col, "B", "C", "D", "E", r) * \
                tet(col, "C", "A", "D", "E", r)
        if lhs != 0 or rhs != 0:
            n += 1
        err = max(err, abs(lhs - rhs))
    return err, n

def check_orth(r):
    S = range(r - 1)
    err = mpf(0)
    for a, b, c, d, f, f2 in itertools.product(S, repeat=6):
        tot = sum(dim(x, r) * dim(f, r) * q6j(a, b, x, c, d, f, r) * q6j(a, b, x, c, d, f2, r)
                  for x in S)
        want = 1 if (f == f2 and adm(b, c, f, r) and adm(a, f, d, r)) else 0
        err = max(err, abs(tot - want))
    return err

def check_14(r):
    S = range(r - 1)
    old = ["AB", "AC", "AD", "BC", "BD", "CD"]
    err, n = mpf(0), 0
    for vals in itertools.product(S, repeat=6):
        col = {frozenset(k): v for k, v in zip(old, vals)}
        rhs0 = tet(col, "A", "B", "C", "D", r)
        for d in S:
            col[frozenset("DE")] = d
            lhs = mpf(0)
            for a, b, c in itertools.product(S, repeat=3):
                col[frozenset("AE")], col[frozenset("BE")], col[frozenset("CE")] = a, b, c
                t = tet(col, "A", "B", "C", "E", r) * tet(col, "A", "B", "D", "E", r) * \
                    tet(col, "A", "C", "D", "E", r) * tet(col, "B", "C", "D", "E", r)
                if t == 0:
                    continue
                f = lambda u, v: col[frozenset((u, v))]
                sg = 1
                for (u, v) in [("A", "B"), ("A", "C"), ("A", "D"), ("B", "C"), ("B", "D"), ("C", "D")]:
                    sg *= ts(f(u, v), f(v, "E"), f(u, "E"))
                lhs += ew(a, r) * ew(b, r) * ew(c, r) * ew(d, r) * sg * t
            rhs = dim(d, r) ** 2 * rhs0
            if lhs != 0 or rhs != 0:
                n += 1
            err = max(err, abs(lhs - rhs))
    return err, n


# --- Temperley-Lieb machinery (independent of the q-Racah formula) ---
import math

def walk_graph(nodes_adj, ends):
    """nodes_adj: dict node -> list of neighbours (multi-edges allowed, list order irrelevant).
    ends: nodes of degree 1. Returns (pairing of ends, number of closed cycles)."""
    used = set()
    pairing = {}
    def step(start):
        prev, cur = None, start
        path = [start]
        while True:
            nb = list(nodes_adj[cur])
            if prev is not None:
                nb.remove(prev)
            if not nb:
                return cur
            prev, cur = cur, nb[0]
            path.append(cur)
            used.add(cur)
    for e in ends:
        if e in pairing:
            continue
        used.add(e)
        other = step(e)
        pairing[e] = other; pairing[other] = e
    loops = 0
    for nd in nodes_adj:
        if nd in used:
            continue
        # cycle
        loops += 1
        stack = [nd]
        while stack:
            c = stack.pop()
            if c in used: continue
            used.add(c)
            stack.extend(nodes_adj[c])
    return pairing, loops

def compose(top, bot, n):
    adj = {}
    def add(a, b):
        adj.setdefault(a, []).append(b); adj.setdefault(b, []).append(a)
    def nm(side, k):  # side 'bot' or 'top'
        if side == 'bot':
            return ('B', k) if k < n else ('G', k - n)
        return ('G', k) if k < n else ('T', k - n)
    for k in range(2 * n):
        if bot[k] > k: add(nm('bot', k), nm('bot', bot[k]))
        if top[k] > k: add(nm('top', k), nm('top', top[k]))
    ends = [('B', i) for i in range(n)] + [('T', i) for i in range(n)]
    pr, loops = walk_graph(adj, ends)
    idx = lambda x: x[1] if x[0] == 'B' else n + x[1]
    out = [None] * (2 * n)
    for a, b in pr.items():
        out[idx(a)] = idx(b)
    return tuple(out), loops

def ident(n): return tuple([n + i for i in range(n)] + [i for i in range(n)])

def gen_e(n, i):
    m = list(ident(n))
    m[i], m[i + 1] = i + 1, i
    m[n + i], m[n + i + 1] = n + i + 1, n + i
    return tuple(m)

def tensor1(D, n):
    """D on n strands -> D (x) identity on n+1 strands."""
    m = [None] * (2 * (n + 1))
    for k in range(2 * n):
        j = D[k]
        f = lambda t: t if t < n else t + 1
        m[f(k)] = f(j)
    m[n] = 2 * n + 1; m[2 * n + 1] = n
    return tuple(m)

def jw(n, d, qn, kl=False):
    """Jones-Wenzl projector as {diagram: coeff}; d = loop value [2]; qn(k) = [k]."""
    P = {ident(1): 1.0}
    for m in range(1, n):
        Pn1 = {tensor1(D, m): c for D, c in P.items()}
        e = gen_e(m + 1, m - 1)
        new = dict(Pn1)
        fac = (qn(m) / qn(m + 1)) if kl else -qn(m) / qn(m + 1)
        for D1, c1 in Pn1.items():
            t1, l1 = compose(e, D1, m + 1)
            for D2, c2 in Pn1.items():
                t2, l2 = compose(D2, t1, m + 1)
                new[t2] = new.get(t2, 0.0) + fac * c1 * c2 * d ** (l1 + l2)
        P = {k: v for k, v in new.items() if abs(v) > 1e-15}
    return P

def network(edges, rot, colors, d, qn, cache):
    """edges: dict name->(u,v); rot: dict vertex->[edge names ccw]; colors: name->n.
    Returns the evaluation (sum over diagram choices of coef * d**loops)."""
    # vertex wiring
    wire = []
    for w, es in rot.items():
        ns = [colors[e] for e in es]
        if ns[0] + ns[1] < ns[2] or ns[1] + ns[2] < ns[0] or ns[2] + ns[0] < ns[1] or sum(ns) % 2:
            return None
        def pt(e, i):
            u, v = edges[e]
            n = colors[e]
            return ('U', e, n - 1 - i) if w == u else ('V', e, i)
        for k in range(3):
            e1, e2 = es[k], es[(k + 1) % 3]
            y = (colors[e1] + colors[e2] - colors[es[(k + 2) % 3]]) // 2
            for t in range(y):
                wire.append((pt(e1, colors[e1] - 1 - t), pt(e2, t)))
    names = list(edges)
    projs = []
    for e in names:
        n = colors[e]
        if n == 0:
            projs.append([({}, 1.0)]); continue
        key = n
        if key not in cache: cache[key] = jw(n, d, qn, d < 0)
        projs.append(list(cache[key].items()))
    total = 0.0
    for choice in itertools.product(*projs):
        coef = 1.0
        adj = {}
        def add(a, b):
            adj.setdefault(a, []).append(b); adj.setdefault(b, []).append(a)
        for (D, c), e in zip(choice, names):
            coef *= c
            n = colors[e]
            for k in range(2 * n):
                if D[k] > k:
                    a = ('U', e, k) if k < n else ('V', e, k - n)
                    b = ('U', e, D[k]) if D[k] < n else ('V', e, D[k] - n)
                    add(a, b)
        for a, b in wire: add(a, b)
        _, loops = walk_graph(adj, [])
        total += coef * d ** loops
    return total

TET_EDGES = {'j1': ('A', 'B'), 'j2': ('A', 'C'), 'j3': ('A', 'D'), 'j6': ('B', 'C'), 'j5': ('B', 'D'), 'j4': ('C', 'D')}
TET_ROT = {'A': ['j1', 'j3', 'j2'], 'B': ['j6', 'j5', 'j1'], 'C': ['j2', 'j4', 'j6'], 'D': ['j4', 'j3', 'j5']}

# The tetrahedron: vertices = triads (A=(j1j2j3), B=(j1j5j6), C=(j4j2j6), D=(j4j5j3)); planar embedding
# with D in the centre; rotations are counter-clockwise.
TET_EDGES = {'j1': ('A', 'B'), 'j2': ('A', 'C'), 'j3': ('A', 'D'), 'j6': ('B', 'C'), 'j5': ('B', 'D'), 'j4': ('C', 'D')}
TET_ROT = {'A': ['j1', 'j3', 'j2'], 'B': ['j6', 'j5', 'j1'], 'C': ['j2', 'j4', 'j6'], 'D': ['j4', 'j3', 'j5']}

def tet_tl(js, r, cache, kl=False):
    d = (-1 if kl else 1) * 2 * math.cos(math.pi / r)
    qn = lambda k: math.sin(k * math.pi / r) / math.sin(math.pi / r)
    colors = dict(zip(['j1', 'j2', 'j3', 'j4', 'j5', 'j6'], js))
    return network(TET_EDGES, TET_ROT, colors, d, qn, cache)

def theta_tl(a, b, c, r, cache, kl=False):
    d = (-1 if kl else 1) * 2 * math.cos(math.pi / r)
    qn = lambda k: math.sin(k * math.pi / r) / math.sin(math.pi / r)
    return network({'a': ('X', 'Y'), 'b': ('X', 'Y'), 'c': ('X', 'Y')},
                   {'X': ['a', 'b', 'c'], 'Y': ['c', 'b', 'a']}, {'a': a, 'b': b, 'c': c}, d, qn, cache)

# ---------------------------------------------------------------------------
# Part A: the Lean propositions Model.BE and Model.Orth, term by term.
# ---------------------------------------------------------------------------
import numpy as np

def f_table(r, angle_r=None):
    """F[j1,..,j6] = qSixJ r j1..j6, colours 0..r-2 (N = r-1). angle_r: use q = e^{i pi/angle_r} in
    the formula but the admissibility of level r (the 'wrong q' control)."""
    N = r - 1
    F = np.zeros((N,) * 6)
    for js in itertools.product(range(N), repeat=6):
        tri = [(js[0], js[1], js[2]), (js[0], js[4], js[5]), (js[3], js[1], js[5]), (js[3], js[4], js[2])]
        if all(adm(*t, r) for t in tri):
            F[js] = float(q6j(*js, angle_r or r))
    return F

def dim_vec(r, integer=False):
    """dim x = qnum r (x+1) for x in range N (integer=True: the wrong dimension x+1)."""
    return np.array([float(x + 1) if integer else float(qnum(x + 1, r)) for x in range(r - 1)])

def check_BE(r, F, dimv, flip=False):
    """Model.BE: for all a b c d e f p q r in range N,
    sum_{x<N} (-1)^((a+b+c+d+e+f+p+q+r+x)/2) dim x f(a,b,x,c,d,p) f(c,d,x,e,f,q) f(e,f,x,b,a,r)
      = f(p,q,r,e,a,d) f(p,q,r,f,b,c)          ('/2' is floor division on naturals).
    Returns (max abs error, number of label tuples with lhs or rhs nonzero, tuples checked)."""
    N = r - 1
    P, Q, R, X = np.meshgrid(*[np.arange(N)] * 4, indexing="ij")
    # (base + p+q+r+x)//2 mod 2 depends on base only through base mod 4
    W = [(-1.0) ** ((m + P + Q + R + X) // 2 + (1 if flip else 0)) * dimv[X] for m in range(4)]
    err, nz, n = 0.0, 0, 0
    for a, b, c, d, e, f in itertools.product(range(N), repeat=6):
        lhs = np.einsum("pqrx,xp,xq,xr->pqr", W[(a + b + c + d + e + f) % 4],
                        F[a, b, :, c, d, :], F[c, d, :, e, f, :], F[e, f, :, b, a, :])
        rhs = F[:, :, :, e, a, d] * F[:, :, :, f, b, c]
        n += N ** 3
        nz += int(np.count_nonzero((np.abs(lhs) > 1e-14) | (np.abs(rhs) > 1e-14)))
        err = max(err, float(np.abs(lhs - rhs).max()))
    return err, nz, n

def check_BE_outside(r, F, dimv, samples=20000):
    """Labels >= N too: every label occurs in some f on both sides, so both sides must be 0."""
    N = r - 1
    ext = np.zeros((N + 2,) * 6)
    ext[(slice(0, N),) * 6] = F
    dext = np.concatenate([dimv, [float(qnum(N + 1, r)), float(qnum(N + 2, r))]])
    rng = np.random.default_rng(0)
    worst, n = 0.0, 0
    for _ in range(samples):
        a, b, c, d, e, f, p, q, rr = [int(v) for v in rng.integers(0, N + 2, 9)]
        if max(a, b, c, d, e, f, p, q, rr) < N:
            continue
        n += 1
        lhs = sum((-1.0) ** ((a + b + c + d + e + f + p + q + rr + x) // 2) * dext[x] *
                  ext[a, b, x, c, d, p] * ext[c, d, x, e, f, q] * ext[e, f, x, b, a, rr]
                  for x in range(N))
        rhs = ext[p, q, rr, e, a, d] * ext[p, q, rr, f, b, c]
        worst = max(worst, abs(lhs - rhs))
    return worst, n

def check_Orth(r, F, dimv):
    """Model.Orth: for all B A E F q: sum_{x<N} dim x f(B,A,x,E,F,q)^2
    = 1/dim q if ok A E q and ok B q F else 0. (q >= N: ok is false and f = 0, asserted.)"""
    N = r - 1
    err, nz = 0.0, 0
    for B, A, E, Fl, q in itertools.product(range(N), repeat=5):
        lhs = float((dimv * F[B, A, :, E, Fl, q] ** 2).sum())
        rhs = 1.0 / dimv[q] if (adm(A, E, q, r) and adm(B, q, Fl, r)) else 0.0
        nz += int(lhs != 0 or rhs != 0)
        err = max(err, abs(lhs - rhs))
    for B, A, E, Fl in itertools.product(range(N), repeat=4):
        for q in (N, N + 1):
            assert not (adm(A, E, q, r) and adm(B, q, Fl, r))
    return err, nz

# ---------------------------------------------------------------------------
# Part B: independent q-6j values from the Temperley-Lieb tetrahedron (above).
# {j1 j2 j3; j4 j5 j6}_q = Tet_KL / sqrt|theta(j1j2j3) theta(j1j5j6) theta(j4j2j6) theta(j4j5j3)|
# with Kauffman-Lins loop value d = -[2]. Tetrahedron vertices = the four triads, edges = labels.
# ---------------------------------------------------------------------------

def tl_sixj(js, r, cache, kl=True):
    t = tet_tl(js, r, cache, kl)
    if t is None:
        return 0.0
    j1, j2, j3, j4, j5, j6 = js
    th = 1.0
    for tri in [(j1, j2, j3), (j1, j5, j6), (j4, j2, j6), (j4, j5, j3)]:
        th *= theta_tl(*tri, r, cache, kl)
    return t / math.sqrt(abs(th))

def tl_compare(r, jmax=3, limit=None, cache=None, **kw):
    """Compare qSixJ with the TL value for all admissible tuples with colours <= jmax.
    Returns (n compared, max |difference|, number of sign disagreements)."""
    cache = {} if cache is None else cache
    n, err, sgn = 0, 0.0, 0
    for js in itertools.product(range(min(jmax, r - 2) + 1), repeat=6):
        ref = float(q6j(*js, r))
        if ref == 0:
            continue
        v = tl_sixj(js, r, cache, **kw)
        n += 1
        err = max(err, abs(ref - v))
        sgn += int(ref * v < 0 and max(abs(ref), abs(v)) > 1e-9)  # exact zeros (e.g. r=6, all 2s) carry noise
        if limit and n >= limit:
            break
    return n, err, sgn

SHOW = [(0, 0, 0, 1, 1, 1), (1, 1, 2, 1, 1, 2), (2, 2, 2, 2, 2, 2), (1, 2, 3, 2, 1, 2),
        (3, 2, 1, 2, 3, 2), (2, 2, 2, 1, 1, 1)]

def run_default():
    ok = True
    def verdict(cond, text):
        nonlocal ok
        print(("PASS  " if cond else "FAIL  ") + text)
        ok = ok and cond
    # D. classical convention check
    e = float(check_classical())
    verdict(e < 1e-12, f"D. r=inf: q-Racah vs SymPy wigner_6j (spins <= 3/2): max err {e:.1e}")
    # B. independent TL values
    cache_by_r = {}
    print("B. independent TL values: qSixJ vs TL (Kauffman-Lins gauge), r=7")
    c7 = cache_by_r.setdefault(7, {})
    for js in SHOW:
        ref, v = float(q6j(*js, 7)), tl_sixj(js, 7, c7)
        print(f"     {js}: qSixJ {ref:+.12f}  TL {v:+.12f}")
        ok = ok and abs(ref - v) < 1e-10
    for r in range(4, 9):
        n, err, sg = tl_compare(r, jmax=3, limit=250, cache=cache_by_r.setdefault(r, {}))
        verdict(n >= 5 and err < 1e-10 and sg == 0,
                f"B. r={r}: {n} admissible tuples (colours <= 3) vs TL: max diff {err:.1e}, sign disagreements {sg}")
    # A. BE and Orth
    for r in range(4, 9):
        F, dv = f_table(r), dim_vec(r)
        eb, nzb, nb = check_BE(r, F, dv)
        eo_, no_ = check_BE_outside(r, F, dv)
        eorth, nzo = check_Orth(r, F, dv)
        verdict(eb < 1e-10 and eo_ < 1e-10 and eorth < 1e-10 and nzb > 0 and nzo > 0,
                f"A. r={r}: BE max err {eb:.1e} on {nb} tuples ({nzb} with a nonzero side; "
                f"{no_} outside-range samples, err {eo_:.1e}); Orth max err {eorth:.1e} ({nzo} nonzero)")
    # C. controls (must fail)
    print("C. wrong-input controls (each must FAIL):")
    for r in (5, 6):
        F, dv = f_table(r), dim_vec(r)
        ctl = {
            "BE with flipped sign": check_BE(r, F, dv, flip=True)[0],
            "BE with integer dim": check_BE(r, F, dim_vec(r, True))[0],
            "BE with wrong q (pi/(r+1))": check_BE(r, f_table(r, r + 1), dv)[0],
            "Orth with integer dim": check_Orth(r, F, dim_vec(r, True))[0],
            "Orth with wrong q (pi/(r+1))": check_Orth(r, f_table(r, r + 1), dv)[0],
        }
        for k, v in ctl.items():
            verdict(v > 1e-3, f"C. r={r}: {k}: max err {v:.2e} (detected)" if v > 1e-3
                    else f"C. r={r}: {k}: max err {v:.2e} NOT detected")
    n, err, sg = tl_compare(6, jmax=3, limit=60, kl=False)
    verdict(sg > 0, f"C. r=6: TL in the other loop-value gauge (+[2]) vs qSixJ: {sg}/{n} sign disagreements (detected)")
    cw = {}
    n = d = 0
    for js in itertools.product(range(4), repeat=6):
        ref = float(q6j(*js, 6))
        if ref == 0:
            continue
        n += 1
        d += int(abs(ref - tl_sixj(js, 7, cw)) > 1e-6)
        if n >= 60:
            break
    verdict(d > 0, f"C. r=6: TL evaluated at r=7 vs qSixJ at r=6: {d}/{n} values differ (detected)")
    print("ALL OK" if ok else "FAILURES")
    return ok

if __name__ == "__main__":
    if "--moves" in sys.argv or WRONG:
        tag = "[WRONG dim] " if WRONG else ""
        if not WRONG:
            print(f"classical q-Racah vs wigner_6j (spins <= 3/2): max err {float(check_classical()):.1e}")
        for r in [3, 4, 5, 6] + ([7] if "--long" in sys.argv else []):
            e23, n23 = check_23(r)
            eo = check_orth(r)
            e14, n14 = check_14(r)
            print(f"{tag}r={r}: 2-3 max err {float(e23):.1e} ({n23} nontrivial); "
                  f"orth max err {float(eo):.1e}; 1-4 max err {float(e14):.1e} ({n14} nontrivial)")
    else:
        sys.exit(0 if run_default() else 1)
