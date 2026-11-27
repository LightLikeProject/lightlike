#!/usr/bin/env python3
"""Numerical model of the local Pachner identities of the Crane-Yetter state sum of Lightlike main
(Lightlike/TuraevViro/CraneYetter.lean: tlDelta, tlTheta, tlTet, cyVertexLoc, cyVertexAt, cyTetWeight, cyN),
transcribed literally (Lean's x/0 = 0, truncated natural subtraction, Int ediv)."""
import cmath, itertools, math, random, sys
from functools import lru_cache

def make(r):
    @lru_cache(None)
    def qnum(n):
        if n % r == 0: return 0.0
        return math.sin(n*math.pi/r)/math.sin(math.pi/r)
    @lru_cache(None)
    def qfact(n):
        p = 1.0
        for k in range(n): p *= qnum(k+1)
        return p
    def div(x, y): return 0 if y == 0 else x/y
    def nsub(a, b): return max(a-b, 0)
    def tri(x, y, z): return (x+y+z) % 2 == 0 and z <= x+y and x <= y+z and y <= x+z
    def qadm(a, b, c): return tri(a, b, c) and a+b+c <= 2*(r-2)
    def delta(n): return (-1)**n*qnum(n+1)
    @lru_cache(None)
    def theta(a, b, c):
        if not qadm(a, b, c): return 0.0
        s = (a+b+c)//2
        return div((-1)**s*qfact(s+1)*qfact(nsub(a+b, c)//2)*qfact(nsub(b+c, a)//2)*qfact(nsub(a+c, b)//2),
                   qfact(a)*qfact(b)*qfact(c))
    @lru_cache(None)
    def tet(A, B, E, C, D, F):
        if not (qadm(A, D, E) and qadm(B, C, E) and qadm(A, B, F) and qadm(C, D, F)): return 0.0
        al = [(A+D+E)//2, (B+C+E)//2, (A+B+F)//2, (C+D+F)//2]
        be = [(B+D+E+F)//2, (A+C+E+F)//2, (A+B+C+D)//2]
        pre = 1.0
        for i in al:
            for j in be: pre *= qfact(nsub(j, i))
        pre = div(pre, qfact(A)*qfact(B)*qfact(C)*qfact(D)*qfact(E)*qfact(F))
        tot = 0.0
        for z in range(max(al), min(be)+1):
            den = 1.0
            for i in al: den *= qfact(nsub(z, i))
            for j in be: den *= qfact(nsub(j, z))
            tot += div((-1)**z*qfact(z+1), den)
        return pre*tot
    qhalf = cmath.exp(1j*math.pi/(2*r))
    def rbr(a, b, c):
        return (-1)**(nsub(a+b, c)//2)*cmath.exp(1j*math.pi*(c*(c+2)-a*(a+2)-b*(b+2))/(4*r))
    def vloc(J, I):
        j = lambda x, y, z: J[frozenset((x, y, z))]
        a = [j(2,3,4), I[0], j(1,2,3), I[4], j(0,1,2), I[3]]
        b = [I[3], j(0,1,4), I[2], j(0,3,4), I[1], j(2,3,4)]
        c = [j(1,2,4), j(1,3,4), j(0,1,3), j(0,2,3), j(0,2,4)]
        pr = lambda x: x*(x+2)
        P = (-pr(I[4])+pr(I[3])-pr(I[2])-pr(I[0])+pr(j(0,1,3))+pr(j(1,2,3))+pr(j(1,3,4))+pr(j(2,3,4)))//2
        s = ((j(1,2,3)+j(1,3,4)-I[0])+(j(0,3,4)+j(0,2,3)-I[1])+(j(2,3,4)+j(0,2,4)-I[1])+(j(0,1,3)+j(0,3,4)-I[2])
             + (j(0,2,4)+j(0,1,2)-I[3])+(j(0,1,2)+j(0,2,3)-I[4]))//2
        tot = 0
        for x in range(2*(r-2)+1):
            if qadm(a[0], b[0], x):
                pt = 1
                for t in range(5):
                    pt *= div(tet(a[t], a[t+1], x, b[t+1], b[t], c[t]), theta(a[t+1], b[t+1], x))
                tot += delta(x)*rbr(a[0], b[0], x)*pt
        return (-1)**(s % 2)*qhalf**P*tot
    def vat(col, simp, o):
        v = sorted(simp)
        J = {frozenset(F): col[frozenset(v[k] for k in F)] for F in itertools.combinations(range(5), 3)}
        I = [col[frozenset(simp) - {v[m]}] for m in range(5)]
        Phi = vloc(J, I)
        return Phi if o == 1 else Phi.conjugate()
    def tetw(col, t):
        v = sorted(t); T = frozenset(t); i = col[T]
        return div(delta(i), theta(i, col[T-{v[0]}], col[T-{v[2]}])*theta(i, col[T-{v[1]}], col[T-{v[3]}]))
    N = r/(2*math.sin(math.pi/r)**2)
    return dict(vat=vat, tetw=tetw, delta=delta, N=N, theta=theta, tet=tet, qadm=qadm, rbr=rbr, qnum=qnum)

S6 = list(range(6))
def inc(S, v): return (-1)**sorted(S).index(v)

def factors(M, simps, tris, tets, osign, after):
    """Factors of a side: (faces needed, function of the colouring)."""
    fs = [(frozenset([f]), (lambda f: lambda c: M['delta'](c[f]))(f)) for f in tris]
    for t in tets:
        need = frozenset([t] + [t - {v} for v in t])
        fs.append((need, (lambda t: lambda c: M['tetw'](c, t))(t)))
    for sm in simps:
        need = frozenset(faces_in(sm))
        o = osign*inc(S6, (set(S6)-set(sm)).pop())
        fs.append((need, (lambda sm, o: lambda c: M['vat'](c, sm, o))(sm, o)))
    return fs

def faces_in(sm):
    return [frozenset(f) for k in (3, 4) for f in itertools.combinations(sorted(sm), k)]

def dfs(r, col, order, fs, rnd=None, first=False):
    """Sum over colourings of `order` (given `col`) of the product of the factors, pruning zeros.
    With first=True, return one random colouring with a nonzero product (or None)."""
    pos = {f: k for k, f in enumerate(order)}
    ready = [[] for _ in order]; pre = []
    for need, fn in fs:
        idx = [pos[f] for f in need if f in pos]
        (ready[max(idx)] if idx else pre).append(fn)
    base = 1
    for fn in pre: base *= fn(col)
    if base == 0: return None if first else 0
    c = dict(col)
    def go(k, acc):
        if k == len(order): return dict(c) if first else acc
        vals = list(range(r-1))
        if rnd: rnd.shuffle(vals)
        tot = 0
        for v in vals:
            c[order[k]] = v
            a = acc
            for fn in ready[k]:
                a = a*fn(c)
                if a == 0: break
            if a == 0: continue
            res = go(k+1, a)
            if first:
                if res is not None: return res
            else: tot += res
        del c[order[k]]
        return None if first else tot
    return go(0, base)

def side(M, r, col, simps, inner, osign):
    tris = [f for f in inner if len(f) == 3]; tets = [f for f in inner if len(f) == 4]
    return dfs(r, col, sorted(inner, key=len), factors(M, simps, tris, tets, osign, False))

def faces_of(simps, k):
    out = set()
    for s in simps:
        for f in itertools.combinations(sorted(s), k): out.add(frozenset(f))
    return out

def check(r, sig, trials, seed=0, after_sign=-1):
    M = make(r); rnd = random.Random(seed)
    sig = frozenset(sig); tau = frozenset(S6) - sig
    before = [frozenset(S6) - {v} for v in tau]; after = [frozenset(S6) - {u} for u in sig]
    bf = [f for k in (3, 4) for f in faces_of(before, k) if not sig <= f]
    inner_b = [f for k in (3, 4) for f in faces_of(before, k) if sig <= f]
    inner_a = [f for k in (3, 4) for f in faces_of(after, k) if tau <= f]
    assert set(bf) == {f for k in (3, 4) for f in faces_of(after, k) if not tau <= f}
    dN = {3: 0, 4: -1, 5: -4}[len(sig)]
    stats = dict(n=0, nonzero=0, maxrel=0.0, worst=None)
    allb = sorted(set(bf) | set(inner_b), key=len)
    tris_all = [f for f in allb if len(f) == 3]; tets_all = [f for f in allb if len(f) == 4]
    fs_all = factors(M, before, tris_all, tets_all, 1, False)
    for _ in range(trials):
        full = dfs(r, {}, allb, fs_all, rnd=rnd, first=True)
        if full is None: break
        col = {f: full[f] for f in bf}
        L = side(M, r, col, before, inner_b, 1)
        R = (M['N']**dN)*side(M, r, col, after, inner_a, after_sign)
        stats['n'] += 1
        if abs(L) > 1e-12 or abs(R) > 1e-12:
            stats['nonzero'] += 1
            rel = abs(L-R)/max(abs(L), abs(R))
            if rel > stats['maxrel']: stats['maxrel'] = rel; stats['worst'] = (L, R)
    return stats

TRUE_MODEL = make

def positive_dims(r):
    """Wrong-input control: the dimensions [n+1] without the sign (-1)^n."""
    M = TRUE_MODEL(r); q = M['qnum']; th = M['theta']
    M['delta'] = lambda n: q(n+1)
    def tetw(col, t):
        v = sorted(t); T = frozenset(t); i = col[T]
        d = th(i, col[T-{v[0]}], col[T-{v[2]}])*th(i, col[T-{v[1]}], col[T-{v[3]}])
        return 0 if d == 0 else q(i+1)/d
    M['tetw'] = tetw
    return M

def run(r, k, trials, after_sign=-1, model=None, patterns=None):
    global make
    saved = make
    if model is not None: make = model
    try:
        out = []
        for sig in (patterns or list(itertools.combinations(S6, k))):
            out.append((sig, check(r, sig, trials, seed=sum(1 << v for v in sig), after_sign=after_sign)))
        return out
    finally:
        make = saved

if __name__ == '__main__':
    full = '--full' in sys.argv
    TOL = 1e-9
    ok = True
    plan = [(3, k, 3, None) for k in (3, 4, 5)] + \
        [(4, 3, 3, [(0, 2, 4), (1, 3, 5)]), (4, 4, 2, [(0, 1, 2, 3)]), (4, 5, 1, [(0, 1, 2, 3, 4)])]
    if full:
        plan = [(r, k, 8, None) for r in (3, 4, 5) for k in (3, 4, 5)]
    for r, k, trials, pats in plan:
        for sig, st in run(r, k, trials, patterns=pats):
            good = st['nonzero'] > 0 and st['maxrel'] < TOL
            ok &= good
            print(f"r={r} move {6-k}-{k} sigma={sig}: {st['nonzero']}/{st['n']} nonzero, max rel {st['maxrel']:.1e}",
                  'ok' if good else 'FAIL', flush=True)
    # wrong-input controls: each must break the identity
    for name, kw in [('added simplices with the removed orientation', dict(after_sign=1)),
                     ('positive dimensions', dict(model=positive_dims))]:
        st = run(4, 3, 3, patterns=[(0, 2, 4)], **kw)[0][1]
        caught = st['maxrel'] > 1e-3
        ok &= caught
        print(f"control ({name}), r=4 3-3: max rel {st['maxrel']:.2f}", 'detected' if caught else 'NOT DETECTED')
    print('PASS' if ok else 'FAIL')
    sys.exit(0 if ok else 1)
