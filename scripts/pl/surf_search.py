"""Search for 2D bistellar move sequences between finite triangulated regions, relative to their
boundary (prototype for the S1 finite computations).

A region is a set of triangles (frozensets of vertex labels).  Boundary edges (those lying in one
region triangle) are never flipped, boundary vertices are never removed, and new edges must avoid
a given set of forbidden pairs (edges of the surrounding complex between boundary vertices).
Interior vertices of the target may be relabelled.
"""
import heapq
import itertools
import sys

def edges_of(K):
    E = {}
    for t in K:
        for e in itertools.combinations(sorted(t, key=str), 2):
            E.setdefault(frozenset(e), []).append(t)
    return E

def verts_of(K):
    return set().union(*K) if K else set()

class Region:
    def __init__(self, K, forbidden=(), fixed_verts=None):
        self.K0 = frozenset(frozenset(t) for t in K)
        E = edges_of(self.K0)
        self.bedges = {e for e, ts in E.items() if len(ts) == 1}
        self.bverts = set().union(*self.bedges) if fixed_verts is None else set(fixed_verts)
        self.forbidden = {frozenset(e) for e in forbidden}

    def moves(self, K, fresh):
        """Yield (description, new complex)."""
        E = edges_of(K)
        V = verts_of(K)
        # sub13
        for t in K:
            x = fresh
            a, b, c = sorted(t, key=str)
            K2 = (K - {t}) | {frozenset({a, b, x}), frozenset({b, c, x}), frozenset({a, c, x})}
            yield (('sub13', tuple(sorted(t, key=str)), x), frozenset(K2))
        # flips
        for e, ts in E.items():
            if e in self.bedges or len(ts) != 2:
                continue
            b, c = tuple(e)
            d = next(iter(ts[0] - e))
            f = next(iter(ts[1] - e))
            ne = frozenset({d, f})
            if d == f or ne in E or ne in self.forbidden:
                continue
            K2 = (K - set(ts)) | {frozenset({b, d, f}), frozenset({c, d, f})}
            yield (('flip', tuple(sorted(e, key=str)), tuple(sorted(ne, key=str))), frozenset(K2))
        # inverse sub13
        for v in V:
            if v in self.bverts:
                continue
            st = [t for t in K if v in t]
            if len(st) != 3:
                continue
            lk = verts_of(st) - {v}
            if len(lk) != 3:
                continue
            nt = frozenset(lk)
            if nt in K:
                continue
            ok = all(frozenset(p) not in self.forbidden for p in itertools.combinations(lk, 2))
            if not ok:
                continue
            K2 = (K - set(st)) | {nt}
            yield (('remove', v, tuple(sorted(lk, key=str))), frozenset(K2))

def canon_rel(K, bverts):
    """A canonical form of K up to relabelling of non-boundary vertices (brute force)."""
    inner = sorted(verts_of(K) - bverts, key=str)
    best = None
    for perm in itertools.permutations(range(len(inner))):
        m = {v: ('i', perm[k]) for k, v in enumerate(inner)}
        img = tuple(sorted(tuple(sorted((str(m.get(u, u)) for u in t))) for t in K))
        if best is None or img < best:
            best = img
    return best

def search(X, Y, forbidden=(), max_nodes=200000, max_inner=None):
    R = Region(X, forbidden)
    target = canon_rel(frozenset(frozenset(t) for t in Y), R.bverts)
    tY = len(Y)
    start = R.K0
    counter = itertools.count()
    def h(K):
        return abs(len(K) - tY)
    pq = [(h(start), 0, next(counter), start, [])]
    seen = {canon_rel(start, R.bverts)}
    nodes = 0
    while pq:
        f, g, _, K, path = heapq.heappop(pq)
        nodes += 1
        if nodes > max_nodes:
            return None, nodes
        if canon_rel(K, R.bverts) == target:
            return path, nodes
        inner = len(verts_of(K) - R.bverts)
        fresh = ('n', g)
        for mv, K2 in R.moves(K, fresh):
            if max_inner is not None and len(verts_of(K2) - R.bverts) > max_inner:
                continue
            c = canon_rel(K2, R.bverts)
            if c in seen:
                continue
            seen.add(c)
            heapq.heappush(pq, (g + 1 + h(K2), g + 1, next(counter), K2, path + [mv]))
    return None, nodes

# --- pieces ---
P6 = [(0,1,2),(0,2,3),(0,3,4),(0,4,5),(0,5,1),(1,2,4),(2,3,5),(3,4,1),(4,5,2),(5,1,3)]

def band(P, tau, site, tag):
    """P minus its triangle tau, glued to `site` (tau[i] -> site[i]), other vertices tagged."""
    m = {tau[i]: site[i] for i in range(3)}
    out = []
    for t in P:
        if frozenset(t) == frozenset(tau):
            continue
        out.append(frozenset(m.get(u, (tag, u)) for u in t))
    return out

def check_closed(K):
    E = edges_of(K)
    return all(len(ts) == 2 for ts in E.values())

if __name__ == '__main__':
    assert check_closed([frozenset(t) for t in P6])
    a, b, c, d = 'a', 'b', 'c', 'd'
    X = band(P6, (0,1,2), (a,b,c), 'p') + [frozenset({b, c, d})]
    for site in [(b, c, d), (c, b, d), (d, b, c), (b, d, c), (c, d, b), (d, c, b)]:
        Y = [frozenset({a, b, c})] + band(P6, (0,1,2), site, 'q')
        path, n = search(X, Y, forbidden=[(a, d)], max_nodes=int(sys.argv[1]) if len(sys.argv) > 1 else 50000, max_inner=5)
        print(site, 'found' if path else 'not found', n, len(path) if path else None)
        if path:
            for mv in path:
                print('   ', mv)
            break


def replay(X, path):
    """Apply a found path to X and return the final complex (labels as in the path)."""
    K = frozenset(frozenset(t) for t in X)
    for mv in path:
        kind = mv[0]
        if kind == 'sub13':
            (a, b, c), x = mv[1], mv[2]
            K = (K - {frozenset({a, b, c})}) | {frozenset({a, b, x}), frozenset({b, c, x}),
                                                  frozenset({a, c, x})}
        elif kind == 'flip':
            (b, c), (d, e) = mv[1], mv[2]
            K = (K - {frozenset({b, c, d}), frozenset({b, c, e})}) | {frozenset({b, d, e}),
                                                                       frozenset({c, d, e})}
        else:
            v, lk = mv[1], mv[2]
            K = frozenset(t for t in K if v not in t) | {frozenset(lk)}
    return K


def to_lean(X, path, labels, bverts):
    """Lean text for `checkChain B S X ms = some Y`, with labels mapped to naturals.  S lists the
    boundary pairs that the chain flips or creates (each must be justified in the context)."""
    L = lambda u: labels[u]
    fmt_t = lambda t: '{' + ', '.join(str(L(u)) for u in sorted(t, key=lambda u: L(u))) + '}'
    fmt_K = lambda K: '{' + ', '.join(fmt_t(t) for t in sorted(K, key=lambda t: sorted(L(u) for u in t))) + '}'
    ms, S = [], set()
    for mv in path:
        if mv[0] == 'sub13':
            (a, b, c), x = mv[1], mv[2]
            ms.append(f'.sub {L(a)} {L(b)} {L(c)} {L(x)}')
        elif mv[0] == 'flip':
            (b, c), (d, e) = mv[1], mv[2]
            ms.append(f'.flip {L(b)} {L(c)} {L(d)} {L(e)}')
            for p in [(b, c), (d, e)]:
                if p[0] in bverts and p[1] in bverts:
                    S.add(tuple(sorted((L(p[0]), L(p[1])))))
        else:
            v, lk = mv[1], mv[2]
            ms.append(f'.unsub {L(lk[0])} {L(lk[1])} {L(lk[2])} {L(v)}')
            if all(u in bverts for u in lk):
                S.add(tuple(sorted((L(lk[0]), L(lk[1])))))
    Y = replay(X, path)
    B = '{' + ', '.join(str(L(u)) for u in sorted(bverts, key=L)) + '}'
    Ss = '[' + ', '.join(f'({p}, {q})' for p, q in sorted(S)) + ']'
    return dict(B=B, S=Ss, X=fmt_K(X), Y=fmt_K(Y), ms='[' + ', '.join(ms) + ']')
