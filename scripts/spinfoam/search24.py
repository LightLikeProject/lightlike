"""Search for a reduction order of the 2-4 move (search aid; Lean checks each step).
Run: python3 -I scripts/spinfoam/search24.py"""
import itertools, sys
sys.path.insert(0, 'scripts/spinfoam')
from net_model import *

W = tuple(range(6)); A = (0, 1, 2, 3); B = (4, 5)

def set_case(Bp):
    global A, B
    B = tuple(Bp); A = tuple(v for v in W if v not in B)
fs = frozenset
def tets_of(s, t):
    return [n for n in s.live_nodes() if s.tet[n] == t]

def loop_ok(s, t, fA):
    ns = tets_of(s, t)
    if len(ns) != 2: return None
    n1, n2 = ns
    if [s.eface[e] for e in s.leg[n1]] != [s.eface[e] for e in s.leg[n2]]: return None
    for lA in range(4):
        eA = s.leg[n1][lA]
        if s.eface[eA] != fA or s.leg[n2][lA] != eA: continue
        if s.neg[n1][lA] != s.neg[n2][lA] or s.kap[eA]: continue
        if any(s.leg[n][l] == eA for n in s.live_nodes() if n not in (n1, n2) for l in range(4)): continue
        if any(s.leg[n][l] == eA for n in (n1, n2) for l in range(4) if l != lA): continue
        if any(eA in (c[0], c[1]) for c in s.cons): continue
        if any(s.elive[e] and e != eA and s.eface[e] in (t, fA) for e in s.elive): continue
        if any(s.tet[n] in (t, fA) for n in s.live_nodes() if n not in (n1, n2)): continue
        if t in s.cst or s.cst.count(fA) % 2: continue
        return (n1, n2, lA)
    return None

def blocks_net():
    nets = [simplex_net(k, W, a) for k, a in enumerate(A)]
    return union(nets)

def T(i, j): return fs(B) | {A[i], A[j]}
def tri(i): return fs(B) | {A[i]}

def try_fix(s, t, fA, maxflip=2):
    """Find flips (nodes), parities (nodes) making loop_ok true; returns (ops, net)."""
    if loop_ok(s, t, fA): return [], s
    nodes = s.live_nodes()
    ops = [('f', n) for n in nodes] + [('p', n) for n in nodes]
    for r in range(1, maxflip + 1):
        for combo in itertools.combinations(ops, r):
            q = s
            for k, n in combo:
                q = q.flip_node(n) if k == 'f' else q.add_parity(n)
            if loop_ok(q, t, fA): return list(combo), q
    return None

def run(order):
    """order: list of ('g', i, j) glue tet T(i,j) or ('l', i, j, k) loop tet T(i,j), triangle tri(k)."""
    s = blocks_net(); log = []
    for st in order:
        if st[0] == 'g':
            ns = tets_of(s, T(st[1], st[2]))
            if len(ns) != 2: return None
            s = s.glue(*ns).elim_all(); log.append(st)
        else:
            r = try_fix(s, T(st[1], st[2]), tri(st[3]))
            if r is None: return None
            ops, s = r
            n1, n2, lA = loop_ok(s, T(st[1], st[2]), tri(st[3]))
            s = s.loop(n1, n2, lA).elim_all(); log.append((st, ops))
    return log, s

pairs = [(i, j) for i in range(4) for j in range(i + 1, 4)]
if __name__ == '__main__':
    found = 0
    for gl in itertools.permutations(pairs, 3):
        # glues must form a spanning tree on blocks (complement pairs)
        edges = [tuple(sorted(set(range(4)) - set(p))) for p in gl]
        comp = {k: k for k in range(4)}
        def r(x):
            while comp[x] != x: x = comp[x]
            return x
        ok = True
        for a, b in edges:
            if r(a) == r(b): ok = False; break
            comp[r(a)] = r(b)
        if not ok: continue
        rest = [p for p in pairs if p not in gl]
        for ks in itertools.permutations((1, 2, 3)):
            for rp in itertools.permutations(rest):
                order = [('g',) + p for p in gl] + [('l', p[0], p[1], k) for p, k in zip(rp, ks)
                         if k in p]
                if len(order) != 6: continue
                res = run(order)
                if res:
                    print('FOUND', [x if x[0] == 'g' else x[0] for x in res[0]]); found += 1
                    if found >= 3: sys.exit()
    print('done', found)
