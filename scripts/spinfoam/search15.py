"""Search for a reduction order of the 1-5 move (search aid; Lean checks each step).
Six positions W; B = one position (the new vertex), A = the other five (the old 4-simplex).
The five 4-simplices W minus a_k are glued along the ten tetrahedra B + three of A; four glues
(a spanning tree) and six loops, one for each inner triangle not through the least vertex of A.
Run: python3 -I scripts/spinfoam/search15.py"""
import itertools, sys
sys.path.insert(0, 'scripts/spinfoam')
from net_model import *

W = tuple(range(6))
fs = frozenset

class Case:
    def __init__(self, p):
        self.B = (p,)
        self.A = tuple(v for v in W if v != p)
        self.triples = list(itertools.combinations(range(5), 3))   # inner tets B + 3 of A
        self.pairs = list(itertools.combinations(range(5), 2))     # inner triangles B + 2 of A
    def T(self, tr): return fs(self.B) | {self.A[i] for i in tr}
    def tri(self, pr): return fs(self.B) | {self.A[i] for i in pr}
    def blocks(self):
        return union([simplex_net(k, W, a) for k, a in enumerate(self.A)])

def tets_of(s, t): return [n for n in s.live_nodes() if s.tet[n] == t]

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

def try_fix(s, t, fA, maxflip=2):
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

def spanning_trees(case):
    """Sets of four tets (triples) whose complement pairs form a spanning tree on the blocks."""
    for tr4 in itertools.combinations(case.triples, 4):
        edges = [tuple(sorted(set(range(5)) - set(t))) for t in tr4]
        comp = list(range(5))
        def r(x):
            while comp[x] != x: x = comp[x]
            return x
        ok = True
        for a, b in edges:
            if r(a) == r(b): ok = False; break
            comp[r(a)] = r(b)
        if ok: yield tr4

def loops_dfs(case, s, rest, free, log):
    """rest: remaining tets to loop; free: triangles still to kill."""
    if not rest:
        return log, s
    for tr in rest:
        for pr in itertools.combinations(tr, 2):
            if pr not in free: continue
            r = try_fix(s, case.T(tr), case.tri(pr))
            if r is None: continue
            ops, q = r
            n1, n2, lA = loop_ok(q, case.T(tr), case.tri(pr))
            q = q.loop(n1, n2, lA).elim_all()
            got = loops_dfs(case, q, [t for t in rest if t != tr], [f for f in free if f != pr],
                            log + [(tr, pr, ops)])
            if got: return got
    return None

def find(p, limit=10**9):
    case = Case(p)
    free0 = [pr for pr in case.pairs if 0 not in pr]
    n = 0
    for tr4 in spanning_trees(case):
        n += 1
        if n > limit: break
        s = case.blocks()
        for tr in tr4:
            ns = tets_of(s, case.T(tr))
            s = s.glue(*ns).elim_all()
        got = loops_dfs(case, s, [t for t in case.triples if t not in tr4], free0, [])
        if got: return case, tr4, got
    return None

if __name__ == '__main__':
    for p in range(6):
        r = find(p)
        print(p, 'NOT FOUND' if r is None else ('glue', r[1], 'loops', [(a, b) for a, b, c in r[2][0]]), flush=True)
