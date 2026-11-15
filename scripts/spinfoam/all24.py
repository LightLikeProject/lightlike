"""Reduction data of the 2-4 move for all 15 splittings of six positions into A (4) and B (2):
the first gluing/loop order found by search24 and the gauge of gauge_match, checked in the
model. Run: python3 -I scripts/spinfoam/all24.py"""
import itertools, sys
sys.path.insert(0, 'scripts/spinfoam')
import search24 as S
from net_model import *
from gauge_match import *

def find_order():
    pairs = S.pairs
    for gl in itertools.permutations(pairs, 3):
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
                order = [('g',) + p for p in gl] + [('l', p[0], p[1], k) for p, k in zip(rp, ks) if k in p]
                if len(order) != 6: continue
                res = S.run(order)
                if res: return order, res
    return None

def case(Bp):
    S.set_case(Bp)
    got = find_order()
    if got is None: return None
    order, (log, P) = got
    Bn = union([simplex_net(0, S.W, S.B[0]), simplex_net(1, S.W, S.B[1])])
    ns = S.tets_of(Bn, S.fs(S.A))
    Q = Bn.glue(*ns).elim_all()
    free = [e for e in P.live_edges() if not any(e in P.leg[n] for n in P.live_nodes())]
    m, msg = match(P, Q, drop_edges=tuple(free))
    return order, log, free, m, msg, P, Q

if __name__ == '__main__':
    for Bp in itertools.combinations(range(6), 2):
        r = case(Bp)
        if r is None: print(Bp, 'NO ORDER'); continue
        order, log, free, m, msg, P, Q = r
        if m is None: print(Bp, 'order', order, 'MATCH FAILED:', msg); continue
        fl, gv, pa, nP, eP = m
        P2 = apply(P, fl, gv, pa, nP, eP)
        print(Bp, 'order', [o if o[0]=='g' else o[:4] for o in order], 'free', len(free),
              'gauge', len(fl), len(gv), len(pa), 'same', same(P2, Q))
