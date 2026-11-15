"""Reduction data of the 1-5 move for the six positions of the new vertex: the order found by
search15 and the gauge of gauge_match, checked in the model.
Run: python3 -I scripts/spinfoam/all15.py"""
import sys
sys.path.insert(0, 'scripts/spinfoam')
import search15 as S
from net_model import *
from gauge_match import *

def case(p):
    r = S.find(p)
    if r is None: return None
    cs, tr4, (loops, P) = r
    Q = simplex_net(0, S.W, cs.B[0])
    free = [e for e in P.live_edges() if not any(e in P.leg[n] for n in P.live_nodes())]
    m, msg = match(P, Q, drop_edges=tuple(free))
    return cs, tr4, loops, free, m, msg, P, Q

if __name__ == '__main__':
    for p in range(6):
        r = case(p)
        if r is None: print(p, 'NO ORDER'); continue
        cs, tr4, loops, free, m, msg, P, Q = r
        if m is None: print(p, 'MATCH FAILED:', msg, 'free', len(free)); continue
        fl, gv, pa, nP, eP = m
        P2 = apply(P, fl, gv, pa, nP, eP)
        print(p, 'free', len(free), 'live nodes', len(P.live_nodes()), 'gauge', len(fl), len(gv), len(pa),
              'same', same(P2, Q), 'cst', sorted(map(sorted, cst_parity(P2))))
