"""Print the Lean tables of Lightlike/SpinFoam/Move24.lean for the 15 cases of the 2-4 move.
Run: python3 -I scripts/spinfoam/gen24.py > /tmp/move24_tables.lean"""
import itertools, sys
sys.path.insert(0, 'scripts/spinfoam')
import search24 as S
import all24
from net_model import *
from gauge_match import *

def mask(f): return sum(1 << v for v in f)

def tab1(rows): return '![' + ', '.join(rows) + ']'
def lst(items): return '[' + ', '.join(items) + ']'
def nlean(n): return '(%d, %d)' % n
def elean(e): return '(%d, %d)' % e

ORDER_LOOPS = [(1, 3, 1), (2, 3, 2), (0, 3, 3)]

def data():
    cases = []
    for Bp in itertools.combinations(range(6), 2):
        order, log, free, m, msg, P, Q = all24.case(Bp)
        assert m is not None and len(free) == 1
        # replay to get loop nodes and preflips
        S.set_case(Bp)
        s = S.blocks_net()
        loops = []
        for st in order:
            if st[0] == 'g':
                ns = S.tets_of(s, S.T(st[1], st[2])); s = s.glue(*ns).elim_all()
            else:
                ops, s = S.try_fix(s, S.T(st[1], st[2]), S.tri(st[3]))
                n1, n2, lA = S.loop_ok(s, S.T(st[1], st[2]), S.tri(st[3]))
                loops.append((ops, n1, n2, lA))
                s = s.loop(n1, n2, lA).elim_all()
        fl, gv, pa, nP, eP = m
        cases.append(dict(B=Bp, A=S.A, loops=loops, free=free[0], fl=[nP[t] for t in fl],
                          gv=[eP[f] for f in gv], pa=[nP[t] for t in pa]))
    return cases

if __name__ == '__main__':
    cs = data()
    pr = lambda *a: print(*a)
    pr('/-- The positions of `A` (four) for the case `c`. -/')
    pr('def aposT : Fin 15 → Fin 4 → Fin 6 :=')
    pr('  ' + tab1([tab1(map(str, c['A'])) for c in cs]))
    pr('/-- The positions of `B` (two) for the case `c`. -/')
    pr('def bposT : Fin 15 → Fin 2 → Fin 6 :=')
    pr('  ' + tab1([tab1(map(str, c['B'])) for c in cs]))
    for k in range(3):
        pr(f'/-- Loop {k + 1}: the node flips, the node parities, the nodes `n₁ n₂` and the leg. -/')
        pr(f'def pre{k + 1}F : Fin 15 → List N4 :=')
        pr('  ' + tab1([lst(nlean(n) for kk, n in c['loops'][k][0] if kk == 'f') for c in cs]))
        pr(f'/-- Loop {k + 1}: the nodes whose parity is flipped before the loop. -/')
        pr(f'def pre{k + 1}P : Fin 15 → List N4 :=')
        pr('  ' + tab1([lst(nlean(n) for kk, n in c['loops'][k][0] if kk == 'p') for c in cs]))
        pr(f'/-- Loop {k + 1}: the nodes `n₁ n₂` that are joined and the leg that is closed. -/')
        pr(f'def loop{k + 1}N : Fin 15 → N4 × N4 × Fin 4 :=')
        pr('  ' + tab1(['(%s, %s, %d)' % (nlean(c['loops'][k][1]), nlean(c['loops'][k][2]), c['loops'][k][3]) for c in cs]))
    pr('/-- The free edge of the reduced left side. -/')
    pr('def freeE : Fin 15 → E4 :=')
    pr('  ' + tab1([elean(c['free']) for c in cs]))
    pr('/-- The nodes of the reduced left side that are flipped. -/')
    pr('def gNT : Fin 15 → List N4 :=')
    pr('  ' + tab1([lst(nlean(n) for n in c['fl']) for c in cs]))
    pr('/-- The edges of the reduced left side that are glued. -/')
    pr('def gET : Fin 15 → List E4 :=')
    pr('  ' + tab1([lst(elean(e) for e in c['gv']) for c in cs]))
    pr('/-- The nodes of the reduced left side whose parity is flipped. -/')
    pr('def gPT : Fin 15 → List N4 :=')
    pr('  ' + tab1([lst(nlean(n) for n in c['pa']) for c in cs]))
    # bitmask tables of the faces of the move
    PAIRS = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    m = lambda s: mask(s)
    pr('/-- The edge `B` of case `c`, as a bitmask. -/')
    pr('def bmT : Fin 15 → Fin 64 :=')
    pr('  ' + tab1([str(m(c['B'])) for c in cs]))
    pr('/-- The tetrahedron `A` of case `c`, as a bitmask. -/')
    pr('def sgT : Fin 15 → Fin 64 :=')
    pr('  ' + tab1([str(m(c['A'])) for c in cs]))
    pr('/-- The inner triangles `B ∪ {a_k}`, as bitmasks. -/')
    pr('def trT : Fin 15 → Fin 4 → Fin 64 :=')
    pr('  ' + tab1([tab1(str(m(set(c['B']) | {a})) for a in c['A']) for c in cs]))
    pr('/-- The inner tetrahedra `B ∪ {a_i, a_j}` in the order 01, 02, 03, 12, 13, 23. -/')
    pr('def teT : Fin 15 → Fin 6 → Fin 64 :=')
    pr('  ' + tab1([tab1(str(m(set(c['B']) | {c['A'][i], c['A'][j]})) for i, j in PAIRS) for c in cs]))
    pr('/-- The outer triangles `{b_e, a_i, a_j}` of the inner tetrahedra, in the order of `teT`. -/')
    pr('def ouT : Fin 15 → Fin 6 → Fin 2 → Fin 64 :=')
    pr('  ' + tab1([tab1(tab1(str(m({c['B'][e], c['A'][i], c['A'][j]})) for e in range(2)) for i, j in PAIRS) for c in cs]))
    pr('/-- The triangles `A ∖ {a_i}` of the tetrahedron `A`, as bitmasks. -/')
    pr('def faT : Fin 15 → Fin 4 → Fin 64 :=')
    pr('  ' + tab1([tab1(str(m(set(c['A']) - {a})) for a in c['A']) for c in cs]))
