"""Print the Lean tables of Lightlike/SpinFoam/Move15.lean for the six cases of the 1-5 move.
Run: python3 -I scripts/spinfoam/gen15.py > /tmp/move15_tables.lean"""
import itertools, sys
sys.path.insert(0, 'scripts/spinfoam')
import search15 as S
import all15
from net_model import *
from gauge_match import *

def mask(f): return sum(1 << v for v in f)
def tab1(rows): return '![' + ', '.join(rows) + ']'
def lst(items): return '[' + ', '.join(items) + ']'
def nlean(n): return '(%d, %d)' % n
def elean(e): return '(%d, %d)' % e

PAIRS = list(itertools.combinations(range(5), 2))
TRIPLES = list(itertools.combinations(range(5), 3))

def role(cs, f):
    """The role of the face f (a frozenset of positions) as a string."""
    B = cs.B[0]
    if B in f:
        rest = tuple(sorted(cs.A.index(v) for v in f if v != B))
        if len(rest) == 2: return 'tr%d' % PAIRS.index(rest)
        if len(rest) == 3: return 'te%d' % TRIPLES.index(rest)
    else:
        rest = tuple(sorted(cs.A.index(v) for v in f))
        if len(rest) == 3: return 'ot%d' % TRIPLES.index(rest)
        if len(rest) == 4: return 'et%d' % ([i for i in range(5) if i not in rest][0])
    raise ValueError(f)

def data():
    out = []
    for p in range(6):
        cs, tr4, loops, free, m, msg, P, Q = all15.case(p)
        assert m is not None and len(free) == 4
        # replay to get the loop nodes, the preparation and the leg roles
        s = cs.blocks(); roles = []
        glue_roles = []
        for tr in tr4:
            ns = S.tets_of(s, cs.T(tr))
            glue_roles.append(sorted(role(cs, s.eface[e]) for e in s.leg[ns[0]]))
            s = s.glue(*ns).elim_all()
        lp = []
        for tr, pr, ops in loops:
            q = s
            for k, n in ops:
                q = q.flip_node(n) if k == 'f' else q.add_parity(n)
            n1, n2, lA = S.loop_ok(q, cs.T(tr), cs.tri(pr))
            fa = role(cs, q.eface[q.leg[n1][lA]])
            others = sorted(role(cs, q.eface[q.leg[n1][l]]) for l in range(4) if l != lA)
            lp.append(dict(tr=tr, pr=pr, ops=ops, n1=n1, n2=n2, lA=lA, strand=fa, others=others))
            s = q.loop(n1, n2, lA).elim_all()
        fl, gv, pa, nP, eP = m
        out.append(dict(p=p, cs=cs, tr4=tr4, glue_roles=glue_roles, loops=lp, free=free,
                        fl=[nP[t] for t in fl], gv=[eP[f] for f in gv], pa=[nP[t] for t in pa],
                        freeroles=[role(cs, P.eface[e]) for e in free]))
    return out

if __name__ == '__main__':
    cs = data()
    pr = lambda *a: print(*a)
    # the structure must be the same for all cases
    for c in cs[1:]:
        assert c['tr4'] == cs[0]['tr4']
        assert [(l['tr'], l['pr']) for l in c['loops']] == [(l['tr'], l['pr']) for l in cs[0]['loops']]
        assert c['glue_roles'] == cs[0]['glue_roles'], (c['glue_roles'], cs[0]['glue_roles'])
        assert [l['others'] for l in c['loops']] == [l['others'] for l in cs[0]['loops']]
        assert [l['strand'] for l in c['loops']] == [l['strand'] for l in cs[0]['loops']]
        assert sorted(c['freeroles']) == sorted(cs[0]['freeroles'])
    print('-- glue triples', cs[0]['tr4'], file=sys.stderr)
    print('-- glue leg roles', cs[0]['glue_roles'], file=sys.stderr)
    for l in cs[0]['loops']:
        print('-- loop', l['tr'], l['pr'], 'strand', l['strand'], 'others', l['others'], file=sys.stderr)
    print('-- free roles per case', [c['freeroles'] for c in cs], file=sys.stderr)
    pr('/-- The positions of `A` (five) for the case `c`. -/')
    pr('def aposT : Fin 6 → Fin 5 → Fin 6 :=')
    pr('  ' + tab1([tab1(map(str, c['cs'].A)) for c in cs]))
    for k in range(6):
        pr(f'/-- Loop {k + 1}: the node flips, the node parities and the nodes `n₁ n₂` and the leg. -/')
        pr(f'def pre{k + 1}F : Fin 6 → List N5 :=')
        pr('  ' + tab1([lst(nlean(n) for kk, n in c['loops'][k]['ops'] if kk == 'f') for c in cs]))
        pr(f'/-- Loop {k + 1}: the nodes whose parity is flipped before the loop. -/')
        pr(f'def pre{k + 1}P : Fin 6 → List N5 :=')
        pr('  ' + tab1([lst(nlean(n) for kk, n in c['loops'][k]['ops'] if kk == 'p') for c in cs]))
        pr(f'/-- Loop {k + 1}: the nodes `n₁ n₂` that are joined and the leg that is closed. -/')
        pr(f'def loop{k + 1}N : Fin 6 → N5 × N5 × Fin 4 :=')
        pr('  ' + tab1(['(%s, %s, %d)' % (nlean(c['loops'][k]['n1']), nlean(c['loops'][k]['n2']), c['loops'][k]['lA']) for c in cs]))
    pr('/-- The four free edges of the reduced network, on the triangles through `a_0` (in the order of `trT`). -/')
    pr('def freeE : Fin 6 → Fin 4 → E5 :=')
    rows = []
    for c in cs:
        by = {r: e for e, r in zip(c['free'], c['freeroles'])}
        rows.append(tab1(elean(by['tr%d' % j]) for j in range(4)))
    pr('  ' + tab1(rows))
    pr('/-- The nodes of the reduced left side that are flipped. -/')
    pr('def gNT : Fin 6 → List N5 :=')
    pr('  ' + tab1([lst(nlean(n) for n in c['fl']) for c in cs]))
    pr('/-- The edges of the reduced left side that are glued. -/')
    pr('def gET : Fin 6 → List E5 :=')
    pr('  ' + tab1([lst(elean(e) for e in c['gv']) for c in cs]))
    pr('/-- The nodes of the reduced left side whose parity is flipped. -/')
    pr('def gPT : Fin 6 → List N5 :=')
    pr('  ' + tab1([lst(nlean(n) for n in c['pa']) for c in cs]))
    pr('/-- The vertex `B` of case `c`, as a bitmask. -/')
    pr('def bmT : Fin 6 → Fin 64 :=')
    pr('  ' + tab1([str(mask(c["cs"].B)) for c in cs]))
    pr('/-- The inner triangles `B ∪ {a_i, a_j}` (pairs in lexicographic order), as bitmasks. -/')
    pr('def trT : Fin 6 → Fin 10 → Fin 64 :=')
    pr('  ' + tab1([tab1(str(mask(c['cs'].tri(q))) for q in PAIRS) for c in cs]))
    pr('/-- The inner tetrahedra `B ∪ {a_i, a_j, a_k}` (triples in lexicographic order), as bitmasks. -/')
    pr('def teT : Fin 6 → Fin 10 → Fin 64 :=')
    pr('  ' + tab1([tab1(str(mask(c['cs'].T(q))) for q in TRIPLES) for c in cs]))
    pr('/-- The outer triangles `{a_i, a_j, a_k}` (triples in lexicographic order), as bitmasks. -/')
    pr('def otT : Fin 6 → Fin 10 → Fin 64 :=')
    pr('  ' + tab1([tab1(str(mask({c['cs'].A[i] for i in q})) for q in TRIPLES) for c in cs]))
