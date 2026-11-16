"""Numerical check (not a proof): can a forcing gauge set be repaired locally after a Pachner move?

For random 4-spheres K reached from the boundary of the 5-simplex by 3 to 6 forward moves, and a random
forcing gauge set T of K (`forcechain.direct_forcing_gauge`: a random minimal forcing set that is
collapsible, of size E - V + 1), every move K -> K' of the five kinds is applied (1-5 on one simplex,
every 2-4, 3-3, 4-2 and 5-1 location). The transported set is T with the triangles that no longer exist
removed and the triangles of the gauge rule added (1-5: {v, a_0, a_j}; 2-4: {p, q, x} for each x of the
tetrahedron; 3-3: T without the moved triangle). A *repair* is a change of at most `maxk` triangles,
from the triangles that share two vertices with the triangles that the move creates or removes, after
which the set is a forcing gauge set of K' (size E - V + 1, collapsible, forcing). Observed on the
seeds below (150 spheres; only 4-2 and 5-1 results that are closed 4-manifold triangulations are
counted: an inverse "move" whose result has a boundary is not a move of spheres): 1-5, 2-4 and 3-3
always have a repair of at most 2 changes (3-3 when the moved triangle is in T needs 1); of the 176
4-2 locations 77 need none, 61 one, 34 two and 4 three; of the 155 5-1 locations 88 need none, 49 one,
17 two and 1 three. So a repair of at most 3 local changes is observed at every location of every
kind; nothing in this sample resists.
`inverse_rule` states the repair of the inverse moves as a rule and checks it on seeds 75000 to 75149,
which were not used to find it: of the triangles through the removed edge (4-2) or vertex (5-1), the
set keeps `k = |T cap N|`; with `k = 1` (4-2) or `k = 4` (5-1) the transported set works, otherwise
adding `k - 1` triangles `{p, x, y}` or `{q, x, y}` of the two new 4-simplices (4-2), or `k - 4` triangles
of the new 4-simplex (5-1), gives a forcing gauge set (169 of 169 and 157 of 157 locations). The
choice of the added triangles is not given by a formula: a search finds it, and the simple candidates
(the triangle opposite each removed vertex) work in about 20% of the cases.
Exit code 0 when 1-5, 2-4 and 3-3 always have a repair of at most 2 changes and every location of
every kind has one of at most 3 local changes.
"""
import itertools
import os
import random
import sys
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import forcechain as F

fs = frozenset


def all_moves(K, rng, nv):
    """(kind, K2, list of candidate base transforms f(T) -> T2)"""
    out=[]
    s=rng.choice(sorted(K,key=sorted)); a=sorted(s); v=nv
    K15=(K-{s})|{fs(set(c)|{v}) for c in itertools.combinations(a,4)}
    out.append(('15',K15,[lambda T,a=a,v=v: T|{fs({v,a[0],x}) for x in a[1:]}]))
    for t,p,q,K24 in F_all24(K):
        out.append(('24',K24,[ (lambda T,p=p,q=q,x=x: T|{fs({p,q,x})}) for x in sorted(t)]))
    for sg,tau,K33 in F.moves33(K):
        out.append(('33',K33,[lambda T,sg=sg: T-{sg}]))
    for e in F.faces(K,2):
        st=[x for x in K if e<=x]
        if len(st)==4:
            tet=fs().union(*[x-e for x in st])
            if len(tet)==4 and all(len(x-e)==3 for x in st):
                p,q=sorted(e); K2=(K-set(st))|{tet|{p},tet|{q}}
                if closed4(K2):
                    out.append(('42',K2,[lambda T,e=e: {f for f in T if not e<=f}]))
    for v0 in {y for x in K for y in x}:
        st=[x for x in K if v0 in x]
        if len(st)==5:
            link=fs().union(*[x-{v0} for x in st])
            if len(link)==5 and all(len(x-{v0})==4 for x in st):
                K51=(K-set(st))|{link}
                if closed4(K51):
                    out.append(('51',K51,[lambda T,v0=v0: {f for f in T if v0 not in f}]))
    return out
def F_all24(K):
    edges=F.faces(K,2)
    for t in sorted(F.faces(K,4),key=sorted):
        ss=[s for s in K if t<=s]
        if len(ss)!=2: continue
        p,q=[next(iter(s-t)) for s in ss]
        if fs({p,q}) in edges: continue
        yield t,p,q,(K-set(ss))|{fs({p,q}|(t-{x})) for x in t}
def closed4(K):
    """Every tetrahedron of K lies in exactly two 4-simplices (a closed 4-manifold triangulation)."""
    cnt = Counter(fs(c) for x in K for c in itertools.combinations(sorted(x), 4))
    return set(cnt.values()) == {2}


def isgauge(K,T):
    return T<=F.faces(K,3) and len(T)==len(F.faces(K,2))-len(F.faces(K,1))+1 and F.collapsible(K,T) and F.forces(K,T)
def repair(K2, base, K=None, maxk=2, local=True):
    """Smallest number of triangle changes (swaps counted as 2) to reach a forcing gauge set; local candidates."""
    if isgauge(K2,base): return 0
    tris=sorted(F.faces(K2,3),key=sorted)
    target=len(F.faces(K2,2))-len(F.faces(K2,1))+1
    d=target-len(base)
    old=F.faces(K,3) if K is not None else set()
    chg=set(tris)^set(old)
    R=set().union(*chg) if chg else set()
    loc=[t for t in tris if (len(t & R) >= 2 or not local)]
    outs=[t for t in sorted(base,key=sorted)]
    ins=[t for t in loc if t not in base]
    best=None
    for ko in range(0,maxk+1):
        ki=ko+d
        if ki<0 or ki>maxk: continue
        if best is not None and ko+ki>=best: break
        for X in itertools.combinations(outs,ko):
            for Y in itertools.combinations(ins,ki):
                T=(base-set(X))|set(Y)
                if isgauge(K2,T):
                    best=ko+ki if best is None else min(best,ko+ki); break
            if best is not None and best<=ko+ki: break
    return best
nones=[]
LOCAL=True


def sphere_and_gauge(seed):
    """A sphere after 3 to 6 forward moves from the boundary of the 5-simplex and a random forcing
    gauge set of it (None if the random search did not find one)."""
    rng = random.Random(seed)
    K, nv = F.start()[0], 6
    for _ in range(rng.randrange(3, 7)):
        r = rng.choice(["15", "24", "33"])
        if r == "15":
            K, _ = F.m15(K, set(), nv, rng)
            nv += 1
        else:
            o = (F.m24 if r == "24" else F.m33)(K, set(), rng)
            if o:
                K = o[0]
    return K, F.direct_forcing_gauge(K, rng, tries=20)


def inverse_rule(seeds):
    """The repair rule for the inverse moves, observed on the given seeds. For a 4-2 move that removes
    the edge e, N = the triangles through e, k = |T cap N|: with k = 1 the set T minus N is a forcing
    gauge set; with k >= 2 it is after adding k - 1 triangles {p, x, y} or {q, x, y} (x, y in the new
    tetrahedron). For a 5-1 move that removes the vertex v, k = |T cap N| for the triangles through v:
    with k = 4 the set T minus N works; otherwise after adding k - 4 triangles of the new 4-simplex.
    Returns a counter of (kind, outcome)."""
    out = Counter()
    for sd in seeds:
        K, T = sphere_and_gauge(sd)
        if T is None:
            continue
        for e in F.faces(K, 2):
            st = [x for x in K if e <= x]
            if len(st) != 4:
                continue
            tet = fs().union(*[x - e for x in st])
            if len(tet) != 4 or not all(len(x - e) == 3 for x in st):
                continue
            p, q = sorted(e)
            K2 = (K - set(st)) | {tet | {p}, tet | {q}}
            if not closed4(K2):
                continue
            N = {f for f in F.faces(K, 3) if e <= f}
            base, k = T - N, len(T & N)
            pool = [fs({z, x, y}) for z in (p, q) for x, y in itertools.combinations(sorted(tet), 2)]
            pool = [y for y in pool if y not in base]
            ok = any(isgauge(K2, base | set(a)) for a in itertools.combinations(pool, k - 1))
            out[("42", "k=1" if k == 1 else "k>=2", ok)] += 1
        for v in {y for x in K for y in x}:
            st = [x for x in K if v in x]
            if len(st) != 5:
                continue
            link = fs().union(*[x - {v} for x in st])
            if len(link) != 5 or not all(len(x - {v}) == 4 for x in st):
                continue
            K2 = (K - set(st)) | {link}
            if not closed4(K2):
                continue
            N = {f for f in F.faces(K, 3) if v in f}
            base, k = T - N, len(T & N)
            pool = [y for y in F.faces(K2, 3) if y <= link and y not in base]
            ok = any(isgauge(K2, base | set(a)) for a in itertools.combinations(pool, max(k - 4, 0)))
            out[("51", "k=4" if k == 4 else "k>=5", ok)] += 1
    return out


def closure_tets(T, tets):
    """The closure of T under the rule 'three triangles of a tetrahedron force the fourth', for the
    tetrahedra `tets` only."""
    Z, ch = set(T), True
    while ch:
        ch = False
        for t in tets:
            miss = [f for f in map(fs, itertools.combinations(sorted(t), 3)) if f not in Z]
            if len(miss) == 1:
                Z.add(miss[0])
                ch = True
    return Z


def rule33(seeds):
    """3-3 move with the moved triangle sigma in T. Observed: with A the closure of T minus sigma under
    the tetrahedra that do not contain sigma, adding one triangle y = {s_i, s_j, c} (two vertices of
    sigma, one of tau) that is not in A to T minus sigma makes that closure complete, so the result
    forces both complexes (`Forces`, via the 3-3 characterization); some such y works at every location (242 of 242 here, 800 of 800 in a longer run over 1200 seeds) and
    every such y works at all but 1 of the 242 (3 of the 800).
    Limit: a finite lemma on the six vertices of the move (exhaustive over the 159 closed patterns of
    the 18 triangles on them) says the same for the neighbourhood alone, but derivations that use the
    tetrahedra outside the six vertices feed back into the neighbourhood, so the finite lemma does
    not give the statement for the whole complex; only the counts below support it.
    Returns a counter of (outcome)."""
    out = Counter()
    for sd in seeds:
        K, T = sphere_and_gauge(sd)
        if T is None:
            continue
        tets = F.faces(K, 4)
        for sg, tau, K2 in F.moves33(K):
            if sg not in T:
                continue
            base = T - {sg}
            P0 = {t for t in tets if not sg <= t}
            C = F.faces(K, 3) - {sg}
            A = closure_tets(base, P0)
            ms = [y for y in C - A if len(y & sg) == 2 and y <= (sg | tau)]
            good = [y for y in ms if C <= closure_tets(base | {y}, P0)]
            out[("some m-type y completes the closure", bool(good))] += 1
            out[("every m-type y not in A completes it", len(good) == len(ms))] += 1
    return out


def main(nseeds=150):
    c = Counter()
    hard = []
    for sd in range(nseeds):
        rng = random.Random(60000 + sd)
        K, nv = F.start()[0], 6
        for _ in range(rng.randrange(3, 7)):
            r = rng.choice(["15", "24", "33"])
            if r == "15":
                K, _ = F.m15(K, set(), nv, rng)
                nv += 1
            else:
                o = (F.m24 if r == "24" else F.m33)(K, set(), rng)
                if o:
                    K = o[0]
        T = F.direct_forcing_gauge(K, rng, tries=20)
        if T is None:
            continue
        for kind, K2, bases in all_moves(K, rng, nv):
            best = None
            for fb in bases:
                r = repair(K2, fb(T), K)
                if r is not None and (best is None or r < best):
                    best = r
            c[(kind, best)] += 1
            if best is None:
                hard.append((kind, K, K2, [fb(T) for fb in bases]))
    for k in sorted(c, key=str):
        print(k, c[k])
    deep = Counter()
    for kind, K, K2, bs in hard[:120]:
        r = min((x for x in (repair(K2, b, K, maxk=3) for b in bs) if x is not None), default=None)
        deep[(kind, "local<=3", r)] += 1
        if r is None:
            r2 = min((x for x in (repair(K2, b, K, maxk=3, local=False) for b in bs) if x is not None),
                     default=None)
            deep[(kind, "nonlocal<=3", r2)] += 1
    print("hard cases retried:", dict(deep))
    rule = inverse_rule(range(75000, 75150))
    print("repair rule for the inverse moves on fresh seeds:", dict(sorted(rule.items(), key=str)))
    assert all(k[2] for k in rule), "the repair rule fails"
    r33 = rule33(range(60000, 60400))
    print("3-3 with the moved triangle in T:", dict(sorted(r33.items(), key=str)))
    assert r33[("some m-type y completes the closure", False)] == 0
    ok = (all(c[(k, None)] == 0 for k in ("15", "24", "33"))
          and all(v for k, v in deep.items() if k[1] == "local<=3" and k[2] is not None) and
          all(k[2] is not None for k in deep if k[1] == "local<=3"))
    print("OK" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
