"""Numerical check (not a proof): the finite-cutoff gauge-fixed Ooguri state sum can depend on the
gauge set when the gauge sets do not force every triangle.

Complex: five 4-simplices on 8 vertices (not a manifold). Four random gauge sets (vertices, edges and
the triangles of T collapse to a point) of size E - V + 1 = 18, all failing to force every triangle;
the state sum with triangle spins <= 1/2 (doubled cutoff 1) is computed with the closed-form vertex of
scripts/spinfoam/vertex_check.py. Expected: more than one distinct value (observed 33, 23.627417, -15,
-7). Control: for the boundary of the 5-simplex the value is 1 for every gauge set (Lean:
amplitudeGF_starT, amplitudeGF_twistT). Floating point; takes about 10 minutes.
"""
import sys
pass
import itertools, random, functools, collections
sys.path.insert(0, __import__('os').path.dirname(__file__))
import os
import vertex_check as vc
a,b,c_,p,q,r=range(6)
simp=[(0, 1, 2, 3, 6), (1, 2, 4, 5, 6), (0, 1, 2, 4, 6), (0, 1, 2, 5, 7), (0, 4, 5, 6, 7)]
def faces(k): return {frozenset(c) for s in simp for c in itertools.combinations(s,k)}
verts,edges,tris,tets=faces(1),faces(2),faces(3),faces(4)
tris=sorted(tris,key=sorted)
n=len(edges)-len(verts)+1
print(len(verts),len(edges),len(tris),len(tets),"gauge size",n)
def collapsible(X):
    X=set(X)
    while len(X)>1:
        for s in list(X):
            cof=[r for r in X if s<r]
            if len(cof)==1 and len(cof[0])==len(s)+1:
                X.discard(s);X.discard(cof[0]);break
        else: return False
    return len(X)==1
rng=random.Random(3); gs=set(); base=verts|edges; tries=0
while len(gs)<4 and tries<2000000:
    tries+=1
    T=frozenset(rng.sample(tris,n))
    if collapsible(base|T): gs.add(T)
print(len(gs),"gauge sets in",tries)
tetcount=collections.Counter(t for s in simp for t in (frozenset(s)-{x} for x in s))
shared=sorted([t for t in tets if tetcount[t]>1],key=sorted); print("shared tets",len(shared))
@functools.lru_cache(None)
def ampc(Jt,Kt):
    Jd={frozenset((x,y)):Jt[i] for i,(x,y) in enumerate(itertools.combinations(range(5),2))}
    return vc.amp_closed(Jd,list(Kt))
def simplex_val(s,col,c,sh_assign):
    Jt=tuple(col[frozenset(s)-{s[x],s[y]}] for x,y in itertools.combinations(range(5),2))
    Jd={frozenset((x,y)):Jt[i] for i,(x,y) in enumerate(itertools.combinations(range(5),2))}
    ks=[]
    for i in range(5):
        tet=frozenset(s)-{s[i]}
        w=[x for x in range(5) if x!=i]
        sp=[Jd[frozenset((i,qq))] for qq in (w[0],w[2],w[1],w[3])]
        if tet in sh_assign: ks.append([sh_assign[tet]] if vc.tri(sp[0],sp[1],sh_assign[tet]) and vc.tri(sh_assign[tet],sp[2],sp[3]) else [])
        else: ks.append([k for k in range(2*c+1) if vc.tri(sp[0],sp[1],k) and vc.tri(k,sp[2],sp[3])])
    if any(not k for k in ks): return 0.0
    return sum(ampc(Jt,K) for K in itertools.product(*ks))
def amp(T,c):
    free=[t for t in tris if t not in T]; tot=0.0
    for vals in itertools.product(range(c+1),repeat=len(free)):
        col={t:0 for t in tris}; col.update(dict(zip(free,vals)))
        w=1
        for t in tris: w*=col[t]+1
        s_=0.0
        for sv in itertools.product(range(2*c+1),repeat=len(shared)):
            sa=dict(zip(shared,sv)); pr=1.0
            for s in simp:
                pr*=simplex_val(s,col,c,{t:v for t,v in sa.items() if t<=frozenset(s)})
                if pr==0: break
            s_+=pr
        tot+=w*s_
    return tot
def _forces(simp,T):
    T=set(T); ch=True
    while ch:
        ch=False
        for t in tets:
            tt=[frozenset(c) for c in itertools.combinations(sorted(t),3)]
            miss=[g for g in tt if g not in T]
            if len(miss)==1: T.add(miss[0]); ch=True
    return set(tris)<=T
class F: forces=staticmethod(_forces)
c=1
print('nonforcing among gs:',sum(1 for T in gs if not F.forces(simp,T)),'free',len(tris)-n,'tets',len(tets),'shared',len(shared))
res=collections.Counter()
for T in gs: res[round(amp(set(T),c),6)]+=1; print(res,flush=True)

print('OK' if len(res)>1 else 'FAIL: no dependence found')
sys.exit(0 if len(res)>1 else 1)
