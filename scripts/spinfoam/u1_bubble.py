"""Numerical evidence (PROXY, U(1) in place of SU(2)), not a proof: growth of the Ooguri-type state sum
without gauge fixing on the boundary of the 5-simplex.

Z(N) = number of integer triangle charges n (20 triangles, |n_f| <= N) with signed closure on each of
the 15 tetrahedra, (M n)_t = 0. The kernel of M has dimension 10, so Z(N) grows like N^10. Controls:
wrong closure signs (all +1) give kernel dimension 5 and much smaller counts; fixing the 10 triangles
through vertex 0 (a gauge set that forces every triangle) leaves only n = 0, so Z = 1 at every N.
Not the SU(2) sum: the exact SU(2) divergence of the cut-off tetrahedron sum is `tetraPartition_ge`.
Run: python3 -I scripts/spinfoam/u1_bubble.py [N_max]   (default 2, about 2 s; N_max = 4 takes 160 s)
"""
import itertools, sys
import numpy as np, sympy as sp
tris=list(itertools.combinations(range(6),3)); tets=list(itertools.combinations(range(6),4))
def mat(sign):
    M=sp.zeros(len(tets),20)
    for i,t in enumerate(tets):
        for k,x in enumerate(t):
            M[i,tris.index(tuple(y for y in t if y!=x))]=(-1)**k if sign else 1
    return M
def count(M,N,fixed=()):
    rows=[list(M.row(i)) for i in range(M.rows)]
    for f in fixed:
        r=[0]*20; r[f]=1; rows.append(r)
    R,piv=sp.Matrix(rows).rref(); free=[j for j in range(20) if j not in piv]
    d=len(free)
    if d==0: return 1,0
    C=np.array([[float(-R[i,fj]) for fj in free] for i in range(len(piv))]) if piv else np.zeros((0,d))
    ax=np.arange(-N,N+1); cnt=0
    # chunk over first d-6 coords via product, vectorise the last 6
    k=min(d,6); head=d-k
    tail=np.array(np.meshgrid(*[ax]*k,indexing='ij')).reshape(k,-1).T if k else np.zeros((1,0))
    for h in itertools.product(ax,repeat=head):
        X=np.hstack([np.tile(np.array(h,float),(len(tail),1)),tail.astype(float)])
        with np.errstate(all='ignore'):  # spurious BLAS flags on some macOS numpy builds
            P=X@C.T
        assert np.isfinite(P).all()
        ok=(np.abs(P-np.round(P))<1e-9).all(1)&(np.abs(P)<=N+1e-9).all(1)
        cnt+=int(ok.sum())
    return cnt,d
if __name__ == "__main__":
    Mc, Mw = mat(True), mat(False)
    assert 20 - Mc.rank() == 10 and 20 - Mw.rank() == 5, "kernel dimensions"
    print("kernel dim correct", 20 - Mc.rank(), "| wrong-sign", 20 - Mw.rank())
    Nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    fx = [tris.index(t) for t in tris if 0 in t]
    known = {1: (4231, 73), 2: (541495, 835)}
    prev = None
    for N in range(1, Nmax + 1):
        c, _ = count(Mc, N); w, _ = count(Mw, N); f, _ = count(Mc, N, fx)
        print("N", N, "correct", c, "wrong-sign", w, "forcing-T", f, flush=True)
        assert f == 1, "gauge-fixed (forcing) sum stays 1"
        assert w < c, "wrong-sign control differs"
        if N in known:
            assert (c, w) == known[N], ("known counts", N)
        if prev:
            assert c > prev, "unbounded growth"
        prev = c
    print("OK")
