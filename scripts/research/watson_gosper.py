"""Watson q-Whipple, L side: numeric Gosper at fixed n to read the Zeilberger certificate R(x,y) as a rational function of y.
Pure Fraction arithmetic (no sympy). Usage: python3 -I watson_gosper.py [n]"""
import sys
from fractions import Fraction as F
q=F(3,2); a,b,c,d,e = F(13,7),F(5,11),F(17,3),F(7,19),F(23,5)
def ratio(x,y):
    z=a*a*q*q*x/(b*c*d*e)
    return (1-a*q*q*y*y)/(1-a*y*y)*(1-a*y)*(1-b*y)*(1-c*y)*(1-d*y)*(1-e*y)*(1-y/x)/((1-q*y)*(1-a*q*y/b)*(1-a*q*y/c)*(1-a*q*y/d)*(1-a*q*y/e)*(1-a*q*x*y))*z
def terms(n):
    x=q**n; t=[F(1)]
    for k in range(n): t.append(t[-1]*ratio(x,q**k))
    return t
def L(n): return sum(terms(n))
def nullspace(M):
    M=[r[:] for r in M]; piv=[]; r=0; nc=len(M[0])
    for c_ in range(nc):
        p=next((i for i in range(r,len(M)) if M[i][c_]!=0),None)
        if p is None: continue
        M[r],M[p]=M[p],M[r]; inv=1/M[r][c_]; M[r]=[v*inv for v in M[r]]
        for i in range(len(M)):
            if i!=r and M[i][c_]!=0:
                f=M[i][c_]; M[i]=[u-f*v for u,v in zip(M[i],M[r])]
        piv.append(c_); r+=1
    free=[j for j in range(nc) if j not in piv]; out=[]
    for fj in free:
        v=[F(0)]*nc; v[fj]=F(1)
        for i,pc in enumerate(piv): v[pc]=-M[i][fj]
        out.append(v)
    return out
DX=4; N=int(sys.argv[1]) if len(sys.argv)>1 else 30
Ls=[L(n) for n in range(0,19)]
rows=[[ (q**n)**m*Ls[n+i] for i in range(3) for m in range(DX+1)] for n in range(0,17)]
ns=nullspace(rows); print('rec nullspace dim',len(ns),flush=True)
v=ns[0]; p=[[v[i*(DX+1)+m] for m in range(DX+1)] for i in range(3)]
x=q**N
pn=[sum(p[i][m]*x**m for m in range(DX+1)) for i in range(3)]
t0,t1,t2=terms(N),terms(N+1),terms(N+2)
t0+= [F(0)]*(len(t2)-len(t0)); t1+=[F(0)]*(len(t2)-len(t1))
Fk=[pn[0]*t0[k]+pn[1]*t1[k]+pn[2]*t2[k] for k in range(len(t2))]
G=[F(0)]
for k in range(len(Fk)): G.append(G[-1]+Fk[k])
print('total (should be 0):',G[-1]==0,flush=True)
# R_k = G_k / t0_k  (t at (n=N)); G_k = sum_{j<k}F_j , G_{k+1}-G_k=F_k. R as function of y=q^k
pts=[(q**k,G[k]/t0[k]) for k in range(0,N+1)]
for tot in range(2,24):
    for dn in range(0,tot+1):
        dd=tot-dn  # numerator degree dn, denominator degree dd (monic-free)
        unk=dn+1+dd+1
        if unk>len(pts)-3: continue
        rows=[[y**j for j in range(dn+1)]+[-r*y**j for j in range(dd+1)] for y,r in pts]
        ns=nullspace(rows)
        if ns:
            v=ns[0]; den=v[dn+1:]
            print('deg num',dn,'deg den',dd,'nullity',len(ns)); print('den coeffs (low->high):',[str(u) for u in den])
            # roots of den as powers of q / a etc: test candidate factors
            for name,r0 in [('1/(q^-?)',None)]: pass
            sys.exit()
print('no rational fit')
