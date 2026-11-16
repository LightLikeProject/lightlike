# Numerical evidence (not proof): F(x,q) = sqrt([x+1][q+1]) * 6j has orthogonal rows and
# columns and a connected support graph, for r = argv[1].
import math, itertools, sys
r=int(sys.argv[1])
def qn(n): return math.sin(n*math.pi/r)/math.sin(math.pi/r)
def qf(n):
    p=1.0
    for k in range(1,n+1): p*=qn(k)
    return p
def inv(n): return 0.0 if n<0 else (1/qf(n) if qf(n)!=0 else 0.0)
def adm(a,b,c): return abs(a-b)<=c<=a+b and (a+b+c)%2==0 and a+b+c<=2*(r-2)
def delta(a,b,c):
    s=(a+b+c)//2
    return math.sqrt(qf(s-a)*qf(s-b)*qf(s-c)/qf(s+1))
def sixj(j1,j2,j3,j4,j5,j6):
    if not(adm(j1,j2,j3) and adm(j1,j5,j6) and adm(j4,j2,j6) and adm(j4,j5,j3)): return 0.0
    al=[(j1+j2+j3)//2,(j1+j5+j6)//2,(j4+j2+j6)//2,(j4+j5+j3)//2]
    be=[(j1+j2+j4+j5)//2,(j2+j3+j5+j6)//2,(j3+j1+j6+j4)//2]
    tot=0.0
    for z in range(0,sum([j1,j2,j3,j4,j5,j6])+1):
        t=(-1)**z*qf(z+1)
        for a in al: t*=inv(z-a)
        for b in be: t*=inv(b-z)
        tot+=t
    return delta(j1,j2,j3)*delta(j1,j5,j6)*delta(j4,j2,j6)*delta(j4,j5,j3)*tot
N=r-1
worst=0; bad=[]; disc=0; cnt=0
for B,A,E,F in itertools.product(range(N),repeat=4):
    M=[[math.sqrt(qn(x+1)*qn(q+1))*sixj(B,A,x,E,F,q) for q in range(N)] for x in range(N)]
    # columns that are nonzero
    sup=[(x,q) for x in range(N) for q in range(N) if abs(M[x][q])>1e-9]
    if not sup: continue
    cnt+=1
    # FtF and FFt diag?
    for q in range(N):
      for q2 in range(N):
        s=sum(M[x][q]*M[x][q2] for x in range(N))
        if q!=q2: worst=max(worst,abs(s))
    for x in range(N):
      for x2 in range(N):
        if x!=x2: worst=max(worst,abs(sum(M[x][q]*M[x2][q] for q in range(N))))
    # connectivity of bipartite support
    par={}
    def f(a):
        while par.setdefault(a,a)!=a:
            par[a]=par[par[a]]; a=par[a]
        return a
    for x,q in sup: par[f(('x',x))]=f(('q',q))
    comps={f(('x',x)) for x,q in sup}
    if len(comps)>1:
        disc+=1
        if len(bad)<3: bad.append((B,A,E,F,len(comps)))
    # norms
    for q in range(N):
        s=sum(M[x][q]**2 for x in range(N))
        if s>1e-9: worst=max(worst,abs(s-1)) if False else worst
print("r",r,"cases",cnt,"max offdiag",worst,"disconnected",disc,bad)
