src=open('wz8.py').read().split("t0=time.time()")[0].replace("USYM = len(sys.argv)>1 and sys.argv[1]=='sym'","USYM=True")
src=src.replace('names="p1 p2 p3 p4 q2 q3 Z"+(" u" if USYM else "")','names="p1 p2 p3 p4 q2 q3 Z u c1 c3 c5"')
src=src.replace("p1,p2,p3,p4,q2,q3,Z=gens[:7]","p1,p2,p3,p4,q2,q3,Z=gens[:7]; c1,c3,c5=gens[8:11]")
exec(src)
exec(open('size.py').read().split("import pickle")[1].split("cs=[")[0] if False else "")
def rho(Zv): return c1/Zv**2+c3+c5*Zv**2
def Qm(M): return (M-1/M)
def zm(Pm,sh,Zv=Z): return Qm(Zv*u**sh/Pm)
def bm(Qq,sh,Zv=Z): return Qm(Qq*u**sh/Zv)
half=F(1)/2
def QQ(e,sh=0): return Qm(mon(e)*upow(sh))
a_=half*QQ(sub(A1,As),1)*QQ(sub(A1,Bs),1)*QQ(sub(A4,Es),1)*QQ(sub(A4,Fs),1)/(QQ(xs,1)*QQ(xs,2))
c_=half*QQ(A1,1)*QQ(A4,1)*QQ(sub(A1,xs),1)*QQ(sub(A4,xs),1)/(QQ(xs,0)*QQ(xs,1))
b_=((Cn(Bs)*Cn(Es)+Cn(As)*Cn(Fs))*Cn(xs)-om*(Cn(Bs)*Cn(Fs)+Cn(As)*Cn(Es)))/(2*QQ(xs,0)*QQ(xs,2))
M0=zm(p1,1)*zm(p2,1)*zm(p3,1)*zm(p4,1)*bm(q2,1)*bm(q3,1)
Mp=zm(p1,0)*zm(p1,1)*zm(p2,1)*zm(p3,1)*zm(p4,0)*zm(p4,1)
Mm=zm(p2,1)*zm(p3,1)*bm(q2,0)*bm(q2,1)*bm(q3,0)*bm(q3,1)
MG0=rho(Z)*zm(p2,0)*zm(p3,0)*zm(p1,1)*zm(p2,1)*zm(p3,1)*zm(p4,1)
MG1=-Qm(Z*u**2)*Qm(mon(b1)/Z)*bm(q2,1)*bm(q3,1)*rho(u*Z)*zm(p2,1)*zm(p3,1)
qsm=mon(qs)
lhs=2*a_*Mp+2*b_*M0+2*c_*Mm-(qsm*u+1/(qsm*u))*M0-(MG1-MG0)
N=lhs.numer; D=lhs.denom
print("numer terms",len(N.terms()),"denom",len(D.terms()),flush=True)
import collections
bz=collections.defaultdict(lambda:0)
# split by Z exponent (index 6)
from sympy import Poly
cnt=collections.Counter()
for m,cf in N.terms(): cnt[m[6]]+=1
print(sorted(cnt.items()))

import pickle
cs=[sp.sympify(s) for s in pickle.load(open('csolsym.pkl','rb'))]
syms=dict(p1=sp.Symbol('p1'),p2=sp.Symbol('p2'),p3=sp.Symbol('p3'),p4=sp.Symbol('p4'),q2=sp.Symbol('q2'),q3=sp.Symbol('q3'),u=sp.Symbol('u'))
# common denominator of c1,c3,c5
Cn_=[F.from_expr(e) if False else None for e in cs]
from sympy import together, fraction, lcm, cancel, expand
fr=[fraction(cancel(together(e))) for e in cs]
dens=[d for _,d in fr]
Dc=dens[0]
for d in dens[1:]: Dc=lcm(Dc,d)
Ns=[expand(cancel(e*Dc)) for e in cs]
print("Dc=",sp.factor(Dc)); print("Nterms",[len(sp.Poly(n).terms()) for n in Ns],flush=True)
# split numerator N by Z exponent and c variable
Nsym=N.as_expr()
names_=[str(g) for g in gens]
P=sp.Poly(Nsym,*[sp.Symbol(n) for n in names_])
parts={}
for mon_,cf in P.terms():
    d=dict(zip(names_,mon_))
    key=(d['Z'],d['c1'],d['c3'],d['c5'])
    parts.setdefault((d['Z'],(d['c1'],d['c3'],d['c5'])),[]).append((cf,d))
import json
res={}
for (zk,cc),lst in parts.items():
    pol=0
    for cf,d in lst:
        t=cf
        for v in ['p1','p2','p3','p4','q2','q3','u']: t*=sp.Symbol(v)**d[v]
        pol+=t
    res.setdefault(zk,{})[cc]=pol
print({k:{c:len(sp.Poly(p,*syms.values()).terms()) for c,p in v.items()} for k,v in res.items()})
pickle.dump((str(Dc),[str(n) for n in Ns],{k:{c:str(p) for c,p in v.items()} for k,v in res.items()}),open('parts.pkl','wb'))
