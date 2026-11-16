import sympy as sp, time, sys
from sympy.polys.fields import field
from sympy import QQ
USYM = len(sys.argv)>1 and sys.argv[1]=='sym'
names="p1 p2 p3 p4 q2 q3 Z"+(" u" if USYM else "")
F,*gens=field(names,QQ)
p1,p2,p3,p4,q2,q3,Z=gens[:7]
u=gens[7] if USYM else F(2)
def mon(e): 
    r=F(1)
    for g,k in zip((p1,p2,p3,p4,q2,q3),e): r=r*g**k
    return r
def qnum(M): return (M-1/M)/(u-1/u)
def lin(*terms):
    e=[0]*6
    for c,f in terms:
        for i in range(6): e[i]+=c*f[i]
    return tuple(e)
A1=(1,0,0,0,0,0);A2=(0,1,0,0,0,0);A3=(0,0,1,0,0,0);A4=(0,0,0,1,0,0);B2=(0,0,0,0,1,0);B3=(0,0,0,0,0,1);Z0=(0,)*6
def upow(n): return u**n if n>=0 else 1/u**(-n)
def qn_(e,sh=0): return qnum(mon(e)*upow(sh))
def Cn(e,sh=0): M=mon(e)*upow(sh+1); return M+1/M
def zq(e,sign,sh): return qnum(mon(e)*upow(sh)*Z**sign if sign>0 else mon(e)*upow(sh)/Z**(-sign))
def sub(e,f): return lin((1,e),(-1,f))
Bs=lin((1,A1),(1,A2),(-1,B2)); As=lin((1,A1),(1,A3),(-1,B3)); Es=lin((1,A3),(1,A4),(-1,B2)); Fs=lin((1,A2),(1,A4),(-1,B3))
qs=lin((-1,A1),(-1,A4),(1,B2),(1,B3)); xs=lin((-1,A2),(-1,A3),(1,B2),(1,B3))
b1=lin((1,A1),(1,A2),(1,A3),(1,A4),(-1,B2),(-1,B3))
K=(u-1/u)**2/2
a=K*qn_(sub(A1,As),1)*qn_(sub(A1,Bs),1)*qn_(sub(A4,Es),1)*qn_(sub(A4,Fs),1)/(qn_(xs,1)*qn_(xs,2))
c=K*qn_(A1,1)*qn_(A4,1)*qn_(sub(A1,xs),1)*qn_(sub(A4,xs),1)/(qn_(xs,0)*qn_(xs,1))
om=u+1/u
b=((Cn(Bs)*Cn(Es)+Cn(As)*Cn(Fs))*Cn(xs)-om*(Cn(Bs)*Cn(Fs)+Cn(As)*Cn(Es)))/(2*(u-1/u)**2*qn_(xs,0)*qn_(xs,2))
neg=lambda e: lin((-1,e))
def Eof(Zv):
    global Z
    zq_=lambda e,s,sh: qnum(mon(e)*upow(sh)*Zv**s)
    rp=zq_(neg(A1),1,0)*zq_(neg(A4),1,0)/(zq_(B2,-1,1)*zq_(B3,-1,1))
    rm=zq_(B2,-1,0)*zq_(B3,-1,0)/(zq_(neg(A1),1,1)*zq_(neg(A4),1,1))
    return 2*a*rp+2*b+2*c*rm-Cn(qs)
# interpolation: rho(Zv) at z=a2 (Zv=u^{a2} ), a3, beta1.
def rho_at(zv_exp,Zv):
    """returns rho(u*Zv) ... as value of rho at Z' = u*Zv  for z with Zv=u^z."""
    pass
t0=time.time()
zq_=lambda Zv,e,s,sh: qnum(mon(e)*upow(sh)*Zv**s)
# equation: -[z+2][b1-z] rho(uZ)/([z+1-a1][z+1-a4]) - [z-a2][z-a3] rho(Z)/([b2+1-z][b3+1-z]) = E(z)
def first_coef(Zv): return -zq_(Zv,Z0,1,2)*zq_(Zv,b1,-1,0)/(zq_(Zv,neg(A1),1,1)*zq_(Zv,neg(A4),1,1))
def second_coef(Zv): return -zq_(Zv,neg(A2),1,0)*zq_(Zv,neg(A3),1,0)/(zq_(Zv,B2,-1,1)*zq_(Zv,B3,-1,1))
# points: z=a2 (Zv=p2): second vanishes -> rho(u*p2) = E/first
# z=a3: rho(u*p3);  z=b1: first vanishes -> rho(p1p2p3p4/(q2q3)) = E/second
pts=[]
for Zv,which in ((p2,'f'),(p3,'f'),(mon(b1),'s')):
    E=Eof(Zv)
    if which=='f': pts.append((u*Zv, E/first_coef(Zv)))
    else: pts.append((Zv, E/second_coef(Zv)))
    print("pt",time.time()-t0,flush=True)
# rho(Y) = c1 Y^-2 + c3 + c5 Y^2 ; solve via Lagrange in W=Y^2 : rho = c1/W + c3 + c5 W
Ws=[y**2 for y,_ in pts]; vs=[v for _,v in pts]
# solve linear system with Cramer
import itertools
M=[[1/W,F(1),W] for W in Ws]
def det3(m):
    return (m[0][0]*(m[1][1]*m[2][2]-m[1][2]*m[2][1])-m[0][1]*(m[1][0]*m[2][2]-m[1][2]*m[2][0])+m[0][2]*(m[1][0]*m[2][1]-m[1][1]*m[2][0]))
D=det3(M)
sol=[]
for k in range(3):
    Mk=[row[:] for row in M]
    for i in range(3): Mk[i][k]=vs[i]
    sol.append(det3(Mk)/D)
    print("c",k,time.time()-t0,flush=True)
import pickle
c1,c3,c5=sol
print("c5 =",c5.as_expr() if False else str(c5.numer.as_expr())[:300] ,flush=True)
pickle.dump([str(s.as_expr()) for s in sol],open('csol%s.pkl'%("sym" if USYM else "num"),'wb'))
print("size", [len(s.numer.terms()) for s in sol],[len(s.denom.terms()) for s in sol])
