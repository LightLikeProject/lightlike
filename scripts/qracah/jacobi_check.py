# Numerical evidence (not proof): the j3-recurrence of the q-Racah sum at q = e^{i pi/r}, built from
# the closed-form coefficients Na, bn, Nc, Cq, Q_k, is satisfied, and the detailed-balance identity
# rho_x A_x D(x)^2 = rho_{x+2} C_{x+2} D(x+2)^2 holds (so the recurrence matrix is symmetric after scaling).
import cmath, math, itertools, sys
r=int(sys.argv[1]); u=cmath.exp(1j*math.pi/r)
def qn(n): return math.sin(n*math.pi/r)/math.sin(math.pi/r)
def qf(n):
    p=1.0
    for k in range(1,n+1): p*=qn(k)
    return p
def inv(n): return 0.0 if n<0 else (1/qf(n) if abs(qf(n))>1e-12 else 0.0)
def bk(M): return M-1/M
def ck(M): return M+1/M
def SR(a1,a2,a3,a4,b1,b2,b3):
    return sum((-1)**z*qf(z+1)*inv(z-a1)*inv(z-a2)*inv(z-a3)*inv(z-a4)*inv(b1-z)*inv(b2-z)*inv(b3-z) for z in range(0,b1+1))
def coef(a1,a2,a3,a4,b2,b3):
    p1,p2,p3,p4=[u**a for a in (a1,a2,a3,a4)]; q2,q3=u**b2,u**b3
    Na=bk(u/p3*q3)*bk(u/p2*q2)*bk(u/p3*q2)*bk(u/p2*q3)
    Nc=bk(u*p1)*bk(u*p4)*bk(u*p1*p2*p3/q2/q3)*bk(u*p2*p3*p4/q2/q3)
    Cq=ck(u/p1/p4*q2*q3)
    bn=(ck(u*p1*p2/q2)*ck(u*p3*p4/q2)+ck(u*p1*p3/q3)*ck(u*p2*p4/q3))*ck(u/p2/p3*q2*q3)-(u+1/u)*(ck(u*p1*p2/q2)*ck(u*p2*p4/q3)+ck(u*p1*p3/q3)*ck(u*p3*p4/q2))
    Q=[bk(u**k/p2/p3*q2*q3) for k in (0,1,2)]
    return Na,Nc,Cq,bn,Q
def params(j1,j2,j3,j4,j5,j6):
    return ((j1+j2+j3)//2,(j1+j5+j6)//2,(j4+j2+j6)//2,(j4+j5+j3)//2,(j1+j2+j4+j5)//2,(j2+j3+j5+j6)//2,(j3+j1+j6+j4)//2)
worst=0;n=0;skip=0
for j1,j2,j4,j5,j6 in itertools.product(range(r-1),repeat=5):
  for j3 in range(0,r-1):
    if (j1+j2+j3)%2 or (j1+j5+j6)%2 or (j4+j2+j6)%2 or (j4+j5+j3)%2: continue
    if j3+2>r-2 or j3<2: continue   # interior rows only
    a1,a2,a3,a4,b1,b2,b3=params(j1,j2,j3,j4,j5,j6)
    Na,Nc,Cq,bn,Q=coef(a1,a2,a3,a4,b2,b3)
    if min(abs(q) for q in Q)<1e-9: skip+=1; continue
    A=Na/(Q[1]*Q[2]); B=bn/(Q[0]*Q[2]); C=Nc/(Q[0]*Q[1])
    S0=SR(a1,a2,a3,a4,b1,b2,b3); Sp=SR(a1+1,a2,a3,a4+1,b1,b2+1,b3+1); Sm=SR(a1-1,a2,a3,a4-1,b1,b2-1,b3-1)
    res=abs(A*Sp+B*S0+C*Sm-Cq*S0); worst=max(worst,res); n+=1
print("r",r,"rows checked",n,"skipped(deg)",skip,"max recurrence residual",worst)
def adm(a,b,c): return abs(a-b)<=c<=a+b and (a+b+c)%2==0 and a+b+c<=2*(r-2)
def D2(a,b,c):
    s=(a+b+c)//2
    return qf(s-a)*qf(s-b)*qf(s-c)/qf(s+1)
w=0;m=0;viol=[]
for j1,j2,j4,j5,j6 in itertools.product(range(r-1),repeat=5):
  for x in range(0,r-1):
    if (j1+j2+x)%2 or (j1+j5+j6)%2 or (j4+j2+j6)%2 or (j4+j5+x)%2: continue
    p=params(j1,j2,x,j4,j5,j6)
    Na,Nc,Cq,bn,Q=coef(*p[:4],p[5],p[6])
    if min(abs(q) for q in Q)<1e-9: continue
    A=Na/(Q[1]*Q[2])
    x2=x+2
    if x2>r-2: continue
    p2=params(j1,j2,x2,j4,j5,j6)
    N2,Nc2,Cq2,bn2,Q2=coef(*p2[:4],p2[5],p2[6])
    if min(abs(q) for q in Q2)<1e-9: continue
    C2=Nc2/(Q2[0]*Q2[1])
    ok=adm(j1,j2,x) and adm(j4,j5,x) and adm(j1,j2,x2) and adm(j4,j5,x2)
    lhs=qn(x+1)*A*D2(j1,j2,x)*D2(j4,j5,x) if ok else None
    if ok:
        rhs=qn(x2+1)*C2*D2(j1,j2,x2)*D2(j4,j5,x2)
        w=max(w,abs(lhs-rhs)); m+=1
print("detailed balance checked",m,"max defect",w)
