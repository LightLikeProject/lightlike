import sys,time
exec(open('wz8.py').read().split("t0=time.time()")[0].replace("USYM = len(sys.argv)>1 and sys.argv[1]=='sym'","USYM=True"))
import pickle
cs=[sp.sympify(s) for s in pickle.load(open('csolsym.pkl','rb'))]
names=dict(p1=p1,p2=p2,p3=p3,p4=p4,q2=q2,q3=q3,u=u)
def tof(e):
    return F.from_expr(e) if hasattr(F,'from_expr') else None
c1,c3,c5=[tof(e) for e in cs]
def rho(Zv): return c1/Zv**2+c3+c5*Zv**2
def Qm(M): return (M-1/M)   # Q-tilde
def zm(Pm,sh,Zv=Z): return Qm(Zv*u**sh/Pm)
def bm(Qq,sh,Zv=Z): return Qm(Qq*u**sh/Zv)
half=F(1)/2
# a,b,c with Qtilde, K=1/2
def QQ(e,sh=0): return Qm(mon(e)*upow(sh))
a_=half*QQ(sub(A1,As),1)*QQ(sub(A1,Bs),1)*QQ(sub(A4,Es),1)*QQ(sub(A4,Fs),1)/(QQ(xs,1)*QQ(xs,2))
c_=half*QQ(A1,1)*QQ(A4,1)*QQ(sub(A1,xs),1)*QQ(sub(A4,xs),1)/(QQ(xs,0)*QQ(xs,1))
b_=((Cn(Bs)*Cn(Es)+Cn(As)*Cn(Fs))*Cn(xs)-om*(Cn(Bs)*Cn(Fs)+Cn(As)*Cn(Es)))/(2*QQ(xs,0)*QQ(xs,2))
M0=zm(p1,1)*zm(p2,1)*zm(p3,1)*zm(p4,1)*bm(q2,1)*bm(q3,1)
Mp=zm(p1,0)*zm(p1,1)*zm(p2,1)*zm(p3,1)*zm(p4,0)*zm(p4,1)
Mm=zm(p2,1)*zm(p3,1)*bm(q2,0)*bm(q2,1)*bm(q3,0)*bm(q3,1)
b1m=mon(b1)
MG0=rho(Z)*zm(p2,0)*zm(p3,0)*zm(p1,1)*zm(p2,1)*zm(p3,1)*zm(p4,1)
MG1=-Qm(Z*u**2)*Qm(b1m/Z)*bm(q2,1)*bm(q3,1)*rho(u*Z)*zm(p2,1)*zm(p3,1)
qsm=mon(qs)
lhs=2*a_*Mp+2*b_*M0+2*c_*Mm-(qsm*u+1/(qsm*u))*M0-(MG1-MG0)
t0=time.time()
print("zero?",lhs==0,time.time()-t0)
