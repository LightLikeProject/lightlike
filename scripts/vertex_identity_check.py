"""Check of the normal-coordinate identity behind the vertex expansion (RC6b), dimension 2.

For a random metric jet (degree 2 polynomial g) at v = 0 it verifies, through order 4 in (w, w'):
  distJet(v + w, w' - w) = |u(w) - u(w')|_{g0}^2 - (R/6) (|w|^2 |w'|^2 - (w.w')^2)
with the displacement u(w) = w + 1/2 Gamma(w,w) + 1/6 (dGamma(w;w,w) + Gamma(w, Gamma(w,w))),
and R the scalar curvature at v. A control with the wrong curvature coefficient must have no
solution. Numerical evidence, not proof.  Run: .venv/bin/python -I scripts/vertex_identity_check.py
"""
import sympy as sp, random, itertools
random.seed(3)
x=sp.symbols('x0 x1'); w=sp.symbols('w0 w1'); v=sp.symbols('v0 v1'); t=sp.symbols('t')
R=lambda: sp.Rational(random.randint(-5,5),random.randint(1,4))
g0=sp.Matrix([[2,sp.Rational(1,2)],[sp.Rational(1,2),1]])
def sym():
    return {}
# metric polynomial to degree 2
g=sp.zeros(2,2)
for i in range(2):
    for j in range(i,2):
        e=g0[i,j]+sum(R()*x[k] for k in range(2))+sum(R()*x[k]*x[l] for k in range(2) for l in range(k,2))
        g[i,j]=e; g[j,i]=e
ginv=g.inv()
def chris(i,j,k):
    return sum(ginv[i,l]*(sp.diff(g[l,j],x[k])+sp.diff(g[l,k],x[j])-sp.diff(g[j,k],x[l])) for l in range(2))/2
def deg_trunc(e,vars_,N):
    e=sp.expand(e)
    P=sp.Poly(e,*vars_)
    return sum(c*sp.prod([vv**m for vv,m in zip(vars_,mon)]) for mon,c in P.terms() if sum(mon)<=N)
def distjet(base,D):
    sub=dict(zip(x,base))
    G=g.subs(sub)
    dm=lambda u: sp.Matrix(2,2,lambda i,j: sum(u[k]*sp.diff(g[i,j],x[k]) for k in range(2))).subs(sub)
    ddm=lambda u,u2: sp.Matrix(2,2,lambda i,j: sum(u[k]*u2[l]*sp.diff(g[i,j],x[k],x[l]) for k in range(2) for l in range(2))).subs(sub)
    ch=sp.Matrix([sum(chris(i,j,k).subs(sub)*D[j]*D[k] for j in range(2) for k in range(2)) for i in range(2)])
    Dv=sp.Matrix(D)
    return (Dv.T*G*Dv)[0]+sp.Rational(1,2)*(Dv.T*dm(D)*Dv)[0]+sp.Rational(1,6)*(Dv.T*ddm(D,D)*Dv)[0]-sp.Rational(1,12)*(ch.T*G*ch)[0]
# base = 0 + a*w (scale param t): points t*w, t*v
W=[t*w[0],t*w[1]]; V=[t*v[0],t*v[1]]
D=[V[0]-W[0],V[1]-W[1]]
d2=distjet(W,D)
# series in t up to 4
d2s=sp.series(sp.expand(d2),t,0,5).removeO()
d2s=sp.expand(d2s)
print("series done")
# curvature scalar at 0
def riem(r,s,m,n_):
    return sp.diff(chris(r,n_,s),x[m])-sp.diff(chris(r,m,s),x[n_])+sum(chris(r,m,l)*chris(l,n_,s)-chris(r,n_,l)*chris(l,m,s) for l in range(2))
ric=lambda s,n_: sum(riem(r,s,r,n_) for r in range(2))
Kscal=sum(ginv[s,n_]*ric(s,n_) for s in range(2) for n_ in range(2)).subs({x[0]:0,x[1]:0})
Kscal=sp.nsimplify(Kscal)
print("scalar curv",Kscal)
# unknown displacement u(w)=w+Q2+Q3
G0=g0
q2=sp.symbols('q2_0:6'); q3=sp.symbols('q3_0:8')
def U(wv):
    a,b=wv
    return sp.Matrix([wv[0]+q2[0]*a*a+q2[1]*a*b+q2[2]*b*b+q3[0]*a**3+q3[1]*a*a*b+q3[2]*a*b*b+q3[3]*b**3,
                      wv[1]+q2[3]*a*a+q2[4]*a*b+q2[5]*b*b+q3[4]*a**3+q3[5]*a*a*b+q3[6]*a*b*b+q3[7]*b**3])
du=U(W)-U(V)
eu=sp.expand((du.T*G0*du)[0])
Ar=sp.expand(sum(0 for _ in [0]))
# area^2 term: |u|^2|u'|^2-(u.u')^2 in g0 at leading order
Wm=sp.Matrix(W);Vm=sp.Matrix(V)
a2=(Wm.T*G0*Wm)[0];b2=(Vm.T*G0*Vm)[0];ab=(Wm.T*G0*Vm)[0]
curv=-Kscal/6*(a2*b2-ab**2)  # candidate: K scalar = 2K_gauss in 2D
pred=sp.expand(eu+curv)
diff=sp.expand(d2s-sp.series(pred,t,0,5).removeO())
eqs=[]
for k in (2,3,4):
    c=sp.Poly(diff.coeff(t,k),*w,*v)
    eqs+=c.coeffs()
sol=sp.solve(eqs[:],list(q2)+list(q3),dict=True)
print("solutions:",len(sol))
assert sol, "FAILED: no displacement reproduces distJet"
if sol: print(sol[0])
# residual check
z={x[0]:0,x[1]:0}
s=sol[0]
for i in range(2):
    G=[[sp.nsimplify(chris(i,j,k).subs(z)) for k in range(2)] for j in range(2)]
    print("Gamma^%d"%i,G)
# Q2 as symmetric tensor: coefficient of a*a, a*b, b*b
print([s[q] for q in q2])
# frame: u should satisfy u = L w where g0 = L^T L? We used G0 metric on u directly so u is in w-coordinates (not orthonormal)
a1,a2=sp.symbols('a1 a2')
ww=sp.symbols('s0 s1')
Gm=lambda i,j,k: chris(i,j,k).subs(z)
dG=lambda i,j,k,l: sp.diff(chris(i,j,k),x[l]).subs(z)
Q3=[]
for i in range(2):
    t1=sum(dG(i,j,l,k)*ww[j]*ww[k]*ww[l] for j in range(2) for k in range(2) for l in range(2))
    t2=sum(Gm(i,j,m)*Gm(m,k,l)*ww[j]*ww[k]*ww[l] for j in range(2) for k in range(2) for l in range(2) for m in range(2))
    Q3.append(a1*t1+a2*t2)
Qa=U(ww).subs({qq:s[qq] for qq in q2}).subs({qq:s[qq] for qq in q3})
eqs=[]
for i in range(2):
    ex=sp.expand(Qa[i]-ww[i]-sum(sp.Rational(1,2)*Gm(i,j,k)*ww[j]*ww[k] for j in range(2) for k in range(2))-Q3[i])
    eqs+=sp.Poly(ex,*ww).coeffs()
sol_a = sp.solve(eqs,[a1,a2],dict=True)
print(sol_a)
assert sol_a, "FAILED: the cubic displacement is not the Gamma/dGamma form"

# control: wrong curvature coefficient (R/3 instead of R/6) must give no displacement
pred_bad=sp.expand(eu-Kscal/3*(a2*b2-ab**2))
diff_bad=sp.expand(d2s-sp.series(pred_bad,t,0,5).removeO())
eqs_bad=[]
for k in (2,3,4):
    eqs_bad+=sp.Poly(diff_bad.coeff(t,k),*w,*v).coeffs()
n_bad = len(sp.solve(eqs_bad,list(q2)+list(q3),dict=True))
print("control solutions (expect 0):",n_bad)
assert n_bad == 0, "FAILED: the wrong curvature coefficient is not rejected"
print("PASS vertex identity and wrong-coefficient control")
