import pickle, sympy as sp
Dc,Ns,res=pickle.load(open('parts.pkl','rb'))
u,p1,p2,p3,p4,q2,q3,Z=sp.symbols("u p1 p2 p3 p4 q2 q3 Z")
Br=lambda M:M-1/M
def zm(p,s): return Br(Z*u**s/p)
def bm(q,s): return Br(q*u**s/Z)
A1,A2,A3,A4,B2,B3=p1,p2,p3,p4,q2,q3
Bs=A1*A2/B2; As=A1*A3/B3; Es=A3*A4/B2; Fs=A2*A4/B3
qs=B2*B3/(A1*A4); xs=B2*B3/(A2*A3); b1=A1*A2*A3*A4/(B2*B3)
QQ=lambda e,s=0:Br(e*u**s); Cn=lambda e,s=0:(e*u**(s+1)+1/(e*u**(s+1)))
Q0,Q1,Q2=QQ(xs,0),QQ(xs,1),QQ(xs,2)
Na=QQ(A1/As,1)*QQ(A1/Bs,1)*QQ(A4/Es,1)*QQ(A4/Fs,1)
Nc=QQ(A1,1)*QQ(A4,1)*QQ(A1/xs,1)*QQ(A4/xs,1)
bn=(Cn(Bs)*Cn(Es)+Cn(As)*Cn(Fs))*Cn(xs)-(u+1/u)*(Cn(Bs)*Cn(Fs)+Cn(As)*Cn(Es))
M0=zm(A1,1)*zm(A2,1)*zm(A3,1)*zm(A4,1)*bm(B2,1)*bm(B3,1)
Mp=zm(A1,0)*zm(A1,1)*zm(A2,1)*zm(A3,1)*zm(A4,0)*zm(A4,1)
Mm=zm(A2,1)*zm(A3,1)*bm(B2,0)*bm(B2,1)*bm(B3,0)*bm(B3,1)
W0=zm(A2,0)*zm(A3,0)*zm(A1,1)*zm(A2,1)*zm(A3,1)*zm(A4,1)
W1=-Br(Z*u**2)*Br(b1/Z)*bm(B2,1)*bm(B3,1)*zm(A2,1)*zm(A3,1)
Cq=Cn(qs)
Q012=Q0*Q1*Q2
X0=2*Q0*Na*Mp+2*Q1*bn*M0+2*Q2*Nc*Mm-2*Q012*Cq*M0
E1=-2*Q012*(W1/(u**2*Z**2)-W0/Z**2); E3=-2*Q012*(W1-W0); E5=-2*Q012*(W1*u**2*Z**2-W0*Z**2)
mine=[X0,E1,E3,E5]
keys=[(0,0,0),(1,0,0),(0,1,0),(0,0,1)]
g=sp.symbols("u p1 p2 p3 p4 q2 q3 Z")
for e,key in zip(mine,keys):
    theirs=sum(Z**k*sp.sympify(res[k][key]) for k in res if key in res[k])
    ratio=sp.simplify(sp.expand(theirs)/sp.expand(e)) if False else None
    me=sp.expand(e); th=sp.expand(theirs)
    # leading-term ratio
    t0=sorted(sp.Poly(th*u**40*p1**40*p2**40*p3**40*p4**40*q2**40*q3**40*Z**40,*g).terms())[0]
    m0=sorted(sp.Poly(me*u**40*p1**40*p2**40*p3**40*p4**40*q2**40*q3**40*Z**40,*g).terms())[0]
    print(key,"terms mine/theirs",len(sp.Poly(me*u**40*p1**40*p2**40*p3**40*p4**40*q2**40*q3**40*Z**40,*g).terms()),len(sp.Poly(th,*g).terms()),"lead",t0,m0)
    # candidate ratio
    mono=sp.prod([x**(a-b) for x,a,b in zip(g,t0[0],m0[0])])*sp.Rational(t0[1],m0[1])
    print("  check theirs == ratio*mine:",sp.expand(th-mono*me)==0,"ratio",mono)
