"""Watson q-Whipple: search a Zeilberger certificate (exact rationals). Usage: python3 -I watson_cert.py [L|R] [dx dy]"""
import sys, random
from fractions import Fraction as F
import sympy as sp

import os
_P=[F(t) for t in os.environ['WPAR'].split(',')] if os.environ.get('WPAR') else [F(3,2),F(13,7),F(5,11),F(17,3),F(7,19),F(23,5)]
q,a,b,c,d,e=_P  # override with WPAR=q,a,b,c,d,e
side = sys.argv[1] if len(sys.argv)>1 else 'L'
DX = int(sys.argv[2]) if len(sys.argv)>2 else 4
DY = int(sys.argv[3]) if len(sys.argv)>3 else 6

def Tfun(x,y):
    """t_{k+1}/t_k as function of x=q^n,y=q^k"""
    if side=='L':
        z=a*a*q*q*x/(b*c*d*e)
        return (1-a*q*q*y*y)/(1-a*y*y)*(1-a*y)*(1-b*y)*(1-c*y)*(1-d*y)*(1-e*y)*(1-y/x)/((1-q*y)*(1-a*q*y/b)*(1-a*q*y/c)*(1-a*q*y/d)*(1-a*q*y/e)*(1-a*q*x*y))*z
    else:
        return (1-a*q*y/(b*c))*(1-d*y)*(1-e*y)*(1-y/x)/((1-q*y)*(1-a*q*y/b)*(1-a*q*y/c)*(1-d*e*y/(a*x)))*q
def shift1(x,y):
    """t_k(n+1)/t_k(n)"""
    if side=='L':
        return y*(1-1/(q*x))/(1-y/(q*x))*(1-a*q*x)/(1-a*q*x*y)
    else:
        # (q^{-n})_k -> (q^{-n-1})_k ; (d e q^{-n}/a)_k -> (d e q^{-n-1}/a)_k in denominator ; P(n) factor
        u=1/x; v=d*e/(a*x)
        r1=(1-u/q)/(1-u*y/q)
        r2=(1-v*y/q)/(1-v/q)   # (v)_k/(v/q)_k inverse: den (v/q)_k vs (v)_k => ratio (v)_k/(v/q)_k
        Pr=(1-a*q*q**0*x)*(1-a*q*x/(d*e))/((1-a*q*x/d)*(1-a*q*x/e))  # P(n+1)/P(n)
        return r1*r2*Pr
def S(i,x,y):
    r=F(1)
    for j in range(i): r*=shift1(x*q**j,y)
    return r
import os
SUB=[int(t) for t in os.environ.get('DSUB','').split(',') if t]
def Dfun(x,y):
    fs=[1-y/(q*x),1-y/(q*q*x),1-a*q*x*y,1-a*q*q*x*y,1-y/x,1-d*e*y/(a*x),1-d*e*y/(a*q*x),1-a*y*y]
    r=F(1)
    for i in SUB: r*=fs[i]
    return r
# unknowns: p_i,m (i=0..2,m<=DX) ; N_{m,j}
nun=3*(DX+1)
mons=[(m,j) for m in range(DX+3) for j in range(DY+1)]
def Dnum(x,y): return Dfun(x,y)
rows=[]
random.seed(1)
npts=len(mons)+3*(DX+1)+40
for _ in range(npts):
    x=F(random.randint(2,60),random.randint(2,60)); y=F(random.randint(2,60),random.randint(2,60))
    row=[]
    for i in range(3):
        for m in range(DX+1): row.append(-(x**m)*S(i,x,y))
    T=Tfun(x,y)
    for (m,j) in mons:
        row.append((x**m)*((q*y)**j)/Dnum(x,q*y)*T - (x**m)*(y**j)/Dnum(x,y))
    rows.append(row)
M=sp.Matrix(rows)
print(M.shape, flush=True)
from sympy.polys.matrices import DomainMatrix
from sympy import QQ
dm=DomainMatrix.from_Matrix(M).convert_to(QQ)
ns=dm.nullspace()
print('nullspace dim',ns.shape[0])
if ns.shape[0]:
    v=ns.to_Matrix().row(0)
    if os.environ.get('WNORM'):
        piv=v[3*(DX+1)-1]; v=v/piv
        print('VEC',[str(t) for t in v])
    else:
        print([v[i] for i in range(3*(DX+1))])
