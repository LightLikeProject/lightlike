import itertools, math
from sympy import Rational as R
from sympy.physics.wigner import wigner_6j
from functools import lru_cache
@lru_cache(maxsize=None)
def w6(a,b,c,d,e,f):  # doubled integer args -> float
    def tri(x,y,z): return z<=x+y and x<=y+z and y<=x+z and (x+y+z)%2==0
    if not (tri(a,b,c) and tri(a,e,f) and tri(d,b,f) and tri(d,e,c)): return 0.0
    return float(wigner_6j(*[R(t,2) for t in (a,b,c,d,e,f)]))
MAX=3  # doubled spins 0..3  (j up to 3/2)
checked=nonzero=0; worst=0.0
for a,b,c,d,e,f,p,q,r in itertools.product(range(MAX+1),repeat=9):
    rhs=w6(p,q,r,e,a,d)*w6(p,q,r,f,b,c)
    S2=a+b+c+d+e+f+p+q+r
    lhs=0.0
    for x in range(0,2*MAX+3):
        t=w6(a,b,x,c,d,p)*w6(c,d,x,e,f,q)*w6(e,f,x,b,a,r)
        if t==0.0: continue
        assert (S2+x)%2==0, (a,b,c,d,e,f,p,q,r,x)
        lhs+=(-1)**((S2+x)//2)*(x+1)*t
    checked+=1
    if abs(rhs)>1e-12 or abs(lhs)>1e-12: nonzero+=1
    worst=max(worst,abs(lhs-rhs))
print("cases",checked,"nontrivial",nonzero,"max |LHS-RHS|",worst)
