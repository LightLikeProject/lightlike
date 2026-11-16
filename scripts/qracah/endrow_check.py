# Numerical evidence (not proof): the endpoint row of the q-6j recurrence at third colour x=0.
# With j1=j2=B, j4=j5=E the row reads  a0 S(2) + b0 S(0) = 2cos((q+1)pi/r) S(0)  and b0 must not depend on q.
import math, sys
r=int(sys.argv[1])
def qn(n): return math.sin(n*math.pi/r)/math.sin(math.pi/r)
def qf(n):
    p=1.0
    for k in range(1,n+1): p*=qn(k)
    return p
def inv(n): return 0.0 if n<0 else (1/qf(n) if abs(qf(n))>1e-12 else 0.0)
def S(j1,j2,j4,j5,q,y):
    # y third colour (any integer), SR sum without the Delta factors
    if (j1+j2+y)%2: return 0.0
    al=[(j1+j2+y)//2,(j1+j5+q)//2,(j4+j2+q)//2,(j4+j5+y)//2]
    be=[(j1+j2+j4+j5)//2,(y+j2+j5+q)//2,(y+j1+q+j4)//2]
    if min(al)<0 or min(be)<0: return 0.0
    return sum((-1)**z*qf(z+1)*math.prod(inv(z-a) for a in al)*math.prod(inv(b-z) for b in be) for z in range(0,sum(al)+sum(be)+2))
worst=0; n=0
for B in range(r-1):
  for E in range(r-1):
    bs=[]
    for q in range(abs(B-E),min(B+E,2*(r-2)-B-E)+1,2):
      s0=S(B,B,E,E,q,0); s2=S(B,B,E,E,q,2)
      if abs(s0)<1e-12: continue
      b0=2*math.cos((q+1)*math.pi/r)-(-4*math.sin(math.pi/r)**2/qn(2))*s2/s0
      bs.append(b0)
    if len(bs)>1:
      n+=1; worst=max(worst,max(bs)-min(bs))
    if bs and B<4 and E<4: print(B,E,[round(b,6) for b in bs])
print("r",r,"cases",n,"max spread of b0 over q",worst)
# Top row x=r-2: j2=r-2-j1, j5=r-2-j4; row  b1 S(x) + c1 S(x-2) = 2cos((q+1)pi/r) S(x),  c1 = (u-1/u)^2/[2].
print("top row")
worst=0; n=0
for B in range(r-1):
  for E in range(r-1):
    bs=[]; x=r-2
    for q in range(r-1):
      if (B+r-2-E+q)%2: continue
      s0=S(B,r-2-B,E,r-2-E,q,x); s2=S(B,r-2-B,E,r-2-E,q,x-2)
      if abs(s0)<1e-12: continue
      bs.append(2*math.cos((q+1)*math.pi/r)-(-4*math.sin(math.pi/r)**2/qn(2))*s2/s0)
    if len(bs)>1: n+=1; worst=max(worst,max(bs)-min(bs))
    if bs and B<3 and E<3: print(B,E,round(bs[0],6), "guess", round(2*math.cos((B+1)*math.pi/r)*2*math.cos((E+1)*math.pi/r)/(2*math.cos(math.pi/r)),6))
print("r",r,"top cases",n,"max spread",worst)
