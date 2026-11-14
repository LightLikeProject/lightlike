import itertools, sys
def adm3(j1,j2,j3,m1,m2,m3):
    return (m1+m2+m3==0 and -j1<=m1<=j1 and -j2<=m2<=j2 and -j3<=m3<=j3 and (j1-m1)%2==0
            and (j2-m2)%2==0 and (j3-m3)%2==0 and j3<=j1+j2 and j1<=j2+j3 and j2<=j1+j3
            and (j1+j2+j3)%2==0)
def support(j):
    j1,j2,j3,j4,j5,j6=j
    S=[]
    for m in itertools.product(*[range(-x,x+1) for x in j]):
        if (adm3(j1,j2,j3,-m[0],-m[1],-m[2]) and adm3(j1,j5,j6,m[0],-m[4],m[5])
            and adm3(j4,j2,j6,m[3],m[1],-m[5]) and adm3(j4,j5,j3,-m[3],m[4],m[2])):
            S.append(m)
    return S
for arg in sys.argv[1:]:
    j=tuple(int(x) for x in arg.split(","))
    S=support(j)
    box=1
    for x in j: box*=2*x+1
    lean="{"+", ".join("!["+", ".join(str(v) for v in m)+"]" for m in S)+"}"
    print(j, "box", box, "support", len(S)); print(lean)
