"""Generate Lightlike/TuraevViro/Reflect/RacahCore.lean: the product trees X0, E1, E3, E5 of the cleared
q-Racah recurrence identity, their equality (kernel) with the Z-power data of RacahCert<k>, and the
resulting identity `Dc*X0 + N1*E1 + N3*E3 + N5*E5 = 0` in any field. Run from scripts/qracah."""
import pickle
Dc,Ns,res=pickle.load(open('parts.pkl','rb'))
def V(**k):
    names=['u','p1','p2','p3','p4','q2','q3','Z']; return tuple(k.get(n,0) for n in names)
def add(*vs): return tuple(sum(x) for x in zip(*vs))
def neg(v): return tuple(-x for x in v)
A1=V(p1=1);A2=V(p2=1);A3=V(p3=1);A4=V(p4=1);B2=V(q2=1);B3=V(q3=1)
def lin(*t):
    r=V()
    for c,v in t: r=add(r,tuple(c*x for x in v))
    return r
def sub(e,f): return lin((1,e),(-1,f))
Bs=lin((1,A1),(1,A2),(-1,B2));As=lin((1,A1),(1,A3),(-1,B3));Es=lin((1,A3),(1,A4),(-1,B2));Fs=lin((1,A2),(1,A4),(-1,B3))
qs=lin((-1,A1),(-1,A4),(1,B2),(1,B3));xs=lin((-1,A2),(-1,A3),(1,B2),(1,B3));b1=lin((1,A1),(1,A2),(1,A3),(1,A4),(-1,B2),(-1,B3))
Zv=V(Z=1);U=lambda n:V(u=n)
def m(v): return "⟨"+", ".join(map(str,v))+"⟩"
def Br(v): return f"(br {m(v)})"
def Cn_(v): return f"(cn {m(v)})"
def QQ(e,sh=0): return Br(add(e,U(sh)))
def zm(p,sh): return Br(add(Zv,U(sh),neg(p)))
def bm(q,sh): return Br(add(q,U(sh),neg(Zv)))
def Cnn(e,sh=0): return Cn_(add(e,U(sh+1)))
def M(*fs):
    s=fs[0]
    for f in fs[1:]: s=f"(mul {s} {f})"
    return s
def S(a,b): return f"(add {a} {b})"
def N(a): return f"(neg {a})"
def mono(v): return f"[({m(v)}, 1)]"
two="[(⟨0,0,0,0,0,0,0,0⟩, 2)]"
Q0,Q1,Q2=QQ(xs,0),QQ(xs,1),QQ(xs,2)
Na=M(QQ(sub(A1,As),1),QQ(sub(A1,Bs),1),QQ(sub(A4,Es),1),QQ(sub(A4,Fs),1))
Nc=M(QQ(A1,1),QQ(A4,1),QQ(sub(A1,xs),1),QQ(sub(A4,xs),1))
om="(add [(⟨1,0,0,0,0,0,0,0⟩,1)] [(⟨-1,0,0,0,0,0,0,0⟩,1)])"
bn=S(M(S(M(Cnn(Bs),Cnn(Es)),M(Cnn(As),Cnn(Fs))),Cnn(xs)), N(M(om,S(M(Cnn(Bs),Cnn(Fs)),M(Cnn(As),Cnn(Es))))))
M0=M(zm(A1,1),zm(A2,1),zm(A3,1),zm(A4,1),bm(B2,1),bm(B3,1))
Mp=M(zm(A1,0),zm(A1,1),zm(A2,1),zm(A3,1),zm(A4,0),zm(A4,1))
Mm=M(zm(A2,1),zm(A3,1),bm(B2,0),bm(B2,1),bm(B3,0),bm(B3,1))
W0=M(zm(A2,0),zm(A3,0),zm(A1,1),zm(A2,1),zm(A3,1),zm(A4,1))
W1=N(M(Br(add(Zv,U(2))),Br(add(b1,neg(Zv))),bm(B2,1),bm(B3,1),zm(A2,1),zm(A3,1)))
Cq=Cn_(add(qs,U(1)))
Q012=M(Q0,Q1,Q2)
_names=[("fQ0",Q0),("fQ1",Q1),("fQ2",Q2),("fNa",Na),("fNc",Nc),("fbn",bn),("fM0",M0),("fMp",Mp),("fMm",Mm),("fW0",W0),("fW1",W1),("fCq",Cq),("fQ012","(mul (mul fQ0 fQ1) fQ2)"),("ftwo",two)]
FULL=dict(_names)
def expand(t):
    import re
    while re.search(r"f[A-Za-z0-9]+",t) and any(k in t for k in FULL):
        t=re.sub(r"f[A-Za-z0-9]+",lambda mm:FULL.get(mm.group(0),mm.group(0)),t)
    return t
FDEFS="".join(f"def {k} : Poly := {v}\n" for k,v in _names)
Q0,Q1,Q2,Na,Nc,bn,M0,Mp,Mm,W0,W1,Cq,Q012,two=[k for k,_ in _names]
X0=S(S(M(two,Q0,Na,Mp),M(two,Q1,bn,M0)),S(M(two,Q2,Nc,Mm),N(M(two,Q012,Cq,M0))))
def E(a,b):  # -2 Q012 (W1 * a - W0 * b), a,b monomials as exponent vectors
    return N(M(two,Q012,S(M(mono(a),W1),N(M(mono(b),W0)))))
E1=E(V(u=-2,Z=-2),V(Z=-2)); E3=E(V(),V()); E5=E(V(u=2,Z=2),V(Z=2))
# index j of the pair (A_j, B_j) in RacahCert<k>, and the canonical names
def jmap(k):
    v=res[k]; out={0:0}; j=1
    for i,cc in ((1,(1,0,0)),(3,(0,1,0)),(5,(0,0,1))):
        if cc in v: out[i]=j; j+=1
    return out
canon={0:"A0_0",1:"A0_1",3:"A0_2",5:"A2_3"}
ks=sorted(res)
mu="⟨-11, -2, -5, -5, -2, -5, -5, -6⟩"
def big(i):
    parts=[f"(scale ((muInv.mul (Zk {k})), -2) B{k}_{jmap(k)[i]})" for k in ks if i in jmap(k)]
    s=parts[0]
    for p in parts[1:]: s=f"(add {s} {p})"
    return s
import re as _re
def _parse(t):
    toks=_re.findall(r"\(|\)|\[|\]|⟨[^⟩]*⟩|[a-z]+|-?\d+|,",t)
    pos=[0]
    def vec(x): return tuple(int(v) for v in x[1:-1].split(","))
    def pm(a,b):
        r={}
        for m1,c1 in a.items():
            for m2,c2 in b.items():
                k=tuple(x+y for x,y in zip(m1,m2)); r[k]=r.get(k,0)+c1*c2
        return {k:v for k,v in r.items() if v}
    def pa(a,b):
        r=dict(a)
        for k,v in b.items(): r[k]=r.get(k,0)+v
        return {k:v for k,v in r.items() if v}
    def go():
        x=toks[pos[0]]
        if x=="[":
            pos[0]+=1; r={}
            while toks[pos[0]]!="]":
                if toks[pos[0]] in ",": pos[0]+=1; continue
                pos[0]+=1; m=vec(toks[pos[0]]); pos[0]+=2; c=int(toks[pos[0]]); pos[0]+=2
                r[m]=r.get(m,0)+c
            pos[0]+=1; return r
        pos[0]+=1; op=toks[pos[0]]; pos[0]+=1
        if op in("br","cn"):
            m=vec(toks[pos[0]]); pos[0]+=2
            return {m:1,tuple(-x for x in m):(-1 if op=="br" else 1)}
        a=go()
        if op=="neg": pos[0]+=1; return {k:-v for k,v in a.items()}
        b=go(); pos[0]+=1
        return pm(a,b) if op=="mul" else pa(a,b)
    return go()
def _lit(p):
    return "["+", ".join(f"(⟨{', '.join(map(str,m))}⟩, {c})" for m,c in sorted(p.items()))+"]"

imports="".join(f"import Lightlike.TuraevViro.Reflect.RacahCert{k}\n" for k in ks)
out=imports+f'''
/-!
# The cleared q-Racah recurrence identity: product trees and the field identity

`X0`, `E1`, `E3`, `E5` are the Laurent polynomials (in `u, p1..p4, q2, q3, Z`) multiplying `1`, `c1`,
`c3`, `c5` in `2 Q0 Q1 Q2 (lhs - rhs)` of the recurrence
`2a M+ + 2b M0 + 2c M- - C(q) M0 = MG1 - MG0`, with `rho(Z) = c1 Z^-2 + c3 + c5 Z^2` and
`ci = Ni / Dc`. Each equals `-2 mu^-1 sum_k Z^k n_k` for the data of `RacahCert<k>` (`mu` the monomial
`muInv` inverted), checked by the kernel. `core_identity` is `Dc X0 + N1 E1 + N3 E3 + N5 E5 = 0`.
Generated by `scripts/qracah/gen_core.py`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Lightlike.TV.Refl

/-- `M - M⁻¹` for a monomial. -/
def br (m : Mono) : Poly := add [(m, 1)] [(⟨-m.e0, -m.e1, -m.e2, -m.e3, -m.e4, -m.e5, -m.e6, -m.e7⟩, -1)]
/-- `M + M⁻¹` for a monomial. -/
def cn (m : Mono) : Poly := add [(m, 1)] [(⟨-m.e0, -m.e1, -m.e2, -m.e3, -m.e4, -m.e5, -m.e6, -m.e7⟩, 1)]

/-- The monomial `Z^k`. -/
def Zk (k : ℤ) : Mono := ⟨0, 0, 0, 0, 0, 0, 0, k⟩
/-- The inverse of `-1/2 * Z^6 p1^2 p2^5 p3^5 p4^2 q2^5 q3^5 u^11` (without the coefficient). -/
def muInv : Mono := {mu}

def Dc : Poly := A0_0
def N1 : Poly := A0_1
def N3 : Poly := A0_2
def N5 : Poly := A2_3

{FDEFS}
def X0 : Poly := {X0}
def E1 : Poly := {E1}
def E3 : Poly := {E3}
def E5 : Poly := {E5}

def bigX0 : Poly := {big(0)}
def bigE1 : Poly := {big(1)}
def bigE3 : Poly := {big(3)}
def bigE5 : Poly := {big(5)}

theorem tree_X0 : X0 = bigX0 := by decide +kernel
theorem tree_E1 : E1 = bigE1 := by decide +kernel
theorem tree_E3 : E3 = bigE3 := by decide +kernel
theorem tree_E5 : E5 = bigE5 := by decide +kernel
'''
for k in ks:
    for i,j in jmap(k).items():
        c=canon[i]
        if f"A{k}_{j}"!=c: out+=f"theorem eqA{k}_{j} : A{k}_{j} = {c} := by decide +kernel\n"
out+='''
theorem eval_Zk {K : Type*} [Field K] (E : Env K) (k : ℤ) : Mono.eval E (Zk k) = E.v7 ^ k := by
  simp [Zk, Mono.eval]

/-- **The cleared identity**: `Dc X0 + N1 E1 + N3 E3 + N5 E5 = 0` for every evaluation of the variables
in a field. -/
theorem core_identity {K : Type*} [Field K] {E : Env K} (hE : E.NZ) :
    Poly.eval E Dc * Poly.eval E X0 + Poly.eval E N1 * Poly.eval E E1 + Poly.eval E N3 * Poly.eval E E3
      + Poly.eval E N5 * Poly.eval E E5 = 0 := by
'''
for k in ks:
    out+=f"  have h{k} := coeff{k} hE\n"
    rws=[f"eqA{k}_{j}" for i,j in jmap(k).items() if f"A{k}_{j}"!=canon[i]]
    if rws: out+=f"  rw [{', '.join(rws)}] at h{k}\n"
out+="  rw [tree_X0, tree_E1, tree_E3, tree_E5]\n"
out+="  simp only [Dc, N1, N3, N5, bigX0, bigE1, bigE3, bigE5, eval_add, eval_scale hE, Mono.eval_mul hE]\n"
out+="  simp only [eval_Zk]\n"
out+="  linear_combination ("+") + (".join(f"(-2 * Mono.eval E muInv * E.v7 ^ ({k}:ℤ)) * h{k}" for k in ks)+")\n"
out+="\nend Lightlike.TV.Refl\n"

D="../../Lightlike/TuraevViro/Reflect/"
lines=out.split("\n")
ci=[i for i,l in enumerate(lines) if l.startswith("import")]
imps=[lines[i] for i in ci]
pre="\n".join(l for i,l in enumerate(lines) if i not in ci)
i0=pre.index("/-!"); i1=pre.index("def X0 :")
head=pre[i0:i1]
rest=pre[i1:]
ns="namespace Lightlike.TV.Refl"
import docs  # module docstrings of the generated files
opts="set_option maxRecDepth 100000\n"  # the heartbeat limits are per declaration (caps.json, chunk.py)
def hdr(t): return t
# base: everything up to X0 def
base_imps="\n".join(imps)+"\n\n"
open(D+"RacahBase.lean","w").write(base_imps+head+"\nend Lightlike.TV.Refl\n")
rl=rest.split("\n")
def grab(names):
    return "\n".join(l for l in rl if any(l.startswith(f"def {n} ") or l.startswith(f"theorem tree_{n} ") for n in names))
for n in ["X0","E1","E3","E5"]:
    body=grab([n,"big"+n])
    if n=="X0":
        Ts=[M(two,Q0,Na,Mp),M(two,Q1,bn,M0),M(two,Q2,Nc,Mm),M(two,Q012,Cq,M0)]
        pre_="".join(f"def T{i+1} : Poly := {t}\ndef Y{i+1} : Poly := {_lit(_parse(expand(t)))}\ntheorem tY{i+1} : T{i+1} = Y{i+1} := by decide +kernel\n" for i,t in enumerate(Ts))
        body=pre_+"def X0 : Poly := (add (add T1 T2) (add T3 (neg T4)))\n"+grab(["bigX0"])+"\ntheorem tree_X0 : X0 = bigX0 := by\n  unfold X0; rw [tY1, tY2, tY3, tY4]; decide +kernel"
    # keep def order
    open(D+f"RacahTree{n}.lean","w").write(base_imps+"import Lightlike.TuraevViro.Reflect.RacahBase\n\n"+docs.DOC[f"Tree{n}"]+"\n\n"+opts+"\n"+ns+"\n\n"+body+"\n\nend Lightlike.TV.Refl\n")
core="\n".join(l for l in rl if not (l.startswith("def X0") or l.startswith("def E1") or l.startswith("def E3") or l.startswith("def E5") or l.startswith("def big") or l.startswith("theorem tree_")))
tim="".join(f"import Lightlike.TuraevViro.Reflect.RacahTree{n}\n" for n in ["X0","E1","E3","E5"])
open(D+"RacahCore.lean","w").write(base_imps+"import Lightlike.TuraevViro.Reflect.RacahBase\n"+tim+"\n"+docs.DOC["Core"]+"\n\n"+opts+"\n"+ns+"\n\n"+core)

import json as _json
_json.dump({k:expand(v) for k,v in _names}, open("facs.out","w"), ensure_ascii=False)
