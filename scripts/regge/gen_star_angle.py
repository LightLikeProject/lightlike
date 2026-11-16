"""Generate the seven edge-class fans of Lightlike/Regge/Conv3/StarAngle.lean.

The Kuhn triangulation of the cube has 36 incidences (tetrahedron sigma, hinge h). For each of the
seven edge directions w the incidences whose hinge has direction w form a fan of 6 or 4 tetrahedra
around the axis w. This script lists the incidences of each class from the tables of KuhnCore.lean
(`kv`, `perms`, `hP`, `hQ`, `hR`, `hS`), orients and chains them into a cycle of lattice vectors
v_0, ..., v_n (consecutive vectors have positive triple product with w, and v_n = v_0 or
v_3 = -v_0, v_6 = v_0 modulo w), and prints the Lean block (from `fan_mem` to `cls6_sum`) that is
pasted between the markers of StarAngle.lean.  Usage: python3 scripts/regge/gen_star_angle.py FILE (the block pasted into Lightlike/Regge/Conv3/StarAngle.lean)
"""
import sys

kv = [(0, 0, 0), (1, 0, 0), (1, 1, 0), (1, 1, 1)]
perms = [(0, 1, 2), (0, 2, 1), (1, 0, 2), (1, 2, 0), (2, 0, 1), (2, 1, 0)]
hP = [0, 0, 0, 1, 1, 2]; hQ = [1, 2, 3, 2, 3, 3]; hR = [2, 1, 1, 0, 0, 0]; hS = [3, 3, 2, 3, 2, 1]
dirs = [(1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 0), (1, 0, 1), (0, 1, 1), (1, 1, 1)]


def kp(s, k): return tuple(kv[k][perms[s][i]] for i in range(3))
def sub(a, b): return tuple(x - y for x, y in zip(a, b))
def trip(w, u, v):
    return w[0]*(u[1]*v[2]-u[2]*v[1])-w[1]*(u[0]*v[2]-u[2]*v[0])+w[2]*(u[0]*v[1]-u[1]*v[0])
def vec(t): return '![%s]' % ', '.join('(%d:ℝ)' % x for x in t)


data = []
for k, w in enumerate(dirs):
    mem = []
    for s in range(6):
        for h in range(6):
            if all(kv[hQ[h]][perms[s][i]] - kv[hP[h]][perms[s][i]] == w[i] for i in range(3)):
                P = kp(s, hP[h]); x = sub(kp(s, hR[h]), P); y = sub(kp(s, hS[h]), P)
                sw = False
                if trip(w, x, y) < 0:
                    x, y = y, x; sw = True
                mem.append([s, h, x, y, sw])
    chain = [mem[0]]; rest = mem[1:]
    while rest:
        for r in rest:
            if r[2] == chain[-1][3]:
                chain.append(r); rest.remove(r); break
        else:
            raise Exception('no chain')
    V = [c[2] for c in chain] + [chain[-1][3]]
    data.append((k, w, len(chain), chain, V))

out=[]
tail={}
out.append('''
/-- Rewriting one member of a class sum into a fan term. -/
theorem fan_mem {G : Matrix (Fin 3) (Fin 3) ℝ} {w X Y : Fin 3 → ℝ} {σ h : Fin 6}
    (hw : wv σ h = w) (hx : xv σ h = X) (hy : yv σ h = Y) :
    fanAng G (wv σ h) (xv σ h) (yv σ h) = fanAng G w X Y := by
  rw [hw, hx, hy]

/-- The fan angle is symmetric in the two opposite vertices. -/
theorem fanAng_swap {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : Gᵀ = G) (w X Y : Fin 3 → ℝ) :
    fanAng G w X Y = fanAng G w Y X := by
  unfold fanAng
  rw [bf_comm hG w X Y, mul_comm (bf G w X X)]

/-- Rewriting one member of a class sum into a fan term, with the two vertices swapped. -/
theorem fan_mem_swap {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : Gᵀ = G) {w X Y : Fin 3 → ℝ} {σ h : Fin 6}
    (hw : wv σ h = w) (hx : xv σ h = Y) (hy : yv σ h = X) :
    fanAng G (wv σ h) (xv σ h) (yv σ h) = fanAng G w X Y := by
  rw [hw, hx, hy, fanAng_swap hG w Y X]
''')
for k,w,n,chain,V in data:
    wl=vec(w)
    Vl='[%s]'%', '.join(vec(v) for v in V)
    # cls expansion lemma
    terms=' + '.join('f %d %d'%(c[0],c[1]) for c in chain)
    out.append(f'''
/-- The members of the edge class {k}: its `clsSum` is a sum of {n} terms. -/
theorem cls{k}_expand (f : Fin 6 → Fin 6 → ℝ) :
    clsSum (dirs {k}) f = {terms} := by
  classical
  simp only [clsSum, Fin.sum_univ_six, InClass, dirs, kv, perms, hP, hQ, Fin.forall_fin_succ]
  simp
  try ring
''')
    vt='(fun i : ℕ => (%s : List (Fin 3 → ℝ)).getD i 0)'%Vl
    if n==6:
        extra='''(by refine ⟨%s, ?_⟩; ext i; fin_cases i <;> simp <;> norm_num) (by refine ⟨%s, ?_⟩; ext i; fin_cases i <;> simp <;> norm_num)'''
        # find c3,c6
        import itertools
        def solve(a,b):  # b = -a + c w
            for c in range(-2,3):
                if all(b[i]==-a[i]+c*w[i] for i in range(3)): return c
            raise Exception('no c')
        c3=solve(V[0],V[3]); c6=solve(V[3],V[6])
        fan=f'hex_fan hG hw {vt} (by intro i hi; interval_cases i <;> simp [trip] <;> norm_num) ⟨({c3}:ℝ), by ext i; fin_cases i <;> simp <;> norm_num⟩ ⟨({c6}:ℝ), by ext i; fin_cases i <;> simp <;> norm_num⟩'
    else:
        def solve0(a,b):
            for c in range(-2,3):
                if all(b[i]==a[i]+c*w[i] for i in range(3)): return c
            raise Exception('no c4')
        c4=solve0(V[0],V[4])
        fan=f'quad_fan hG hw {vt} (by intro i hi; interval_cases i <;> simp [trip] <;> norm_num) ⟨({c4}:ℝ), by ext i; fin_cases i <;> simp <;> norm_num⟩'
    mems=[]
    for j,c in enumerate(chain):
        s,h,x,y,sw=c
        a=vec(V[j]); b=vec(V[j+1])
        tac='by ext i; fin_cases i <;> simp [{}, kpos, kv, perms, hP, hQ, hR, hS] <;> norm_num'
        wt=tac.format('wv'); xt=tac.format('xv'); yt=tac.format('yv')
        if not sw:
            mems.append(f'  have m{j} : fanAng (g m) (wv {s} {h}) (xv {s} {h}) (yv {s} {h}) = fanAng (g m) {wl} {a} {b} :=\n    fan_mem ({wt}) ({xt}) ({yt})')
        else:
            mems.append(f'  have m{j} : fanAng (g m) (wv {s} {h}) (xv {s} {h}) (yv {s} {h}) = fanAng (g m) {wl} {a} {b} :=\n    fan_mem_swap hs ({wt}) ({xt}) ({yt})')
    rws=', '.join('m%d'%j for j in range(n))
    sumsimp=' '.join([])
    out.append(f'''
/-- The dihedral angles of the Gram star in edge class {k} add up to `2π`. -/
theorem cls{k}_sum {{g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ}} {{m : Fin 3 → ℝ}}
    (hG : (g m).PosDef) :
    clsSum (dirs {k}) (fun σ h => Dsq (incQ g m σ h)) = 2 * π := by
  have hs := posDef_symm hG
  have hw : ({wl} : Fin 3 → ℝ) ≠ 0 := by
    intro e; have := congrFun e 0; have := congrFun e 1; have := congrFun e 2; simp_all
  have H := {fan}
  rw [cls{k}_expand]
  simp only [Dsq_incQ hG]
{chr(10).join(mems)}
  rw [{rws}]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at H
  simpa using H
''')
open(sys.argv[1],'w').write('\n'.join(out))
