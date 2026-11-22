import Std.Data.HashMap
/-!
# Brute-force experiment: exchange-connectedness of maximal trees on small 3-spheres

Executable (`#eval`) search, independent of the Lean proofs: for a list of tetrahedra, enumerate all
spanning trees of the 1-skeleton and union those related by a triangle exchange (the same move as
`Lightlike.PR.TreeExchange`). Reports the number of exchange classes. Used to test whether
tree-connectedness survives the 2-3 move (programme item L13).
-/

namespace Lightlike.PR.Experiment

abbrev Tet := List Nat

def key (a b : Nat) : Nat := if a < b then a * 64 + b else b * 64 + a

def pairsOf (t : Tet) : List (Nat × Nat) :=
  (t.flatMap fun a => t.filterMap fun b => if a < b then some (a, b) else none)

def triplesOf (t : Tet) : List (Nat × Nat × Nat) :=
  t.flatMap fun a => t.flatMap fun b => t.filterMap fun c =>
    if a < b ∧ b < c then some (a, b, c) else none

def dedup (l : List (Nat × Nat)) : List (Nat × Nat) :=
  l.foldl (fun acc p => if acc.contains p then acc else acc ++ [p]) []

def dedup3 (l : List (Nat × Nat × Nat)) : List (Nat × Nat × Nat) :=
  l.foldl (fun acc p => if acc.contains p then acc else acc ++ [p]) []

def edgesOf (ts : List Tet) : Array (Nat × Nat) := (dedup (ts.flatMap pairsOf)).toArray
def trisOf (ts : List Tet) : List (Nat × Nat × Nat) := dedup3 (ts.flatMap triplesOf)
def vertsOf (ts : List Tet) : List Nat := (ts.flatten).eraseDups

partial def enumGo (es : Array (Nat × Nat)) (n : Nat) (i : Nat) (comp : Array Nat) (k mask : Nat)
    (acc : Array Nat) : Array Nat :=
  if k == n - 1 then acc.push mask
  else if i ≥ es.size then acc
  else
    let (a, b) := es[i]!
    let acc := enumGo es n (i + 1) comp k mask acc
    if comp[a]! != comp[b]! then
      let ca := comp[a]!
      let cb := comp[b]!
      let comp' := comp.map (fun c => if c == cb then ca else c)
      enumGo es n (i + 1) comp' (k + 1) (mask ||| (1 <<< i)) acc
    else acc

partial def find (p : Array Nat) (x : Nat) : Nat :=
  if p[x]! == x then x else find p p[x]!

/-- Number of exchange classes of spanning trees (and the number of trees). -/
def classes (ts : List Tet) : Nat × Nat := Id.run do
  let es := edgesOf ts
  let vs := vertsOf ts
  let n := vs.length
  let m := (vs.foldl max 0) + 1
  let trees := enumGo es n 0 (Array.range m) 0 0 #[]
  let eidx : Std.HashMap Nat Nat := Id.run do
    let mut h : Std.HashMap Nat Nat := {}
    for i in [0:es.size] do
      h := h.insert (key es[i]!.1 es[i]!.2) i
    return h
  let mut tidx : Std.HashMap Nat Nat := {}
  for i in [0:trees.size] do
    tidx := tidx.insert trees[i]! i
  let mut par := Array.range trees.size
  let tr := trisOf ts
  for i in [0:trees.size] do
    let t := trees[i]!
    for (a, b, c) in tr do
      for (u, v, w) in [(a, b, c), (a, c, b), (b, a, c), (b, c, a), (c, a, b), (c, b, a)] do
        let iuv := eidx[key u v]!
        let ivw := eidx[key v w]!
        let iuw := eidx[key u w]!
        if (t >>> iuv) % 2 == 1 && (t >>> ivw) % 2 == 1 && (t >>> iuw) % 2 == 0 then
          let t' := (t ^^^ (1 <<< iuv)) ||| (1 <<< iuw)
          match tidx[t']? with
          | some j =>
            let ri := find par i
            let rj := find par j
            if ri != rj then par := par.set! ri rj
          | none => pure ()
  let mut cnt := 0
  for i in [0:trees.size] do
    if find par i == i then cnt := cnt + 1
  return (cnt, trees.size)

def sortTet (t : Tet) : Tet := t.mergeSort

def move14 (ts : List Tet) (t : Tet) (e : Nat) : List Tet :=
  (ts.filter (fun s => sortTet s != sortTet t)) ++ (t.map fun x => e :: t.filter (· != x))

def tetsWith (ts : List Tet) (tri : List Nat) : List Tet :=
  ts.filter fun s => tri.all (s.contains ·)

def move23 (ts : List Tet) (a b c d e : Nat) : List Tet :=
  (ts.filter fun s => !(s.contains a && s.contains b && s.contains c)) ++
    [[a, b, d, e], [b, c, d, e], [c, a, d, e]]

/-- All valid 2-3 moves `(a,b,c,d,e)`. -/
def moves23 (ts : List Tet) : List (Nat × Nat × Nat × Nat × Nat) := Id.run do
  let es := edgesOf ts
  let mut out := []
  for t in ts do
    for (a, b, c) in triplesOf t do
      let sh := tetsWith ts [a, b, c]
      if sh.length == 2 then
        let d := (sh[0]!.filter (fun x => x != a && x != b && x != c))[0]!
        let e := (sh[1]!.filter (fun x => x != a && x != b && x != c))[0]!
        if d != e && !(es.contains (if d < e then (d, e) else (e, d))) then
          out := (a, b, c, d, e) :: out
  return out

def S3 : List Tet := [[1,2,3,4],[0,2,3,4],[0,1,3,4],[0,1,2,4],[0,1,2,3]]

def lcg (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

/-- Random walk of forward moves starting at `S3`, up to `maxV` vertices; returns the first
complex with more than one exchange class, if any, together with the number of complexes checked. -/
partial def walk (ts : List Tet) (nv : Nat) (maxV : Nat) (seed : Nat) (fuel : Nat) (checked : Nat) :
    Option (List Tet) × Nat :=
  if fuel == 0 then (none, checked)
  else
    let s1 := lcg seed
    let m := moves23 ts
    let use23 := (s1 / 7) % 3 != 0 && !m.isEmpty && nv ≤ maxV
    if use23 || nv ≥ maxV then
      if m.isEmpty then (none, checked)
      else
        let (a, b, c, d, e) := m[(s1 / 11) % m.length]!
        let ts' := move23 ts a b c d e
        if (classes ts').1 != 1 then (some ts', checked + 1)
        else walk ts' nv maxV s1 (fuel - 1) (checked + 1)
    else
      let t := ts[(s1 / 13) % ts.length]!
      let ts' := move14 ts t nv
      if (classes ts').1 != 1 then (some ts', checked + 1)
      else walk ts' (nv + 1) maxV s1 (fuel - 1) (checked + 1)

/-- For each exchange class: (size, intersection mask, union mask). -/
def classInfo (ts : List Tet) : Array (Nat × Nat × Nat) := Id.run do
  let es := edgesOf ts
  let vs := vertsOf ts
  let n := vs.length
  let m := (vs.foldl max 0) + 1
  let trees := enumGo es n 0 (Array.range m) 0 0 #[]
  let eidx : Std.HashMap Nat Nat := Id.run do
    let mut h : Std.HashMap Nat Nat := {}
    for i in [0:es.size] do
      h := h.insert (key es[i]!.1 es[i]!.2) i
    return h
  let mut tidx : Std.HashMap Nat Nat := {}
  for i in [0:trees.size] do
    tidx := tidx.insert trees[i]! i
  let mut par := Array.range trees.size
  let tr := trisOf ts
  for i in [0:trees.size] do
    let t := trees[i]!
    for (a, b, c) in tr do
      for (u, v, w) in [(a, b, c), (a, c, b), (b, a, c), (b, c, a), (c, a, b), (c, b, a)] do
        let iuv := eidx[key u v]!
        let ivw := eidx[key v w]!
        let iuw := eidx[key u w]!
        if (t >>> iuv) % 2 == 1 && (t >>> ivw) % 2 == 1 && (t >>> iuw) % 2 == 0 then
          let t' := (t ^^^ (1 <<< iuv)) ||| (1 <<< iuw)
          match tidx[t']? with
          | some j =>
            let ri := find par i
            let rj := find par j
            if ri != rj then par := par.set! ri rj
          | none => pure ()
  let mut info : Std.HashMap Nat (Nat × Nat × Nat) := {}
  for i in [0:trees.size] do
    let r := find par i
    let t := trees[i]!
    match info[r]? with
    | some (s, a, o) => info := info.insert r (s + 1, a &&& t, o ||| t)
    | none => info := info.insert r (1, t, t)
  return info.toArray.map (·.2)

inductive Mv | m14 (t : Tet) (e : Nat) | m23 (a b c d e : Nat)
  deriving Repr

/-- Same walk, recording the moves; returns the moves up to the first failing complex. -/
partial def walkTrace (ts : List Tet) (nv : Nat) (maxV : Nat) (seed : Nat) (fuel : Nat)
    (tr : List Mv) : Option (List Mv) :=
  if fuel == 0 then none
  else
    let s1 := lcg seed
    let m := moves23 ts
    let use23 := (s1 / 7) % 3 != 0 && !m.isEmpty && nv ≤ maxV
    if use23 || nv ≥ maxV then
      if m.isEmpty then none
      else
        let (a, b, c, d, e) := m[(s1 / 11) % m.length]!
        let ts' := move23 ts a b c d e
        let tr' := tr ++ [Mv.m23 a b c d e]
        if (classes ts').1 != 1 then some tr'
        else walkTrace ts' nv maxV s1 (fuel - 1) tr'
    else
      let t := ts[(s1 / 13) % ts.length]!
      let ts' := move14 ts t nv
      let tr' := tr ++ [Mv.m14 t nv]
      if (classes ts').1 != 1 then some tr'
      else walkTrace ts' (nv + 1) maxV s1 (fuel - 1) tr'

def traces (maxV : Nat) (seeds : List Nat) : List (List Mv) :=
  seeds.filterMap fun s => walkTrace S3 5 maxV s 14 []

def decode (ts : List Tet) (mask : Nat) : List (Nat × Nat) :=
  let es := edgesOf ts
  (List.range es.size).filterMap fun i => if (mask >>> i) % 2 == 1 then some es[i]! else none

def counter1 : List Tet := move23 (move23 (move14 (move23 (move14 S3 [0,1,3,4] 5) 0 3 4 2 5)
  [0,1,2,4] 6) 0 1 2 3 6) 0 1 3 5 6

-- 7^5 = 16807 trees; connected would be one class; here 8 classes (one of 16800 trees, seven
-- isolated Hamiltonian paths).
#eval (classInfo counter1).map (·.1)
#eval ((classInfo counter1).filter (·.1 == 1)).map fun p => decode counter1 p.2.1

end Lightlike.PR.Experiment
