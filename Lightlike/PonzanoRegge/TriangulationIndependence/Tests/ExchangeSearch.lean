import Std.Data.HashMap
/-!
# Brute-force experiment: exchange-connectedness of maximal trees on small 3-spheres

Executable (`#eval`) search, independent of the Lean proofs: for a list of tetrahedra, enumerate all
spanning trees of the 1-skeleton and union those related by a triangle exchange (the same move as
`Lightlike.PR.TreeExchange`). Reports the number of exchange classes. Used to test whether
tree-connectedness survives the 2-3 move (programme item L13).
-/

namespace Lightlike.PR.Experiment

/-- A tetrahedron, as the list of its four vertex labels. -/
abbrev Tet := List Nat

/-- Unordered pair of vertex labels packed into one natural number (labels below 64). -/
def key (a b : Nat) : Nat := if a < b then a * 64 + b else b * 64 + a

/-- The six unordered vertex pairs (edges) of a tetrahedron. -/
def pairsOf (t : Tet) : List (Nat × Nat) :=
  (t.flatMap fun a => t.filterMap fun b => if a < b then some (a, b) else none)

/-- The four vertex triples (triangles) of a tetrahedron. -/
def triplesOf (t : Tet) : List (Nat × Nat × Nat) :=
  t.flatMap fun a => t.flatMap fun b => t.filterMap fun c =>
    if a < b ∧ b < c then some (a, b, c) else none

/-- Remove duplicate vertex pairs, keeping first occurrences. -/
def dedup (l : List (Nat × Nat)) : List (Nat × Nat) :=
  l.foldl (fun acc p => if acc.contains p then acc else acc ++ [p]) []

/-- Remove duplicate vertex triples, keeping first occurrences. -/
def dedup3 (l : List (Nat × Nat × Nat)) : List (Nat × Nat × Nat) :=
  l.foldl (fun acc p => if acc.contains p then acc else acc ++ [p]) []

/-- The deduplicated edges of a list of tetrahedra, as an array. -/
def edgesOf (ts : List Tet) : Array (Nat × Nat) := (dedup (ts.flatMap pairsOf)).toArray
/-- The deduplicated triangles of a list of tetrahedra. -/
def trisOf (ts : List Tet) : List (Nat × Nat × Nat) := dedup3 (ts.flatMap triplesOf)
/-- The deduplicated vertices of a list of tetrahedra. -/
def vertsOf (ts : List Tet) : List Nat := (ts.flatten).eraseDups

/-- Depth-first enumeration of edge subsets (spanning-tree candidates) with union-find components; tallies the trees found. -/
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

/-- Union-find root lookup with path following. -/
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

/-- A tetrahedron with its vertex labels sorted. -/
def sortTet (t : Tet) : Tet := t.mergeSort

/-- The 1-4 Pachner move: subdivide tetrahedron `t` by adding the new vertex `e`. -/
def move14 (ts : List Tet) (t : Tet) (e : Nat) : List Tet :=
  (ts.filter (fun s => sortTet s != sortTet t)) ++ (t.map fun x => e :: t.filter (· != x))

/-- The tetrahedra of `ts` that contain all the vertices of the triangle `tri`. -/
def tetsWith (ts : List Tet) (tri : List Nat) : List Tet :=
  ts.filter fun s => tri.all (s.contains ·)

/-- The 2-3 Pachner move on the two tetrahedra sharing the triangle `a b c`, with apexes `d` and `e`. -/
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

/-- The boundary of the 4-simplex on vertices 0..4, a triangulated 3-sphere. -/
def S3 : List Tet := [[1,2,3,4],[0,2,3,4],[0,1,3,4],[0,1,2,4],[0,1,2,3]]

/-- Linear congruential pseudo-random step (deterministic, for reproducible searches). -/
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

/-- A recorded Pachner move: a 1-4 move or a 2-3 move. -/
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

/-- Move traces of pseudo-random walks for the given seeds. -/
def traces (maxV : Nat) (seeds : List Nat) : List (List Mv) :=
  seeds.filterMap fun s => walkTrace S3 5 maxV s 14 []

/-- Decode a bitmask into the edge subset it selects. -/
def decode (ts : List Tet) (mask : Nat) : List (Nat × Nat) :=
  let es := edgesOf ts
  (List.range es.size).filterMap fun i => if (mask >>> i) % 2 == 1 then some es[i]! else none

/-- The candidate counterexample triangulation reached by a fixed sequence of 1-4 and 2-3 moves from `S3`. -/
def counter1 : List Tet := move23 (move23 (move14 (move23 (move14 S3 [0,1,3,4] 5) 0 3 4 2 5)
  [0,1,2,4] 6) 0 1 2 3 6) 0 1 3 5 6

-- 7^5 = 16807 trees; connected would be one class; here 8 classes (one of 16800 trees, seven
-- isolated Hamiltonian paths).
#eval (classInfo counter1).map (·.1)
#eval ((classInfo counter1).filter (·.1 == 1)).map fun p => decode counter1 p.2.1

/-! ## Numerical gauge-fixed Ponzano–Regge amplitude (Float, Racah 6j in doubled spins) -/

/-- Factorial as a `Float`. -/
def fact (n : Nat) : Float := (List.range n).foldl (fun acc i => acc * (i + 1).toFloat) 1.0

/-- Whether spins `a b c` satisfy the triangle inequality and parity condition. -/
def triOk (a b c : Nat) : Bool :=
  (a + b + c) % 2 == 0 && a ≤ b + c && b ≤ a + c && c ≤ a + b

/-- The triangle coefficient of the 6j-symbol, as a `Float`. -/
def delta (a b c : Nat) : Float :=
  Float.sqrt (fact ((a + b - c) / 2) * fact ((a + c - b) / 2) * fact ((b + c - a) / 2) /
    fact ((a + b + c) / 2 + 1))

/-- Wigner 6j `{j1 j2 j3; j4 j5 j6}` in doubled spins (Racah formula). -/
def sixj (j1 j2 j3 j4 j5 j6 : Nat) : Float :=
  if triOk j1 j2 j3 && triOk j1 j5 j6 && triOk j4 j2 j6 && triOk j4 j5 j3 then
    let a1 := (j1 + j2 + j3) / 2
    let a2 := (j1 + j5 + j6) / 2
    let a3 := (j4 + j2 + j6) / 2
    let a4 := (j4 + j5 + j3) / 2
    let b1 := (j1 + j2 + j4 + j5) / 2
    let b2 := (j2 + j3 + j5 + j6) / 2
    let b3 := (j3 + j1 + j6 + j4) / 2
    let lo := max (max a1 a2) (max a3 a4)
    let hi := min (min b1 b2) b3
    let pre := delta j1 j2 j3 * delta j1 j5 j6 * delta j4 j2 j6 * delta j4 j5 j3
    let s := (List.range (hi + 1 - lo)).foldl (fun acc k =>
      let t := lo + k
      let sg : Float := if t % 2 == 0 then 1.0 else -1.0
      acc + sg * fact (t + 1) / (fact (t - a1) * fact (t - a2) * fact (t - a3) * fact (t - a4) *
        fact (b1 - t) * fact (b2 - t) * fact (b3 - t))) 0.0
    pre * s
  else 0.0

/-- Gauge-fixed amplitude: spin `0` on `gauge` edges, spins `0..cut` on the others. -/
def ampGF (ts : List Tet) (gauge : List (Nat × Nat)) (cut : Nat) : Float := Id.run do
  let es := edgesOf ts
  let eidx : Std.HashMap Nat Nat := Id.run do
    let mut h : Std.HashMap Nat Nat := {}
    for i in [0:es.size] do
      h := h.insert (key es[i]!.1 es[i]!.2) i
    return h
  let ei (a b : Nat) : Nat := eidx[key a b]!
  let isG : Array Bool := (Array.range es.size).map fun i =>
    gauge.any fun (a, b) => key a b == key es[i]!.1 es[i]!.2
  let free := ((Array.range es.size).filter fun i => !isG[i]!)
  let tr := (trisOf ts).map fun (a, b, c) => (ei a b, ei b c, ei c a)
  let tets := ts.map fun t => match t.mergeSort with
    | [a, b, c, d] => (ei a b, ei b c, ei c a, ei c d, ei a d, ei b d)
    | _ => (0, 0, 0, 0, 0, 0)
  -- position of each edge in the DFS order (gauge edges: decided from the start)
  let pos : Array Nat := (Array.range es.size).map fun i =>
    if isG[i]! then 0 else (free.findIdx? (· == i)).getD 0 + 1
  let mut total : Float := 0.0
  -- iterative DFS with explicit stack of (position, colouring)
  let mut stack : List (Nat × Array Nat) := [(0, Array.replicate es.size 0)]
  let mut fuel := 200000000
  while !stack.isEmpty && fuel > 0 do
    fuel := fuel - 1
    match stack with
    | [] => pure ()
    | (p, col) :: rest =>
      stack := rest
      if p == free.size then
        let mut w : Float := 1.0
        for i in [0:es.size] do
          let J := col[i]!
          w := w * (J + 1).toFloat * (if J % 2 == 0 then 1.0 else -1.0)
        for (x, y, z) in tr do
          let s := (col[x]! + col[y]! + col[z]!) / 2
          w := w * (if s % 2 == 0 then 1.0 else -1.0)
        for (x, y, z, u, v, q) in tets do
          w := w * sixj col[x]! col[y]! col[z]! col[u]! col[v]! col[q]!
        total := total + w
      else
        let e := free[p]!
        for J in [0:cut + 1] do
          let col' := col.set! e J
          -- check triangles containing e whose edges are all decided
          let ok := tr.all fun (x, y, z) =>
            if x == e || y == e || z == e then
              (pos[x]! ≤ p + 1 || isG[x]!) && (pos[y]! ≤ p + 1 || isG[y]!) &&
                (pos[z]! ≤ p + 1 || isG[z]!) → triOk col'[x]! col'[y]! col'[z]!
            else true
          if ok then stack := (p + 1, col') :: stack
  return total

/-- A path spanning tree of the 1-skeleton of `S3` (five vertices). -/
def pathK5 : List (Nat × Nat) := [(0, 1), (1, 2), (2, 3), (3, 4)]
/-- A star spanning tree of the 1-skeleton of `S3` (five vertices). -/
def starK5 : List (Nat × Nat) := [(0, 1), (0, 2), (0, 3), (0, 4)]
#eval (ampGF S3 pathK5 1, ampGF S3 starK5 1)
#eval (ampGF S3 pathK5 2, ampGF S3 starK5 2)

/-- A path-like spanning tree on the seven vertices of the counterexample. -/
def pathS7 : List (Nat × Nat) := [(1, 2), (3, 4), (0, 1), (0, 3), (4, 6), (5, 6)]
/-- The star spanning tree centred at vertex 0 on seven vertices. -/
def starS7 : List (Nat × Nat) := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6)]
/-- The star spanning tree centred at vertex 1 on seven vertices. -/
def star1S7 : List (Nat × Nat) := [(1, 0), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6)]
/-- The linear path spanning tree 0-1-...-6 on seven vertices. -/
def path2S7 : List (Nat × Nat) := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6)]
#eval (ampGF counter1 pathS7 1, ampGF counter1 starS7 1, ampGF counter1 star1S7 1,
  ampGF counter1 path2S7 1)

end Lightlike.PR.Experiment
