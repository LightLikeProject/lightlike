/-!
# Scratch: numerical sign test on the boundary of the 5-simplex (not imported, not built by `lake build`)

Run with `lake env lean Lightlike/SpinFoam/EPRLStateSum/SignScratch.lean`. Admissible random
colourings (triangle spins, intrinsic tetrahedron labels `l` with `Tri t₀ t₂ l`, `Tri l t₁ t₃`) of
`∂Δ⁵`; for each 4-simplex the exponent of `(-1)^(J12+J14+J34) · ampSign J K` is summed (the
`ΣK` part of `recoupSign` cancels, each tetrahedron lies in two simplices).

Results (22 Nov, round 18): the full sign product is `+1` and `-1` equally often (so
`recoupSign · ampP` alone is not the Ooguri weight), but the *triangle part*
`J12+J14+J34+J02+J04+J24` summed over the six simplices is always even, also for triangle
parities that are an arbitrary mod-2 coboundary `δx` (1102 samples, no odd). The discrepancy is
therefore a product of tetrahedron-local signs (the `K`-parities and half-perimeters in `ampSign`).
-/

def verts (m : Nat) : List Nat := (List.range 6).filter fun v => m.testBit v

def popc (m : Nat) : Nat := (verts m).length

/-- sorted vertices of simplex s (bitmask) -/
def sv (s : Nat) : Array Nat := (verts s).toArray

def er (s v : Nat) : Nat := s - 2 ^ v

def triOk (x y z : Nat) : Bool := (x + y + z) % 2 == 0 && z ≤ x + y && x ≤ y + z && y ≤ x + z

/-- LCG -/
def nxt (g : Nat) : Nat := (g * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- exponent of the sign discrepancy of one simplex -/
def expo (col : Nat → Nat) (s : Nat) : Nat :=
  let v := sv s
  let J := fun p q => col (er (er s v[p]!) v[q]!)
  let K := fun a => col (er s v[a]!)
  (J 1 2 + J 1 4 + J 3 4) +
  (J 0 2 + J 0 4 + J 2 4 + K 0 + K 4 + K 2 + (J 1 3 + J 0 1 + K 1) / 2 +
    (K 2 + J 2 4 + J 1 2) / 2 + (J 2 3 + J 0 2 + K 2) / 2 + (K 3 + J 3 4 + J 1 3) / 2)

def tris : List Nat := (List.range 64).filter fun m => popc m == 3
def tets : List Nat := (List.range 64).filter fun m => popc m == 4
def simps : List Nat := (List.range 64).filter fun m => popc m == 5

/-- sample a colouring: triangles from base parity b with values b+2*r, tets by rejection -/
def sample (g0 : Nat) (b : Nat) : Option (Array Nat) × Nat := Id.run do
  let mut g := g0
  let mut col : Array Nat := Array.replicate 64 0
  for m in tris do
    g := nxt g
    col := col.set! m (b + 2 * ((g / 2 ^ 20) % 3))
  let mut ok := true
  for m in tets do
    let w := sv m
    let t := fun j => col[er m w[j]!]!
    -- choose l
    let mut cands : List Nat := []
    for l in List.range 20 do
      if triOk (t 0) (t 2) l && triOk l (t 1) (t 3) then cands := l :: cands
    if cands.isEmpty then ok := false
    else
      g := nxt g
      col := col.set! m (cands[(g / 2 ^ 20) % cands.length]!)
  if ok then return (some col, g) else return (none, g)

def sigma (col : Array Nat) : Nat := (simps.map fun s => expo (fun m => col[m]!) s).sum

/-- triangle part of the exponent -/
def expoTri (col : Nat → Nat) (s : Nat) : Nat :=
  let v := sv s
  let J := fun p q => col (er (er s v[p]!) v[q]!)
  (J 1 2 + J 1 4 + J 3 4) + (J 0 2 + J 0 4 + J 2 4)

def sigmaTri (col : Array Nat) : Nat := (simps.map fun s => expoTri (fun m => col[m]!) s).sum

def edges : List Nat := (List.range 64).filter fun m => popc m == 2

/-- sample with triangle parities p = δx, x random on edges -/
def sample2 (g0 : Nat) : Option (Array Nat) × Nat := Id.run do
  let mut g := g0
  let mut x : Array Nat := Array.replicate 64 0
  for e in edges do
    g := nxt g
    x := x.set! e ((g / 2 ^ 30) % 2)
  let mut col : Array Nat := Array.replicate 64 0
  for m in tris do
    g := nxt g
    let p := ((verts m).map fun v => x[er m v]!).foldl (· + ·) 0
    col := col.set! m (p % 2 + 2 * ((g / 2 ^ 20) % 3))
  let mut ok := true
  for m in tets do
    let w := sv m
    let t := fun j => col[er m w[j]!]!
    let mut cands : List Nat := []
    for l in List.range 20 do
      if triOk (t 0) (t 2) l && triOk l (t 1) (t 3) then cands := l :: cands
    if cands.isEmpty then ok := false
    else
      g := nxt g
      col := col.set! m (cands[(g / 2 ^ 20) % cands.length]!)
  if ok then return (some col, g) else return (none, g)

#eval Id.run do
  let mut g := 777
  let mut c0 := 0
  let mut c1 := 0
  let mut d0 := 0
  let mut d1 := 0
  for _ in List.range 6000 do
    let (r, g') := sample2 g
    g := g'
    match r with
    | none => pure ()
    | some col =>
      if sigmaTri col % 2 == 0 then c0 := c0 + 1 else c1 := c1 + 1
      if sigma col % 2 == 0 then d0 := d0 + 1 else d1 := d1 + 1
  return (c0, c1, d0, d1)

def sumOver (col : Array Nat) (l : List Nat) : Nat := (l.map fun m => col[m]!).sum

#eval Id.run do
  let mut g := 12345
  -- counts indexed by (sigma parity, triangle sum /2 parity, tet sum parity, b)
  let mut tab : List ((Nat × Nat × Nat × Nat) × Nat) := []
  for it in List.range 20000 do
    let b := it % 2
    let (r, g') := sample g b
    g := g'
    match r with
    | none => pure ()
    | some col =>
      let key := (sigma col % 2, (sumOver col tris / 2) % 2, (sumOver col tets / 2) % 2, b)
      match tab.lookup key with
      | some c => tab := (key, c + 1) :: tab.filter (fun p => p.1 != key)
      | none => tab := (key, 1) :: tab
  return tab
