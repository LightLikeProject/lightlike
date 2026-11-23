import Lightlike.Regge.CMS4.Inc4

/-!
# The combinatorics of the star of a triangle class in dimension 4 (decidable part)

The 50 admissible triangle classes `c : Fin 4 → Fin 3` of the Kuhn triangulation of the 4-cube each
have 4 or 6 incidences `(σ, h)` in their star. This file computes them with integer arithmetic
(`incsOf`), orders them into a closed chain of positively oriented fan vectors (`chainOf`) and
checks by kernel evaluation the certificate (`quadCert`, `hexCert`) that the fan theorems
`quad_fan4`, `hex_fan4` need.

## Main results

* `kvZ`, `vZ`: the integer vertices of the orthoscheme and the edge vectors of an incidence.
* `incsOf`, `chainOf`, `quadCert`, `hexCert`: the incidences of a class, their chain and its checks.
* `cert_all`: every admissible class has a valid certificate (kernel evaluation, 81 classes).
-/

namespace Lightlike.Regge4

/-- Integer version of the orthoscheme vertices `kv4`. -/
def kvZ : Fin 5 → Fin 4 → ℤ :=
  ![![0, 0, 0, 0], ![1, 0, 0, 0], ![1, 1, 0, 0], ![1, 1, 1, 0], ![1, 1, 1, 1]]

/-- The integer edge vector `t - p` of the simplex `σ`. -/
def vZ (σ : Fin 24) (t p : Fin 5) : Fin 4 → ℤ := fun i => kvZ t (perms4 σ i) - kvZ p (perms4 σ i)

/-- Integer version of `clsW1`. -/
def cw1 (c : Fin 4 → Fin 3) : Fin 4 → ℤ := fun i => if c i = 1 then 1 else 0

/-- Integer version of `clsW2`. -/
def cw2 (c : Fin 4 → Fin 3) : Fin 4 → ℤ := fun i => if c i = 2 then 1 else 0

/-- The second axis vector `w₁ + w₂ = x r - x p`. -/
def ax2 (c : Fin 4 → Fin 3) : Fin 4 → ℤ := fun i => cw1 c i + cw2 c i

/-- Boolean test that the hinge of `(σ, h)` lies in the class `c`. -/
def inClsB (c : Fin 4 → Fin 3) (σ : Fin 24) (h : Fin 10) : Bool :=
  decide (vZ σ (hQ h) (hP h) = cw1 c) && decide (vZ σ (hR h) (hQ h) = cw2 c)

/-- The `3 × 3` minor expansion used for the integer `det4Z`. -/
def d3Z (a b c : Fin 4 → ℤ) (i j k : Fin 4) : ℤ :=
  a i * (b j * c k - b k * c j) - a j * (b i * c k - b k * c i) + a k * (b i * c j - b j * c i)

/-- The integer `4 × 4` determinant with rows `a, b, c, d`. -/
def det4Z (a b c d : Fin 4 → ℤ) : ℤ :=
  a 0 * d3Z b c d 1 2 3 - a 1 * d3Z b c d 0 2 3 + a 2 * d3Z b c d 0 1 3 - a 3 * d3Z b c d 0 1 2

/-- The incidences whose hinge lies in the class `c`. -/
def incsOf (c : Fin 4 → Fin 3) : List (Fin 24 × Fin 10) :=
  (List.finRange 24).flatMap fun σ =>
    ((List.finRange 10).filter fun h => inClsB c σ h).map fun h => (σ, h)

/-- The ordered pair of quotient vectors of an incidence, positively oriented for the axis. -/
def orient (c : Fin 4 → Fin 3) (e : Fin 24 × Fin 10) : (Fin 4 → ℤ) × (Fin 4 → ℤ) :=
  let A := vZ e.1 (hS e.2) (hP e.2)
  let B := vZ e.1 (hU e.2) (hP e.2)
  if 0 < det4Z (cw1 c) (ax2 c) A B then (A, B) else (B, A)

/-- Chain the incidences of the class: each next incidence starts where the previous ends. -/
def chainOf (c : Fin 4 → Fin 3) : List (Fin 24 × Fin 10) :=
  let L := incsOf c
  match L with
  | [] => []
  | e0 :: _ =>
    (List.range L.length).foldl (fun (acc : List (Fin 24 × Fin 10)) _ =>
      match acc.getLast? with
      | none => acc
      | some e => match L.find? (fun e' => (orient c e').1 == (orient c e).2) with
          | some e' => acc ++ [e']
          | none => acc) [e0]

/-- Positivity of the orientation of an incidence. -/
def posB (c : Fin 4 → Fin 3) (e : Fin 24 × Fin 10) : Bool :=
  decide (0 < det4Z (cw1 c) (ax2 c) (orient c e).1 (orient c e).2)

/-- Adjacency in the chain. -/
def adjB (c : Fin 4 → Fin 3) (e e' : Fin 24 × Fin 10) : Bool :=
  decide ((orient c e).2 = (orient c e').1)

/-- `v = -u` modulo the axis plane, with small integer coefficients. -/
def antiB (c : Fin 4 → Fin 3) (u v : Fin 4 → ℤ) : Bool :=
  (List.range 9).any fun a => (List.range 9).any fun b =>
    decide (v = fun i => -u i + ((a : ℤ) - 4) * cw1 c i + ((b : ℤ) - 4) * ax2 c i)

/-- The certificate for a class with four incidences. -/
def quadCert (c : Fin 4 → Fin 3) : Bool :=
  let L := incsOf c
  let ch := chainOf c
  decide (L.length = 4) && decide (ch.length = 5) && decide (ch.take 4).Nodup &&
    decide (ch.getD 4 default = ch.getD 0 default) &&
    (List.range 4).all (fun i => posB c (ch.getD i default) &&
      adjB c (ch.getD i default) (ch.getD (i + 1) default)) &&
    L.all (fun e => decide (e ∈ ch.take 4)) && (ch.take 4).all (fun e => decide (e ∈ L))

/-- The certificate for a class with six incidences. -/
def hexCert (c : Fin 4 → Fin 3) : Bool :=
  let L := incsOf c
  let ch := chainOf c
  decide (L.length = 6) && decide (ch.length = 7) && decide (ch.take 6).Nodup &&
    decide (ch.getD 6 default = ch.getD 0 default) &&
    (List.range 6).all (fun i => posB c (ch.getD i default) &&
      adjB c (ch.getD i default) (ch.getD (i + 1) default)) &&
    antiB c (orient c (ch.getD 0 default)).1 (orient c (ch.getD 3 default)).1 &&
    antiB c (orient c (ch.getD 3 default)).1 (orient c (ch.getD 6 default)).1 &&
    L.all (fun e => decide (e ∈ ch.take 6)) && (ch.take 6).all (fun e => decide (e ∈ L))

/-- Boolean version of `ClsOK`. -/
def clsOKB (c : Fin 4 → Fin 3) : Bool :=
  (List.finRange 4).any (fun i => decide (c i = 1)) && (List.finRange 4).any (fun i => decide (c i = 2))

/-- The class with base-3 digits of `n`. -/
def clsOfNat (n : ℕ) : Fin 4 → Fin 3 := fun i => ⟨(n / 3 ^ i.val) % 3, Nat.mod_lt _ (by norm_num)⟩

/-- Every class is `clsOfNat n` for some `n < 81`. -/
theorem exists_clsOfNat (c : Fin 4 → Fin 3) : ∃ n < 81, clsOfNat n = c := by
  have : ∀ c : Fin 4 → Fin 3, ∃ n : Fin 81, clsOfNat n.val = c := by decide +kernel
  obtain ⟨n, hn⟩ := this c
  exact ⟨n.val, n.2, hn⟩

/-- **Certificates for all classes** (kernel evaluation): each admissible class has either four or
six incidences with a valid closed positively oriented chain. -/
theorem cert_all : ∀ n : Fin 81, clsOKB (clsOfNat n) = true →
    quadCert (clsOfNat n) = true ∨ hexCert (clsOfNat n) = true := by decide +kernel

end Lightlike.Regge4
