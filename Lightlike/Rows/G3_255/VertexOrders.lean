import Mathlib

/-!
# Graviton self-vertices from the Einstein–Hilbert expansion: bookkeeping

Row G3-255.  Write `g = η + κ h` and `L_EH = (2/κ²) √(-g) R`.  Since `R` and `√(-g)` are series in
`κ h`, the part of `L_EH` with exactly `n` fields `h` carries `κ^(n-2)`: the `n = 2` part is the
Fierz–Pauli kinetic term (`κ⁰`, the propagator), the `n = 3` part is the cubic vertex (`κ¹`),
the `n = 4` part the quartic vertex (`κ²`).  (The origin of the lower orders of `√(-g)` is
`Lightlike.Rows.G3_255.volOrder2`.)  This file records only the counting; it does not compute
vertex tensors.

* `GravVertex`: the graviton self-interactions that are vertices (cubic, quartic).
* `GravVertex.legs`, `GravVertex.kappaOrder`: number of `h` legs and power of `κ`.
* `GravVertex.kappaOrder_add_two`: `kappaOrder v + 2 = legs v`.
* `kappaPower_list`: for a list of vertices, the total power of `κ` is
  `Σ legs - 2 · (number of vertices)`.
-/

namespace Lightlike.Rows.G3_255

/-- Graviton self-interaction vertices coming from the expansion of the Einstein–Hilbert action
(the quadratic term is the propagator, not a vertex). -/
inductive GravVertex
  | cubic
  | quartic
  deriving DecidableEq, Repr

namespace GravVertex

/-- Number of graviton legs `n` of the vertex. -/
def legs : GravVertex → ℕ
  | cubic => 3
  | quartic => 4

/-- Power of `κ` carried by the `n`-point vertex: `κ^(n-2)`. -/
def kappaOrder : GravVertex → ℕ
  | cubic => 1
  | quartic => 2

/-- The `n`-point graviton vertex carries `κ^(n-2)`. -/
theorem kappaOrder_add_two (v : GravVertex) : v.kappaOrder + 2 = v.legs := by
  cases v <;> rfl

/-- Every vertex has at least three legs. -/
theorem three_le_legs (v : GravVertex) : 3 ≤ v.legs := by
  cases v <;> decide

/-- The vertex with a given number of legs, if it is a self-vertex of the expansion up to
order `κ²`. -/
def ofLegs : ℕ → Option GravVertex
  | 3 => some cubic
  | 4 => some quartic
  | _ => none

theorem ofLegs_legs (v : GravVertex) : ofLegs v.legs = some v := by
  cases v <;> rfl

end GravVertex

/-- Total power of `κ` of a product of vertices. -/
def totalKappa (l : List GravVertex) : ℕ := (l.map GravVertex.kappaOrder).sum

/-- Total number of legs of a product of vertices. -/
def totalLegs (l : List GravVertex) : ℕ := (l.map GravVertex.legs).sum

/-- For a product of vertices the power of `κ` is `Σ legs - 2 · (number of vertices)`;
stated additively to avoid truncated subtraction. -/
theorem kappaPower_list (l : List GravVertex) :
    totalKappa l + 2 * l.length = totalLegs l := by
  induction l with
  | nil => simp [totalKappa, totalLegs]
  | cons v l ih =>
    have h := GravVertex.kappaOrder_add_two v
    simp only [totalKappa, totalLegs, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    omega

/-- A product of `k` cubic vertices carries `κ^k`. -/
theorem totalKappa_replicate_cubic (k : ℕ) :
    totalKappa (List.replicate k GravVertex.cubic) = k := by
  simp [totalKappa, GravVertex.kappaOrder, List.map_replicate, List.sum_replicate]

end Lightlike.Rows.G3_255
