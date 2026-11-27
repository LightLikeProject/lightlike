import Lightlike.Spin4.Vertex

/-!
# The Barrett–Crane vertex amplitude

The vertex amplitude of the Euclidean Barrett–Crane model, built on the SU(2) recoupling theory of
`Lightlike/Recoupling/` and the contraction `k5Contract4` of `Lightlike/Spin4/Vertex.lean`.
Doubled spins throughout.

Every triangle carries a **simple** representation `(j, j)` of Spin(4) (`j` a doubled spin; the
simplicity constraint of the model is `j⁺ = j⁻`). Every tetrahedron carries the **Barrett–Crane
intertwiner** `Σ_i ι_i ⊗ ι_i`, the sum over an orthonormal basis `ι_i` of the SU(2) intertwiners of
its four legs, with one copy on the self-dual and one on the anti-self-dual factor
(`bcNode`). It does not depend on the basis; this is the property that makes it the
unique intertwiner of the four simple representations. The vertex amplitude
(`bcVertex`) is the contraction of five such tensors along the edges of `K₅`.

## Main results

* `bcVertex_eq_sum`: **the vertex is a sum of squares of 15j symbols**,
  `A_v(j) = Σ_{i} {15j}(j; i)²` over the virtual spins `i_a` of the five tetrahedra.
* `bcVertex_im`, `bcVertex_nonneg`: the amplitude is real and non-negative.
* `bcVertex_zero`: the value `1` at spin `0`.

## Conventions

The 15j symbol is `Lightlike.Recoupling.fifteenJSimplex`, in the orthonormal basis of
`Lightlike.Recoupling.fourJ` (no dimension factor per tetrahedron). The face amplitude of the model
is the dimension `(j + 1)²` of `(j, j)`.

## References

* `barrett-crane-1998`, §IV: the vertex amplitude of the model.
* `reisenberger-1999`: the Barrett–Crane intertwiner is the unique one of four simple
  representations (`bcNode_unique`, `Lightlike/SpinFoam/BarrettCraneUnique.lean`).
-/

open Finset Matrix Lightlike.Recoupling

namespace Lightlike.SpinFoam.BC

open Lightlike.Spin4

/-- **The Barrett–Crane node tensor** of a tetrahedron whose four legs carry the simple
representations `(j k, j k)`: `Σ_i ι_i(μ) ι_i(ν)` over the intertwiner basis of the four spins `j`,
as a function of the self-dual projections `μ` and the anti-self-dual projections `ν`. -/
noncomputable def bcNode (j : Fin 4 → ℕ) (μ ν : Fin 4 → ℤ) : ℂ :=
  ∑ i ∈ channel (j 0) (j 1) (j 2) (j 3), fourJNode j i μ * fourJNode j i ν

/-- **The Barrett–Crane vertex amplitude**: the contraction of five Barrett–Crane node tensors
along the edges of `K₅`, the ten edges carrying the simple representations `(j e, j e)`. -/
noncomputable def bcVertex (j : Fin 10 → ℕ) : ℂ :=
  k5Contract4 j j fun a => bcNode (k5Spins j a)

/-- The channels of the five nodes of the vertex with spins `j`. -/
def nodeChans (j : Fin 10 → ℕ) : Fin 5 → Finset ℕ := fun a =>
  channel (k5Spins j a 0) (k5Spins j a 1) (k5Spins j a 2) (k5Spins j a 3)

/-- **The vertex as a sum of squares of 15j symbols**: `A_v = Σ_i {15j}(j; i)²`. -/
theorem bcVertex_eq_sum (j : Fin 10 → ℕ) :
    bcVertex j = ∑ P ∈ Fintype.piFinset (nodeChans j),
      (fifteenJSimplex (j 0) (j 1) (j 2) (j 3) (j 4) (j 5) (j 6) (j 7) (j 8) (j 9)
        (P 0) (P 1) (P 2) (P 3) (P 4) : ℂ) ^ 2 := by
  unfold bcVertex bcNode
  have := k5Contract4_sum j j (nodeChans j) (fun _ _ => 1)
    (fun a i μ ν => fourJNode (k5Spins j a) i μ * fourJNode (k5Spins j a) i ν)
  simp only [one_mul] at this
  rw [show (fun a μ ν => ∑ i ∈ channel (k5Spins j a 0) (k5Spins j a 1) (k5Spins j a 2)
      (k5Spins j a 3), fourJNode (k5Spins j a) i μ * fourJNode (k5Spins j a) i ν) =
    fun a μ ν => ∑ i ∈ nodeChans j a, fourJNode (k5Spins j a) i μ * fourJNode (k5Spins j a) i ν
    from rfl, this]
  refine Finset.sum_congr rfl fun P _ => ?_
  simp only [prod_const_one, one_mul]
  rw [k5Contract4_mul, sq,
    fifteenJSimplex_eq_k5Contract j P]

/-- The Barrett–Crane vertex is real and non-negative: it is the real number `Σ {15j}²`. -/
theorem bcVertex_eq_real (j : Fin 10 → ℕ) :
    bcVertex j = ((∑ P ∈ Fintype.piFinset (nodeChans j),
      fifteenJSimplex (j 0) (j 1) (j 2) (j 3) (j 4) (j 5) (j 6) (j 7) (j 8) (j 9)
        (P 0) (P 1) (P 2) (P 3) (P 4) ^ 2 : ℝ) : ℂ) := by
  rw [bcVertex_eq_sum]; push_cast; rfl

/-- The vertex is real. -/
theorem bcVertex_im (j : Fin 10 → ℕ) : (bcVertex j).im = 0 := by
  rw [bcVertex_eq_real]; exact Complex.ofReal_im _

/-- The vertex is non-negative. -/
theorem bcVertex_nonneg (j : Fin 10 → ℕ) : 0 ≤ (bcVertex j).re := by
  rw [bcVertex_eq_real, Complex.ofReal_re]
  exact sum_nonneg fun _ _ => sq_nonneg _

/-! ## Simplicity -/

/-- **The simple representations are the diagonal ones.** For `n + m > 0` the weak simplicity
constraint at `γ = 0`, `Yᴴ (K - 0 · L) Y = 0` on the image of the highest-spin embedding, holds for
the representation `(n/2, m/2)` exactly when `n = m`. So a non-simple representation violates the
constraint of the Barrett–Crane model. -/
theorem simple_iff {n m : ℕ} (hpos : 0 < n + m) :
    (∀ X : Matrix (Fin 2) (Fin 2) ℂ, X 1 1 = -X 0 0 →
        (eprlMap n m)ᴴ * simplicityOp 0 n m X * eprlMap n m = 0) ↔ n = m := by
  rw [weak_simplicity_iff hpos]
  constructor
  · intro h
    have : (n : ℝ) = m := by linarith
    exact_mod_cast this
  · rintro rfl; simp

/-! ## The Baez–Christensen sign convention -/

/-- **The Baez–Christensen sign** of a vertex with doubled edge spins `j`: `(-1)^(Σ_e j_e)`, which
is `(-1)^(2 Σ_e s_e)` for the spins `s_e = j_e / 2`. It is `+1` when the ten spins sum to an
integer and `-1` when they sum to a half-integer. -/
def bcSign (j : Fin 10 → ℕ) : ℝ := (-1) ^ ∑ e, j e

/-- **The vertex in the Baez–Christensen convention**: `(-1)^(2 Σ_e s_e)` times
`Lightlike.SpinFoam.BC.bcVertex`. Their Riemannian 10j symbol carries this sign relative to the
sum of squares of 15j symbols of `bcVertex_eq_sum` (Baez–Christensen, *Positivity of spin foam
amplitudes*, Class. Quantum Grav. 19 (2002) 2291, arXiv:gr-qc/0110044). -/
noncomputable def bcVertexBC (j : Fin 10 → ℕ) : ℝ := bcSign j * (bcVertex j).re

/-- The sign is `±1`. -/
theorem bcSign_sq (j : Fin 10 → ℕ) : bcSign j ^ 2 = 1 := by
  unfold bcSign; rw [← pow_mul, mul_comm, pow_mul]; simp

/-- **The two conventions differ by the sign only**: `bcVertexBC j = ± (bcVertex j).re`, with the
sign `+` when the doubled spins sum to an even number. -/
theorem bcVertexBC_of_even {j : Fin 10 → ℕ} (h : Even (∑ e, j e)) :
    bcVertexBC j = (bcVertex j).re := by
  unfold bcVertexBC bcSign; rw [h.neg_one_pow, one_mul]

/-- With an odd sum of doubled spins the Baez–Christensen vertex is minus ours. -/
theorem bcVertexBC_of_odd {j : Fin 10 → ℕ} (h : Odd (∑ e, j e)) :
    bcVertexBC j = -(bcVertex j).re := by
  unfold bcVertexBC bcSign; rw [h.neg_one_pow, neg_one_mul]

/-- **Bridge.** The absolute value of the Baez–Christensen vertex is the Barrett–Crane vertex
`Σ {15j}²`, for all spins. -/
theorem abs_bcVertexBC (j : Fin 10 → ℕ) : |bcVertexBC j| = (bcVertex j).re := by
  rcases Nat.even_or_odd (∑ e, j e) with h | h
  · rw [bcVertexBC_of_even h, abs_of_nonneg (bcVertex_nonneg j)]
  · rw [bcVertexBC_of_odd h, abs_neg, abs_of_nonneg (bcVertex_nonneg j)]

/-- The Baez–Christensen vertex is non-negative when the spins sum to an integer. -/
theorem bcVertexBC_nonneg_of_even {j : Fin 10 → ℕ} (h : Even (∑ e, j e)) :
    0 ≤ bcVertexBC j := by
  rw [bcVertexBC_of_even h]; exact bcVertex_nonneg j

/-- **The sign of the Baez–Christensen vertex.** It is non-positive when the spins sum to a
half-integer. -/
theorem bcVertexBC_nonpos_of_odd {j : Fin 10 → ℕ} (h : Odd (∑ e, j e)) :
    bcVertexBC j ≤ 0 := by
  rw [bcVertexBC_of_odd h]; exact neg_nonpos.mpr (bcVertex_nonneg j)

/-- At odd parity and a nonzero vertex the two conventions disagree. -/
theorem bcVertexBC_ne_of_odd {j : Fin 10 → ℕ} (h : Odd (∑ e, j e)) (h0 : (bcVertex j).re ≠ 0) :
    bcVertexBC j ≠ (bcVertex j).re := by
  rw [bcVertexBC_of_odd h]; intro h'; apply h0; linarith

end Lightlike.SpinFoam.BC
