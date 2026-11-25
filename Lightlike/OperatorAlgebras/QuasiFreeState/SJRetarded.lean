import Lightlike.OperatorAlgebras.QuasiFreeState.SorkinJohnston
import Lightlike.CausalSets.Basic

/-!
# The retarded matrix `K_R = a M (1 - a b M)⁻¹` of the Sorkin-Johnston state (CS7)

Johnston (arXiv:0909.0944, read: eqs. (10), (16)) writes the retarded propagator of a finite causal set as
`K_R = a L (1 - a b L)⁻¹` (`L` the link matrix in four dimensions; the causal matrix `C` in two dimensions,
`b = -m²/ρ` for a mass `m`, `b = 0` the massless case with `K_R = a C`), and the Pauli-Jordan matrix as `Δ = K_R - K_Rᵀ`.

* `retardedMatrix a b M = a • M * (1 - (a b) • M)⁻¹` and `pjRetarded a b M = K_R - K_Rᵀ`;
* `isUnit_one_sub_smul`: for a matrix `M` supported on a strict order (the causal matrix or the link matrix) `1 - c M` is
  invertible for every `c` (`M` is nilpotent, by a height function), so the inverse in `K_R` is a genuine inverse and
  `K_R (1 - a b M) = a M` (`retardedMatrix_mul`);
* `isPureState_retarded`: **the quasi-free state of `(pjRetarded a b M, |i pjRetarded a b M|)` is pure** for every
  coefficient and every matrix `M` (the purity does not depend on the particular retarded matrix).

Not claimed: no comparison with the Afshordi-Aslanbeigi-Sorkin paper (arXiv:1205.1296, not read); the mass and dimension enter
only through the values of `b` and the choice `M = L` or `M = C`.
-/

open scoped Matrix
open Finset Matrix

namespace Lightlike.OperatorAlgebras.QuasiFreeState

universe u

section Retarded

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- The retarded matrix `K_R = a M (1 - a b M)⁻¹`. -/
noncomputable def retardedMatrix (a b : ℝ) (M : Matrix α α ℝ) : Matrix α α ℝ :=
  a • (M * (1 - (a * b) • M)⁻¹)

/-- The Pauli-Jordan matrix `Δ = K_R - K_Rᵀ` of a retarded matrix. -/
noncomputable def pjRetarded (a b : ℝ) (M : Matrix α α ℝ) : Matrix α α ℝ :=
  retardedMatrix a b M - (retardedMatrix a b M)ᵀ

/-- `Δ` is antisymmetric. -/
lemma pjRetarded_anti (a b : ℝ) (M : Matrix α α ℝ) : (pjRetarded a b M)ᵀ = -pjRetarded a b M := by
  simp [pjRetarded]

/-- **The Sorkin-Johnston state of a retarded matrix `a M (1 - a b M)⁻¹` is pure**, for every `a`, `b` and `M`. -/
theorem isPureState_retarded (a b : ℝ) (M : Matrix α α ℝ) :
    ∃ H : Matrix α α ℝ, ∃ h : PJData (pjRetarded a b M) H,
      haveI : Fact (qfKerM (pjOmega (pjRetarded a b M)) (pjEta H)).PosSemidef :=
        qfFact _ _ (pj_omega_antisymm h) (pj_isCovariance h)
      IsPureState (qfState (pjOmega (pjRetarded a b M)) (pjEta H) (pj_omega_antisymm h)) := by
  obtain ⟨H, h⟩ := exists_pjData (pjRetarded a b M) (pjRetarded_anti a b M)
  exact ⟨H, h, isPureState_pauliJordan h⟩

section Strict

variable [PartialOrder α] [DecidableRel ((· < ·) : α → α → Prop)]

/-- The height `#{z | z < x}`, strictly increasing along `<`. -/
def height (x : α) : ℕ := (univ.filter (· < x)).card

lemma height_lt {x y : α} (h : x < y) : height x < height y := by
  unfold height
  apply card_lt_card
  refine ⟨fun z hz => ?_, fun hsub => ?_⟩
  · simp only [mem_filter, mem_univ, true_and] at hz ⊢; exact hz.trans h
  · have := hsub (show x ∈ (univ.filter (· < y)) by simp [h])
    simp at this

lemma height_lt_card (x : α) : height x < Fintype.card α := by
  unfold height
  have : (univ.filter (· < x)).card < (univ : Finset α).card := by
    apply card_lt_card
    refine ⟨subset_univ _, fun hsub => ?_⟩
    have := hsub (mem_univ x)
    simp at this
  simpa using this

/-- A matrix supported on a strict order is nilpotent: its `k`-th power moves the height by at least `k`. -/
lemma pow_apply_ne_zero {M : Matrix α α ℝ} (hM : ∀ x y, M x y ≠ 0 → x < y) :
    ∀ k x y, (M ^ k) x y ≠ 0 → height x + k ≤ height y := by
  intro k
  induction k with
  | zero =>
    intro x y h
    rw [pow_zero, Matrix.one_apply] at h
    by_cases hxy : x = y
    · subst hxy; simp
    · simp [hxy] at h
  | succ k ih =>
    intro x y h
    rw [pow_succ, Matrix.mul_apply] at h
    obtain ⟨z, _, hz⟩ := exists_ne_zero_of_sum_ne_zero h
    have h1 := ih x z (left_ne_zero_of_mul hz)
    have h2 := height_lt (hM z y (right_ne_zero_of_mul hz))
    omega

lemma isNilpotent_of_strict {M : Matrix α α ℝ} (hM : ∀ x y, M x y ≠ 0 → x < y) (c : ℝ) :
    IsNilpotent (c • M) := by
  refine ⟨Fintype.card α, ?_⟩
  ext x y
  rw [smul_pow, Matrix.smul_apply, Matrix.zero_apply]
  by_cases h : (M ^ Fintype.card α) x y = 0
  · simp [h]
  · have := pow_apply_ne_zero hM _ x y h
    have := height_lt_card y
    omega

/-- **`1 - c M` is invertible** for a matrix supported on a strict order. -/
lemma isUnit_one_sub_smul {M : Matrix α α ℝ} (hM : ∀ x y, M x y ≠ 0 → x < y) (c : ℝ) :
    IsUnit (1 - c • M) :=
  (isNilpotent_of_strict hM c).isUnit_one_sub

/-- **`K_R (1 - a b M) = a M`**: the defining relation of the retarded matrix. -/
theorem retardedMatrix_mul {M : Matrix α α ℝ} (hM : ∀ x y, M x y ≠ 0 → x < y) (a b : ℝ) :
    retardedMatrix a b M * (1 - (a * b) • M) = a • M := by
  have hu := isUnit_one_sub_smul hM (a * b)
  have hdet : IsUnit (1 - (a * b) • M).det := (Matrix.isUnit_iff_isUnit_det _).mp hu
  unfold retardedMatrix
  rw [Matrix.smul_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]

/-- The causal matrix is supported on the strict order. -/
lemma causal_support [DecidableRel ((· < ·) : α → α → Prop)] :
    ∀ x y, (Matrix.of fun x y : α => if x < y then (1 : ℝ) else 0) x y ≠ 0 → x < y := by
  intro x y h
  by_contra hxy
  simp [hxy] at h

open Classical in
/-- **The link matrix** `L_xy = 1` if `y` covers `x` (a link of the causal set), `0` otherwise. -/
noncomputable def linkMatrix : Matrix α α ℝ := Matrix.of fun x y => if x ⋖ y then 1 else 0

/-- The link matrix is supported on the strict order. -/
lemma link_support : ∀ x y : α, (linkMatrix : Matrix α α ℝ) x y ≠ 0 → x < y := by
  classical
  intro x y h
  by_contra hxy
  have : ¬ x ⋖ y := fun hc => hxy hc.lt
  simp [linkMatrix, this] at h

end Strict

end Retarded

end Lightlike.OperatorAlgebras.QuasiFreeState
