import Mathlib

/-!
# Connes' distance on the two-point space (finite spectral triple)

The algebra is `ℂ²` acting diagonally on `ℂ²`, `f = diag(a, b)`, and the Dirac operator is
`D = [[0, m], [m̄, 0]]`.  The commutator is `[D, f] = [[0, m(b-a)], [m̄(a-b), 0]]`.  We say
`‖C‖ ≤ 1` (`NormLe`) when `C` does not increase the Hilbert norm on `ℂ²`.  We prove
`‖[D, f]‖ ≤ 1 ↔ ‖m‖ ‖a-b‖ ≤ 1`, and therefore the distance between the two points
`sup {‖a-b‖ : ‖[D,f]‖ ≤ 1}` equals `1/‖m‖` (the textbook value of the two-point space).
-/

open Matrix

namespace Lightlike.Dirac

/-- The Dirac matrix of the two-point space with mass parameter `m`. -/
def twoD (m : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![0, m; (starRingEnd ℂ) m, 0]

/-- The diagonal matrix `diag(a, b)`: a function on the two points. -/
def twoF (a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![a, 0; 0, b]

/-- `C` does not increase the Hilbert (ℓ²) norm on `ℂ²`: `‖C‖ ≤ 1`. -/
def NormLe (C : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∀ v : Fin 2 → ℂ, ∑ i, ‖(C.mulVec v) i‖ ^ 2 ≤ ∑ i, ‖v i‖ ^ 2

lemma twoComm (m a b : ℂ) :
    twoD m * twoF a b - twoF a b * twoD m
      = !![0, m * (b - a); (starRingEnd ℂ) m * (a - b), 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twoD, twoF] <;> ring

/-- Norm bound for an off-diagonal matrix. -/
lemma normLe_offDiag (α β : ℂ) :
    NormLe !![0, α; β, 0] ↔ ‖α‖ ≤ 1 ∧ ‖β‖ ≤ 1 := by
  constructor
  · intro h
    have h1 := h ![0, 1]
    have h2 := h ![1, 0]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h1 h2
    refine ⟨?_, ?_⟩
    · nlinarith [norm_nonneg α]
    · nlinarith [norm_nonneg β]
  · rintro ⟨hα, hβ⟩ v
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    simp
    have a1 : ‖α‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg α]
    have b1 : ‖β‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg β]
    have := sq_nonneg ‖v 0‖
    have := sq_nonneg ‖v 1‖
    nlinarith [mul_le_mul_of_nonneg_right a1 (sq_nonneg ‖v 1‖),
      mul_le_mul_of_nonneg_right b1 (sq_nonneg ‖v 0‖)]

/-- **Commutator norm on the two-point space**: `‖[D, diag(a,b)]‖ ≤ 1 ↔ ‖m‖‖a-b‖ ≤ 1`. -/
theorem normLe_comm_iff (m a b : ℂ) :
    NormLe (twoD m * twoF a b - twoF a b * twoD m) ↔ ‖m‖ * ‖a - b‖ ≤ 1 := by
  rw [twoComm, normLe_offDiag]
  have h1 : ‖m * (b - a)‖ = ‖m‖ * ‖a - b‖ := by rw [norm_mul, norm_sub_rev]
  have h2 : ‖(starRingEnd ℂ) m * (a - b)‖ = ‖m‖ * ‖a - b‖ := by
    rw [norm_mul, Complex.norm_conj]
  rw [h1, h2]
  simp

/-- The set of values `‖a - b‖` over test functions with `‖[D, f]‖ ≤ 1`. -/
def twoSet (m : ℂ) : Set ℝ :=
  {r | ∃ a b : ℂ, NormLe (twoD m * twoF a b - twoF a b * twoD m) ∧ r = ‖a - b‖}

/-- Connes' distance between the two points of the two-point space. -/
noncomputable def twoDist (m : ℂ) : ℝ := sSup (twoSet m)

/-- **Connes distance on the two-point space**: `d = 1/‖m‖` for `m ≠ 0`. -/
theorem twoDist_eq (m : ℂ) (hm : m ≠ 0) : twoDist m = 1 / ‖m‖ := by
  have hpos : 0 < ‖m‖ := norm_pos_iff.mpr hm
  apply IsGreatest.csSup_eq
  refine ⟨⟨((1 / ‖m‖ : ℝ) : ℂ), 0, ?_, ?_⟩, ?_⟩
  · rw [normLe_comm_iff]
    simp [hpos.ne']
  · simp
  · rintro r ⟨a, b, h, rfl⟩
    rw [normLe_comm_iff] at h
    rw [le_div_iff₀ hpos]
    linarith [mul_comm ‖m‖ ‖a - b‖]

end Lightlike.Dirac
