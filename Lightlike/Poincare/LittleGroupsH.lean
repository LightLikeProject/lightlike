module

public import Lightlike.Poincare.WignerRotation

/-!
# Little groups in `SL(2,ℂ)`

Momenta as Hermitian matrices `P = p⁰ + p·σ`, `SL(2,ℂ)` acting by `A • P = A P Aᴴ`.

* The little group of the rest momentum `m · 1` (`m ≠ 0`) is `SU(2)` (`actP_rest_eq_iff`).
* The little group of the light-like momentum `K = diag(2, 0)`, i.e. `p = (1, 0, 0, 1)`, is the group of upper
  triangular matrices `[[e^{iθ}, b], [0, e^{−iθ}]]` (`actP_massless_eq_iff`): the double cover of the Euclidean
  group `E(2)` (rotations `θ`, translations `b`), which is not compact (`not_isCompact_littleGroupH_massless`).

**Difference from the source (kind: representation).** Bekaert–Boulanger write the standard boost, the little
group and the Wigner rotation for `Λ ∈ SO(D−1,1)↑` acting on `ℝ^{D−1,1}` (§3.1, equations (10)–(13); §3.2); here
they are stated for the universal cover `SL(2,ℂ) ≅ Spin(3,1)` acting on Hermitian `2 × 2` momenta, which is how
§1.1 (page 3) says the representations are meant ("a single (or double) valued representation of `SO(D−1,1)↑` is
meant to be a genuine representation of `Spin(D−1,1)`"). The `SO(3,1)↑` form is not derived from this file.

## References

* X. Bekaert, N. Boulanger, *The unitary representations of the Poincaré group in any spacetime dimension*,
  arXiv:hep-th/0611263v2, §3.2 (page 12 of v2: the stabiliser of a time-like vector is the rotation group, of a
  light-like vector the Euclidean group `ISO(D − 2)`), §3.3 (table, page 13).
-/

@[expose] public section

noncomputable section

open Matrix Lightlike.Lorentz

namespace Lightlike.Poincare

/-- **The massive little group is `SU(2)`**: `A` fixes `m · 1` iff `A Aᴴ = 1`. -/
theorem actP_rest_eq_iff {m : ℝ} (hm : m ≠ 0) (A : SL2C) :
    actP A ((m : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = (m : ℂ) • 1 ↔
      (A : Matrix (Fin 2) (Fin 2) ℂ) * (A : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = 1 := by
  simp only [actP, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  exact (smul_right_injective (Matrix (Fin 2) (Fin 2) ℂ) hm').eq_iff

/-- The light-like standard momentum `p = (1, 0, 0, 1)`, i.e. `p⁰ + p·σ = diag(2, 0)`. -/
def masslessH : Matrix (Fin 2) (Fin 2) ℂ := !![2, 0; 0, 0]

/-- **The massless little group**: `A` fixes `diag(2, 0)` iff `A` is upper triangular with `|A₀₀| = 1`. -/
theorem actP_massless_eq_iff (A : SL2C) :
    actP A masslessH = masslessH ↔ (A : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 ∧
      ‖(A : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ = 1 := by
  set a := (A : Matrix (Fin 2) (Fin 2) ℂ) 0 0
  set c := (A : Matrix (Fin 2) (Fin 2) ℂ) 1 0
  have h00 : (actP A masslessH) 0 0 = 2 * (a * starRingEnd ℂ a) := by
    simp [actP, masslessH, Matrix.mul_apply, Fin.sum_univ_two, a]; ring
  have h01 : (actP A masslessH) 0 1 = 2 * (a * starRingEnd ℂ c) := by
    simp [actP, masslessH, Matrix.mul_apply, Fin.sum_univ_two, a, c]; ring
  have h10 : (actP A masslessH) 1 0 = 2 * (c * starRingEnd ℂ a) := by
    simp [actP, masslessH, Matrix.mul_apply, Fin.sum_univ_two, a, c]; ring
  have h11 : (actP A masslessH) 1 1 = 2 * (c * starRingEnd ℂ c) := by
    simp [actP, masslessH, Matrix.mul_apply, Fin.sum_univ_two, c]; ring
  have hnorm : ∀ z : ℂ, z * starRingEnd ℂ z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  constructor
  · intro h
    have e00 := congrFun (congrFun h 0) 0
    have e11 := congrFun (congrFun h 1) 1
    rw [h00] at e00
    rw [h11] at e11
    simp only [masslessH, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] at e00 e11
    rw [hnorm] at e00 e11
    have hc : ‖c‖ ^ 2 = 0 := by exact_mod_cast (mul_eq_zero.1 e11).resolve_left two_ne_zero
    have ha : ‖a‖ ^ 2 = 1 := by
      have : ((‖a‖ ^ 2 : ℝ) : ℂ) = 1 := by linear_combination e00 / 2
      exact_mod_cast this
    refine ⟨norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hc), ?_⟩
    nlinarith [norm_nonneg a]
  · rintro ⟨hc, ha⟩
    ext i j
    fin_cases i <;> fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue]; rw [h00, hnorm, ha]; simp [masslessH]
    · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one]; rw [h01, show c = 0 from hc]; simp [masslessH]
    · simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta]; rw [h10, show c = 0 from hc]; simp [masslessH]
    · simp only [Fin.mk_one, Fin.isValue]; rw [h11, show c = 0 from hc]; simp [masslessH]

/-- The upper triangular element `[[1, b], [0, 1]]` ("translation" of the massless little group). -/
def masslessTrans (b : ℂ) : SL2C := ⟨!![1, b; 0, 1], by simp [Matrix.det_fin_two]⟩

lemma masslessTrans_fix (b : ℂ) : actP (masslessTrans b) masslessH = masslessH :=
  (actP_massless_eq_iff _).2 ⟨by simp [masslessTrans], by simp [masslessTrans]⟩

/-- The little group of the light-like momentum, as a set. -/
def littleGroupH (K : Matrix (Fin 2) (Fin 2) ℂ) : Set SL2C := {A | actP A K = K}

/-- **The massless little group is not compact** (its translations are unbounded). -/
theorem not_isCompact_littleGroupH_massless : ¬ IsCompact (littleGroupH masslessH) := by
  intro hc
  have hcont : Continuous fun A : SL2C => ‖(A : Matrix (Fin 2) (Fin 2) ℂ) 0 1‖ :=
    (continuous_norm.comp ((continuous_apply 1).comp ((continuous_apply 0).comp continuous_subtype_val)))
  obtain ⟨C, hC⟩ := (hc.image hcont).bddAbove
  have hmem : masslessTrans ((|C| + 1 : ℝ) : ℂ) ∈ littleGroupH masslessH := masslessTrans_fix _
  have hle := hC ⟨_, hmem, rfl⟩
  simp only [masslessTrans] at hle
  have : ‖(((|C| + 1 : ℝ) : ℂ))‖ = |C| + 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] at hle
  rw [this] at hle
  linarith [le_abs_self C]

end Lightlike.Poincare
