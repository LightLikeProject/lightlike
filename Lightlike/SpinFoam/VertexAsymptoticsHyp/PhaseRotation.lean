import Lightlike.Asymptotics.Lorentzian.Vertex
import Lightlike.Asymptotics.Lorentzian.Stationary

/-!
# Phase rotation of one boundary spinor (SF10, T-SF10-P2 statement defect)

Multiplying the source spinor `ξ = firstCol (g k 0)` of one edge `k` by a phase `c`, `‖c‖ = 1`,
changes neither `‖ξ‖`, nor `spinVec ξ` (hence not the closure and nondegeneracy hypotheses of
`lorHessian_invertible_at_critical`), nor the real part of the vertex action, but it rotates the
overlap `⟨Z, ξ⟩ ⟨Jξ', Z'⟩` of edge `k` by `c`.  This is the tool behind the observation that
`lorHessian_invertible_at_critical` has no hypothesis keeping the overlaps off the branch cut of
`Complex.log` (see `HANDOFF.md`).  Supporting lemmas only.
-/

open Complex
open scoped ComplexConjugate

namespace Lightlike.Asymptotics.Lorentzian

open Lightlike.Asymptotics.EPRL

/-- Multiplying a matrix on the right by `diag(c, 1)` multiplies its first column by `c`. -/
lemma firstCol_mul_diag (M : Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ) :
    firstCol (M * !![c, 0; 0, 1]) = c • firstCol M := by
  ext i
  fin_cases i <;> simp [firstCol, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

/-- `J (c ξ) = conj c · J ξ`. -/
lemma jMap_smul (c : ℂ) (ξ : Spinor) : jMap (c • ξ) = conj c • jMap ξ := by
  ext i
  fin_cases i <;> simp

/-- A phase does not change the norm of a spinor. -/
lemma norm_smul_unit {c : ℂ} (hc : ‖c‖ = 1) (ξ : Spinor) : ‖c • ξ‖ = ‖ξ‖ := by
  rw [norm_smul, hc, one_mul]

/-- The overlaps of the rotated source spinor: `⟨Z, c ξ⟩ = c ⟨Z, ξ⟩`. -/
lemma inner_smul_phase (c : ℂ) (Z ξ : Spinor) : inner ℂ Z (c • ξ) = c * inner ℂ Z ξ :=
  inner_smul_right _ _ _

/-- The overlaps of the rotated target spinor: `⟨J (c ξ'), Z'⟩ = c ⟨J ξ', Z'⟩`. -/
lemma inner_jMap_smul_phase (c : ℂ) (ξ' Z' : Spinor) :
    inner ℂ (jMap (c • ξ')) Z' = c * inner ℂ (jMap ξ') Z' := by
  rw [jMap_smul, inner_smul_left, Complex.conj_conj]

/-- The real part of `log w` is `log ‖w‖`, with no condition on `w`. -/
lemma re_log_eq (w : ℂ) : (Complex.log w).re = Real.log ‖w‖ := Complex.log_re w

/-- **Phase invariance of `Re S_e`**: rotating the source spinor of one triangle by a phase does
not change the real part of its action (junk values included). -/
theorem re_triAction_smul_unit (k p : ℝ) (Z Z' ξ ξ' : Spinor) {c : ℂ} (hc : ‖c‖ = 1) :
    (triAction k p Z (c • ξ) Z' ξ').re = (triAction k p Z ξ Z' ξ').re := by
  have key : (Complex.log (c * inner ℂ Z ξ * inner ℂ (jMap ξ') Z')).re =
      (Complex.log (inner ℂ Z ξ * inner ℂ (jMap ξ') Z')).re := by
    rw [re_log_eq, re_log_eq, norm_mul, norm_mul, norm_mul, hc, one_mul]
  unfold triAction
  rw [inner_smul_phase]
  simp [Complex.mul_re, key]

/-- The boundary data `g` with the first column of `g k 0` multiplied by `c`. -/
noncomputable def rotSrc (g : BdryData) (k : Fin 10) (c : ℂ) : BdryData :=
  fun k' i => if k' = k ∧ i = 0 then g k' i * !![c, 0; 0, 1] else g k' i

lemma firstCol_rotSrc (g : BdryData) (k : Fin 10) (c : ℂ) (k' : Fin 10) (i : Fin 2) :
    firstCol (rotSrc g k c k' i) =
      if k' = k ∧ i = 0 then c • firstCol (g k' i) else firstCol (g k' i) := by
  unfold rotSrc
  split_ifs with h
  · exact firstCol_mul_diag _ _
  · rfl

/-- The spin vectors of the boundary spinors are unchanged by `rotSrc` for `‖c‖ = 1`: closure and
nondegeneracy hypotheses (which only involve `spinVec ∘ firstCol`) transfer. -/
lemma spinVec_firstCol_rotSrc {c : ℂ} (hc : ‖c‖ = 1) (g : BdryData) (k : Fin 10)
    (k' : Fin 10) (i : Fin 2) :
    spinVec (firstCol (rotSrc g k c k' i)) = spinVec (firstCol (g k' i)) := by
  rw [firstCol_rotSrc]
  split_ifs
  · funext m; exact spinVec_smul_unit hc _ m
  · rfl

/-- The unit-norm hypotheses transfer along `rotSrc`. -/
lemma norm_firstCol_rotSrc {c : ℂ} (hc : ‖c‖ = 1) (g : BdryData) (k : Fin 10)
    (k' : Fin 10) (i : Fin 2) :
    ‖firstCol (rotSrc g k c k' i)‖ = ‖firstCol (g k' i)‖ := by
  rw [firstCol_rotSrc]
  split_ifs
  · exact norm_smul_unit hc _
  · rfl

/-- **`Re S` is invariant under `rotSrc`**, at every point of `SL(2,ℂ)^5 × (ℂ²)^10`. -/
theorem re_lorAction_rotSrc (j p : Fin 10 → ℝ) {c : ℂ} (hc : ‖c‖ = 1) (g : BdryData) (k : Fin 10)
    (X : Fin 5 → Lightlike.Lorentz.SL2C) (z : Fin 10 → Spinor) :
    (lorAction j p (rotSrc g k c) X z).re = (lorAction j p g X z).re := by
  unfold lorAction
  rw [Complex.re_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases he : e = k
  · subst he
    rw [firstCol_rotSrc, firstCol_rotSrc]
    simp only [true_and, ite_true, Fin.one_eq_zero_iff]
    exact re_triAction_smul_unit _ _ _ _ _ _ hc
  · rw [firstCol_rotSrc, firstCol_rotSrc]
    simp [he]

end Lightlike.Asymptotics.Lorentzian
