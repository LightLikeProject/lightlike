import Lightlike.Poincare.PauliLubanskiGenerators

/-!
# The chart of the mass shell by the spatial momentum

The map `Q ↦ q` (the spatial momentum, `coordV`) from the mass shell to `ℝ³` has the continuous inverse
`p ↦ √(m² + |p|²) + p·σ` (`chartInv`, `chartInv_coordV`, `coordV_chartInv`); in particular the points of the shell
whose spatial momentum lies in a compact set form a compact set (`isCompact_coordV_preimage`). The positivity of
`p⁰ + p·σ` for `p⁰ > |p|` is `posDef_momH`.

Supporting lemmas for the generators on `L²`; no catalogue entry.
-/

open Matrix Complex
open scoped ComplexOrder

namespace Lightlike.Poincare

noncomputable section

/-- The Euclidean square `|p|²` of the spatial momentum. -/
def sqV (p : Fin 3 → ℝ) : ℝ := p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2

lemma sqV_nonneg (p : Fin 3 → ℝ) : 0 ≤ sqV p := by unfold sqV; positivity

lemma continuous_sqV : Continuous sqV := by unfold sqV; fun_prop

/-- **`p⁰ + p·σ` is positive definite when `p⁰ > |p|`.** The quadratic form is `p⁰ |x|² + p·v` with `v` the Hopf
image of `x`, `|v| = |x|²`, and `|p·v| ≤ |p| |x|² < p⁰ |x|²`. -/
lemma posDef_momH {p0 : ℝ} {p : Fin 3 → ℝ} (h0 : 0 < p0) (h : sqV p < p0 ^ 2) : (momH p0 p).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · refine Matrix.IsHermitian.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [momH]
  · set a := (x 0).re
    set b := (x 0).im
    set c := (x 1).re
    set d := (x 1).im
    have hs : 0 < a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
      have e0 : Complex.normSq (x 0) = a ^ 2 + b ^ 2 := by rw [Complex.normSq_apply]; ring
      have e1 : Complex.normSq (x 1) = c ^ 2 + d ^ 2 := by rw [Complex.normSq_apply]; ring
      have hex : ∃ i, x i ≠ 0 := by
        by_contra hne
        exact hx (funext fun i => not_not.1 fun h => hne ⟨i, h⟩)
      rcases Fin.exists_fin_two.1 hex with h | h
      · have := Complex.normSq_pos.2 h
        rw [e0] at this
        nlinarith [sq_nonneg c, sq_nonneg d]
      · have := Complex.normSq_pos.2 h
        rw [e1] at this
        nlinarith [sq_nonneg a, sq_nonneg b]
    set s := a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2
    set v1 := 2 * (a * c + b * d)
    set v2 := 2 * (a * d - b * c)
    set v3 := a ^ 2 + b ^ 2 - c ^ 2 - d ^ 2
    have hv : v1 ^ 2 + v2 ^ 2 + v3 ^ 2 = s ^ 2 := by simp only [v1, v2, v3, s]; ring
    have hcs : (p 0 * v1 + p 1 * v2 + p 2 * v3) ^ 2 ≤ sqV p * s ^ 2 := by
      rw [← hv]; unfold sqV
      nlinarith [sq_nonneg (p 0 * v2 - p 1 * v1), sq_nonneg (p 0 * v3 - p 2 * v1),
        sq_nonneg (p 1 * v3 - p 2 * v2)]
    have hlt : (p 0 * v1 + p 1 * v2 + p 2 * v3) ^ 2 < (p0 * s) ^ 2 := by
      have : sqV p * s ^ 2 < p0 ^ 2 * s ^ 2 := mul_lt_mul_of_pos_right h (by positivity)
      nlinarith
    have hpos : 0 < p0 * s + (p 0 * v1 + p 1 * v2 + p 2 * v3) := by
      have hps : 0 < p0 * s := mul_pos h0 hs
      nlinarith
    rw [Complex.lt_def]
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Pi.star_apply, momH]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Complex.add_re, Complex.mul_re, Complex.mul_im,
      Complex.add_im, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im, Complex.zero_re, Complex.zero_im]
    refine ⟨?_, ?_⟩
    · simp only [v1, v2, v3, s] at hpos
      nlinarith [hpos]
    · ring

lemma coord0_pos {m : ℝ} (P : MassShell m) : 0 < coord0 P.1 := by
  have h := P.2.1
  have h0 := h.diag_pos (i := 0)
  have h1 := h.diag_pos (i := 1)
  rw [Complex.lt_def] at h0 h1
  simp only [coord0, Complex.div_ofNat_re, Complex.add_re]
  simp only [Complex.zero_re] at h0 h1
  linarith [h0.1, h1.1]

lemma coord0_eq_sqrt {m : ℝ} (P : MassShell m) : coord0 P.1 = Real.sqrt (m ^ 2 + sqV (coordV P.1)) := by
  have h := coords_sq P
  rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq (by unfold sqV; positivity) (coord0_pos P).le]
  unfold sqV
  nlinarith [h]

/-- The inverse of the chart: `p ↦ √(m² + |p|²) + p·σ`. -/
def chartInv {m : ℝ} (hm : 0 < m) (p : Fin 3 → ℝ) : MassShell m :=
  ⟨momH (Real.sqrt (m ^ 2 + sqV p)) p, by
    refine ⟨posDef_momH (Real.sqrt_pos.2 (by have := sqV_nonneg p; positivity)) ?_, ?_⟩
    · rw [Real.sq_sqrt (by have := sqV_nonneg p; positivity)]
      nlinarith [hm]
    · rw [det_momH]
      congr 1
      rw [Real.sq_sqrt (by have := sqV_nonneg p; positivity)]
      unfold sqV; ring⟩

lemma continuous_chartInv {m : ℝ} (hm : 0 < m) : Continuous (chartInv hm) := by
  refine Continuous.subtype_mk ?_ _
  have hs : Continuous fun p : Fin 3 → ℝ => Real.sqrt (m ^ 2 + sqV p) :=
    (continuous_const.add continuous_sqV).sqrt
  unfold momH
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp only [Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
    Matrix.cons_val_fin_one] <;> fun_prop

lemma chartInv_coordV {m : ℝ} (hm : 0 < m) (P : MassShell m) : chartInv hm (coordV P.1) = P := by
  apply Subtype.ext
  change momH (Real.sqrt (m ^ 2 + sqV (coordV P.1))) (coordV P.1) = P.1
  rw [← coord0_eq_sqrt, momH_coords_shell]

lemma coordV_momH (p0 : ℝ) (p : Fin 3 → ℝ) : coordV (momH p0 p) = p := by
  funext i; fin_cases i <;> simp [coordV, momH]

lemma coordV_chartInv {m : ℝ} (hm : 0 < m) (p : Fin 3 → ℝ) : coordV (chartInv hm p).1 = p :=
  coordV_momH _ _

lemma continuous_coordV : Continuous (coordV : Matrix (Fin 2) (Fin 2) ℂ → Fin 3 → ℝ) := by
  refine continuous_pi fun i => ?_
  have h10 : Continuous fun A : Matrix (Fin 2) (Fin 2) ℂ => A 1 0 :=
    (continuous_apply 0).comp (continuous_apply 1)
  have h00 : Continuous fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 0 :=
    (continuous_apply 0).comp (continuous_apply 0)
  have h11 : Continuous fun A : Matrix (Fin 2) (Fin 2) ℂ => A 1 1 :=
    (continuous_apply 1).comp (continuous_apply 1)
  fin_cases i
  · exact Complex.continuous_re.comp h10
  · exact Complex.continuous_im.comp h10
  · exact Complex.continuous_re.comp ((h00.sub h11).div_const 2)

lemma continuous_coordV_shell {m : ℝ} : Continuous fun P : MassShell m => coordV P.1 :=
  continuous_coordV.comp continuous_subtype_val

/-- **The points of the shell with spatial momentum in a compact set form a compact set.** -/
lemma isCompact_coordV_preimage {m : ℝ} (hm : 0 < m) {K : Set (Fin 3 → ℝ)} (hK : IsCompact K) :
    IsCompact {P : MassShell m | coordV P.1 ∈ K} := by
  have : {P : MassShell m | coordV P.1 ∈ K} = chartInv hm '' K := by
    ext P
    constructor
    · intro hP
      exact ⟨coordV P.1, hP, chartInv_coordV hm P⟩
    · rintro ⟨p, hp, rfl⟩
      change coordV (chartInv hm p).1 ∈ K
      rw [coordV_chartInv]; exact hp
  rw [this]
  exact hK.image (continuous_chartInv hm)

end

end Lightlike.Poincare
