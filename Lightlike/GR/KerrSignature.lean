import Lightlike.GR.Kerr

/-!
# The Lorentzian signature of the Kerr metric outside the horizon

For `M > 0` on `r > 0`, `Δ > 0`, `0 < θ < π` the Kerr metric is congruent to `η = diag(-1, 1, 1, 1)`:
completing the square in the `(t, φ)` block,
`g_tt dt² + 2 g_tφ dt dφ + g_φφ dφ² = -N² dt² + g_φφ (dφ + (g_tφ/g_φφ) dt)²`, `N² = (g_tφ² - g_tt g_φφ)/g_φφ = Δ sin²θ/g_φφ`
(`kerr_isLorentzian_ext`). Inside the horizon (`Δ < 0`) the roles of `t` and `r` swap and a permutation is needed:
not done here.

Gap row GE6, supporting file. Source comparison: not read (Visser 0706.0622 states the metric only).
-/

open Matrix Real

noncomputable section

namespace Lightlike

variable (M a : ℝ)

/-- The exterior domain `r > 0`, `Δ > 0`, `0 < θ < π`. -/
def kerrUext : Set (Fin 4 → ℝ) := {y | 0 < y 1 ∧ 0 < kerrD M a y ∧ 0 < y 2 ∧ y 2 < π}

lemma isOpen_kerrUext : IsOpen (kerrUext M a) := by
  refine (isOpen_lt continuous_const (continuous_apply 1)).inter
    ((isOpen_lt (continuous_const : Continuous fun _ : Fin 4 → ℝ => (0 : ℝ))
      (by unfold kerrD; fun_prop : Continuous fun y : Fin 4 → ℝ => kerrD M a y)).inter
      ((isOpen_lt continuous_const (continuous_apply 2)).inter
        (isOpen_lt (continuous_apply 2) continuous_const)))

lemma kerrUext_sub : kerrUext M a ⊆ kerrU M a :=
  fun _ hy => ⟨hy.1, hy.2.1.ne', hy.2.2.1, hy.2.2.2⟩

/-- **Completing the square in the `(t, φ)` block.** -/
theorem block_congruent (g00 g03 g33 g11 g22 : ℝ) (h33 : 0 < g33) (h11 : 0 < g11) (h22 : 0 < g22)
    (hN : 0 < g03 ^ 2 - g00 * g33) :
    ∃ P : Matrix (Fin 4) (Fin 4) ℝ, IsUnit P.det ∧
      !![g00, 0, 0, g03; 0, g11, 0, 0; 0, 0, g22, 0; g03, 0, 0, g33] = Pᵀ * eta 4 * P := by
  set N := √((g03 ^ 2 - g00 * g33) / g33) with hNdef
  have hNpos : 0 < N := Real.sqrt_pos.2 (div_pos hN h33)
  have hN2 : N ^ 2 = (g03 ^ 2 - g00 * g33) / g33 := Real.sq_sqrt (div_pos hN h33).le
  have h33s : 0 < √g33 := Real.sqrt_pos.2 h33
  have h33q : √g33 ^ 2 = g33 := Real.sq_sqrt h33.le
  have h11s : 0 < √g11 := Real.sqrt_pos.2 h11
  have h11q : √g11 ^ 2 = g11 := Real.sq_sqrt h11.le
  have h22s : 0 < √g22 := Real.sqrt_pos.2 h22
  have h22q : √g22 ^ 2 = g22 := Real.sq_sqrt h22.le
  refine ⟨!![N, 0, 0, 0; 0, √g11, 0, 0; 0, 0, √g22, 0; g03 / √g33, 0, 0, √g33], ?_, ?_⟩
  · have hdet : (!![N, 0, 0, 0; 0, √g11, 0, 0; 0, 0, √g22, 0; g03 / √g33, 0, 0, √g33] :
        Matrix (Fin 4) (Fin 4) ℝ).det = N * √g11 * √g22 * √g33 := by
      simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
      ring
    rw [hdet]
    exact (mul_pos (mul_pos (mul_pos hNpos h11s) h22s) h33s).ne'.isUnit
  · have hNN : N * N = (g03 ^ 2 - g00 * g33) / g33 := by rw [← sq]; exact hN2
    have h1 : (g03 / √g33) * (g03 / √g33) = g03 ^ 2 / g33 := by
      rw [div_mul_div_comm, Real.mul_self_sqrt h33.le]; ring
    have hne : √g33 ≠ 0 := h33s.ne'
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, eta, etaDiag, Matrix.diagonal_apply] <;>
      first
      | linarith [h11q]
      | linarith [h22q]
      | linarith [h33q]
      | (rw [hNN, h1]; field_simp; ring)
      | field_simp

/-- **Kerr has Lorentzian signature outside the horizon** (`M > 0`). -/
theorem kerr_isLorentzian_ext (hM : 0 < M) : IsLorentzianCoordMetric (kerrMetric M a) (kerrUext M a) := by
  refine ⟨⟨isOpen_kerrUext M a, fun y hy => (isCoordMetric_kerr M a).symm y (kerrUext_sub M a hy),
    fun y hy => (isCoordMetric_kerr M a).isUnit_det y (kerrUext_sub M a hy),
    fun i j => ((isCoordMetric_kerr M a).smooth i j).mono (kerrUext_sub M a)⟩, fun y hy => ?_⟩
  obtain ⟨hr, hD, hθ, hθ'⟩ := hy
  have hS : 0 < kerrS a y := kerrS_pos a hr
  have hs : 0 < sin (y 2) := sin_pos_of_pos_of_lt_pi hθ hθ'
  have hS2 : kerrS a y = y 1 ^ 2 + a ^ 2 * cos (y 2) ^ 2 := rfl
  have hD2 : kerrD M a y = y 1 ^ 2 - 2 * M * y 1 + a ^ 2 := rfl
  have hc := sin_sq_add_cos_sq (y 2)
  have g33 : 0 < kerrMetric M a y 3 3 := by
    simp only [kerrMetric]
    simp
    positivity
  have g11 : 0 < kerrMetric M a y 1 1 := by
    simp [kerrMetric]; exact div_pos hS hD
  have g22 : 0 < kerrMetric M a y 2 2 := by simp [kerrMetric]; exact hS
  have hN : 0 < kerrMetric M a y 0 3 ^ 2 - kerrMetric M a y 0 0 * kerrMetric M a y 3 3 := by
    have : kerrMetric M a y 0 3 ^ 2 - kerrMetric M a y 0 0 * kerrMetric M a y 3 3 =
        kerrD M a y * sin (y 2) ^ 2 := by
      simp only [kerrMetric]
      simp
      field_simp
      rw [hS2, hD2, show cos (y 2) ^ 2 = 1 - sin (y 2) ^ 2 by linarith]
      ring
    rw [this]; positivity
  obtain ⟨P, hP, hE⟩ := block_congruent _ _ _ _ _ g33 g11 g22 hN
  refine ⟨P, hP, ?_⟩
  rw [← hE]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kerrMetric]

end Lightlike
