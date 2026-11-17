import Lightlike.CausalSets.Myrheim

/-!
# The volume of a causal interval in `3 + 1` dimensions

The volume of the causal interval `{z | 0 ≼ z ≼ w}` between `0` and a future causal vector `w` of
Minkowski space `ℝ^{3+1}` is the volume of the unit causal diamond times the fourth power of the
proper time `τ(w) = √(w⁰² - |w⃗|²)` (`volume_interval4_all`). The proof moves `w` to `τ e₀` by a
Lorentz boost (an explicit matrix of determinant `1` that preserves the Minkowski form and the
future cone, `boostMat_det`, `boost_form`, `coneLE_boost`), then rescales by `τ`; a lightlike `w`
is approached from above. This is part of a bridge between Lorentzian geometry and causal sets:
the interval volume is the input of the Myrheim–Meyer count in `Lightlike/CausalSets/Myrheim4D.lean`.

## References

* J. Myrheim, *Statistical geometry*, CERN preprint TH-2538 (1978).
* D. A. Meyer, *The dimension of causal sets*, PhD thesis, MIT (1988).
* S. Surya, *The causal set approach to the problem of quantum gravity*, Living Reviews in
  Relativity 22 (2019), section 2.
-/

open Matrix MeasureTheory
open Lightlike
open scoped Pointwise

namespace Lightlike.CausalSets

/-- The matrix of the **Lorentz boost** of `ℝ^{3+1}` along the unit vector `n` with Lorentz factor
`g` and rapidity parameter `h` (`g² - h² = 1`): `t ↦ g t - h n·x`,
`x ↦ x + ((g - 1) n·x - h t) n`. -/
def boostMat (n : Fin 3 → ℝ) (g h : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![g, -h * n 0, -h * n 1, -h * n 2;
     -h * n 0, 1 + (g - 1) * n 0 * n 0, (g - 1) * n 0 * n 1, (g - 1) * n 0 * n 2;
     -h * n 1, (g - 1) * n 1 * n 0, 1 + (g - 1) * n 1 * n 1, (g - 1) * n 1 * n 2;
     -h * n 2, (g - 1) * n 2 * n 0, (g - 1) * n 2 * n 1, 1 + (g - 1) * n 2 * n 2]

/-- The boost matrix has determinant `1` when `n` is a unit vector and `g² - h² = 1`, so the boost
preserves Lebesgue measure. -/
lemma boostMat_det (n : Fin 3 → ℝ) (g h : ℝ) (hn : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1)
    (hg : g ^ 2 - h ^ 2 = 1) : (boostMat n g h).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.det_fin_three]
  simp [boostMat, Fin.succAbove, Fin.lt_def]
  linear_combination (g ^ 2 - g - h ^ 2) * hn + hg


/-- The Lorentz boost as a map of `ℝ^{3+1}` (`boostMat n g h` acting on a vector). -/
def boost (n : Fin 3 → ℝ) (g h : ℝ) (z : Fin 4 → ℝ) : Fin 4 → ℝ := (boostMat n g h).mulVec z

lemma boost0 (n : Fin 3 → ℝ) (g h : ℝ) (z : Fin 4 → ℝ) :
    boost n g h z 0 = g * z 0 - h * (n 0 * z 1 + n 1 * z 2 + n 2 * z 3) := by
  simp [boost, boostMat, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]; ring

lemma boost1 (n : Fin 3 → ℝ) (g h : ℝ) (z : Fin 4 → ℝ) :
    boost n g h z 1 = z 1 + ((g - 1) * (n 0 * z 1 + n 1 * z 2 + n 2 * z 3) - h * z 0) * n 0 := by
  simp [boost, boostMat, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]; ring

lemma boost2 (n : Fin 3 → ℝ) (g h : ℝ) (z : Fin 4 → ℝ) :
    boost n g h z 2 = z 2 + ((g - 1) * (n 0 * z 1 + n 1 * z 2 + n 2 * z 3) - h * z 0) * n 1 := by
  simp [boost, boostMat, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]; ring

lemma boost3 (n : Fin 3 → ℝ) (g h : ℝ) (z : Fin 4 → ℝ) :
    boost n g h z 3 = z 3 + ((g - 1) * (n 0 * z 1 + n 1 * z 2 + n 2 * z 3) - h * z 0) * n 2 := by
  simp [boost, boostMat, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]; ring

lemma spatialSq_four (v : Fin 4 → ℝ) : spatialSq v = v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 := by
  simp [spatialSq, Fin.sum_univ_succ, add_assoc]

/-- Lorentz invariance of the boost. -/
lemma boost_form (n : Fin 3 → ℝ) (g h : ℝ) (hn : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1)
    (hg : g ^ 2 - h ^ 2 = 1) (z : Fin 4 → ℝ) :
    (boost n g h z 0) ^ 2 - spatialSq (boost n g h z) = z 0 ^ 2 - spatialSq z := by
  rw [spatialSq_four, spatialSq_four, boost0, boost1, boost2, boost3]
  generalize n 0 = n0 at hn ⊢
  generalize n 1 = n1 at hn ⊢
  generalize n 2 = n2 at hn ⊢
  generalize z 0 = z0
  generalize z 1 = z1
  generalize z 2 = z2
  generalize z 3 = z3
  linear_combination (-g^2*n0^2*z1^2 - 2*g^2*n0*n1*z1*z2 - 2*g^2*n0*n2*z1*z3 - g^2*n1^2*z2^2 - 2*g^2*n1*n2*z2*z3 - g^2*n2^2*z3^2 - g^2*z1^2 + 2*g*h*n0*z0*z1 + 2*g*h*n1*z0*z2 + 2*g*h*n2*z0*z3 + 2*g*n0^2*z1^2 + 4*g*n0*n1*z1*z2 + 4*g*n0*n2*z1*z3 + 2*g*n1^2*z2^2 + 4*g*n1*n2*z2*z3 + 2*g*n2^2*z3^2 - h^2*z0^2 + h^2*z1^2 - 2*h*n0*z0*z1 - 2*h*n1*z0*z2 - 2*h*n2*z0*z3 - n0^2*z1^2 - 2*n0*n1*z1*z2 - 2*n0*n2*z1*z3 - n1^2*z2^2 - 2*n1*n2*z2*z3 - n2^2*z3^2 + z1^2) * hn + (-2*n0*n1*z1*z2 - 2*n0*n2*z1*z3 + n1^2*z1^2 - n1^2*z2^2 - 2*n1*n2*z2*z3 + n2^2*z1^2 - n2^2*z3^2 + z0^2 - z1^2) * hg


lemma boostMat_inv (n : Fin 3 → ℝ) (g h : ℝ) (hn : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1)
    (hg : g ^ 2 - h ^ 2 = 1) : boostMat n g (-h) * boostMat n g h = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [boostMat, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (-h^2) * hn + (1) * hg
  · simp [boostMat, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (g*h*(n 0) - h*(n 0)) * hn + (0) * hg
  · simp [boostMat, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (g*h*(n 1) - h*(n 1)) * hn + (0) * hg
  · simp [boostMat, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (g*h*(n 2) - h*(n 2)) * hn + (0) * hg
  · simp [boostMat, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (-g*h*(n 0) + h*(n 0)) * hn + (0) * hg
  · simp [boostMat, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (g^2*(n 0)^2 + g^2 - 2*g*(n 0)^2 - h^2 + (n 0)^2 - 1) * hn + (-(n 1)^2 - (n 2)^2 + 1) * hg
  · simp [boostMat, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (g^2*(n 0)*(n 1) - 2*g*(n 0)*(n 1) + (n 0)*(n 1)) * hn + ((n 0)*(n 1)) * hg
  · simp [boostMat, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (g^2*(n 0)*(n 2) - 2*g*(n 0)*(n 2) + (n 0)*(n 2)) * hn + ((n 0)*(n 2)) * hg
  · simp [boostMat, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (-g*h*(n 1) + h*(n 1)) * hn + (0) * hg
  · simp [boostMat, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (g^2*(n 0)*(n 1) - 2*g*(n 0)*(n 1) + (n 0)*(n 1)) * hn + ((n 0)*(n 1)) * hg
  · simp [boostMat, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (g^2*(n 1)^2 - 2*g*(n 1)^2 + (n 1)^2) * hn + ((n 1)^2) * hg
  · simp [boostMat, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (g^2*(n 1)*(n 2) - 2*g*(n 1)*(n 2) + (n 1)*(n 2)) * hn + ((n 1)*(n 2)) * hg
  · simp [boostMat, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (-g*h*(n 2) + h*(n 2)) * hn + (0) * hg
  · simp [boostMat, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (g^2*(n 0)*(n 2) - 2*g*(n 0)*(n 2) + (n 0)*(n 2)) * hn + ((n 0)*(n 2)) * hg
  · simp [boostMat, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (g^2*(n 1)*(n 2) - 2*g*(n 1)*(n 2) + (n 1)*(n 2)) * hn + ((n 1)*(n 2)) * hg
  · simp [boostMat, Matrix.mul_apply, Fin.sum_univ_succ]
    linear_combination (g^2*(n 2)^2 - 2*g*(n 2)^2 + (n 2)^2) * hn + ((n 2)^2) * hg

/-- `v` is in the closed future light cone of `ℝ^{3+1}`: `0 ≤ v⁰` and `|v⃗|² ≤ (v⁰)²`. -/
def Fut (v : Fin 4 → ℝ) : Prop := 0 ≤ v 0 ∧ spatialSq v ≤ v 0 ^ 2

lemma boost_fut (n : Fin 3 → ℝ) (g h : ℝ) (hn : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1)
    (hg : g ^ 2 - h ^ 2 = 1) (hg0 : 0 < g) {z : Fin 4 → ℝ} (hz : Fut z) :
    Fut (boost n g h z) := by
  obtain ⟨hz0, hz1⟩ := hz
  have hform := boost_form n g h hn hg z
  refine ⟨?_, by nlinarith [hform]⟩
  rw [boost0]
  have hS : (n 0 * z 1 + n 1 * z 2 + n 2 * z 3) ^ 2 ≤ spatialSq z := by
    rw [spatialSq_four]
    nlinarith [sq_nonneg (n 0 * z 2 - n 1 * z 1), sq_nonneg (n 0 * z 3 - n 2 * z 1),
      sq_nonneg (n 1 * z 3 - n 2 * z 2)]
  have hs : |n 0 * z 1 + n 1 * z 2 + n 2 * z 3| ≤ z 0 :=
    abs_le_of_sq_le_sq' (hS.trans hz1) hz0 |> fun h => abs_le.2 h
  have hh : |h| ≤ g := by
    apply abs_le_of_sq_le_sq' _ hg0.le |> fun h => abs_le.2 h
    nlinarith
  have := abs_le.1 hs
  have := abs_le.1 hh
  nlinarith [mul_nonneg hz0 hg0.le, mul_nonneg (sub_nonneg.2 hs) (sub_nonneg.2 (le_abs_self h))]

lemma boost_sub (n : Fin 3 → ℝ) (g h : ℝ) (x y : Fin 4 → ℝ) :
    boost n g h (y - x) = boost n g h y - boost n g h x := by
  simp [boost, Matrix.mulVec_sub]

lemma boost_inv (n : Fin 3 → ℝ) (g h : ℝ) (hn : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1)
    (hg : g ^ 2 - h ^ 2 = 1) (z : Fin 4 → ℝ) : boost n g (-h) (boost n g h z) = z := by
  simp [boost, Matrix.mulVec_mulVec, boostMat_inv n g h hn hg]

lemma Fut_iff_coneLE (x y : Fin 4 → ℝ) : Fut (y - x) ↔ coneLE x y := by
  rw [coneLE_iff_spatial]; rfl

lemma coneLE_boost (n : Fin 3 → ℝ) (g h : ℝ) (hn : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1)
    (hg : g ^ 2 - h ^ 2 = 1) (hg0 : 0 < g) (x y : Fin 4 → ℝ) :
    coneLE (boost n g h x) (boost n g h y) ↔ coneLE x y := by
  rw [← Fut_iff_coneLE, ← Fut_iff_coneLE, ← boost_sub]
  constructor
  · intro hf
    have := boost_fut n g (-h) hn (by linarith [hg]) hg0 hf
    rwa [boost_inv n g h hn hg] at this
  · exact boost_fut n g h hn hg hg0

/-- The **causal interval** between `0` and `w` in `ℝ^{3+1}`: the points `z` with `0 ≼ z ≼ w`. -/
def interval4 (w : Fin 4 → ℝ) : Set (Fin 4 → ℝ) := {z | coneLE 0 z ∧ coneLE z w}

lemma boost_image_interval (n : Fin 3 → ℝ) (g h : ℝ) (hn : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1)
    (hg : g ^ 2 - h ^ 2 = 1) (hg0 : 0 < g) (w : Fin 4 → ℝ) :
    boost n g h '' interval4 w = interval4 (boost n g h w) := by
  have h0 : boost n g h 0 = 0 := by simp [boost]
  ext z
  constructor
  · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← h0]; exact (coneLE_boost n g h hn hg hg0 _ _).2 hx1
    · exact (coneLE_boost n g h hn hg hg0 _ _).2 hx2
  · rintro ⟨hz1, hz2⟩
    have hg' : g ^ 2 - (-h) ^ 2 = 1 := by linarith [hg]
    have e : boost n g h (boost n g (-h) z) = z := by
      simpa using boost_inv n g (-h) hn hg' z
    refine ⟨boost n g (-h) z, ⟨?_, ?_⟩, e⟩
    · have := (coneLE_boost n g (-h) hn hg' hg0 0 z).2 hz1
      rwa [show boost n g (-h) 0 = 0 by simp [boost]] at this
    · have := (coneLE_boost n g (-h) hn hg' hg0 z (boost n g h w)).2 hz2
      rwa [boost_inv n g h hn hg] at this

lemma volume_boost_image (n : Fin 3 → ℝ) (g h : ℝ) (hn : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1)
    (hg : g ^ 2 - h ^ 2 = 1) (s : Set (Fin 4 → ℝ)) :
    MeasureTheory.volume (boost n g h '' s) = MeasureTheory.volume s := by
  have hf : boost n g h = ⇑(Matrix.toLin' (boostMat n g h)) := by
    funext z; simp [boost, Matrix.toLin'_apply]
  rw [hf, MeasureTheory.Measure.addHaar_image_linearMap, LinearMap.det_toLin',
    boostMat_det n g h hn hg]
  simp

lemma coneLE_smul {c : ℝ} (hc : 0 < c) (x y : Fin 4 → ℝ) : coneLE (c • x) (c • y) ↔ coneLE x y := by
  rw [coneLE_iff_spatial, coneLE_iff_spatial, ← smul_sub]
  have h1 : spatialSq (c • (y - x)) = c ^ 2 * spatialSq (y - x) := by
    simp [spatialSq, mul_pow, Finset.mul_sum]
  rw [h1]
  simp only [Pi.smul_apply, smul_eq_mul]
  constructor
  · rintro ⟨a, b⟩
    refine ⟨by nlinarith, ?_⟩
    have : c ^ 2 * spatialSq (y - x) ≤ c ^ 2 * ((y - x) 0) ^ 2 := by nlinarith
    exact le_of_mul_le_mul_left this (by positivity)
  · rintro ⟨a, b⟩
    exact ⟨by positivity, by nlinarith [b, sq_nonneg c]⟩

lemma interval4_smul {c : ℝ} (hc : 0 < c) (w : Fin 4 → ℝ) :
    interval4 (c • w) = c • interval4 w := by
  ext z
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨c⁻¹ • z, ⟨?_, ?_⟩, by simp [smul_smul, hc.ne']⟩
    · have := (coneLE_smul (inv_pos.2 hc) 0 z).2 h1
      simpa using this
    · have := (coneLE_smul (inv_pos.2 hc) z (c • w)).2 h2
      simpa [smul_smul, hc.ne'] using this
  · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · have := (coneLE_smul hc 0 x).2 h1; simpa using this
    · exact (coneLE_smul hc x w).2 h2

lemma diamond3_eq : diamond 3 = interval4 (diamondTop 3) := rfl

/-- **The volume of a causal interval in `3 + 1` dimensions** is the volume of the unit diamond times
the fourth power of the proper time. -/
lemma volume_interval4 {w : Fin 4 → ℝ} (hw : Fut w) (hτ : 0 < w 0 ^ 2 - spatialSq w) :
    MeasureTheory.volume (interval4 w) =
      ENNReal.ofReal ((w 0 ^ 2 - spatialSq w) ^ 2) * MeasureTheory.volume (diamond 3) := by
  set τ := √(w 0 ^ 2 - spatialSq w) with hτdef
  have hτ0 : 0 < τ := Real.sqrt_pos.2 hτ
  have hτ2 : τ ^ 2 = w 0 ^ 2 - spatialSq w := Real.sq_sqrt hτ.le
  set c := √(spatialSq w) with hc
  have hc2 : c ^ 2 = spatialSq w := Real.sq_sqrt (spatialSq_nonneg w)
  have hw0 : 0 < w 0 := by
    rcases hw.1.eq_or_lt with h | h
    · exfalso; nlinarith [spatialSq_nonneg w]
    · exact h
  -- the direction
  obtain ⟨n, hn, hnw⟩ : ∃ n : Fin 3 → ℝ, n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 ∧
      ∀ i : Fin 3, w i.succ = c * n i := by
    by_cases hc0 : c = 0
    · refine ⟨![1, 0, 0], by simp, fun i => ?_⟩
      have : spatialSq w = 0 := by rw [← hc2, hc0]; norm_num
      rw [spatialSq_four] at this
      have h1 : w 1 = 0 := by nlinarith [sq_nonneg (w 1), sq_nonneg (w 2), sq_nonneg (w 3)]
      have h2 : w 2 = 0 := by nlinarith [sq_nonneg (w 1), sq_nonneg (w 2), sq_nonneg (w 3)]
      have h3 : w 3 = 0 := by nlinarith [sq_nonneg (w 1), sq_nonneg (w 2), sq_nonneg (w 3)]
      fin_cases i <;> simp [hc0, h1, h2, h3]
    · refine ⟨fun i => w i.succ / c, ?_, fun i => by field_simp⟩
      have : spatialSq w = c ^ 2 := hc2.symm
      rw [spatialSq_four] at this
      simp only [Fin.isValue]
      field_simp
      simpa using this
  have hg : (w 0 / τ) ^ 2 - (c / τ) ^ 2 = 1 := by
    field_simp; nlinarith [hτ2, hc2]
  have hg0 : 0 < w 0 / τ := by positivity
  have hnw' : n 0 * w 1 + n 1 * w 2 + n 2 * w 3 = c := by
    have e1 := hnw 0; have e2 := hnw 1; have e3 := hnw 2
    simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at e1 e2 e3
    have e4 : w 3 = c * n 2 := by simpa using hnw 2
    rw [e1, e2, e4]; linear_combination c * hn
  have hBw : boost n (w 0 / τ) (c / τ) w = τ • diamondTop 3 := by
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue]
      rw [boost0, hnw']
      simp [diamondTop]
      field_simp
      nlinarith [hτ2, hc2]
    · simp only [Fin.mk_one, Fin.isValue]
      rw [boost1, hnw']
      have := hnw 0; simp only [Fin.succ_zero_eq_one] at this
      simp [diamondTop, this]
      field_simp; ring
    · simp only [Fin.reduceFinMk, Fin.isValue]
      rw [boost2, hnw']
      have := hnw 1; simp only [Fin.succ_one_eq_two] at this
      simp [diamondTop, this]
      field_simp; ring
    · simp only [Fin.reduceFinMk, Fin.isValue]
      rw [boost3, hnw']
      have := hnw 2; simp at this
      simp [diamondTop, this]
      field_simp; ring
  calc MeasureTheory.volume (interval4 w)
      = MeasureTheory.volume (boost n (w 0 / τ) (c / τ) '' interval4 w) :=
        (volume_boost_image n _ _ hn hg _).symm
    _ = MeasureTheory.volume (interval4 (τ • diamondTop 3)) := by
        rw [boost_image_interval n _ _ hn hg hg0, hBw]
    _ = _ := by
        rw [interval4_smul hτ0, MeasureTheory.Measure.addHaar_smul, diamond3_eq]
        simp only [Module.finrank_fin_fun]
        rw [abs_of_pos (by positivity)]
        congr 2
        rw [← hτ2]; ring


lemma interval4_mono {w w' : Fin 4 → ℝ} (h : coneLE w w') : interval4 w ⊆ interval4 w' :=
  fun _ hz => ⟨hz.1, coneLE_trans hz.2 h⟩

/-- **The volume of a causal interval in `3 + 1` dimensions**: for a future causal vector `w`, the
interval between `0` and `w` has volume `τ⁴` times the volume of the unit diamond, with
`τ² = (w⁰)² - |w⃗|²` (the formula also holds, with value `0`, for a lightlike `w`). -/
lemma volume_interval4_all {w : Fin 4 → ℝ} (hw : Fut w) :
    MeasureTheory.volume (interval4 w) =
      ENNReal.ofReal ((w 0 ^ 2 - spatialSq w) ^ 2) * MeasureTheory.volume (diamond 3) := by
  have hτ0 : 0 ≤ w 0 ^ 2 - spatialSq w := by linarith [hw.2]
  rcases hτ0.eq_or_lt with h0 | hpos
  · -- lightlike: approximate from above
    rw [← h0]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, ENNReal.ofReal_zero, zero_mul]
    set V := MeasureTheory.volume (diamond 3) with hV
    have hle : ∀ ε : ℝ, 0 < ε → MeasureTheory.volume (interval4 w) ≤
        ENNReal.ofReal (((w 0 + ε) ^ 2 - spatialSq w) ^ 2) * V := by
      intro ε hε
      have hsp : spatialSq (w + ε • diamondTop 3) = spatialSq w := by
        rw [spatialSq_four, spatialSq_four]; simp [diamondTop]
      have hw0' : (w + ε • diamondTop 3) 0 = w 0 + ε := by simp [diamondTop]
      have hF : Fut (w + ε • diamondTop 3) := by
        refine ⟨by rw [hw0']; linarith [hw.1], ?_⟩
        rw [hsp, hw0']; nlinarith [hw.1, hw.2]
      have hsub : interval4 w ⊆ interval4 (w + ε • diamondTop 3) := by
        apply interval4_mono
        rw [coneLE_iff_spatial]
        have e : (w + ε • diamondTop 3) - w = ε • diamondTop 3 := by abel
        rw [e]
        have : spatialSq (ε • diamondTop 3) = 0 := by
          rw [spatialSq_four]; simp [diamondTop]
        rw [this]
        simp [diamondTop]
        exact ⟨hε.le, sq_nonneg ε⟩
      have hτ' : 0 < (w + ε • diamondTop 3) 0 ^ 2 - spatialSq (w + ε • diamondTop 3) := by
        rw [hsp, hw0']; nlinarith [hw.1, hw.2]
      refine (measure_mono hsub).trans ?_
      rw [volume_interval4 hF hτ', hsp, hw0']
    have hT : Filter.Tendsto (fun ε : ℝ => ENNReal.ofReal (((w 0 + ε) ^ 2 - spatialSq w) ^ 2) * V)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hc : Continuous fun ε : ℝ => ENNReal.ofReal (((w 0 + ε) ^ 2 - spatialSq w) ^ 2) :=
        ENNReal.continuous_ofReal.comp (by fun_prop)
      have h1 := hc.tendsto 0
      have h2 : ENNReal.ofReal (((w 0 + 0) ^ 2 - spatialSq w) ^ 2) = 0 := by
        rw [add_zero, ← h0]; simp
      rw [h2] at h1
      have h3 : Filter.Tendsto (fun ε : ℝ => ENNReal.ofReal (((w 0 + ε) ^ 2 - spatialSq w) ^ 2))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := h1.mono_left nhdsWithin_le_nhds
      have := ENNReal.Tendsto.mul_const h3 (Or.inr (volume_diamond_lt_top 3).ne)
      simpa using this
    have := ge_of_tendsto hT (eventually_nhdsWithin_of_forall fun ε hε => hle ε hε)
    exact le_antisymm this bot_le
  · exact volume_interval4 hw hpos

end Lightlike.CausalSets
