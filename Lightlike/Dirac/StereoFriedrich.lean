import Mathlib
import Lightlike.Dirac.StereoBochner

/-!
# Friedrich bound `D² ≥ n²/4` on the round sphere chart

Pointwise (Cauchy–Schwarz, the "twistor" estimate): `‖∑ᵢ γᵢ uᵢ‖² ≤ n ∑ᵢ ‖uᵢ‖²` for a skew Clifford
module (each `γᵢ` is an isometry).  With `uᵢ = ∇ᵢ f` this gives `‖D f‖² ≤ n ∑ ‖∇ᵢ f‖²`, and together with
the integrated Lichnerowicz formula `∫ ‖D f‖² = ∫ ∑‖∇ᵢ f‖² + (n(n-1)/4) ∫ ‖f‖²` it yields
`(n²/4) ∫ ‖f‖² ≤ ∫ ‖D f‖²` (Friedrich's bound; on `S²` `|λ| ≥ 1`, sharp for the spectrum `±(k+1)`).

## References

* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators* (1992), chapter
  "Clifford Modules and Dirac Operators" (source key `bgv-1992`); no equation number is claimed.
-/

namespace Lightlike.Dirac

open scoped RealInnerProductSpace
open MeasureTheory

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `γᵢ` is an isometry for a skew Clifford module. -/
lemma norm_gam_apply {ρ : CliffordRep n V} (hρ : IsSkewRep ρ) (i : Fin n) (u : V) :
    ‖gam ρ i u‖ = ‖u‖ := by
  have hρ' : ∀ (i : Fin n) (w u : V), inner ℝ (gam ρ i w) u = -inner ℝ w (gam ρ i u) := hρ
  have h : ‖gam ρ i u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, hρ', gam_sq, inner_neg_right, neg_neg,
      real_inner_self_eq_norm_sq]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- **Twistor estimate.** `‖∑ᵢ γᵢ uᵢ‖² ≤ n ∑ᵢ ‖uᵢ‖²` for a skew Clifford module. -/
lemma norm_sum_gam_sq_le {ρ : CliffordRep n V} (hρ : IsSkewRep ρ) (u : Fin n → V) :
    ‖∑ i, gam ρ i (u i)‖ ^ 2 ≤ (n : ℝ) * ∑ i, ‖u i‖ ^ 2 := by
  have h1 : ‖∑ i, gam ρ i (u i)‖ ≤ ∑ i, ‖u i‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_gam_apply hρ i (u i)).le)
  have h2 : (∑ i, ‖u i‖) ^ 2 ≤ (Finset.univ : Finset (Fin n)).card * ∑ i, ‖u i‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  simp only [Finset.card_univ, Fintype.card_fin] at h2
  calc ‖∑ i, gam ρ i (u i)‖ ^ 2 ≤ (∑ i, ‖u i‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

/-- Pointwise: `‖D f‖² ≤ n ∑ᵢ ‖∇ᵢ f‖²` in any frame, for a skew Clifford module. -/
lemma norm_diracF_sq_le {ρ : CliffordRep n V} (hρ : IsSkewRep ρ) (F : E n → Fin n → E n)
    (ω : E n → Fin n → Matrix (Fin n) (Fin n) ℝ) (f : E n → V) (x : E n) :
    ‖diracF ρ F ω f x‖ ^ 2 ≤ (n : ℝ) * ∑ i, ‖nablaF ρ F ω i f x‖ ^ 2 :=
  norm_sum_gam_sq_le hρ fun i => nablaF ρ F ω i f x

/-- **Friedrich bound on the sphere chart.** For `n ≥ 2` and a compactly supported `C²` spinor field,
`(n²/4) ∫ ‖f‖² h^{-n} ≤ ∫ ‖D f‖² h^{-n}`. -/
theorem integral_norm_diracF_stereo_ge_friedrich {ρ : CliffordRep n V} (hρ : IsSkewRep ρ)
    (hn : 2 ≤ n) {f : E n → V} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ((n : ℝ) ^ 2 / 4) * ∫ x, ‖f x‖ ^ 2 * stereoW n x ≤
      ∫ x, ‖diracF ρ stereoF stereoOmega f x‖ ^ 2 * stereoW n x := by
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hBint : Integrable (fun x => (∑ i, ‖nablaF ρ stereoF stereoOmega i f x‖ ^ 2) *
      stereoW n x) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · refine (continuous_finsetSum _ fun i _ => ?_).mul continuous_stereoW
      exact ((contDiff_nablaF_stereo hf i).continuous).norm.pow 2
    · refine HasCompactSupport.intro hfc.isCompact fun x hx => ?_
      simp [nablaF_stereo_eq_zero hx]
  have hDint : Integrable (fun x => ‖diracF ρ stereoF stereoOmega f x‖ ^ 2 * stereoW n x) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((continuous_diracF_stereo (hf.of_le (by norm_num))).norm.pow 2).mul
        continuous_stereoW
    · exact HasCompactSupport.intro hfc.isCompact fun x hx => by
        simp [diracF_stereo_eq_zero hx]
  have hle : ∫ x, ‖diracF ρ stereoF stereoOmega f x‖ ^ 2 * stereoW n x ≤
      (n : ℝ) * ∫ x, (∑ i, ‖nablaF ρ stereoF stereoOmega i f x‖ ^ 2) * stereoW n x := by
    rw [← integral_const_mul]
    refine integral_mono hDint (hBint.const_mul _) fun x => ?_
    have := mul_le_mul_of_nonneg_right (norm_diracF_sq_le hρ stereoF stereoOmega f x)
      (stereoW_pos x).le
    linarith
  have hsq := integral_norm_diracF_stereo_sq hρ hf hfc
  set A := ∫ x, ‖diracF ρ stereoF stereoOmega f x‖ ^ 2 * stereoW n x
  set B := ∫ x, (∑ i, ‖nablaF ρ stereoF stereoOmega i f x‖ ^ 2) * stereoW n x
  set C := ∫ x, ‖f x‖ ^ 2 * stereoW n x
  have hC : 0 ≤ C := integral_nonneg fun x => mul_nonneg (sq_nonneg _) (stereoW_pos x).le
  -- A = B + n(n-1)/4 C, A ≤ n B ⇒ (n-1) A ≥ n(n-1)/4 · n C
  have hn1 : 0 < (n : ℝ) - 1 := by linarith
  have key : ((n : ℝ) - 1) * (((n : ℝ) ^ 2 / 4) * C) ≤ ((n : ℝ) - 1) * A := by
    nlinarith [hsq, hle]
  exact le_of_mul_le_mul_left key hn1

/-- The case of the unit 2-sphere: `∫ ‖f‖² h^{-2} ≤ ∫ ‖D f‖² h^{-2}` (the Friedrich constant `n²/4 = 1`,
the lowest `|λ| = 1` of the spectrum `±(k+1)`; improves the Lichnerowicz constant `1/2`). -/
theorem integral_norm_diracF_stereo_ge_friedrich_two {ρ : CliffordRep 2 V} (hρ : IsSkewRep ρ)
    {f : E 2 → V} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ∫ x, ‖f x‖ ^ 2 * stereoW 2 x ≤ ∫ x, ‖diracF ρ stereoF stereoOmega f x‖ ^ 2 * stereoW 2 x := by
  have h := integral_norm_diracF_stereo_ge_friedrich hρ le_rfl hf hfc
  norm_num at h
  exact h

/-- **Friedrich eigenvalue bound on the sphere chart.** If a nonzero compactly supported `C²` spinor
field satisfies `D f = λ f` then `λ² ≥ n²/4` (`n ≥ 2`; on `S²`, `λ² ≥ 1`). -/
theorem eigen_sq_ge_friedrich_stereo {ρ : CliffordRep n V} (hρ : IsSkewRep ρ) (hn : 2 ≤ n)
    {f : E n → V} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (lam : ℝ)
    (hD : ∀ x, diracF ρ stereoF stereoOmega f x = lam • f x) (x₀ : E n) (hx₀ : f x₀ ≠ 0) :
    (n : ℝ) ^ 2 / 4 ≤ lam ^ 2 := by
  have h := integral_norm_diracF_stereo_ge_friedrich hρ hn hf hfc
  have hI : 0 < ∫ x, ‖f x‖ ^ 2 * stereoW n x := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := x₀)
      ((hf.continuous.norm.pow 2).mul continuous_stereoW) ?_
      (fun x => mul_nonneg (sq_nonneg _) (stereoW_pos x).le) ?_
    · exact HasCompactSupport.intro hfc.isCompact fun x hx => by
        simp [image_eq_zero_of_notMem_tsupport hx]
    · exact (mul_pos (pow_pos (norm_pos_iff.mpr hx₀) 2) (stereoW_pos x₀)).ne'
  have e : ∫ x, ‖diracF ρ stereoF stereoOmega f x‖ ^ 2 * stereoW n x =
      lam ^ 2 * ∫ x, ‖f x‖ ^ 2 * stereoW n x := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hD, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  rw [e] at h
  exact le_of_mul_le_mul_right h hI

end Lightlike.Dirac
