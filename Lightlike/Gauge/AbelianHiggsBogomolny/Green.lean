import Lightlike.Gauge.AbelianHiggsBogomolny.Current

/-!
# Green's theorem for the Bogomolny integrand (CO24)

For `φ` of class `C²` and gauge potentials `A₁, A₂` of class `C¹` on `ℝ²`, put
`W_j = e v² A_j + J_j` (`J_j` the Higgs current of `Current.lean`). Then
`∂₁W₂ − ∂₂W₁ = e v² B + curlJ` (`bogoTerm`), and Mathlib's divergence theorem on a rectangle
(`MeasureTheory.integral2_divergence_prod_of_hasFDerivAt`) turns the integral of `bogoTerm` over a
rectangle into a boundary integral of `W` (`box_integral_bogoTerm`).

## Main results

* `contDiff_current`: the current is `C¹` for `φ ∈ C²`, `a ∈ C¹`.
* `bogoTerm`: the integrand `e v² B + curlJ`.
* `box_integral_bogoTerm`: its integral over a rectangle equals a boundary integral of `W`.
-/

noncomputable section
namespace Lightlike.Vortex

open Complex MeasureTheory Set

/-- The current is `C¹` when `φ` is `C²` and the gauge component is `C¹`. -/
theorem contDiff_current (e : ℝ) {a : ℝ × ℝ → ℝ} {φ : ℝ × ℝ → ℂ} (v : ℝ × ℝ)
    (hφ : ContDiff ℝ 2 φ) (ha : ContDiff ℝ 1 a) : ContDiff ℝ 1 (current e a φ v) := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hd : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (m := 1) (by norm_num)
  have hdv : ContDiff ℝ 1 (fun p => fderiv ℝ φ p v) := hd.clm_apply contDiff_const
  have hao : ContDiff ℝ 1 (fun p => ((e * a p : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.mul ha)
  have hc : ContDiff ℝ 1 (fun p => (starRingEnd ℂ) (φ p)) :=
    Complex.conjCLE.contDiff.comp hφ1
  have := Complex.imCLM.contDiff.comp
    (hc.mul (hdv.sub (((contDiff_const (c := Complex.I)).mul hao).mul hφ1)))
  exact this

/-- The Bogomolny integrand `e v² B + curlJ` of a configuration `(φ, A₁, A₂)` at a point,
`B = ∂₁A₂ − ∂₂A₁`, `D_jφ = ∂_jφ − i e A_j φ`. -/
def bogoTerm (e v : ℝ) (A₁ A₂ : ℝ × ℝ → ℝ) (φ : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  e * v ^ 2 * (fderiv ℝ A₂ p (1, 0) - fderiv ℝ A₁ p (0, 1)) +
    curlJ e (fderiv ℝ A₂ p (1, 0) - fderiv ℝ A₁ p (0, 1)) (φ p)
      (covD e (A₁ p) (fderiv ℝ φ p (1, 0)) (φ p))
      (covD e (A₂ p) (fderiv ℝ φ p (0, 1)) (φ p))

/-- The vector field `W_j = e v² A_j + J_j`, with `J_j` the current along `u`. -/
def Wfield (e v : ℝ) (A : ℝ × ℝ → ℝ) (φ : ℝ × ℝ → ℂ) (u : ℝ × ℝ) (p : ℝ × ℝ) : ℝ :=
  e * v ^ 2 * A p + current e A φ u p

/-- **Green's theorem for the Bogomolny integrand.** The integral of `e v² B + curlJ` over a
rectangle is the boundary integral of `W₂ dy − W₁ dx` (with the orientation of
`MeasureTheory.integral2_divergence_prod_of_hasFDerivAt`). -/
theorem box_integral_bogoTerm (e v : ℝ) {A₁ A₂ : ℝ × ℝ → ℝ} {φ : ℝ × ℝ → ℂ}
    (hφ : ContDiff ℝ 2 φ) (hA₁ : ContDiff ℝ 1 A₁) (hA₂ : ContDiff ℝ 1 A₂)
    (a₁ b₁ a₂ b₂ : ℝ) :
    (∫ x in a₁..b₁, ∫ y in a₂..b₂, bogoTerm e v A₁ A₂ φ (x, y)) =
      (((∫ x in a₁..b₁, -Wfield e v A₁ φ (1, 0) (x, b₂)) -
          ∫ x in a₁..b₁, -Wfield e v A₁ φ (1, 0) (x, a₂)) +
        ∫ y in a₂..b₂, Wfield e v A₂ φ (0, 1) (b₁, y)) -
        ∫ y in a₂..b₂, Wfield e v A₂ φ (0, 1) (a₁, y) := by
  have hF : ContDiff ℝ 1 (Wfield e v A₂ φ (0, 1)) :=
    (contDiff_const.mul hA₂).add (contDiff_current e (0, 1) hφ hA₂)
  have hG : ContDiff ℝ 1 (fun p => -Wfield e v A₁ φ (1, 0) p) :=
    ((contDiff_const.mul hA₁).add (contDiff_current e (1, 0) hφ hA₁)).neg
  have key : ∀ p, fderiv ℝ (Wfield e v A₂ φ (0, 1)) p (1, 0) +
      fderiv ℝ (fun p => -Wfield e v A₁ φ (1, 0) p) p (0, 1) = bogoTerm e v A₁ A₂ φ p := by
    intro p
    obtain ⟨f', g', hf, hg, hcurl⟩ := curl_current e hφ.contDiffAt
      ((hA₁.differentiable one_ne_zero) p) ((hA₂.differentiable one_ne_zero) p)
    have h2 : HasFDerivAt (Wfield e v A₂ φ (0, 1)) ((e * v ^ 2) • fderiv ℝ A₂ p + f') p :=
      (((hA₂.differentiable one_ne_zero) p).hasFDerivAt.const_mul (e * v ^ 2)).add hf
    have h1 : HasFDerivAt (fun p => -Wfield e v A₁ φ (1, 0) p)
        (-((e * v ^ 2) • fderiv ℝ A₁ p + g')) p :=
      ((((hA₁.differentiable one_ne_zero) p).hasFDerivAt.const_mul (e * v ^ 2)).add hg).neg
    rw [h2.fderiv, h1.fderiv]
    simp only [bogoTerm, add_apply, smul_apply, neg_apply, smul_eq_mul]
    linarith
  have := integral2_divergence_prod_of_hasFDerivAt (Wfield e v A₂ φ (0, 1))
    (fun p => -Wfield e v A₁ φ (1, 0) p) (fun p => fderiv ℝ (Wfield e v A₂ φ (0, 1)) p)
    (fun p => fderiv ℝ (fun p => -Wfield e v A₁ φ (1, 0) p) p) a₁ a₂ b₁ b₂
    hF.continuous.continuousOn hG.continuous.continuousOn
    (fun x _ => ((hF.differentiable one_ne_zero) x).hasFDerivAt)
    (fun x _ => ((hG.differentiable one_ne_zero) x).hasFDerivAt) (by
      have hc : Continuous fun p => fderiv ℝ (Wfield e v A₂ φ (0, 1)) p (1, 0) +
          fderiv ℝ (fun p => -Wfield e v A₁ φ (1, 0) p) p (0, 1) :=
        ((hF.continuous_fderiv one_ne_zero).clm_apply continuous_const).add
          ((hG.continuous_fderiv one_ne_zero).clm_apply continuous_const)
      exact hc.continuousOn.integrableOn_compact
        (isCompact_uIcc.prod isCompact_uIcc))
  simp only [key] at this
  exact this

end Lightlike.Vortex
