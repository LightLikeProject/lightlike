import Lightlike.Rows.G1_047.Density

/-!
# The curl of the Higgs current (CO24)

For a complex scalar `φ : ℝ × ℝ → ℂ` and a gauge component `a : ℝ × ℝ → ℝ`, the
`v`-component of the current is `J_v = Im(conj φ · D_vφ)`, `D_vφ = ∂_vφ − i e a φ`
(`current`). For `φ` of class `C²` and gauge potentials of class `C¹` the curl of the current is

`∂₁J₂ − ∂₂J₁ = 2 Im(conj D₁φ · D₂φ) − e B |φ|²`, `B = ∂₁A₂ − ∂₂A₁`

(`curl_current`), i.e. it equals the expression `curlJ` of `Density.lean`. The symmetry of the
second derivatives of `φ` is what makes the second-derivative terms cancel.

## Main results

* `current`: the current component `J_v`.
* `hasFDerivAt_current`: its Fréchet derivative.
* `curl_current`: `∂₁J₂ − ∂₂J₁ = curlJ`.
-/

noncomputable section
namespace Lightlike.Vortex

open Complex

/-- The `v`-component of the Higgs current, `J_v = Im(conj φ · D_vφ)` with
`D_vφ = ∂_vφ − i e a φ` (`a` is the gauge-potential component along `v`). -/
def current (e : ℝ) (a : ℝ × ℝ → ℝ) (φ : ℝ × ℝ → ℂ) (v : ℝ × ℝ) (p : ℝ × ℝ) : ℝ :=
  ((starRingEnd ℂ) (φ p) * covD e (a p) (fderiv ℝ φ p v) (φ p)).im

/-- The complex function whose imaginary part is the current. -/
def currentC (e : ℝ) (a : ℝ × ℝ → ℝ) (φ : ℝ × ℝ → ℂ) (v : ℝ × ℝ) (p : ℝ × ℝ) : ℂ :=
  (starRingEnd ℂ) (φ p) * covD e (a p) (fderiv ℝ φ p v) (φ p)

/-- The Fréchet derivative of the complex function `conj φ · D_vφ` (supporting lemma). -/
theorem hasFDerivAt_currentC (e : ℝ) {a : ℝ × ℝ → ℝ} {φ : ℝ × ℝ → ℂ} (v : ℝ × ℝ) {p : ℝ × ℝ}
    (hφ : ContDiffAt ℝ 2 φ p) (ha : DifferentiableAt ℝ a p) :
    ∃ G' : ℝ × ℝ →L[ℝ] ℂ, HasFDerivAt (currentC e a φ v) G' p ∧
      ∀ w, G' w = (starRingEnd ℂ) (fderiv ℝ φ p w) * covD e (a p) (fderiv ℝ φ p v) (φ p) +
        (starRingEnd ℂ) (φ p) *
          (fderiv ℝ (fderiv ℝ φ) p w v - I * ((e * fderiv ℝ a p w : ℝ) : ℂ) * φ p -
            I * ((e * a p : ℝ) : ℂ) * fderiv ℝ φ p w) := by
  have hφ1 : HasFDerivAt φ (fderiv ℝ φ p) p :=
    (hφ.differentiableAt (by norm_num)).hasFDerivAt
  have hφ2 : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) p) p :=
    ((hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have hd := hφ2.clm_apply (hasFDerivAt_const v p)
  have hc : HasFDerivAt (fun q => (starRingEnd ℂ) (φ q))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ φ p)) p :=
    Complex.conjCLE.hasFDerivAt.comp p hφ1
  have hao : HasFDerivAt (fun q => ((e * a q : ℝ) : ℂ))
      ((Complex.ofRealCLM : ℝ →L[ℝ] ℂ).comp (e • fderiv ℝ a p)) p :=
    Complex.ofRealCLM.hasFDerivAt.comp p (ha.hasFDerivAt.const_mul e)
  have hm := hc.mul ((hd.sub ((hasFDerivAt_const I p).mul hao |>.mul hφ1)))
  refine ⟨_, hm, ?_⟩
  intro w
  simp [covD]
  ring

/-- The Fréchet derivative of the current `J_v` (for `φ` of class `C²`, `a` differentiable). -/
theorem hasFDerivAt_current (e : ℝ) {a : ℝ × ℝ → ℝ} {φ : ℝ × ℝ → ℂ} (v : ℝ × ℝ) {p : ℝ × ℝ}
    (hφ : ContDiffAt ℝ 2 φ p) (ha : DifferentiableAt ℝ a p) :
    ∃ J' : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt (current e a φ v) J' p ∧
      ∀ w, J' w = ((starRingEnd ℂ) (fderiv ℝ φ p w) * covD e (a p) (fderiv ℝ φ p v) (φ p) +
        (starRingEnd ℂ) (φ p) *
          (fderiv ℝ (fderiv ℝ φ) p w v - I * ((e * fderiv ℝ a p w : ℝ) : ℂ) * φ p -
            I * ((e * a p : ℝ) : ℂ) * fderiv ℝ φ p w)).im := by
  obtain ⟨G', hG, hw⟩ := hasFDerivAt_currentC e v hφ ha
  exact ⟨Complex.imCLM.comp G', Complex.imCLM.hasFDerivAt.comp p hG, fun w => by simp [hw]⟩

/-- **Curl of the current.** For `φ` of class `C²` and differentiable `A₁, A₂` the currents
`J₁ = current e A₁ φ (1,0)`, `J₂ = current e A₂ φ (0,1)` are differentiable at `p`, with
`∂₁J₂ − ∂₂J₁ = 2 Im(conj D₁φ · D₂φ) − e B |φ|² = curlJ`, where `B = ∂₁A₂ − ∂₂A₁`. -/
theorem curl_current (e : ℝ) {A₁ A₂ : ℝ × ℝ → ℝ} {φ : ℝ × ℝ → ℂ} {p : ℝ × ℝ}
    (hφ : ContDiffAt ℝ 2 φ p) (hA₁ : DifferentiableAt ℝ A₁ p) (hA₂ : DifferentiableAt ℝ A₂ p) :
    ∃ f' g' : ℝ × ℝ →L[ℝ] ℝ,
      HasFDerivAt (current e A₂ φ (0, 1)) f' p ∧ HasFDerivAt (current e A₁ φ (1, 0)) g' p ∧
      f' (1, 0) - g' (0, 1) =
        curlJ e (fderiv ℝ A₂ p (1, 0) - fderiv ℝ A₁ p (0, 1)) (φ p)
          (covD e (A₁ p) (fderiv ℝ φ p (1, 0)) (φ p))
          (covD e (A₂ p) (fderiv ℝ φ p (0, 1)) (φ p)) := by
  obtain ⟨f', hf, hf'⟩ := hasFDerivAt_current e (0, 1) hφ hA₂
  obtain ⟨g', hg, hg'⟩ := hasFDerivAt_current e (1, 0) hφ hA₁
  refine ⟨f', g', hf, hg, ?_⟩
  have hsym := hφ.isSymmSndFDerivAt (by simp) (1, 0) (0, 1)
  rw [hf', hg', hsym]
  simp [curlJ, covD, normSq_apply]
  ring

end Lightlike.Vortex
