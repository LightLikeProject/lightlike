import Lightlike.SpinFoam.VertexAsymptoticsHyp.LogCut
import Lightlike.SpinFoam.VertexAsymptoticsHyp.ZeroSetTangent

/-!
# `λ · log ∘ f + R` is not differentiable on the branch cut (SF10, P2 defect)

If `f` is differentiable at `y` with `f y < 0` real and `d(Im f) ≠ 0` there, then `Im f` takes
negative values arbitrarily close to `y`, so `log ∘ f` is discontinuous at `y` (`LogCut`), and a
function `φ = λ log ∘ f + R` with `λ ≠ 0` and `R` continuous at `y` is not differentiable at `y`.
Consequently `fderiv ℝ φ y = 0` there (junk value), the input of `CutRank`.
Supporting lemmas only.
-/

open Filter Topology

namespace Lightlike.SpinFoam.CutNondiff

open Lightlike.SpinFoam.ZeroSetTangent

/-- `Im f` takes negative values arbitrarily close to a zero `y` of `Im f` at which
`d (Im f) ≠ 0`. -/
theorem frequently_im_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℂ}
    {y : E} {D : E →L[ℝ] ℂ} (hf : HasFDerivAt f D y) (him : (f y).im = 0)
    (hD : Complex.imCLM.comp D ≠ 0) : ∃ᶠ z in 𝓝 y, (f z).im < 0 := by
  have hF : HasFDerivAt (fun z => (f z).im) (Complex.imCLM.comp D) y :=
    Complex.imCLM.hasFDerivAt.comp y hf
  obtain ⟨w0, hw0⟩ : ∃ w, (Complex.imCLM.comp D) w ≠ 0 := by
    by_contra h
    exact hD (ContinuousLinearMap.ext fun x => not_not.1 (not_exists.1 h x))
  obtain ⟨w, hw⟩ : ∃ w, (Complex.imCLM.comp D) w < 0 := by
    rcases lt_or_gt_of_ne hw0 with h | h
    · exact ⟨w0, h⟩
    · exact ⟨-w0, by simpa using h⟩
  have hneg := eventually_neg_ray hF him hw
  have hlim : Tendsto (fun t : ℝ => y + t • w) (𝓝[>] (0 : ℝ)) (𝓝 y) := by
    have : Tendsto (fun t : ℝ => y + t • w) (𝓝 0) (𝓝 (y + (0 : ℝ) • w)) :=
      (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  exact hlim.frequently hneg.frequently

/-- **`λ log ∘ f + R` is not differentiable on the cut.** -/
theorem not_differentiableAt_of_cut {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f R φ : E → ℂ} {lam : ℂ} {y : E} {D : E →L[ℝ] ℂ} (hlam : lam ≠ 0)
    (hφ : ∀ z, φ z = lam * Complex.log (f z) + R z) (hf : HasFDerivAt f D y)
    (hR : ContinuousAt R y) (hre : (f y).re < 0) (him : (f y).im = 0)
    (hD : Complex.imCLM.comp D ≠ 0) : ¬ DifferentiableAt ℝ φ y := by
  intro hdiff
  have hlog : ContinuousAt (fun z => Complex.log (f z)) y := by
    have h1 : ContinuousAt (fun z => lam⁻¹ * (φ z - R z)) y :=
      continuousAt_const.mul (hdiff.continuousAt.sub hR)
    refine h1.congr (Eventually.of_forall fun z => ?_)
    show lam⁻¹ * (φ z - R z) = Complex.log (f z)
    rw [hφ z]
    field_simp
    ring
  exact Lightlike.Asymptotics.Lorentzian.not_continuousAt_log_of_frequently_im_neg hre him (frequently_im_neg hf him hD) hlog

/-- On the cut, the partial derivatives of `φ` are the junk value `0`. -/
theorem coordDeriv_eq_zero_of_cut {n : ℕ} {f R φ : (Fin n → ℝ) → ℂ} {lam : ℂ}
    {y : Fin n → ℝ} {D : (Fin n → ℝ) →L[ℝ] ℂ} (hlam : lam ≠ 0)
    (hφ : ∀ z, φ z = lam * Complex.log (f z) + R z) (hf : HasFDerivAt f D y)
    (hR : ContinuousAt R y) (hre : (f y).re < 0) (him : (f y).im = 0)
    (hD : Complex.imCLM.comp D ≠ 0) (i : Fin n) : Lightlike.Oscillatory.coordDeriv φ i y = 0 := by
  have h := not_differentiableAt_of_cut hlam hφ hf hR hre him hD
  show fderiv ℝ φ y (Pi.single i 1) = 0
  rw [fderiv_zero_of_not_differentiableAt h]
  rfl

end Lightlike.SpinFoam.CutNondiff
