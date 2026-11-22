import Lightlike.SpinFoam.VertexAsymptoticsHyp.CutNondiff
import Lightlike.SpinFoam.VertexAsymptoticsHyp.CutRank

/-!
# Degenerate Hessian for `λ log ∘ f + R` at a point of the branch cut (SF10, P2 defect, T4)

Assembly of `ZeroSetTangent`, `CutNondiff` and `CutRank`: if `φ = λ · log ∘ f + R` with `λ ≠ 0`,
`f`, `R` of class `C¹` at `a`, `f a` negative real and `d (Im f) (a) ≠ 0`, then `hessMat φ a` has
rank at most one, so its determinant vanishes (`n ≥ 2`).  Supporting lemma only.
-/

open Filter Topology Lightlike.Oscillatory

namespace Lightlike.SpinFoam.CutAssemble

open Lightlike.SpinFoam.ZeroSetTangent Lightlike.SpinFoam.CutNondiff Lightlike.SpinFoam.CutRank

/-- **Hessian determinant vanishes at a branch-cut point.** -/
theorem det_hessMat_eq_zero_of_log_cut {n : ℕ} (hn : 2 ≤ n) {f R φ : (Fin n → ℝ) → ℂ} {lam : ℂ}
    {a : Fin n → ℝ} (hlam : lam ≠ 0) (hφ : ∀ z, φ z = lam * Complex.log (f z) + R z)
    (hf : ContDiffAt ℝ 1 f a) (hR : ContDiffAt ℝ 1 R a) (hre : (f a).re < 0)
    (him : (f a).im = 0) (hD : Complex.imCLM.comp (fderiv ℝ f a) ≠ 0) :
    (hessMat φ a).det = 0 := by
  have hfev : ∀ᶠ y in 𝓝 a, ContDiffAt ℝ 1 f y := hf.eventually (by simp)
  have hRev : ∀ᶠ y in 𝓝 a, ContDiffAt ℝ 1 R y := hR.eventually (by simp)
  have hDc : ContinuousAt (fun y => Complex.imCLM.comp (fderiv ℝ f y)) a :=
    (ContinuousLinearMap.compL ℝ (Fin n → ℝ) ℂ ℝ Complex.imCLM |>.continuous.continuousAt).comp
      (hf.continuousAt_fderiv one_ne_zero)
  have hDne : ∀ᶠ y in 𝓝 a, Complex.imCLM.comp (fderiv ℝ f y) ≠ 0 :=
    hDc.eventually_ne hD
  have hrev : ∀ᶠ y in 𝓝 a, (f y).re < 0 :=
    (Complex.continuous_re.continuousAt.comp hf.continuousAt).eventually (gt_mem_nhds hre)
  set U : Set (Fin n → ℝ) := {y | ContDiffAt ℝ 1 f y ∧ ContDiffAt ℝ 1 R y ∧
    Complex.imCLM.comp (fderiv ℝ f y) ≠ 0 ∧ (f y).re < 0} with hU
  have hUn : U ∈ 𝓝 a := by
    filter_upwards [hfev, hRev, hDne, hrev] with y h1 h2 h3 h4 using ⟨h1, h2, h3, h4⟩
  set Z : Set (Fin n → ℝ) := {y | (fun z => (f z).im) y = 0} ∩ U with hZ
  have hF : HasFDerivAt (fun z => (f z).im) (Complex.imCLM.comp (fderiv ℝ f a)) a :=
    Complex.imCLM.hasFDerivAt.comp a (hf.differentiableAt one_ne_zero).hasFDerivAt
  have hc : ∀ᶠ y in 𝓝 a, ContinuousAt (fun z => (f z).im) y := by
    filter_upwards [hfev] with y hy
    exact Complex.continuous_im.continuousAt.comp hy.continuousAt
  have htan : ∀ u, Complex.imCLM.comp (fderiv ℝ f a) u = 0 → u ∈ tangentConeAt ℝ Z a := by
    intro u hu
    rw [hZ, tangentConeAt_inter_nhds hUn]
    exact ker_subset_tangentCone_zeroSet hF him hc hD hu
  have haZ : a ∈ Z := ⟨him, mem_of_mem_nhds hUn⟩
  refine det_hessMat_eq_zero_of_cut hn haZ ?_ (Complex.imCLM.comp (fderiv ℝ f a)) hD htan
  intro y hy i
  obtain ⟨hy1, hy2, hy3, hy4, hy5⟩ := hy
  exact coordDeriv_eq_zero_of_cut hlam hφ
    ((hy2.differentiableAt one_ne_zero).hasFDerivAt) hy3.continuousAt hy5 hy1 hy4 i

end Lightlike.SpinFoam.CutAssemble
