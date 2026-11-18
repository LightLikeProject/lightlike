import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.TangentCone.Defs
import Mathlib.Analysis.Calculus.TangentCone.Basic

/-!
# The kernel of a surjective derivative lies in the tangent cone of the level set

Part of the third attempt at the nonlinear Dirac algorithm (`DiracNonlinear`, `DiracWire`): the stage surfaces are zero
sets of regular constraint tuples, and "the evolution velocity is tangent to the surface" must be turned into the
linear condition `Φ'(x) v = 0`. One half, the one that needs the implicit function theorem, is here: if `f` has a
strict derivative `f'` at `a` with `f'` onto a finite-dimensional space, then `ker f'` is contained in the tangent
cone at `a` of the level set `f ⁻¹ {f a}`. The curve in the level set is `t ↦ ψ (t v)` for Mathlib's implicit function
`ψ`, whose derivative at `0` is the inclusion of `ker f'`.
-/

open Filter Topology

namespace Lightlike.Gauge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **`ker f'` is in the tangent cone of the level set** (implicit function theorem). -/
theorem ker_subset_tangentCone_levelSet {f : E → F} {f' : E →L[ℝ] F} {a : E}
    (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) :
    (f'.ker : Set E) ⊆ tangentConeAt ℝ (f ⁻¹' {f a}) a := by
  intro v hv
  set ψ := hf.implicitFunction f f' hf' (f a) with hψ
  have hψd : HasStrictFDerivAt ψ f'.ker.subtypeL 0 := hf.to_implicitFunction hf'
  have hψ0 : ψ 0 = a := hf.implicitFunction_apply_image hf'
  let v' : f'.ker := ⟨v, hv⟩
  have hline : HasDerivAt (fun t : ℝ => ψ (t • v')) (v' : E) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t • v') v' 0 := by
      have := (hasDerivAt_id' (0 : ℝ)).smul_const v'
      simpa using this
    have h2 := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hψd.hasFDerivAt) h1 (by simp)
    exact (by simpa using h2 : HasDerivAt (ψ ∘ fun t : ℝ => t • v') (v' : E) 0)
  have hslope := hasDerivAt_iff_tendsto_slope_zero.mp hline
  let tn : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have htn0 : Tendsto tn atTop (𝓝 0) := by
    simpa [tn, one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have htn : Tendsto tn atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨htn0, Eventually.of_forall fun n => by simp [tn]; positivity⟩
  have hcont : Tendsto (fun n => ψ (tn n • v')) atTop (𝓝 a) := by
    have := hline.continuousAt.tendsto.comp htn0
    simpa [Function.comp_def, hψ0] using this
  refine mem_tangentConeAt_of_seq atTop (fun n : ℕ => ((n : ℝ) + 1)) (fun n => ψ (tn n • v') - a) ?_ ?_ ?_
  · simpa using hcont.sub_const a
  · have hev := hf.map_implicitFunction_eq hf'
    have hp : Tendsto (fun n => ((f a, tn n • v') : F × f'.ker)) atTop (𝓝 (f a, 0)) := by
      refine tendsto_const_nhds.prodMk_nhds ?_
      simpa using htn0.smul_const v'
    filter_upwards [hp.eventually hev] with n hn
    simpa using hn
  · have := hslope.comp htn
    refine this.congr fun n => ?_
    simp [Function.comp_def, tn, hψ0]

end Lightlike.Gauge
