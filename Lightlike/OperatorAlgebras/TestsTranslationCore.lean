import Lightlike.OperatorAlgebras.TranslationCore
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Trust checks for the `C_c^∞` core of the momentum operator

The core statement is not vacuous: a bump function is a `C_c^∞` function whose class in `L²(ℝ)` is nonzero,
so `smoothCS` is not the zero subspace. The sign of the generator on such functions (`-i d/dx`, not
`+i d/dx`) is the check `translationGroup_generator_ne` of `GeneratorTranslation.lean`.
-/

open MeasureTheory
open scoped ContDiff

namespace Lightlike.OperatorAlgebras

/-- A smooth bump function centred at `0`. -/
noncomputable def bumpRB : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The bump function as a complex function. -/
noncomputable def bumpR : ℝ → ℂ := fun x => ((bumpRB x : ℝ) : ℂ)

lemma bumpR_contDiff : ContDiff ℝ ∞ bumpR :=
  Complex.ofRealCLM.contDiff.comp bumpRB.contDiff

lemma bumpR_compact : HasCompactSupport bumpR := by
  refine bumpRB.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)

/-- **Non-vacuity**: the class of a bump function is a nonzero element of `smoothCS`. -/
theorem smoothCS_exists_ne_zero : ∃ f ∈ smoothCS, f ≠ 0 := by
  refine ⟨ofCS bumpR_contDiff.continuous bumpR_compact,
    mem_smoothCS_iff.2 ⟨bumpR, bumpR_contDiff, bumpR_compact, rfl⟩, ?_⟩
  intro h
  have h0 : (ofCS bumpR_contDiff.continuous bumpR_compact : ℝ → ℂ) =ᵐ[volume] 0 :=
    Lp.eq_zero_iff_ae_eq_zero.1 h
  have h1 : (ofCS bumpR_contDiff.continuous bumpR_compact : ℝ → ℂ) =ᵐ[volume] bumpR :=
    MemLp.coeFn_toLp _
  have h2 : bumpR =ᵐ[volume] (0 : ℝ → ℂ) := h1.symm.trans h0
  have h3 : bumpR = 0 := (Continuous.ae_eq_iff_eq volume bumpR_contDiff.continuous
    continuous_const).1 h2
  have h4 : bumpR 0 = 1 := by
    simp [bumpR, bumpRB.one_of_mem_closedBall (Metric.mem_closedBall_self bumpRB.rIn_pos.le)]
  rw [h3] at h4
  simp at h4

end Lightlike.OperatorAlgebras
