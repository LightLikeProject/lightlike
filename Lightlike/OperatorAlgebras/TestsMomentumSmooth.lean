import Lightlike.OperatorAlgebras.MomentumSmooth
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# Trust checks for `momentumGraphSmooth`

The smooth graph is not trivial: a bump function supported in `(0, 1)` gives a nonzero vector of it. So the
statement of `T-OP1-P6`, that its closure equals the closure of `momentumGraph`, is not about the zero
subspace.
-/

open MeasureTheory Set
open scoped ContDiff

namespace Lightlike.OperatorAlgebras

/-- A smooth bump function centred at `1/2`, with support in the closed ball of radius `1/4`. -/
noncomputable def bumpHalf : ContDiffBump (1 / 2 : ℝ) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

/-- The bump function as a complex function. -/
noncomputable def bumpC : ℝ → ℂ := fun x => ((bumpHalf x : ℝ) : ℂ)

lemma bumpC_contDiff : ContDiff ℝ ∞ bumpC :=
  Complex.ofRealCLM.contDiff.comp bumpHalf.contDiff

lemma bumpC_tsupport : tsupport bumpC ⊆ Ioo (0 : ℝ) 1 := by
  have h1 : tsupport bumpC ⊆ tsupport (bumpHalf : ℝ → ℝ) := by
    refine closure_mono ?_
    intro x hx
    simp only [Function.mem_support, bumpC] at hx ⊢
    exact fun h => hx (by simp [h])
  refine h1.trans ?_
  rw [bumpHalf.tsupport_eq]
  intro x hx
  have : |x - 1 / 2| ≤ 1 / 4 := by simpa [bumpHalf, Metric.mem_closedBall, Real.dist_eq] using hx
  rw [abs_le] at this
  constructor <;> linarith [this.1, this.2]

/-- **Non-vacuity**: `momentumGraphSmooth` contains a nonzero vector. -/
theorem momentumGraphSmooth_ne_bot : momentumGraphSmooth ≠ ⊥ := by
  have hmem : bumpC ∈ testFunctions :=
    ⟨bumpC_contDiff.of_le (by norm_num), bumpC_tsupport⟩
  set f : testFunctions := ⟨bumpC, hmem⟩
  have hs : f ∈ smoothTestFunctions := bumpC_contDiff
  rw [Submodule.ne_bot_iff]
  refine ⟨momentumPairLin f, Submodule.mem_map_of_mem hs, ?_⟩
  intro h0
  have h1 : (momentumPairLin f).1 = 0 := by rw [h0]; rfl
  have h2 : bumpC = 0 := eq_zero_of_classI_eq_zero f.2.1.continuous f.2.2 h1
  have h3 : bumpC (1 / 2) = 0 := by rw [h2]; rfl
  have hb : bumpHalf (1 / 2) = 1 :=
    bumpHalf.one_of_mem_closedBall (Metric.mem_closedBall_self bumpHalf.rIn_pos.le)
  have h4 : bumpC (1 / 2) = 1 := by
    show ((bumpHalf (1 / 2) : ℝ) : ℂ) = 1
    rw [hb]; simp
  rw [h3] at h4; exact zero_ne_one h4

end Lightlike.OperatorAlgebras
