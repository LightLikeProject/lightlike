import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# A smooth cutoff on the line (G1-012, step D4)

For an open set `I ∋ a` there is a smooth `χ : ℝ → ℝ` with `χ a = 1`, `0 ≤ χ ≤ 1`, supported in a compact subinterval
of `I`.
-/

open Set Metric
open scoped ContDiff

namespace Lightlike.Penrose

/-- **A smooth cutoff supported in `I`.** -/
theorem exists_cutoff {I : Set ℝ} (hI : IsOpen I) {a : ℝ} (ha : a ∈ I) :
    ∃ (χ : ℝ → ℝ) (r : ℝ), 0 < r ∧ Icc (a - r) (a + r) ⊆ I ∧ ContDiff ℝ ∞ χ ∧ χ a = 1 ∧
      (∀ t, 0 ≤ χ t ∧ χ t ≤ 1) ∧ (∀ t, χ t ≠ 0 → t ∈ Icc (a - r) (a + r)) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hI a ha
  set r : ℝ := ε / 2 with hr
  have hrpos : 0 < r := by positivity
  let b : ContDiffBump a := ⟨r / 2, r, by positivity, by linarith⟩
  refine ⟨fun t => b t, r, hrpos, ?_, b.contDiff, b.one_of_mem_closedBall (mem_closedBall_self (by positivity)),
    fun t => ⟨b.nonneg, b.le_one⟩, ?_⟩
  · intro t ht
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  · intro t ht
    have : t ∈ Function.support b := ht
    rw [b.support_eq] at this
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at this
    exact ⟨by linarith [this.1], by linarith [this.2]⟩

/-- **A smooth function on an open set times a cutoff supported inside it is smooth on the line.** -/
theorem contDiff_cutoff_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {I : Set ℝ} (hI : IsOpen I)
    {χ : ℝ → ℝ} {a r : ℝ} (hχ : ContDiff ℝ ∞ χ) (hsupp : ∀ t, χ t ≠ 0 → t ∈ Icc (a - r) (a + r))
    (hsub : Icc (a - r) (a + r) ⊆ I) {f : ℝ → E} (hf : ContDiffOn ℝ ∞ f I) :
    ContDiff ℝ ∞ (fun t => χ t • f t) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : t ∈ Icc (a - r) (a + r)
  · exact (hχ.contDiffAt).smul (hf.contDiffAt (hI.mem_nhds (hsub ht)))
  · -- `χ` vanishes near `t`
    have hnhds : (Icc (a - r) (a + r))ᶜ ∈ nhds t := isClosed_Icc.isOpen_compl.mem_nhds ht
    have hzero : (fun s => χ s • f s) =ᶠ[nhds t] fun _ => (0 : E) := by
      filter_upwards [hnhds] with s hs
      have : χ s = 0 := by
        by_contra hne
        exact hs (hsupp s hne)
      simp [this]
    exact (contDiffAt_const).congr_of_eventuallyEq hzero

end Lightlike.Penrose
