import Lightlike.Asymptotics.Tauberian.ComplexLaplace
import Lightlike.Asymptotics.Tauberian.CrossingBound
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# The crossing measure

`crossingDensity a` is continuous on `[0, ∞)` (locally uniform convergence of the series), hence measurable
on `(0, ∞)`; the crossing measure `rho0 a = δ₀ + crossingDensity a dx` on `(0, ∞)` has complex Laplace
transform `e^{a/z}` (`laplaceC_rho0`), the vacuum contribution of the dual channel in MZ (2.7).
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace Lightlike.Tauberian

lemma continuousOn_crossingTerm (a : ℝ) (k : ℕ) : Continuous (crossingTerm a k) := by
  unfold crossingTerm; fun_prop

lemma continuousOn_crossingDensity {a : ℝ} (ha : 0 < a) : ContinuousOn (crossingDensity a) (Ici 0) := by
  refine continuousOn_of_locally_continuousOn fun x hx => ?_
  obtain ⟨N, hN⟩ := exists_nat_gt x
  refine ⟨Iio ((N : ℝ) + 1), isOpen_Iio, by simp only [mem_Iio]; linarith, ?_⟩
  set u : ℕ → ℝ := fun k => a * (a * ((N : ℝ) + 1)) ^ k / (k.factorial : ℝ) with hu
  have hsum : Summable u := by
    have := (hasSum_exp_div (z := a * ((N : ℝ) + 1))).summable.mul_left a
    refine this.congr fun k => ?_
    simp only [hu]; ring
  have hbd : ∀ (k : ℕ) (y : ℝ), y ∈ Ico (0 : ℝ) ((N : ℝ) + 1) → ‖crossingTerm a k y‖ ≤ u k := by
    intro k y hy
    have hy0 : 0 ≤ y := hy.1
    have hy1 : y < (N : ℝ) + 1 := hy.2
    rw [Real.norm_of_nonneg (crossingTerm_nonneg ha k hy0)]
    unfold crossingTerm
    have h1 : a ^ (k + 1) * y ^ k = a * (a * y) ^ k := by rw [pow_succ, mul_pow]; ring
    rw [h1]
    have h2 : (a * y) ^ k ≤ (a * ((N : ℝ) + 1)) ^ k :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hy1.le ha.le) k
    have hf : (0 : ℝ) < k.factorial := Nat.cast_pos.2 (Nat.factorial_pos k)
    have hf1 : (1 : ℝ) ≤ ((k + 1).factorial : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
    simp only [hu]
    calc a * (a * y) ^ k / (((k + 1).factorial : ℝ) * (k.factorial : ℝ))
        ≤ a * (a * y) ^ k / (k.factorial : ℝ) := by
          refine div_le_div_of_nonneg_left (by positivity) hf ?_
          nlinarith
      _ ≤ a * (a * ((N : ℝ) + 1)) ^ k / (k.factorial : ℝ) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h2 ha.le) hf.le
  have hC : ContinuousOn (fun y => ∑' n, crossingTerm a n y) (Ico (0 : ℝ) ((N : ℝ) + 1)) :=
    continuousOn_tsum (s := Ico (0 : ℝ) ((N : ℝ) + 1)) (u := u)
      (fun k => (continuousOn_crossingTerm a k).continuousOn) hsum hbd
  refine hC.mono ?_
  intro y hy
  exact ⟨hy.1, hy.2⟩

end Lightlike.Tauberian
