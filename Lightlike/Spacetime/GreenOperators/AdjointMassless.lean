import Lightlike.Spacetime.GreenOperators.IntegralForm
import Lightlike.Spacetime.GreenOperators.Advanced

/-!
# Adjointness of the retarded and advanced Green operators (massless, 1+1 Minkowski space)

For `f`, `h` continuous with compact support, `∫ f · G⁺h = ∫ (G⁻f) · h`
(`retarded_advanced_adjoint`), by Fubini from the integral forms `retardedSol_eq_integral`
and `advancedSol_eq_integral`: both sides are `-(1/2) ∬ f(p) h(q) 1[q ≤ p]`.

Limits: massless operator `-∂ₜ² + ∂ₓ²` on `1+1` Minkowski space only; the massive and the curved cases
(Bär–Ginoux–Pfäffle, Prop. 3.4.4) are not covered by this file.
-/

open Set MeasureTheory

noncomputable section

namespace Lightlike.GreenOperators

/-- **The retarded and advanced Green operators are adjoint** (massless, `1+1` Minkowski). -/
theorem retarded_advanced_adjoint {f h : ℝ × ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hh : Continuous h) (hhc : HasCompactSupport h) :
    ∫ p, f p * retardedSol h p = ∫ q, advancedSol f q * h q := by
  set C : Set ((ℝ × ℝ) × (ℝ × ℝ)) := {z | causalLE2 z.2 z.1} with hC
  have hCc : IsClosed C := by
    have : C = {z : (ℝ × ℝ) × (ℝ × ℝ) | |z.1.2 - z.2.2| ≤ z.1.1 - z.2.1} := rfl
    rw [this]
    exact isClosed_le (by fun_prop) (by fun_prop)
  set F : (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun z => f z.1 * h z.2 * C.indicator 1 z with hF
  have hfi : Integrable f := hf.integrable_of_hasCompactSupport hfc
  have hhi : Integrable h := hh.integrable_of_hasCompactSupport hhc
  have hFi : Integrable F (volume.prod volume) := by
    have h1 : Integrable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => f z.1 * h z.2) (volume.prod volume) :=
      hfi.mul_prod hhi
    refine h1.norm.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · exact (((hf.comp continuous_fst).mul (hh.comp continuous_snd)).aestronglyMeasurable).mul
        ((measurable_const.indicator hCc.measurableSet).aestronglyMeasurable)
    · by_cases hz : z ∈ C
      · simp [hF, hz]
      · simp only [hF, Set.indicator_of_notMem hz, mul_zero, norm_zero]
        exact norm_nonneg _
  have hsw := integral_integral_swap (f := fun p q => F (p, q)) hFi
  have hL : ∀ p, f p * retardedSol h p = -(1 / 2 : ℝ) * ∫ q, F (p, q) := by
    intro p
    rw [retardedSol_eq_integral hh p]
    have : ∫ q, F (p, q) = f p * ∫ q in {q : ℝ × ℝ | causalLE2 q p}, h q := by
      rw [← integral_const_mul]
      have hS : MeasurableSet {q : ℝ × ℝ | causalLE2 q p} := by
        have : IsClosed {q : ℝ × ℝ | causalLE2 q p} := by
          show IsClosed {q : ℝ × ℝ | |p.2 - q.2| ≤ p.1 - q.1}
          exact isClosed_le (by fun_prop) (by fun_prop)
        exact this.measurableSet
      rw [← integral_indicator hS]
      refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
      by_cases hq : causalLE2 q p
      · have hz : (p, q) ∈ C := hq
        simp [hF, hz, Set.indicator_of_mem, hq]
      · have hz : (p, q) ∉ C := hq
        simp [hF, hz, hq]
    rw [this]; ring
  have hR : ∀ q, advancedSol f q * h q = -(1 / 2 : ℝ) * ∫ p, F (p, q) := by
    intro q
    rw [advancedSol_eq_integral hf q]
    have : ∫ p, F (p, q) = h q * ∫ p in {p : ℝ × ℝ | causalLE2 q p}, f p := by
      rw [← integral_const_mul]
      have hS : MeasurableSet {p : ℝ × ℝ | causalLE2 q p} := by
        have : IsClosed {p : ℝ × ℝ | causalLE2 q p} := by
          show IsClosed {p : ℝ × ℝ | |p.2 - q.2| ≤ p.1 - q.1}
          exact isClosed_le (by fun_prop) (by fun_prop)
        exact this.measurableSet
      rw [← integral_indicator hS]
      refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      by_cases hp : causalLE2 q p
      · have hz : (p, q) ∈ C := hp
        simp [hF, hz, hp]
        ring
      · have hz : (p, q) ∉ C := hp
        simp [hF, hz, hp]
    rw [this]; ring
  simp_rw [hL, hR, integral_const_mul]
  rw [hsw]

end Lightlike.GreenOperators
