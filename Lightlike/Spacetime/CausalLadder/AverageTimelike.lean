import Lightlike.Spacetime.CausalLadder.ConeAlgebra
import Lightlike.Spacetime.Causal.ConeConvex

/-!
# The average of future timelike vectors is future timelike

For a Lorentzian form `B` on a finite-dimensional space, with `B X X < 0`, the future timelike vectors
`{v | B v v < 0 ∧ B v X < 0}` form a convex set that is not closed, so the average of a function with
values in it lies a priori only in its closure, the future causal vectors. It is future timelike: it is
nonzero, since `B (·) X` has a strictly negative average, hence has strictly negative product with every
future timelike vector, so `B u u`, the average of `B u (f x)`, is strictly negative.

Supporting lemma for the causal ladder; no catalogue entry.
-/

open MeasureTheory Set

namespace Lightlike

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {n : ℕ} {B : E →L[ℝ] E →L[ℝ] ℝ}

/-- The average of a function that is strictly negative almost everywhere is strictly negative. -/
theorem integral_neg_of_ae_neg {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    [NeZero μ] {g : α → ℝ} (hg : Integrable g μ) (hneg : ∀ᵐ x ∂μ, g x < 0) : ∫ x, g x ∂μ < 0 := by
  have h1 : Integrable (fun x => -g x) μ := hg.neg
  have h2 : 0 ≤ᵐ[μ] fun x => -g x := by
    filter_upwards [hneg] with x hx using by simp only [Pi.zero_apply]; linarith
  have h3 := (integral_pos_iff_support_of_nonneg_ae h2 h1).2 (by
    have : Function.support (fun x => -g x) =ᵐ[μ] Set.univ := by
      filter_upwards [hneg] with x hx
      simp only [Function.mem_support, ne_eq, neg_eq_zero, eq_iff_iff, mem_univ, iff_true]
      exact hx.ne
    rw [measure_congr this]
    simp [NeZero.ne μ])
  rw [integral_neg] at h3
  linarith

/-- **The average of future timelike vectors is future timelike.** -/
theorem IsLorentzianForm.average_futureTimelike (h : IsLorentzianForm n B) {X : E} (hX : B X X < 0)
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] [NeZero μ] {f : α → E}
    (hf : ∀ᵐ x ∂μ, B (f x) (f x) < 0 ∧ B (f x) X < 0) (hfi : Integrable f μ) :
    B (∫ x, f x ∂μ) (∫ x, f x ∂μ) < 0 ∧ B (∫ x, f x ∂μ) X < 0 := by
  set u : E := ∫ x, f x ∂μ with hu
  -- the product with `X`
  have hLX : B u X < 0 := by
    have := (B.flip X).integral_comp_comm hfi
    have h1 : B u X = ∫ x, B (f x) X ∂μ := by simpa [hu] using this.symm
    rw [h1]
    refine integral_neg_of_ae_neg ?_ ?_
    · exact ((B.flip X).integrable_comp hfi)
    · filter_upwards [hf] with x hx using hx.2
  -- `u` is causal: it lies in the closure of the future timelike cone
  have hcl : u ∈ closure {v : E | B v v < 0 ∧ B v X < 0} := by
    have := (h.convex_futureTimelike hX).set_average_mem_closure (μ := μ) (t := univ) (f := f)
      (by simp [NeZero.ne μ]) (by simp) (by simpa using hf) hfi.integrableOn
    simp only [Measure.restrict_univ, average_eq, measureReal_def] at this
    have hpos : 0 < (μ univ).toReal := ENNReal.toReal_pos (by simp [NeZero.ne μ]) (by simp)
    have hmaps : MapsTo (fun v : E => (μ univ).toReal • v) {v : E | B v v < 0 ∧ B v X < 0}
        {v : E | B v v < 0 ∧ B v X < 0} := fun v hv => by
      refine ⟨?_, ?_⟩
      · simp only [map_smul, smul_apply, smul_eq_mul]
        nlinarith [hv.1, mul_pos hpos hpos]
      · simp only [map_smul, smul_apply, smul_eq_mul]
        nlinarith [hv.2]
    have hmap := map_mem_closure (continuous_const_smul ((μ univ).toReal)) this hmaps
    simpa [smul_smul, hpos.ne'] using hmap
  have hQ : B u u ≤ 0 := by
    have : closure {v : E | B v v < 0 ∧ B v X < 0} ⊆ {v : E | B v v ≤ 0} := by
      refine closure_minimal (fun v hv => hv.1.le) (isClosed_le (by fun_prop) continuous_const)
    exact this hcl
  have hu0 : u ≠ 0 := fun h0 => by simp [h0] at hLX
  -- `B u (f x) < 0`
  have hneg : ∀ᵐ x ∂μ, B u (f x) < 0 := by
    filter_upwards [hf] with x hx
    have hle : B u (f x) ≤ 0 := h.nonpos_of_futureCausal hX hQ hx.1.le hLX hx.2
    refine lt_of_le_of_ne hle fun h0 => ?_
    have := h.eq_zero_of_orthogonal_timelike (X := f x) hx.1 h0 hQ
    exact hu0 this
  have := (B u).integral_comp_comm hfi
  refine ⟨?_, hLX⟩
  have h1 : B u u = ∫ x, B u (f x) ∂μ := by simpa [hu] using this.symm
  rw [h1]
  exact integral_neg_of_ae_neg ((B u).integrable_comp hfi) hneg

end Lightlike
