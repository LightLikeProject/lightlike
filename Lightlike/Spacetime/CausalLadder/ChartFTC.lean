import Mathlib

/-!
# The fundamental theorem of calculus for Lipschitz curves, and the chord in a convex set

A Lipschitz curve `f : ℝ → E` into a finite-dimensional space is differentiable almost everywhere
and `∫ₐᵇ f' = f b - f a` (`lipschitz_integral_deriv`; Mathlib has it for real-valued absolutely
continuous functions, and the vector case follows by testing against linear functionals). Hence the
chord `(f b - f a) / (b - a)` is the average of the velocity, so it lies in every closed convex set
that contains the velocity almost everywhere (`chord_mem_of_deriv_mem`). This is the step that turns
a cone condition on the velocity of a causal curve, in a chart, into the same condition on its chord.

Supporting lemmas; no catalogue entry.
-/

open MeasureTheory Set intervalIntegral

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A Lipschitz curve on `[a, b]` is differentiable at almost every point of `(a, b]` but `b`. -/
theorem lipschitz_ae_differentiableAt {f : ℝ → E} {a b : ℝ} {K : NNReal}
    (hf : LipschitzOnWith K f (Icc a b)) :
    ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo a b → DifferentiableAt ℝ f t := by
  have h : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Icc a b → DifferentiableWithinAt ℝ f (Icc a b) t :=
    hf.ae_differentiableWithinAt_of_mem
  filter_upwards [h] with t ht hmem
  exact (ht (Ioo_subset_Icc_self hmem)).differentiableAt (Icc_mem_nhds hmem.1 hmem.2)

/-- **Fundamental theorem of calculus for a Lipschitz curve in a finite-dimensional space.** -/
theorem lipschitz_integral_deriv {f : ℝ → E} {a b : ℝ} {K : NNReal} (hab : a ≤ b)
    (hf : LipschitzOnWith K f (Icc a b)) :
    ∫ t in a..b, deriv f t = f b - f a := by
  let _ : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  have hbd : ∀ t ∈ Ioo a b, ‖deriv f t‖ ≤ K := fun t ht =>
    norm_deriv_le_of_lipschitzOn (Icc_mem_nhds ht.1 ht.2) hf
  have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ b := by
    simpa using (Set.countable_singleton b).ae_notMem (volume : Measure ℝ)
  have hint : IntervalIntegrable (deriv f) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    refine Measure.integrableOn_of_bounded (μ := volume) (M := K) (by simp)
      (measurable_deriv f).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hne] with t htb ht
    exact hbd t ⟨ht.1, lt_of_le_of_ne ht.2 htb⟩
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 fun ℓ => ?_
  have hg : LipschitzOnWith (‖ℓ‖₊ * K) (fun t => ℓ (f t)) (Icc a b) :=
    ℓ.lipschitzWith.comp_lipschitzOnWith hf
  have hac : AbsolutelyContinuousOnInterval (fun t => ℓ (f t)) a b :=
    LipschitzOnWith.absolutelyContinuousOnInterval (by rwa [uIcc_of_le hab]) |>.mono le_rfl
  have hftc := hac.integral_deriv_eq_sub
  rw [← ℓ.intervalIntegral_comp_comm hint, map_sub]
  rw [← hftc]
  refine intervalIntegral.integral_congr_ae ?_
  have hd := lipschitz_ae_differentiableAt hf
  filter_upwards [hd, hne] with t ht htb hmem
  rw [uIoc_of_le hab] at hmem
  have hd' : DifferentiableAt ℝ f t := ht ⟨hmem.1, lt_of_le_of_ne hmem.2 htb⟩
  exact ((ℓ.hasFDerivAt.comp_hasDerivAt t hd'.hasDerivAt).deriv).symm

/-- **The chord of a Lipschitz curve lies in a closed convex set containing its velocity almost
everywhere**: if `deriv f t ∈ K` for almost every `t` then `(f b - f a) / (b - a) ∈ K`. -/
theorem chord_mem_of_deriv_mem {f : ℝ → E} {a b : ℝ} {K : NNReal} {S : Set E} (hab : a < b)
    (hf : LipschitzOnWith K f (Icc a b)) (hS : Convex ℝ S) (hSc : IsClosed S)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo a b → deriv f t ∈ S) :
    (b - a)⁻¹ • (f b - f a) ∈ S := by
  let _ : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  have hbd : ∀ t ∈ Ioo a b, ‖deriv f t‖ ≤ K := fun t ht =>
    norm_deriv_le_of_lipschitzOn (Icc_mem_nhds ht.1 ht.2) hf
  have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ b := by
    simpa using (Set.countable_singleton b).ae_notMem (volume : Measure ℝ)
  have hint : IntegrableOn (deriv f) (Ioc a b) volume := by
    refine Measure.integrableOn_of_bounded (μ := volume) (M := K) (by simp)
      (measurable_deriv f).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hne] with t htb ht
    exact hbd t ⟨ht.1, lt_of_le_of_ne ht.2 htb⟩
  have h0 : (volume : Measure ℝ) (Ioc a b) ≠ 0 := by simp [hab]
  have h1 : (volume : Measure ℝ) (Ioc a b) ≠ ⊤ := by simp
  have hmem := hS.set_average_mem hSc h0 h1 (by
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hd, hne] with t ht htb hmem
    exact ht ⟨hmem.1, lt_of_le_of_ne hmem.2 htb⟩) hint
  rw [setAverage_eq, ← intervalIntegral.integral_of_le hab.le, lipschitz_integral_deriv hab.le hf] at hmem
  simpa [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.2 hab.le)] using hmem

end Lightlike.Causal
