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

/-- The derivative of a Lipschitz curve on `[a, b]` is integrable there. -/
theorem lipschitz_intervalIntegrable_deriv {f : ℝ → E} {a b : ℝ} {K : NNReal} (hab : a ≤ b)
    (hf : LipschitzOnWith K f (Icc a b)) : IntervalIntegrable (deriv f) volume a b := by
  let _ : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  have hbd : ∀ t ∈ Ioo a b, ‖deriv f t‖ ≤ K := fun t ht =>
    norm_deriv_le_of_lipschitzOn (Icc_mem_nhds ht.1 ht.2) hf
  have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ b := by
    simpa using (Set.countable_singleton b).ae_notMem (volume : Measure ℝ)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine Measure.integrableOn_of_bounded (μ := volume) (M := K) (by simp)
    (measurable_deriv f).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hne] with t htb ht
  exact hbd t ⟨ht.1, lt_of_le_of_ne ht.2 htb⟩

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

/-- **A functional that is increasing along a Lipschitz curve almost everywhere is increasing.**
If `λ (F' t) > 0` for almost every `t`, then `t ↦ λ (F t)` is nondecreasing on `[a, b]` and strictly
larger at `b` than at `a`. -/
theorem functional_increasing_of_ae_pos {F : ℝ → E} {a b : ℝ} {K : NNReal} (hab : a < b)
    (hF : LipschitzOnWith K F (Icc a b)) (lam : E →L[ℝ] ℝ)
    (hpos : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo a b → 0 < lam (deriv F t)) :
    (∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → lam (F s) ≤ lam (F t)) ∧ lam (F a) < lam (F b) := by
  have hg : LipschitzOnWith (‖lam‖₊ * K) (fun t => lam (F t)) (Icc a b) :=
    lam.lipschitzWith.comp_lipschitzOnWith hF
  have hdiff := lipschitz_ae_differentiableAt hF
  have hderiv : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo a b → 0 < deriv (fun t => lam (F t)) t := by
    filter_upwards [hdiff, hpos] with t h1 h2 ht
    have hd := h1 ht
    have : deriv (fun t => lam (F t)) t = lam (deriv F t) :=
      (lam.hasFDerivAt.comp_hasDerivAt t hd.hasDerivAt).deriv
    rw [this]; exact h2 ht
  set f : ℝ → ℝ := fun t => lam (F t) with hf
  have hftc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
      ∫ x in s..t, deriv f x = f t - f s := fun s hs t ht hst =>
    lipschitz_integral_deriv hst (hg.mono (Icc_subset_Icc hs.1 ht.2))
  have hint := lipschitz_intervalIntegrable_deriv hab.le hg
  have hne2 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ a ∧ x ≠ b := by
    have h1 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ a := by
      simpa using (Set.countable_singleton a).ae_notMem (volume : Measure ℝ)
    have h2 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ b := by
      simpa using (Set.countable_singleton b).ae_notMem (volume : Measure ℝ)
    filter_upwards [h1, h2] with x hx1 hx2 using ⟨hx1, hx2⟩
  have hnn : ∀ s t : ℝ, s ∈ Icc a b → t ∈ Icc a b → ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Icc s t → 0 ≤ deriv f x := by
    intro s t hs ht
    filter_upwards [hderiv, hne2] with x hx hxe hxm
    exact (hx ⟨lt_of_le_of_ne (hs.1.trans hxm.1) (Ne.symm hxe.1),
      lt_of_le_of_ne (hxm.2.trans ht.2) hxe.2⟩).le
  refine ⟨fun s hs t ht hst => ?_, ?_⟩
  · have h1 := hftc s hs t ht hst
    have h2 : 0 ≤ ∫ x in s..t, deriv f x := by
      refine intervalIntegral.integral_nonneg_of_ae_restrict hst ?_
      have := (ae_restrict_iff' measurableSet_Icc).2 (hnn s t hs ht)
      exact this
    simp only [hf] at h1 ⊢
    linarith
  · have h1 := hftc a ⟨le_rfl, hab.le⟩ b ⟨hab.le, le_rfl⟩ hab.le
    have h2 : 0 < ∫ x in a..b, deriv f x := by
      rw [intervalIntegral.integral_of_le hab.le]
      have hnn' : 0 ≤ᵐ[volume.restrict (Ioc a b)] deriv f := by
        rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
        filter_upwards [hderiv, hne2] with x hx hxe hxm
        exact (hx ⟨hxm.1, lt_of_le_of_ne hxm.2 hxe.2⟩).le
      rw [integral_pos_iff_support_of_nonneg_ae hnn' (hint.1)]
      have hsupp : Function.support (deriv f) =ᵐ[volume.restrict (Ioc a b)] (Set.univ : Set ℝ) := by
        have : ∀ᵐ x ∂(volume.restrict (Ioc a b)), x ∈ Function.support (deriv f) ↔ x ∈ (Set.univ : Set ℝ) := by
          rw [ae_restrict_iff' measurableSet_Ioc]
          filter_upwards [hderiv, hne2] with x hx hxe hxm
          have hpos := hx ⟨hxm.1, lt_of_le_of_ne hxm.2 hxe.2⟩
          simp only [Function.mem_support, ne_eq, mem_univ, iff_true]
          exact hpos.ne'
        exact this.mono fun x hx => propext hx
      rw [measure_congr hsupp, Measure.restrict_apply_univ]
      simp [hab]
    simp only [hf] at h1 ⊢
    linarith

end Lightlike.Causal
