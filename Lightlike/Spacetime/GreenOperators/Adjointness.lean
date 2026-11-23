import Mathlib
import Lightlike.Spacetime.GreenOperators.GreenIdentities

/-!
# Integration tools for the adjointness of the Green operators on 1+1 Minkowski space

Supporting file for G1-021 (SC6; Bär–Ginoux–Pfäffle 2007, source key `bgp-2007`).
The identity `∫ f · G⁺h = ∫ (G⁻f) · h` is proved by integrating the divergence
`(P v) u - v (P u) = ∂(…)` of a vector field supported in `supp u ∩ supp v`, where `u = G⁺ h`,
`v = G⁻ f`.  This file provides the two analytic ingredients:

* `integral_fderiv_eq_zero`: the integral of a directional derivative of a `C¹` function with compact
  support vanishes;
* `isCompact_tsupport_inter_of_null_bounds`: if `u` vanishes outside `{t - x ≥ α, t + x ≥ β}` and `v`
  vanishes outside `{t - x ≤ α', t + x ≤ β'}` then `tsupport u ∩ tsupport v` is compact.

This is a supporting result; no catalogue entry.
-/

open Set MeasureTheory

namespace Lightlike.GreenOperators

/-- The integral of a directional derivative of a `C¹` function with compact support is zero. -/
theorem integral_fderiv_eq_zero {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (v : ℝ × ℝ) : ∫ x, fderiv ℝ g x v = 0 := by
  have hcont : Continuous (fun x => fderiv ℝ g x v) :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcs : HasCompactSupport (fun x => fderiv ℝ g x v) :=
    (hc.fderiv ℝ).comp_left (g := fun L : (ℝ × ℝ) →L[ℝ] ℝ => L v) (by simp)
  have hint : Integrable (fun x => fderiv ℝ g x v) volume := hcont.integrable_of_hasCompactSupport hcs
  have hgint : Integrable g volume := hg.continuous.integrable_of_hasCompactSupport hc
  have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun _ : ℝ × ℝ => (1 : ℝ)) (g := g) (v := v)
    (by simp) (by simpa using hint) (by simpa using hgint)
    (fun x _ => differentiableAt_const _) (fun x _ => (hg.differentiable one_ne_zero) x)
  simpa using this

/-- The closed box `{α ≤ t - x ≤ α', β ≤ t + x ≤ β'}` is compact. -/
lemma isCompact_nullBox (α α' β β' : ℝ) :
    IsCompact {p : ℝ × ℝ | α ≤ p.1 - p.2 ∧ p.1 - p.2 ≤ α' ∧ β ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ β'} := by
  have hsub : {p : ℝ × ℝ | α ≤ p.1 - p.2 ∧ p.1 - p.2 ≤ α' ∧ β ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ β'} ⊆
      Icc ((α + β) / 2) ((α' + β') / 2) ×ˢ Icc ((β - α') / 2) ((β' - α) / 2) := by
    rintro ⟨t, x⟩ ⟨h1, h2, h3, h4⟩
    simp only [mem_prod, mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only at h1 h2 h3 h4 <;> linarith
  refine (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset ?_ hsub
  have c1 : Continuous (fun p : ℝ × ℝ => p.1 - p.2) := continuous_fst.sub continuous_snd
  have c2 : Continuous (fun p : ℝ × ℝ => p.1 + p.2) := continuous_fst.add continuous_snd
  simp only [ofPred_and]
  exact (isClosed_le continuous_const c1).inter ((isClosed_le c1 continuous_const).inter
    ((isClosed_le continuous_const c2).inter (isClosed_le c2 continuous_const)))

/-- If `u` vanishes outside `{t - x ≥ α, t + x ≥ β}` and `v` vanishes outside
`{t - x ≤ α', t + x ≤ β'}`, then `tsupport u ∩ tsupport v` is compact. -/
theorem isCompact_tsupport_inter_of_null_bounds {u v : ℝ × ℝ → ℝ} {α α' β β' : ℝ}
    (hu : ∀ p, u p ≠ 0 → α ≤ p.1 - p.2 ∧ β ≤ p.1 + p.2)
    (hv : ∀ p, v p ≠ 0 → p.1 - p.2 ≤ α' ∧ p.1 + p.2 ≤ β') :
    IsCompact (tsupport u ∩ tsupport v) := by
  have c1 : Continuous (fun p : ℝ × ℝ => p.1 - p.2) := continuous_fst.sub continuous_snd
  have c2 : Continuous (fun p : ℝ × ℝ => p.1 + p.2) := continuous_fst.add continuous_snd
  have hU : tsupport u ⊆ {p : ℝ × ℝ | α ≤ p.1 - p.2 ∧ β ≤ p.1 + p.2} := by
    refine closure_minimal (fun p hp => hu p hp) ?_
    simp only [ofPred_and]
    exact (isClosed_le continuous_const c1).inter (isClosed_le continuous_const c2)
  have hV : tsupport v ⊆ {p : ℝ × ℝ | p.1 - p.2 ≤ α' ∧ p.1 + p.2 ≤ β'} := by
    refine closure_minimal (fun p hp => hv p hp) ?_
    simp only [ofPred_and]
    exact (isClosed_le c1 continuous_const).inter (isClosed_le c2 continuous_const)
  refine (isCompact_nullBox α α' β β').of_isClosed_subset
    (isClosed_tsupport u |>.inter (isClosed_tsupport v)) ?_
  rintro p ⟨hp1, hp2⟩
  exact ⟨(hU hp1).1, (hV hp2).1, (hU hp1).2, (hV hp2).2⟩

end Lightlike.GreenOperators
