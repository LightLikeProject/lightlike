import Lightlike.Asymptotics.Karamata.Abelian

/-!
# Karamata's Tauberian theorem: a non-vacuity test

For Lebesgue measure on `[0, ∞)` the Laplace transform is `1 / β` (`laplace_lebesgue`), so the hypotheses of
`karamata_tauberian` hold with `C = 1`, `α = 1`, and the theorem gives `ρ [0, X] / X → 1 / Γ(2) = 1`
(`karamata_lebesgue`), in agreement with `ρ [0, X] = X`.

Tests; no catalogue entry.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace Lightlike.Karamata

open Lightlike.Tauberian

/-- The Laplace transform of Lebesgue measure on `[0, ∞)` is `1 / β`. -/
lemma laplace_lebesgue {β : ℝ} (hβ : 0 < β) : laplace (volume.restrict (Ici (0 : ℝ))) β = 1 / β := by
  unfold laplace
  rw [integral_Ici_eq_integral_Ioi, integral_exp_mul_Ioi (by linarith : -β < 0), mul_zero,
    Real.exp_zero, neg_div_neg_eq]

/-- **Non-vacuity of Karamata's theorem**: Lebesgue measure on `[0, ∞)` satisfies its hypotheses with
`C = 1`, `α = 1`. -/
theorem karamata_lebesgue :
    Tendsto (fun X => counting (volume.restrict (Ici (0 : ℝ))) X / X ^ (1 : ℝ)) atTop
      (𝓝 (1 / Real.Gamma (1 + 1))) := by
  have hρ : (volume.restrict (Ici (0 : ℝ))) (Iio 0) = 0 := by
    rw [Measure.restrict_apply measurableSet_Iio]
    have h : Iio (0 : ℝ) ∩ Ici 0 = ∅ := by
      ext x
      simp
    rw [h, measure_empty]
  have hint : ∀ β : ℝ, 0 < β →
      Integrable (fun x : ℝ => Real.exp (-β * x)) (volume.restrict (Ici (0 : ℝ))) := by
    intro β hβ
    have h := exp_neg_integrableOn_Ioi 0 hβ
    rw [← integrableOn_Ici_iff_integrableOn_Ioi] at h
    exact h
  refine karamata_tauberian hρ hint one_pos one_pos ?_
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with β hβ
  have hβ' : (0 : ℝ) < β := hβ
  rw [laplace_lebesgue hβ', Real.rpow_one, one_div, inv_mul_cancel₀ hβ'.ne']

end Lightlike.Karamata
