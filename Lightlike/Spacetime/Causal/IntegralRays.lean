import Lightlike.Spacetime.Causal.IntegralCurves

/-!
# Integral curves with no endpoint, from a given point and parameter

The maximal integral curve through a point, translated to start at a given parameter, is an
integral curve on an open interval without a future endpoint; reflecting in the parameter and
reversing the field gives one without a past endpoint.
-/

open Bundle Manifold Set MeasureTheory Filter Topology
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike

namespace Causal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M] [CompleteSpace E] {Y : (x : M) → TangentSpace I x}

/-- **A forward ray**: an integral curve of `Y` on an open interval through `x` at parameter `b`,
with no future endpoint. -/
theorem exists_ray_future (hY : CMDiff 1 (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M)))
    (hY0 : ∀ x, Y x ≠ 0) (x : M) (b : ℝ) :
    ∃ (R : ℝ → M) (D : Set ℝ), IsOpen D ∧ D.OrdConnected ∧ b ∈ D ∧ R b = x ∧
      IsMIntegralCurveOn R Y D ∧ ∀ p, ¬ HasFutureEndpoint R (D ∩ Ici b) p := by
  refine ⟨curveMax Y x ∘ (· - b), {t | t - b ∈ domMax Y x}, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (isOpen_domMax hY x).preimage (continuous_sub_right b)
  · refine ⟨fun u hu v hv z hz => ?_⟩
    exact (ordConnected_domMax (Y := Y) x).out hu hv ⟨by linarith [hz.1], by linarith [hz.2]⟩
  · simpa using zero_mem_domMax hY x
  · simp [curveMax_zero hY]
  · exact (isMIntegralCurveOn_comp_sub (dt := b)).2 (isMIntegralCurveOn_curveMax hY x)
  · intro p hp
    refine curveMax_not_hasFutureEndpoint hY hY0 x p fun U hU => ?_
    obtain ⟨c0, hc0, hc⟩ := hp U hU
    refine ⟨c0 - b, ⟨hc0.1, by simpa using hc0.2⟩, fun t ht hct => ?_⟩
    have := hc (t + b) ⟨by simpa using ht.1, by simpa using ht.2⟩ (by simpa using hct)
    simpa using this

/-- **A backward ray**: an integral curve of `Y` on an open interval through `x` at parameter `a`,
with no past endpoint. -/
theorem exists_ray_past (hY : CMDiff 1 (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M)))
    (hY0 : ∀ x, Y x ≠ 0) (x : M) (a : ℝ) :
    ∃ (L : ℝ → M) (D : Set ℝ), IsOpen D ∧ D.OrdConnected ∧ a ∈ D ∧ L a = x ∧
      IsMIntegralCurveOn L Y D ∧ ∀ p, ¬ HasPastEndpoint L (D ∩ Iic a) p := by
  have hY' : CMDiff 1 (fun x ↦ (⟨x, (-Y) x⟩ : TangentBundle I M)) := hY.neg_section
  obtain ⟨R, D', hDo, hDc, hbD, hRb, hint, hnf⟩ :=
    exists_ray_future (Y := -Y) hY' (fun x => neg_ne_zero.2 (hY0 x)) x (-a)
  have e : ((-1 : ℝ) • (-Y) : (x : M) → TangentSpace I x) = Y := by
    ext x; simp
  refine ⟨R ∘ (· * (-1)), {t | t * (-1) ∈ D'}, hDo.preimage (continuous_id.mul continuous_const), ?_, ?_,
    by simpa using hRb, ?_, ?_⟩
  · refine ⟨fun u hu v hv z hz => ?_⟩
    exact hDc.out hv hu ⟨by linarith [hz.2], by linarith [hz.1]⟩
  · simpa using hbD
  · have := hint.comp_mul (-1)
    rwa [e] at this
  · intro p hp
    refine hnf p fun U hU => ?_
    obtain ⟨c0, hc0, hc⟩ := hp U hU
    refine ⟨-c0, ⟨by simpa using hc0.1, by simp only [mem_Ici]; linarith [show c0 ≤ a from hc0.2]⟩, fun t ht hct => ?_⟩
    have := hc (-t) ⟨by simpa using ht.1, by simp only [mem_Iic]; linarith [show -a ≤ t from ht.2]⟩
      (by linarith [show -c0 ≤ t from hct])
    simpa using this

end Causal

end Lightlike
