import Lightlike.Spacetime.Causal.CurveOps

/-!
# Lorentzian length of a curve (row G1-007)

The *Lorentzian length* (proper time) of a locally Lipschitz curve `γ : ℝ → M` on `[a, b]` in a
Lorentzian manifold `(M, g)` is
`L(γ) = ∫ₐᵇ √(-g(γ', γ')) dt`,
with the convention `√x = 0` for `x ≤ 0`, so only the timelike part of the velocity counts. The
integral is a Lebesgue integral with values in `ℝ≥0∞`: this avoids any integrability hypothesis, and
the length of a causal curve is finite anyway (a locally Lipschitz curve has bounded chart velocity).
The velocity is taken along `[a, b]` (`Causal.velocity I γ (Icc a b)`), as in `Causal.IsCurveWith`.

This is the first object of the row: the Lorentzian length is the quantity that Hawking's
cosmological singularity theorem (milestone CO3) bounds, "no past-directed timelike curve from the
Cauchy surface longer than `-3/C`". The maximizing-geodesic step is not part of this file.

## Main definitions

* `Causal.lorentzSpeed g γ s t`: the integrand `√(-g(γ'(t), γ'(t)))`, in `ℝ≥0∞`.
* `Causal.lorentzLength g γ a b`: the Lorentzian length of `γ` on `[a, b]`.

## Main statements

* `Causal.lorentzLength_self`: a degenerate interval has length `0`.
* `Causal.lorentzLength_const`: a constant curve has length `0`.
* `Causal.lorentzLength_add`: additivity of the length at an interior parameter.

## References

* S. W. Hawking and G. F. R. Ellis, *The Large Scale Structure of Space-Time*, Cambridge University
  Press (1973), Section 6.2 (the length of a timelike curve).
-/

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff ENNReal

noncomputable section

namespace Lightlike

namespace Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} (g : LorentzianMetric I M n)

/-- The **Lorentzian speed** `√(-g(γ'(t), γ'(t)))` of a curve `γ` along the set `s` at the
parameter `t`, with values in `ℝ≥0∞`; it is `0` wherever the velocity is not timelike (because
`√x = 0` for `x ≤ 0`). -/
def lorentzSpeed (γ : ℝ → M) (s : Set ℝ) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (√(-(g.g (γ t) (velocity I γ s t) (velocity I γ s t))))

/-- The **Lorentzian length** (proper time) `∫ₐᵇ √(-g(γ', γ')) dt` of a curve `γ` on `[a, b]`,
with values in `ℝ≥0∞`. The velocity is taken along `[a, b]`; for a locally Lipschitz curve it exists
almost everywhere. -/
def lorentzLength (γ : ℝ → M) (a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Icc a b, lorentzSpeed g γ (Icc a b) t

/-- A degenerate parameter interval gives length `0`. -/
theorem lorentzLength_self (γ : ℝ → M) (a : ℝ) : lorentzLength g γ a a = 0 := by
  unfold lorentzLength
  rw [Icc_self]
  exact setLIntegral_measure_zero _ _ (by simp)

/-- A **constant curve** has length `0`: its velocity is `0`. -/
theorem lorentzLength_const (p : M) (a b : ℝ) : lorentzLength g (fun _ => p) a b = 0 := by
  have hv : ∀ t, velocity I (fun _ : ℝ => p) (Icc a b) t = 0 := fun t => by
    unfold velocity
    rw [mfderivWithin_const]
    rfl
  unfold lorentzLength lorentzSpeed
  simp [hv]

/-- The speed along a subinterval agrees almost everywhere on the subinterval with the speed along
the whole interval, for a curve with an almost everywhere defined velocity. -/
theorem lorentzSpeed_ae_restrict {P : ∀ x : M, TangentSpace I x → Prop} {γ : ℝ → M} {a b c d : ℝ}
    (h : IsCurveWith (I := I) P γ (Icc a b)) (hsub : Icc c d ⊆ Icc a b) (hcd : c < d) :
    ∀ᵐ t ∂(volume.restrict (Icc c d)),
      lorentzSpeed g γ (Icc c d) t = lorentzSpeed g γ (Icc a b) t := by
  have h1 := ae_mono (Measure.restrict_mono hsub le_rfl) h.ae_velocity
  filter_upwards [ae_restrict_mem measurableSet_Icc, h1] with t ht ⟨h2, _⟩
  have hu : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Icc c d) t :=
    (uniqueDiffOn_Icc hcd t ht).uniqueMDiffWithinAt
  have hv : velocity I γ (Icc c d) t = velocity I γ (Icc a b) t := by
    unfold velocity
    rw [h2.mfderivWithin_mono hu hsub]
  unfold lorentzSpeed
  rw [hv]

/-- **Additivity of the length.** For a curve with an almost everywhere defined velocity on
`[a, c]` and `a ≤ b ≤ c`, the length on `[a, c]` is the sum of the lengths on `[a, b]` and
`[b, c]`. -/
theorem lorentzLength_add {P : ∀ x : M, TangentSpace I x → Prop} {γ : ℝ → M} {a b c : ℝ}
    (h : IsCurveWith (I := I) P γ (Icc a c)) (hab : a ≤ b) (hbc : b ≤ c) :
    lorentzLength g γ a c = lorentzLength g γ a b + lorentzLength g γ b c := by
  rcases hab.eq_or_lt with rfl | hab
  · rw [lorentzLength_self, zero_add]
  rcases hbc.eq_or_lt with rfl | hbc
  · rw [lorentzLength_self, add_zero]
  have e : Icc a c = Icc a b ∪ Ioc b c := (Icc_union_Ioc_eq_Icc hab.le hbc.le).symm
  have hd : Disjoint (Icc a b) (Ioc b c) :=
    Set.disjoint_left.2 fun x hx hx' => absurd hx.2 (not_le.2 hx'.1)
  have hu := lintegral_union (μ := volume) (f := lorentzSpeed g γ (Icc a c))
    measurableSet_Ioc hd
  rw [← e] at hu
  unfold lorentzLength
  rw [hu]
  congr 1
  · refine lintegral_congr_ae ?_
    filter_upwards [lorentzSpeed_ae_restrict g h (Icc_subset_Icc le_rfl hbc.le) hab] with t ht
    exact ht.symm
  · rw [setLIntegral_congr Ioc_ae_eq_Icc]
    refine lintegral_congr_ae ?_
    filter_upwards [lorentzSpeed_ae_restrict g h (Icc_subset_Icc hab.le le_rfl) hbc] with t ht
    exact ht.symm

end Causal

end Lightlike
