import Lightlike.Spacetime.EHManifold.IntrinsicIntegrand
import Lightlike.Spacetime.EHManifold.PieceLinear

/-!
# Where the perturbation vanishes, the variation vanishes

* `ehFluxDiv_eq_zero_of_eventuallyEq`: the flux divergence vanishes at a point near which the perturbation
  vanishes.
* `pieceVar_eq_zero`: the variation over a piece `A` vanishes when the perturbation vanishes on an open set
  containing `A`.
* `ehIntegrand_eq_zero`: the integrand `⟨G + Λ g, h⟩_g` vanishes where `h` does.

Supporting lemmas for cutting a perturbation into pieces with a partition of unity; no catalogue entry.
-/

open MeasureTheory Set Manifold TopologicalSpace Matrix Filter Metric
open scoped ContDiff ENNReal Topology

noncomputable section

namespace Lightlike

/-- The flux divergence vanishes at a point near which the perturbation vanishes. -/
theorem ehFluxDiv_eq_zero_of_eventuallyEq {n : ℕ} (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun y => g y a b)) (hh : ∀ a b, ContDiff ℝ ∞ (fun y => h y a b))
    (x : Fin n → ℝ) (hz : ∀ a b, (fun z => h z a b) =ᶠ[𝓝 x] fun _ => (0 : ℝ)) :
    ehFluxDiv g h x = 0 := by
  have hev : ∀ᶠ y in 𝓝 x, ∀ a b, (fun z => h z a b) =ᶠ[𝓝 y] fun _ => (0 : ℝ) :=
    eventually_all.2 fun a => eventually_all.2 fun b => (hz a b).eventuallyEq_nhds
  unfold ehFluxDiv
  refine Finset.sum_eq_zero fun ρ _ => ?_
  have hF : (fun y => √|(g y).det| * Wvec g h ρ y) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [hev] with y hy
    have hW : Wvec g h ρ y = 0 := by
      unfold Wvec
      simp [dChristoffel_eq_zero g h hg hh y hy]
    show √|(g y).det| * Wvec g h ρ y = 0
    rw [hW, mul_zero]
  unfold pd
  rw [hF.fderiv_eq]
  simp

set_option synthInstance.maxHeartbeats 400000

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]

omit [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] in
/-- The integrand `⟨G + Λ g, h⟩_g` vanishes where `h` does. -/
theorem ehIntegrand_eq_zero (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)
    (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (Λ : ℝ) {p : M} (hp : h.h p = 0) :
    ehIntegrand g h Λ p = 0 := by
  have hB : (h.h p).toBilinForm = 0 := by
    rw [hp]
    exact LinearMap.ext₂ fun u v => rfl
  unfold ehIntegrand formContract
  rw [hB, map_zero, Matrix.mul_zero, Matrix.trace_zero]

/-- **The variation over a piece vanishes** when the perturbation vanishes on an open set containing the
piece. -/
theorem pieceVar_eq_zero (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M)
    (x₀ : M) {c : Fin n → ℝ} (φ : ContDiffBump c)
    (hball : ball c φ.rOut ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) (Λ : ℝ) {T A O : Set M}
    (hT : IsCompact T) (hT0 : T ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source)
    (hTball : extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' T ⊆ ball c φ.rIn) (hAT : A ⊆ T) (hO : IsOpen O)
    (hAO : A ⊆ O) (hzero : ∀ p ∈ O, h.h p = 0) :
    pieceVar g h x₀ φ Λ T A = 0 := by
  have hTc : IsCompact (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' T) :=
    hT.image_of_continuousOn ((continuousOn_extChartAt x₀).mono hT0)
  rw [pieceVar_eq, Measure.restrict_restrict hTc.isClosed.measurableSet]
  refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
  obtain ⟨p, hpA, rfl⟩ := hy.2
  have hps : p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source := hT0 (hAT hpA)
  have hyt : extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target :=
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source hps
  have hTn : (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target ∈ 𝓝 (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p) :=
    (isOpen_extChartAt_target x₀).mem_nhds hyt
  have hcs : ContinuousAt (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p) :=
    (continuousOn_extChartAt_symm x₀).continuousAt hTn
  have hOn : (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm ⁻¹' O ∈ 𝓝 (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p) :=
    hcs.preimage_mem_nhds (hO.mem_nhds (by
      rw [(extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).left_inv hps]
      exact hAO hpA))
  have hBn : ball c φ.rIn ∈ 𝓝 (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p) :=
    isOpen_ball.mem_nhds (hTball ⟨p, hAT hpA, rfl⟩)
  have hHz : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p), h.coordCompR x₀ φ z = 0 := by
    filter_upwards [hOn, hBn] with z hzO hzB
    show h.coordComp x₀ (ballRetract φ z) = 0
    rw [ballRetract_of_mem φ hzB]
    ext i j
    simp only [SymBilinField.coordComp, hzero _ hzO, ContinuousLinearMap.zero_apply,
      Matrix.zero_apply]
  have hH0 : h.coordCompR x₀ φ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p) = 0 := hHz.self_of_nhds
  have hflux : ehFluxDiv (g.coordMetricR x₀ φ) (h.coordCompR x₀ φ)
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p) = 0 :=
    ehFluxDiv_eq_zero_of_eventuallyEq _ _ (g.contDiff_coordMetricR x₀ φ hball)
      (h.contDiff_coordCompR x₀ φ hball) _ fun a b => hHz.mono fun z hz => by
        show h.coordCompR x₀ φ z a b = 0
        rw [hz, Matrix.zero_apply]
  show pieceIntegrand g h x₀ φ Λ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p) = 0
  unfold pieceIntegrand
  rw [hflux, hH0]
  simp

end Lightlike
