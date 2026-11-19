import Lightlike.Spacetime.EHManifold.FRManifoldPiece

/-!
# The `f(R)` piece variation: additivity in the perturbation, vanishing, additivity of the action

* `fRPieceVar_sum`: the variation over a piece is additive in the perturbation;
* `fRPieceVar_eq_zero`: it vanishes when the perturbation vanishes on an open set containing the piece;
* `fRAction_biUnion`: the `f(R)` action is additive over disjoint measurable pieces inside charts.

Supporting statements, the `f(R)` versions of `pieceVar_sum`, `pieceVar_eq_zero`, `ehAction_biUnion`; no
catalogue entry.
-/

open MeasureTheory Set Manifold TopologicalSpace Matrix Filter Metric
open scoped ContDiff ENNReal Topology

noncomputable section

namespace Lightlike

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]

/-- The integrand of `fRPieceVar`. -/
def fRPieceIntegrand (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M)
    (x₀ : M) {c : Fin n → ℝ} (φ : ContDiffBump c) (f : ℝ → ℝ) (y : Fin n → ℝ) : ℝ :=
  -√|(g.coordMetricR x₀ φ y).det| * ∑ α, ∑ β, h.coordCompR x₀ φ y α β *
      (deriv f (scalarCurvature (g.coordMetricR x₀ φ) y) * ricciUp (g.coordMetricR x₀ φ) y α β -
        (1 / 2) * f (scalarCurvature (g.coordMetricR x₀ φ) y) * (g.coordMetricR x₀ φ y)⁻¹ α β) +
    deriv f (scalarCurvature (g.coordMetricR x₀ φ) y) *
      ehFluxDiv (g.coordMetricR x₀ φ) (h.coordCompR x₀ φ) y

lemma fRPieceVar_eq (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M)
    (x₀ : M) {c : Fin n → ℝ} (φ : ContDiffBump c) (f : ℝ → ℝ) (T A : Set M) :
    fRPieceVar g h x₀ φ f T A = ∫ y in extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' T,
      fRPieceIntegrand g h x₀ φ f y ∂(volume.restrict (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' A)) := rfl

variable (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (x₀ : M) {c : Fin n → ℝ} (φ : ContDiffBump c)
  (hball : ball c φ.rOut ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target)

include hball in
/-- The integrand of `fRPieceVar` is continuous. -/
lemma continuous_fRPieceIntegrand (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (f : ℝ → ℝ)
    (hf : Continuous f) (hdf : Continuous (deriv f)) :
    Continuous (fRPieceIntegrand g h x₀ φ f) := by
  have hG := g.contDiff_coordMetricR x₀ φ hball
  have hH := h.contDiff_coordCompR x₀ φ hball
  have hdet := g.det_coordMetricR_ne_zero x₀ φ hball
  have hGc : Continuous (g.coordMetricR x₀ φ) := continuous_matrix fun i j => (hG i j).continuous
  have hsq : Continuous (fun y => √|(g.coordMetricR x₀ φ y).det|) :=
    Real.continuous_sqrt.comp (continuous_abs.comp hGc.matrix_det)
  have hR : Continuous (fun y => scalarCurvature (g.coordMetricR x₀ φ) y) :=
    (contDiff_scalarCurvature (g.coordMetricR x₀ φ) hG hdet).continuous
  have hφc : Continuous (fun y => deriv f (scalarCurvature (g.coordMetricR x₀ φ) y)) := hdf.comp hR
  have hE : Continuous (fun y => ∑ α, ∑ β, h.coordCompR x₀ φ y α β *
      (deriv f (scalarCurvature (g.coordMetricR x₀ φ) y) * ricciUp (g.coordMetricR x₀ φ) y α β -
        (1 / 2) * f (scalarCurvature (g.coordMetricR x₀ φ) y) * (g.coordMetricR x₀ φ y)⁻¹ α β)) :=
    continuous_finsetSum _ fun α _ => continuous_finsetSum _ fun β _ =>
      (hH α β).continuous.mul
        ((hφc.mul (contDiff_ricciUp (g.coordMetricR x₀ φ) hG hdet α β).continuous).sub
          ((continuous_const.mul (hf.comp hR)).mul
            (contDiff_inv_entry (g.coordMetricR x₀ φ) hG hdet α β).continuous))
  have hF : Continuous (ehFluxDiv (g.coordMetricR x₀ φ) (h.coordCompR x₀ φ)) := by
    unfold ehFluxDiv
    exact continuous_finsetSum _ fun ρ _ =>
      (contDiff_pd (contDiff_flux (g.coordMetricR x₀ φ) (h.coordCompR x₀ φ) hG hH hdet ρ) ρ).continuous
  unfold fRPieceIntegrand
  exact (hsq.neg.mul hE).add (hφc.mul hF)

include hball in
/-- **The `f(R)` variation over a piece is additive in the perturbation.** -/
theorem fRPieceVar_sum {ι : Type*} (s : Finset ι) (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M)
    (hs : ι → SymBilinField 𝓘(ℝ, Fin n → ℝ) M)
    (hH : ∀ y, h.coordCompR x₀ φ y = ∑ i ∈ s, (hs i).coordCompR x₀ φ y) (f : ℝ → ℝ)
    (hf : Continuous f) (hdf : Continuous (deriv f)) {T : Set M}
    (hT : IsCompact T) (hT0 : T ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) (A : Set M) :
    fRPieceVar g h x₀ φ f T A = ∑ i ∈ s, fRPieceVar g (hs i) x₀ φ f T A := by
  have hTc : IsCompact (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' T) :=
    hT.image_of_continuousOn ((continuousOn_extChartAt x₀).mono hT0)
  have hpt : ∀ y, fRPieceIntegrand g h x₀ φ f y = ∑ i ∈ s, fRPieceIntegrand g (hs i) x₀ φ f y := by
    intro y
    have hfun : h.coordCompR x₀ φ = fun z => ∑ i ∈ s, (hs i).coordCompR x₀ φ z := funext hH
    unfold fRPieceIntegrand
    rw [hfun, ehFluxDiv_sum (g.coordMetricR x₀ φ) (g.contDiff_coordMetricR x₀ φ hball)
      (g.det_coordMetricR_ne_zero x₀ φ hball) s (fun i => (hs i).coordCompR x₀ φ)
      (fun i => (hs i).contDiff_coordCompR x₀ φ hball) y, sum_sum_matrix_sum_mul,
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  have hint : ∀ i ∈ s, Integrable (fRPieceIntegrand g (hs i) x₀ φ f)
      ((volume.restrict (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' A)).restrict
        (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' T)) := fun i _ =>
    ((continuous_fRPieceIntegrand g x₀ φ hball (hs i) f hf hdf).continuousOn.integrableOn_compact
      hTc).mono_measure Measure.restrict_le_self
  simp only [fRPieceVar_eq]
  rw [← integral_finsetSum s hint]
  exact integral_congr_ae (Filter.Eventually.of_forall hpt)

/-- **The `f(R)` variation over a piece vanishes** when the perturbation vanishes on an open set containing
the piece. -/
theorem fRPieceVar_eq_zero (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M)
    (hball : ball c φ.rOut ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) (f : ℝ → ℝ) {T A O : Set M}
    (hT : IsCompact T) (hT0 : T ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source)
    (hTball : extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' T ⊆ ball c φ.rIn) (hAT : A ⊆ T) (hO : IsOpen O)
    (hAO : A ⊆ O) (hzero : ∀ p ∈ O, h.h p = 0) :
    fRPieceVar g h x₀ φ f T A = 0 := by
  have hTc : IsCompact (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' T) :=
    hT.image_of_continuousOn ((continuousOn_extChartAt x₀).mono hT0)
  rw [fRPieceVar_eq, Measure.restrict_restrict hTc.isClosed.measurableSet]
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
  show fRPieceIntegrand g h x₀ φ f (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p) = 0
  unfold fRPieceIntegrand
  rw [hflux, hH0]
  simp

/-- The `f(R)` action is additive over finitely many disjoint measurable pieces, each inside a compact
subset of a chart domain. -/
theorem fRAction_biUnion (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (f : ℝ → ℝ) (hf : Continuous f)
    {ι : Type*} (s : Finset ι) (A T : ι → Set M) (x : ι → M) (hA : ∀ i ∈ s, MeasurableSet (A i))
    (hd : Set.Pairwise (↑s) (Function.onFun Disjoint A)) (hT : ∀ i ∈ s, IsCompact (T i))
    (hT0 : ∀ i ∈ s, T i ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) (x i)).source) (hAT : ∀ i ∈ s, A i ⊆ T i) :
    fRAction g f (⋃ i ∈ s, A i) = ∑ i ∈ s, fRAction g f (A i) := by
  unfold fRAction
  exact integral_biUnion_finset s hA hd fun i hi =>
    NondegMetric.integrableOn_of_continuousOn g (x i) (hT i hi) (hT0 i hi)
      ((continuousOn_fR g f hf (x i)).mono (hT0 i hi)) (hAT i hi)

end Lightlike
