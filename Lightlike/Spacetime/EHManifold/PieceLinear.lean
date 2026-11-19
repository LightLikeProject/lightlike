import Lightlike.Spacetime.VariationCritical
import Lightlike.Spacetime.EHManifold.FluxLinear
import Lightlike.Spacetime.EHManifold.PieceAction

/-!
# The variation over a piece is additive in the perturbation

`pieceVar_sum`: if the chart components of `h` are the sum of those of finitely many fields `hs i`, then
`pieceVar g h … = ∑ i, pieceVar g (hs i) …`.

Supporting lemma for cutting a perturbation into pieces with a partition of unity; no catalogue entry.
-/

open MeasureTheory Set Manifold TopologicalSpace Matrix Filter Metric
open scoped ContDiff ENNReal Topology

noncomputable section

namespace Lightlike

/-- A double sum against a finite sum of matrices. -/
lemma sum_sum_matrix_sum_mul {n : ℕ} {ι : Type*} (s : Finset ι) (F : ι → Matrix (Fin n) (Fin n) ℝ)
    (X : Fin n → Fin n → ℝ) :
    ∑ α, ∑ β, (∑ i ∈ s, F i) α β * X α β = ∑ i ∈ s, ∑ α, ∑ β, F i α β * X α β := by
  simp only [Matrix.sum_apply, Finset.sum_mul]
  calc ∑ α, ∑ β, ∑ i ∈ s, F i α β * X α β = ∑ α, ∑ i ∈ s, ∑ β, F i α β * X α β :=
        Finset.sum_congr rfl fun α _ => Finset.sum_comm
    _ = ∑ i ∈ s, ∑ α, ∑ β, F i α β * X α β := Finset.sum_comm

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]

/-- The integrand of `pieceVar`. -/
def pieceIntegrand (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M)
    (x₀ : M) {c : Fin n → ℝ} (φ : ContDiffBump c) (Λ : ℝ) (y : Fin n → ℝ) : ℝ :=
  -√|(g.coordMetricR x₀ φ y).det| * ∑ α, ∑ β, h.coordCompR x₀ φ y α β *
      einsteinUp (g.coordMetricR x₀ φ) Λ y α β +
    ehFluxDiv (g.coordMetricR x₀ φ) (h.coordCompR x₀ φ) y

lemma pieceVar_eq (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M)
    (x₀ : M) {c : Fin n → ℝ} (φ : ContDiffBump c) (Λ : ℝ) (T A : Set M) :
    pieceVar g h x₀ φ Λ T A = ∫ y in extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' T,
      pieceIntegrand g h x₀ φ Λ y ∂(volume.restrict (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' A)) := rfl

variable (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (x₀ : M) {c : Fin n → ℝ} (φ : ContDiffBump c)
  (hball : ball c φ.rOut ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target)

include hball in
/-- The integrand of `pieceVar` is continuous. -/
lemma continuous_pieceIntegrand (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (Λ : ℝ) :
    Continuous (pieceIntegrand g h x₀ φ Λ) := by
  have hG := g.contDiff_coordMetricR x₀ φ hball
  have hH := h.contDiff_coordCompR x₀ φ hball
  have hdet := g.det_coordMetricR_ne_zero x₀ φ hball
  have hGc : Continuous (g.coordMetricR x₀ φ) := continuous_matrix fun i j => (hG i j).continuous
  have hsq : Continuous (fun y => √|(g.coordMetricR x₀ φ y).det|) :=
    Real.continuous_sqrt.comp (continuous_abs.comp hGc.matrix_det)
  have hE : Continuous (fun y => ∑ α, ∑ β, h.coordCompR x₀ φ y α β *
      einsteinUp (g.coordMetricR x₀ φ) Λ y α β) :=
    continuous_finsetSum _ fun α _ => continuous_finsetSum _ fun β _ =>
      (hH α β).continuous.mul
        (contDiff_einsteinUp (g.coordMetricR x₀ φ) hG hdet (g.coordMetricR_symm x₀ φ) Λ α β).continuous
  have hF : Continuous (ehFluxDiv (g.coordMetricR x₀ φ) (h.coordCompR x₀ φ)) := by
    unfold ehFluxDiv
    exact continuous_finsetSum _ fun ρ _ =>
      (contDiff_pd (contDiff_flux (g.coordMetricR x₀ φ) (h.coordCompR x₀ φ) hG hH hdet ρ) ρ).continuous
  unfold pieceIntegrand
  exact (hsq.neg.mul hE).add hF

include hball in
/-- **The variation over a piece is additive in the perturbation.** -/
theorem pieceVar_sum {ι : Type*} (s : Finset ι) (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M)
    (hs : ι → SymBilinField 𝓘(ℝ, Fin n → ℝ) M)
    (hH : ∀ y, h.coordCompR x₀ φ y = ∑ i ∈ s, (hs i).coordCompR x₀ φ y) (Λ : ℝ) {T : Set M}
    (hT : IsCompact T) (hT0 : T ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) (A : Set M) :
    pieceVar g h x₀ φ Λ T A = ∑ i ∈ s, pieceVar g (hs i) x₀ φ Λ T A := by
  have hTc : IsCompact (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' T) :=
    hT.image_of_continuousOn ((continuousOn_extChartAt x₀).mono hT0)
  have hpt : ∀ y, pieceIntegrand g h x₀ φ Λ y = ∑ i ∈ s, pieceIntegrand g (hs i) x₀ φ Λ y := by
    intro y
    have hfun : h.coordCompR x₀ φ = fun z => ∑ i ∈ s, (hs i).coordCompR x₀ φ z := funext hH
    unfold pieceIntegrand
    rw [hfun, ehFluxDiv_sum (g.coordMetricR x₀ φ) (g.contDiff_coordMetricR x₀ φ hball)
      (g.det_coordMetricR_ne_zero x₀ φ hball) s (fun i => (hs i).coordCompR x₀ φ)
      (fun i => (hs i).contDiff_coordCompR x₀ φ hball) y, sum_sum_matrix_sum_mul,
      Finset.mul_sum, ← Finset.sum_add_distrib]
  have hint : ∀ i ∈ s, Integrable (pieceIntegrand g (hs i) x₀ φ Λ)
      ((volume.restrict (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' A)).restrict
        (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ '' T)) := fun i _ =>
    ((continuous_pieceIntegrand g x₀ φ hball (hs i) Λ).continuousOn.integrableOn_compact
      hTc).mono_measure (Measure.restrict_mono le_rfl Measure.restrict_le_self)
  simp only [pieceVar_eq]
  rw [← integral_finsetSum s hint]
  exact integral_congr_ae (Filter.Eventually.of_forall hpt)

end Lightlike
