import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Lightlike.Spacetime.VariationCritical
import Lightlike.Spacetime.EHManifold.ChartField
import Lightlike.Spacetime.EHManifold.CompactVariation

/-!
# Stationary points of the Einstein–Hilbert action on a manifold are the solutions of Einstein's equation

`IsEHStationary g Λ`: the first variation of the Einstein–Hilbert action of `g` vanishes for every smooth
symmetric tensor field of compact support.

`isEHStationary_iff`: `g` is stationary if and only if, in every chart, the symmetric part of
`R^{αβ} - ½ R g^{αβ} + Λ g^{αβ}` vanishes (the vacuum Einstein equations with cosmological constant, in the
components of the chart).

## References

* S. M. Carroll, *Lecture Notes on General Relativity*, arXiv gr-qc/9712019, chapter 4, eqs. (4.66) and
  (4.67), p. 116.
-/

open MeasureTheory Set Manifold TopologicalSpace Matrix Filter Metric
open scoped ContDiff ENNReal Topology

noncomputable section

namespace Lightlike

set_option synthInstance.maxHeartbeats 400000

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]

open Classical in
/-- A function on the chart target, supported in a compact subset of it, carried to the manifold and
extended by zero. -/
def chartExtend (x₁ : M) (η : (Fin n → ℝ) → ℝ) (p : M) : ℝ :=
  if p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).source then η (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ p) else 0

variable (x₁ : M) {η : (Fin n → ℝ) → ℝ} (hηc : HasCompactSupport η)
  (hηs : tsupport η ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target)

lemma chartExtend_of_mem {p : M} (hp : p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).source) :
    chartExtend x₁ η p = η (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ p) := by
  simp only [chartExtend, if_pos hp]

include hηs in
/-- Outside the inverse chart image of the support, the extension vanishes. -/
lemma chartExtend_eq_zero {p : M}
    (hp : p ∉ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).symm '' tsupport η) : chartExtend x₁ η p = 0 := by
  by_cases hps : p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).source
  · rw [chartExtend_of_mem x₁ hps]
    by_contra hne
    exact hp ⟨extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ p, subset_tsupport _ hne,
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).left_inv hps⟩
  · simp only [chartExtend, if_neg hps]

include hηc hηs in
lemma isCompact_symm_image_tsupport :
    IsCompact ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).symm '' tsupport η) :=
  hηc.isCompact.image_of_continuousOn ((continuousOn_extChartAt_symm x₁).mono hηs)

include hηs in
lemma symm_image_tsupport_subset_source :
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).symm '' tsupport η ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).source := by
  rintro _ ⟨z, hz, rfl⟩
  exact (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).map_target (hηs hz)

variable [T2Space M]

include hηc hηs in
/-- The extension is smooth. -/
lemma contMDiff_chartExtend (hη : ContDiff ℝ ∞ η) :
    ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ (chartExtend x₁ η) := by
  refine contMDiff_of_locally_contMDiffOn fun p => ?_
  by_cases hp : p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).source
  · refine ⟨_, isOpen_extChartAt_source x₁, hp, ?_⟩
    have hc : ContMDiffOn 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁)
        (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).source := by
      rw [extChartAt_source]
      exact contMDiffOn_extChartAt
    exact (hη.contMDiff.comp_contMDiffOn hc).congr fun q hq => chartExtend_of_mem x₁ hq
  · refine ⟨((extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).symm '' tsupport η)ᶜ,
      (isCompact_symm_image_tsupport x₁ hηc hηs).isClosed.isOpen_compl,
      fun h => hp (symm_image_tsupport_subset_source x₁ hηs h), ?_⟩
    exact (contMDiffOn_const (c := (0 : ℝ))).congr fun q hq => chartExtend_eq_zero x₁ hηs hq

include hηc hηs in
lemma tsupport_chartExtend_subset :
    tsupport (chartExtend x₁ η) ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).symm '' tsupport η :=
  closure_minimal (fun p hp => by
    by_contra hpn
    exact hp (chartExtend_eq_zero x₁ hηs hpn))
    (isCompact_symm_image_tsupport x₁ hηc hηs).isClosed

omit hηc hηs

variable [SecondCountableTopology M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M]
  [BorelSpace M]

/-- **The metric is a stationary point of the Einstein–Hilbert action**: the first variation vanishes for
every smooth symmetric tensor field of compact support. -/
def IsEHStationary (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (Λ : ℝ) : Prop :=
  ∀ (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (K : Set M), IsCompact K → (∀ p, p ∉ K → h.h p = 0) →
    HasDerivAt (fun t : ℝ => ehAction (g.perturb h t) Λ K) 0 0

/-- The integrand `⟨G + Λ g, h⟩_g` vanishes when the Einstein equations hold in the chart at the point. -/
lemma ehIntegrand_eq_zero_of_einstein (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)
    (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (Λ : ℝ) (p : M)
    (hE : ∀ α β, einsteinUp (g.coordMetric p) Λ (extChartAt 𝓘(ℝ, Fin n → ℝ) p p) α β +
      einsteinUp (g.coordMetric p) Λ (extChartAt 𝓘(ℝ, Fin n → ℝ) p p) β α = 0) :
    ehIntegrand g h Λ p = 0 := by
  have h1 := ehIntegrand_chart g h Λ p (mem_extChartAt_target p)
  rw [(extChartAt 𝓘(ℝ, Fin n → ℝ) p).left_inv (mem_extChartAt_source p)] at h1
  rw [h1]
  have hsw : ∑ α, ∑ β, h.coordComp p (extChartAt 𝓘(ℝ, Fin n → ℝ) p p) α β *
        einsteinUp (g.coordMetric p) Λ (extChartAt 𝓘(ℝ, Fin n → ℝ) p p) α β =
      ∑ α, ∑ β, h.coordComp p (extChartAt 𝓘(ℝ, Fin n → ℝ) p p) α β *
        einsteinUp (g.coordMetric p) Λ (extChartAt 𝓘(ℝ, Fin n → ℝ) p p) β α := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    rw [h.coordComp_symm p _ β α]
  have h2 : ∑ α, ∑ β, h.coordComp p (extChartAt 𝓘(ℝ, Fin n → ℝ) p p) α β *
        einsteinUp (g.coordMetric p) Λ (extChartAt 𝓘(ℝ, Fin n → ℝ) p p) α β +
      ∑ α, ∑ β, h.coordComp p (extChartAt 𝓘(ℝ, Fin n → ℝ) p p) α β *
        einsteinUp (g.coordMetric p) Λ (extChartAt 𝓘(ℝ, Fin n → ℝ) p p) β α = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun α _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun β _ => ?_
    rw [← mul_add, hE α β, mul_zero]
  have h3 : ∑ α, ∑ β, h.coordComp p (extChartAt 𝓘(ℝ, Fin n → ℝ) p p) α β *
      einsteinUp (g.coordMetric p) Λ (extChartAt 𝓘(ℝ, Fin n → ℝ) p p) α β = 0 := by
    rw [← hsw] at h2
    linarith
  exact h3

/-- **Solutions of Einstein's equation are stationary points of the Einstein–Hilbert action.** -/
theorem isEHStationary_of_einstein (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (Λ : ℝ)
    (hE : ∀ x₁ : M, ∀ y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target, ∀ α β,
      einsteinUp (g.coordMetric x₁) Λ y α β + einsteinUp (g.coordMetric x₁) Λ y β α = 0) :
    IsEHStationary g Λ := by
  intro h K hK hsupp
  have hmain := eh_first_variation_manifold_compact g h hK hsupp Λ
  have hz : ∫ p in K, ehIntegrand g h Λ p ∂(NondegMetric.volumeMeasure g) = 0 := by
    rw [setIntegral_congr_fun hK.measurableSet (g := fun _ => (0 : ℝ)) fun p _ =>
      ehIntegrand_eq_zero_of_einstein g h Λ p (hE p _ (mem_extChartAt_target p))]
    simp
  rw [hz, neg_zero] at hmain
  exact hmain

/-- **Stationary points of the Einstein–Hilbert action satisfy Einstein's equation**, in every chart. -/
theorem einstein_of_isEHStationary (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (Λ : ℝ)
    (hst : IsEHStationary g Λ) (x₁ : M) {y₀ : Fin n → ℝ}
    (hy₀ : y₀ ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target) (a b : Fin n) :
    einsteinUp (g.coordMetric x₁) Λ y₀ a b + einsteinUp (g.coordMetric x₁) Λ y₀ b a = 0 := by
  have hc := g.isCoordMetric_coordMetric x₁
  -- continuity of the pieces on the chart target
  have hinv : ∀ i j, ContinuousOn (fun y => (g.coordMetric x₁ y)⁻¹ i j)
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target := fun i j => (hc.contDiffOn_inv i j).continuousOn
  have hric : ∀ i j, ContinuousOn (fun y => ricci (g.coordMetric x₁) i j y)
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target := fun i j => (hc.contDiffOn_ricci i j).continuousOn
  have hR : ContinuousOn (fun y => scalarCurvature (g.coordMetric x₁) y)
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target := hc.contDiffOn_scalarCurvature.continuousOn
  have hE : ∀ α β, ContinuousOn (fun y => einsteinUp (g.coordMetric x₁) Λ y α β)
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target := by
    intro α β
    unfold einsteinUp ricciUp
    exact ((continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ =>
      ((hinv α i).mul (hric i j)).mul (hinv j β)).sub
        ((continuousOn_const.mul hR).mul (hinv α β))).add (continuousOn_const.mul (hinv α β))
  obtain ⟨f, hf⟩ : ∃ f : (Fin n → ℝ) → ℝ, f = fun y => NondegMetric.volDensity g x₁ y *
      (einsteinUp (g.coordMetric x₁) Λ y a b + einsteinUp (g.coordMetric x₁) Λ y b a) := ⟨_, rfl⟩
  have hfc : ContinuousOn f (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target := by
    rw [hf]
    exact (NondegMetric.continuousOn_volDensity g x₁).mul ((hE a b).add (hE b a))
  obtain ⟨S, hS⟩ : ∃ S : Matrix (Fin n) (Fin n) ℝ, S = Matrix.of fun i j =>
      (if i = a ∧ j = b then (1 : ℝ) else 0) + (if i = b ∧ j = a then 1 else 0) := ⟨_, rfl⟩
  have hSs : ∀ i j, S i j = S j i := by
    intro i j
    simp only [hS, Matrix.of_apply]
    rw [add_comm]
    simp only [and_comm]
  have hTo : IsOpen (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target := isOpen_extChartAt_target x₁
  have hzero : ∀ η : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target → ∫ y, η y • f y = 0 := by
    intro η hη hηc hηs
    have hρ := contMDiff_chartExtend x₁ hηc hηs hη
    have hρs : tsupport (chartExtend x₁ η) ⊆ (chartTriv n x₁).baseSet := by
      refine (tsupport_chartExtend_subset x₁ hηc hηs).trans ?_
      rintro _ ⟨z, hz, rfl⟩
      exact symm_mem_chartTriv_baseSet x₁ (hηs hz)
    have hKc := isCompact_symm_image_tsupport x₁ hηc hηs
    have hK0 := symm_image_tsupport_subset_source x₁ hηs
    have hsupp : ∀ p, p ∉ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).symm '' tsupport η →
        (SymBilinField.ofChart x₁ (chartExtend x₁ η) hρ hρs S hSs).h p = 0 := fun p hp =>
      SymBilinField.ofChart_eq_zero x₁ _ hρ hρs S hSs (chartExtend_eq_zero x₁ hηs hp)
    have hder := hst (SymBilinField.ofChart x₁ (chartExtend x₁ η) hρ hρs S hSs) _ hKc hsupp
    have hv := eh_first_variation_manifold_compact g
      (SymBilinField.ofChart x₁ (chartExtend x₁ η) hρ hρs S hSs) hKc hsupp Λ
    have hint : ∫ p in (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).symm '' tsupport η,
        ehIntegrand g (SymBilinField.ofChart x₁ (chartExtend x₁ η) hρ hρs S hSs) Λ p
        ∂(NondegMetric.volumeMeasure g) = 0 := neg_eq_zero.1 (hv.unique hder)
    have himg : extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ '' ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).symm '' tsupport η) =
        tsupport η := by
      ext z
      constructor
      · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
        rw [(extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).right_inv (hηs hw)]
        exact hw
      · intro hz
        exact ⟨_, ⟨z, hz, rfl⟩, (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).right_inv (hηs hz)⟩
    have hmeas : AEStronglyMeasurable
        (ehIntegrand g (SymBilinField.ofChart x₁ (chartExtend x₁ η) hρ hρs S hSs) Λ)
        ((NondegMetric.volumeMeasure g).restrict ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).symm '' tsupport η)) :=
      ((continuousOn_ehIntegrand g _ Λ x₁).aestronglyMeasurable
        (isOpen_extChartAt_source x₁).measurableSet).mono_measure (Measure.restrict_mono hK0 le_rfl)
    rw [NondegMetric.setIntegral_volumeMeasure_chart g x₁ hKc.measurableSet hK0 _ hmeas, himg] at hint
    have hsuppz : ∀ y, y ∉ tsupport η → η y • f y = 0 := by
      intro y hy
      rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsuppz, ← hint]
    refine setIntegral_congr_fun (isClosed_tsupport η).measurableSet fun y hy => ?_
    have hyt := hηs hy
    have hcomp : ∀ i j, (SymBilinField.ofChart x₁ (chartExtend x₁ η) hρ hρs S hSs).coordComp x₁ y i j =
        η y * S i j := by
      intro i j
      rw [SymBilinField.coordComp_ofChart x₁ _ hρ hρs S hSs hyt,
        chartExtend_of_mem x₁ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).map_target hyt),
        (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).right_inv hyt]
    have hsum : ∑ α, ∑ β, (η y * S α β) * einsteinUp (g.coordMetric x₁) Λ y α β =
        η y * (einsteinUp (g.coordMetric x₁) Λ y a b + einsteinUp (g.coordMetric x₁) Λ y b a) := by
      simp only [hS, Matrix.of_apply]
      simp [mul_add, add_mul, Finset.sum_add_distrib, ite_and, Finset.sum_ite_eq']
    show η y • f y = NondegMetric.volDensity g x₁ y *
      ehIntegrand g (SymBilinField.ofChart x₁ (chartExtend x₁ η) hρ hρs S hSs) Λ
        ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).symm y)
    rw [ehIntegrand_chart g _ Λ x₁ hyt]
    simp only [hcomp]
    show η y • f y = NondegMetric.volDensity g x₁ y *
      ∑ α, ∑ β, (η y * S α β) * einsteinUp (g.coordMetric x₁) Λ y α β
    rw [hsum, hf, smul_eq_mul]
    ring
  have hae := hTo.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
    (hfc.locallyIntegrableOn hTo.measurableSet) hzero
  have hopen : IsOpen ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target ∩ {y | f y ≠ 0}) :=
    hfc.isOpen_inter_preimage hTo isOpen_ne
  have hnull0 : volume {y : Fin n → ℝ | ¬(y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target → f y = 0)} = 0 :=
    ae_iff.1 hae
  have hsub : (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target ∩ {y | f y ≠ 0} ⊆
      {y : Fin n → ℝ | ¬(y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target → f y = 0)} :=
    fun y hy himp => hy.2 (himp hy.1)
  have hempty : (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target ∩ {y | f y ≠ 0} = ∅ :=
    (hopen.measure_eq_zero_iff volume).1 (measure_mono_null hsub hnull0)
  have hfy : f y₀ = 0 := by
    by_contra hne
    have hmem : y₀ ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target ∩ {y | f y ≠ 0} := ⟨hy₀, hne⟩
    rw [hempty] at hmem
    exact hmem
  rw [hf] at hfy
  have hpos : 0 < NondegMetric.volDensity g x₁ y₀ :=
    Real.sqrt_pos.2 (abs_pos.2 (g.coordMetric_isUnit_det x₁ hy₀).ne_zero)
  exact (mul_eq_zero.1 hfy).resolve_left hpos.ne'

/-- **Stationary points of the Einstein–Hilbert action are the solutions of Einstein's equation**: `g` is
stationary if and only if, in every chart, the symmetric part of `R^{αβ} - ½ R g^{αβ} + Λ g^{αβ}` vanishes. -/
theorem isEHStationary_iff (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (Λ : ℝ) :
    IsEHStationary g Λ ↔ ∀ x₁ : M, ∀ y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target, ∀ α β,
      einsteinUp (g.coordMetric x₁) Λ y α β + einsteinUp (g.coordMetric x₁) Λ y β α = 0 :=
  ⟨fun hst x₁ _ hy α β => einstein_of_isEHStationary g Λ hst x₁ hy α β,
    isEHStationary_of_einstein g Λ⟩

end Lightlike
