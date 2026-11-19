import Lightlike.Spacetime.EHManifold.ManifoldStationary
import Lightlike.Spacetime.EHManifold.FRCompact

/-!
# Stationary points of the `f(R)` action on a manifold are the solutions of the `f(R)` field equations

`IsFRStationary g f`: the first variation of `∫_K f(R) d vol` vanishes for every symmetric tensor field
vanishing outside a compact set `K`.

`isFRStationary_iff`: `g` is stationary if and only if, in every chart and on every small coordinate ball,
the symmetric part of `fRTensorUp = f'(R) R^{ab} - ½ f(R) g^{ab} - ∇^a ∇^b f'(R) + g^{ab} □ f'(R)` of the
chart components of `g` vanishes: the vacuum field equations of metric `f(R)` gravity, in charts.

## References

* T. P. Sotiriou, V. Faraoni, *f(R) theories of gravity*, arXiv:0805.1726, section II.A, (5)–(6), p. 5.
-/

open MeasureTheory Set Manifold TopologicalSpace Matrix Filter Metric
open scoped ContDiff ENNReal Topology

noncomputable section

namespace Lightlike

set_option synthInstance.maxHeartbeats 400000

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]

/-- **Stationarity of the `f(R)` action**: the first variation vanishes for every symmetric tensor field
with compact support. -/
def IsFRStationary (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (f : ℝ → ℝ) : Prop :=
  ∀ (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (K : Set M), IsCompact K → (∀ p, p ∉ K → h.h p = 0) →
    HasDerivAt (fun t : ℝ => fRAction (g.perturb h t) f K) 0 0

/-- **Stationary points satisfy the `f(R)` field equations** on every small coordinate ball. -/
theorem fRTensor_of_isFRStationary (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (f : ℝ → ℝ)
    (hf : ContDiff ℝ 1 f) (hf' : ContDiff ℝ 2 (deriv f)) (hst : IsFRStationary g f) (x₁ : M)
    {c : Fin n → ℝ} (φ : ContDiffBump c)
    (hball : ball c φ.rOut ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target) {y₀ : Fin n → ℝ}
    (hy₀ : y₀ ∈ ball c φ.rIn) (a b : Fin n) :
    fRTensorUp (g.coordMetricR x₁ φ) f y₀ a b + fRTensorUp (g.coordMetricR x₁ φ) f y₀ b a = 0 := by
  have hG := g.contDiff_coordMetricR x₁ φ hball
  have hdet := g.det_coordMetricR_ne_zero x₁ φ hball
  have hrr : ball c φ.rIn ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target :=
    (ball_subset_ball φ.rIn_lt_rOut.le).trans hball
  have hGc : Continuous (g.coordMetricR x₁ φ) := continuous_matrix fun i j => (hG i j).continuous
  have hsq : Continuous (fun y => √|(g.coordMetricR x₁ φ y).det|) :=
    Real.continuous_sqrt.comp (continuous_abs.comp hGc.matrix_det)
  have hE : ∀ α β, Continuous fun y => fRTensorUp (g.coordMetricR x₁ φ) f y α β := fun α β =>
    continuous_fRTensorUp (g.coordMetricR x₁ φ) hG hdet f hf hf' α β
  obtain ⟨F, hF⟩ : ∃ F : (Fin n → ℝ) → ℝ, F = fun y => √|(g.coordMetricR x₁ φ y).det| *
      (fRTensorUp (g.coordMetricR x₁ φ) f y a b + fRTensorUp (g.coordMetricR x₁ φ) f y b a) :=
    ⟨_, rfl⟩
  have hFc : Continuous F := by
    rw [hF]
    exact hsq.mul ((hE a b).add (hE b a))
  obtain ⟨S, hS⟩ : ∃ S : Matrix (Fin n) (Fin n) ℝ, S = Matrix.of fun i j =>
      (if i = a ∧ j = b then (1 : ℝ) else 0) + (if i = b ∧ j = a then 1 else 0) := ⟨_, rfl⟩
  have hSs : ∀ i j, S i j = S j i := by
    intro i j
    simp only [hS, Matrix.of_apply]
    rw [add_comm]
    simp only [and_comm]
  have hTo : IsOpen (ball c φ.rIn) := isOpen_ball
  have hzero : ∀ η : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ ball c φ.rIn → ∫ y, η y • F y = 0 := by
    intro η hη hηc hηb
    have hηs : tsupport η ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target := hηb.trans hrr
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
    have himg : extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ '' ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).symm '' tsupport η) =
        tsupport η := by
      ext z
      constructor
      · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
        rw [(extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).right_inv (hηs hw)]
        exact hw
      · intro hz
        exact ⟨_, ⟨z, hz, rfl⟩, (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).right_inv (hηs hz)⟩
    have hder := hst (SymBilinField.ofChart x₁ (chartExtend x₁ η) hρ hρs S hSs) _ hKc hsupp
    have hv := fR_first_variation_manifold g
      (SymBilinField.ofChart x₁ (chartExtend x₁ η) hρ hρs S hSs) x₁ hKc hK0 φ hball
      (by rw [himg]; exact hηb) hsupp f hf hf'
    have hint := neg_eq_zero.1 (hv.unique hder)
    rw [himg] at hint
    have hsuppz : ∀ y, y ∉ tsupport η → η y • F y = 0 := by
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
    have hsum : ∑ α, ∑ β, (η y * S α β) * fRTensorUp (g.coordMetricR x₁ φ) f y α β =
        η y * (fRTensorUp (g.coordMetricR x₁ φ) f y a b +
          fRTensorUp (g.coordMetricR x₁ φ) f y b a) := by
      simp only [hS, Matrix.of_apply]
      simp [mul_add, add_mul, Finset.sum_add_distrib, ite_and, Finset.sum_ite_eq']
    simp only [hcomp]
    show η y • F y = √|(g.coordMetricR x₁ φ y).det| *
      ∑ α, ∑ β, (η y * S α β) * fRTensorUp (g.coordMetricR x₁ φ) f y α β
    rw [hsum, hF, smul_eq_mul]
    ring
  have hae := hTo.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
    (hFc.continuousOn.locallyIntegrableOn hTo.measurableSet) hzero
  have hopen : IsOpen (ball c φ.rIn ∩ {y | F y ≠ 0}) :=
    hFc.continuousOn.isOpen_inter_preimage hTo isOpen_ne
  have hnull0 : volume {y : Fin n → ℝ | ¬(y ∈ ball c φ.rIn → F y = 0)} = 0 := ae_iff.1 hae
  have hsub : ball c φ.rIn ∩ {y | F y ≠ 0} ⊆ {y : Fin n → ℝ | ¬(y ∈ ball c φ.rIn → F y = 0)} :=
    fun y hy himp => hy.2 (himp hy.1)
  have hempty : ball c φ.rIn ∩ {y | F y ≠ 0} = ∅ :=
    (hopen.measure_eq_zero_iff volume).1 (measure_mono_null hsub hnull0)
  have hFy : F y₀ = 0 := by
    by_contra hne
    have hmem : y₀ ∈ ball c φ.rIn ∩ {y | F y ≠ 0} := ⟨hy₀, hne⟩
    rw [hempty] at hmem
    exact hmem
  rw [hF] at hFy
  have hpos : 0 < √|(g.coordMetricR x₁ φ y₀).det| := Real.sqrt_pos.2 (abs_pos.2 (hdet y₀))
  exact (mul_eq_zero.1 hFy).resolve_left hpos.ne'

/-- **Solutions of the `f(R)` field equations are stationary.** -/
theorem isFRStationary_of_fRTensor (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (f : ℝ → ℝ)
    (hf : ContDiff ℝ 1 f) (hf' : ContDiff ℝ 2 (deriv f))
    (hE : ∀ (x₁ : M) (c : Fin n → ℝ) (φ : ContDiffBump c),
      ball c φ.rOut ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target → ∀ y ∈ ball c φ.rIn, ∀ a b,
      fRTensorUp (g.coordMetricR x₁ φ) f y a b + fRTensorUp (g.coordMetricR x₁ φ) f y b a = 0) :
    IsFRStationary g f := by
  intro h K hK hsupp
  rcases isEmpty_or_nonempty M with hM | hM
  · have hKe : K = ∅ := Set.eq_empty_of_isEmpty K
    subst hKe
    simp only [fRAction, Measure.restrict_empty, integral_zero_measure]
    exact hasDerivAt_const 0 0
  obtain ⟨N, x, c, φ, ρ, hρ, hball, -, -, -, hin, hmain⟩ :=
    fR_first_variation_manifold_compact g h hK hsupp f hf hf'
  have hz : ∑ i ∈ Finset.range N,
      ∫ y in extChartAt 𝓘(ℝ, Fin n → ℝ) (x i) '' (K ∩ tsupport (ρ i)),
        √|(g.coordMetricR (x i) (φ i) y).det| *
          ∑ α, ∑ β, (h.smulFun (ρ i) (hρ i)).coordComp (x i) y α β *
            fRTensorUp (g.coordMetricR (x i) (φ i)) f y α β = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
    rw [sum_symm_mul_eq_zero (fun α β => (h.smulFun (ρ i) (hρ i)).coordComp (x i) y α β)
      (fun α β => fRTensorUp (g.coordMetricR (x i) (φ i)) f y α β)
      (fun α β => (h.smulFun (ρ i) (hρ i)).coordComp_symm (x i) y α β)
      (fun α β => hE (x i) (c i) (φ i) (hball i) y (hin i hy) α β), mul_zero]
  rw [hz, neg_zero] at hmain
  exact hmain

/-- **Stationary points of the `f(R)` action on a manifold are the solutions of the vacuum `f(R)` field
equations**, in every chart and on every small coordinate ball. -/
theorem isFRStationary_iff (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (f : ℝ → ℝ)
    (hf : ContDiff ℝ 1 f) (hf' : ContDiff ℝ 2 (deriv f)) :
    IsFRStationary g f ↔ ∀ (x₁ : M) (c : Fin n → ℝ) (φ : ContDiffBump c),
      ball c φ.rOut ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target → ∀ y ∈ ball c φ.rIn, ∀ a b,
      fRTensorUp (g.coordMetricR x₁ φ) f y a b + fRTensorUp (g.coordMetricR x₁ φ) f y b a = 0 :=
  ⟨fun hst x₁ _ φ hball _ hy a b => fRTensor_of_isFRStationary g f hf hf' hst x₁ φ hball hy a b,
    isFRStationary_of_fRTensor g f hf hf'⟩

end Lightlike
