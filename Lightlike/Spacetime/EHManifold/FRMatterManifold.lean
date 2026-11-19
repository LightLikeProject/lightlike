import Lightlike.Spacetime.EHManifold.FRStationary

/-!
# The metric `f(R)` field equations with matter on a manifold

* `symm_part_eq_zero_of_forall_chart_integral`: the fundamental lemma for symmetric tensor fields supported
  in a small coordinate ball of a chart of a manifold;
* `fR_matter_stationary_manifold_iff`: let `S_M` be a matter action on the metrics of a manifold whose
  variation under a perturbation `h` supported in a small coordinate ball is
  `½ ∫ √|g| h_{ab} T^{ab} dy` in the components of the chart (this defines `T` in each chart). Then the total
  action `(1/2κ) ∫ f(R) d vol + S_M` is stationary under all such perturbations iff, in every chart and on
  every small coordinate ball, `fRTensorUp^{ab} + fRTensorUp^{ba} = κ (T^{ab} + T^{ba})`.

## References

* T. P. Sotiriou, V. Faraoni, *f(R) theories of gravity*, arXiv:0805.1726, section II.A, (5)–(7), p. 5.
-/

open MeasureTheory Set Manifold TopologicalSpace Matrix Filter Metric
open scoped ContDiff ENNReal Topology

noncomputable section

namespace Lightlike

set_option synthInstance.maxHeartbeats 400000

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]

/-- **The fundamental lemma for symmetric tensor fields supported in a small coordinate ball.** -/
theorem symm_part_eq_zero_of_forall_chart_integral (x₁ : M) {c : Fin n → ℝ} (φ : ContDiffBump c)
    (hball : ball c φ.rOut ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target)
    (w : (Fin n → ℝ) → ℝ) (hw : Continuous w) (hwpos : ∀ y, 0 < w y)
    (E : (Fin n → ℝ) → Fin n → Fin n → ℝ) (hE : ∀ a b, Continuous fun y => E y a b)
    (hz : ∀ (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (K : Set M), IsCompact K →
      K ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).source →
      extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ '' K ⊆ ball c φ.rIn → (∀ p, p ∉ K → h.h p = 0) →
      ∫ y in extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ '' K,
        w y * ∑ α, ∑ β, h.coordComp x₁ y α β * E y α β = 0)
    {y₀ : Fin n → ℝ} (hy₀ : y₀ ∈ ball c φ.rIn) (a b : Fin n) : E y₀ a b + E y₀ b a = 0 := by
  have hrr : ball c φ.rIn ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target :=
    (ball_subset_ball φ.rIn_lt_rOut.le).trans hball
  obtain ⟨F, hF⟩ : ∃ F : (Fin n → ℝ) → ℝ, F = fun y => w y * (E y a b + E y b a) := ⟨_, rfl⟩
  have hFc : Continuous F := by
    rw [hF]
    exact hw.mul ((hE a b).add (hE b a))
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
      · rintro ⟨_, ⟨w', hw', rfl⟩, rfl⟩
        rw [(extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).right_inv (hηs hw')]
        exact hw'
      · intro hz'
        exact ⟨_, ⟨z, hz', rfl⟩, (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).right_inv (hηs hz')⟩
    have hint := hz (SymBilinField.ofChart x₁ (chartExtend x₁ η) hρ hρs S hSs) _ hKc hK0
      (by rw [himg]; exact hηb) hsupp
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
    have hsum : ∑ α, ∑ β, (η y * S α β) * E y α β = η y * (E y a b + E y b a) := by
      simp only [hS, Matrix.of_apply]
      simp [mul_add, add_mul, Finset.sum_add_distrib, ite_and, Finset.sum_ite_eq']
    simp only [hcomp]
    show η y • F y = w y * ∑ α, ∑ β, (η y * S α β) * E y α β
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
  exact (mul_eq_zero.1 hFy).resolve_left (hwpos y₀).ne'

/-- **The metric `f(R)` field equations with matter on a manifold**, for perturbations supported in small
coordinate balls. -/
theorem fR_matter_stationary_manifold_iff (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (f : ℝ → ℝ)
    (hf : ContDiff ℝ 1 f) (hf' : ContDiff ℝ 2 (deriv f)) (κ : ℝ) (hκ : κ ≠ 0)
    (SM : NondegMetric 𝓘(ℝ, Fin n → ℝ) M → ℝ)
    (Tm : M → (c : Fin n → ℝ) → ContDiffBump c → (Fin n → ℝ) → Fin n → Fin n → ℝ)
    (hTm : ∀ x₁ c φ a b, Continuous fun y => Tm x₁ c φ y a b)
    (hM : ∀ (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (K : Set M) (x₁ : M) (c : Fin n → ℝ)
      (φ : ContDiffBump c), IsCompact K → K ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).source →
      ball c φ.rOut ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target →
      extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ '' K ⊆ ball c φ.rIn → (∀ p, p ∉ K → h.h p = 0) →
      HasDerivAt (fun t : ℝ => SM (g.perturb h t))
        ((1 / 2) * ∫ y in extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ '' K, √|(g.coordMetricR x₁ φ y).det| *
          ∑ α, ∑ β, h.coordComp x₁ y α β * Tm x₁ c φ y α β) 0) :
    (∀ (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (K : Set M) (x₁ : M) (c : Fin n → ℝ)
      (φ : ContDiffBump c), IsCompact K → K ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).source →
      ball c φ.rOut ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target →
      extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ '' K ⊆ ball c φ.rIn → (∀ p, p ∉ K → h.h p = 0) →
      HasDerivAt (fun t : ℝ => (1 / (2 * κ)) * fRAction (g.perturb h t) f K + SM (g.perturb h t))
        0 0) ↔
    ∀ (x₁ : M) (c : Fin n → ℝ) (φ : ContDiffBump c),
      ball c φ.rOut ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target → ∀ y ∈ ball c φ.rIn, ∀ a b,
      fRTensorUp (g.coordMetricR x₁ φ) f y a b + fRTensorUp (g.coordMetricR x₁ φ) f y b a =
        κ * (Tm x₁ c φ y a b + Tm x₁ c φ y b a) := by
  -- the derivative of the total action for a perturbation in a small ball
  have htot : ∀ (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (K : Set M) (x₁ : M) (c : Fin n → ℝ)
      (φ : ContDiffBump c), IsCompact K → K ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).source →
      ball c φ.rOut ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target →
      extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ '' K ⊆ ball c φ.rIn → (∀ p, p ∉ K → h.h p = 0) →
      HasDerivAt (fun t : ℝ => (1 / (2 * κ)) * fRAction (g.perturb h t) f K + SM (g.perturb h t))
        (-(1 / (2 * κ)) * ∫ y in extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ '' K,
          √|(g.coordMetricR x₁ φ y).det| * ∑ α, ∑ β, h.coordComp x₁ y α β *
            (fRTensorUp (g.coordMetricR x₁ φ) f y α β - κ * Tm x₁ c φ y α β)) 0 := by
    intro h K x₁ c φ hK hK0 hball hKball hsupp
    have hG := g.contDiff_coordMetricR x₁ φ hball
    have hdet := g.det_coordMetricR_ne_zero x₁ φ hball
    have hTc : IsCompact (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ '' K) :=
      hK.image_of_continuousOn ((continuousOn_extChartAt x₁).mono hK0)
    have hsub : extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ '' K ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target := by
      rintro _ ⟨p, hp, rfl⟩
      exact (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).map_source (hK0 hp)
    have hGc : Continuous (g.coordMetricR x₁ φ) := continuous_matrix fun i j => (hG i j).continuous
    have hsq : Continuous (fun y => √|(g.coordMetricR x₁ φ y).det|) :=
      Real.continuous_sqrt.comp (continuous_abs.comp hGc.matrix_det)
    have hhc : ∀ α β, ContinuousOn (fun y => h.coordComp x₁ y α β)
        (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ '' K) := fun α β =>
      ((h.coordComp_smooth x₁ α β).continuousOn).mono hsub
    have hEc : ∀ α β, Continuous fun y => fRTensorUp (g.coordMetricR x₁ φ) f y α β := fun α β =>
      continuous_fRTensorUp (g.coordMetricR x₁ φ) hG hdet f hf hf' α β
    have iE : IntegrableOn (fun y => √|(g.coordMetricR x₁ φ y).det| *
        ∑ α, ∑ β, h.coordComp x₁ y α β * fRTensorUp (g.coordMetricR x₁ φ) f y α β)
        (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ '' K) volume :=
      (hsq.continuousOn.mul (continuousOn_finsetSum _ fun α _ => continuousOn_finsetSum _ fun β _ =>
        (hhc α β).mul (hEc α β).continuousOn)).integrableOn_compact hTc
    have iT : IntegrableOn (fun y => √|(g.coordMetricR x₁ φ y).det| *
        ∑ α, ∑ β, h.coordComp x₁ y α β * Tm x₁ c φ y α β)
        (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ '' K) volume :=
      (hsq.continuousOn.mul (continuousOn_finsetSum _ fun α _ => continuousOn_finsetSum _ fun β _ =>
        (hhc α β).mul (hTm x₁ c φ α β).continuousOn)).integrableOn_compact hTc
    have hI : ∫ y in extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ '' K, √|(g.coordMetricR x₁ φ y).det| *
          ∑ α, ∑ β, h.coordComp x₁ y α β *
            (fRTensorUp (g.coordMetricR x₁ φ) f y α β - κ * Tm x₁ c φ y α β) =
        (∫ y in extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ '' K, √|(g.coordMetricR x₁ φ y).det| *
          ∑ α, ∑ β, h.coordComp x₁ y α β * fRTensorUp (g.coordMetricR x₁ φ) f y α β) -
        κ * ∫ y in extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ '' K, √|(g.coordMetricR x₁ φ y).det| *
          ∑ α, ∑ β, h.coordComp x₁ y α β * Tm x₁ c φ y α β := by
      rw [← integral_const_mul, ← integral_sub iE (iT.const_mul κ)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      have e : ∑ α, ∑ β, h.coordComp x₁ y α β *
            (fRTensorUp (g.coordMetricR x₁ φ) f y α β - κ * Tm x₁ c φ y α β) =
          (∑ α, ∑ β, h.coordComp x₁ y α β * fRTensorUp (g.coordMetricR x₁ φ) f y α β) -
            κ * ∑ α, ∑ β, h.coordComp x₁ y α β * Tm x₁ c φ y α β := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun β _ => by ring
      show √|(g.coordMetricR x₁ φ y).det| * ∑ α, ∑ β, h.coordComp x₁ y α β *
            (fRTensorUp (g.coordMetricR x₁ φ) f y α β - κ * Tm x₁ c φ y α β) =
        √|(g.coordMetricR x₁ φ y).det| *
            (∑ α, ∑ β, h.coordComp x₁ y α β * fRTensorUp (g.coordMetricR x₁ φ) f y α β) -
          κ * (√|(g.coordMetricR x₁ φ y).det| * ∑ α, ∑ β, h.coordComp x₁ y α β * Tm x₁ c φ y α β)
      rw [e]
      ring
    have h1 := ((fR_first_variation_manifold g h x₁ hK hK0 φ hball hKball hsupp f hf hf').const_mul
      (1 / (2 * κ))).add (hM h K x₁ c φ hK hK0 hball hKball hsupp)
    refine h1.congr_deriv ?_
    rw [hI]
    field_simp
    ring
  constructor
  · intro hstat x₁ c φ hball y hy a b
    have hG := g.contDiff_coordMetricR x₁ φ hball
    have hdet := g.det_coordMetricR_ne_zero x₁ φ hball
    have hGc : Continuous (g.coordMetricR x₁ φ) := continuous_matrix fun i j => (hG i j).continuous
    have key := symm_part_eq_zero_of_forall_chart_integral x₁ φ hball
      (fun y => √|(g.coordMetricR x₁ φ y).det|)
      (Real.continuous_sqrt.comp (continuous_abs.comp hGc.matrix_det))
      (fun y => Real.sqrt_pos.2 (abs_pos.2 (hdet y)))
      (fun y a b => fRTensorUp (g.coordMetricR x₁ φ) f y a b - κ * Tm x₁ c φ y a b)
      (fun a b => (continuous_fRTensorUp (g.coordMetricR x₁ φ) hG hdet f hf hf' a b).sub
        (continuous_const.mul (hTm x₁ c φ a b)))
      (fun h K hK hK0 hKball hsupp => by
        have hu := (htot h K x₁ c φ hK hK0 hball hKball hsupp).unique
          (hstat h K x₁ c φ hK hK0 hball hKball hsupp)
        have hne : -(1 / (2 * κ)) ≠ 0 := by
          rw [neg_ne_zero]
          exact one_div_ne_zero (mul_ne_zero two_ne_zero hκ)
        exact (mul_eq_zero.1 hu).resolve_left hne) hy a b
    linarith
  · intro hfe h K x₁ c φ hK hK0 hball hKball hsupp
    have h0 : ∫ y in extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ '' K, √|(g.coordMetricR x₁ φ y).det| *
        ∑ α, ∑ β, h.coordComp x₁ y α β *
          (fRTensorUp (g.coordMetricR x₁ φ) f y α β - κ * Tm x₁ c φ y α β) = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
      rw [sum_symm_mul_eq_zero (fun α β => h.coordComp x₁ y α β)
        (fun α β => fRTensorUp (g.coordMetricR x₁ φ) f y α β - κ * Tm x₁ c φ y α β)
        (fun α β => h.coordComp_symm x₁ y α β)
        (fun α β => by have := hfe x₁ c φ hball y (hKball hy) α β; linarith), mul_zero]
    have h1 := htot h K x₁ c φ hK hK0 hball hKball hsupp
    rw [h0, mul_zero] at h1
    exact h1

end Lightlike
