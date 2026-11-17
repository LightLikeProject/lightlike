import Lightlike.CausalSets.IntervalVolume

/-!
# The Myrheim–Meyer relation probability in `3 + 1` dimensions

Two independent uniform points of the causal diamond of `ℝ^{3+1}` are related with probability
`1/20` (`relProb_three_eq`), so `n` uniform points have `n (n - 1) / 20` relations in expectation.
This is the case of spacetime dimension `4` of the Myrheim–Meyer count
`Γ(D + 1) Γ(D / 2) / (4 Γ(3 D / 2))`, which is `1/20` at `D = 4`. **Scope.** Only `D = 4` (and `D = 2`
in `Lightlike/CausalSets/Myrheim.lean`) is proved; the formula in general dimension is open
(`T-CS2-P1`). The comparison of the values with the sources is pending.

The proof counts the pairs `p ≺ q` of the diamond as `∫_{p ∈ D} vol J⁺(p) ∩ D`, where the volume of the
interval from `p` to the top of the diamond is the unit diamond volume times the fourth power of
the proper time (`Lightlike/CausalSets/IntervalVolume.lean`). The remaining integrals over the
diamond are radial: the volume of the diamond is `π / 24` and `∫_D τ⁴ = π / 480`, computed with
the polar-coordinate formula of `ℝ³` (`integral_radial_E3`). This is part of a bridge between
Lorentzian geometry and causal sets.

## References

* J. Myrheim, *Statistical geometry*, CERN preprint TH-2538 (1978).
* D. A. Meyer, *The dimension of causal sets*, PhD thesis, MIT (1988).
* S. Surya, *The causal set approach to the problem of quantum gravity*, Living Reviews in
  Relativity 22 (2019), section 2.
-/

open MeasureTheory Set
open Lightlike

namespace Lightlike.CausalSets

/-- The squared spatial length in `ℝ^{3+1}`. -/
lemma spatialSq_four (v : Fin 4 → ℝ) : spatialSq v = v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 := by
  simp [spatialSq, Fin.sum_univ_succ, add_assoc]

lemma gamma_five_half : Real.Gamma (5 / 2) = 3 * √Real.pi / 4 := by
  have h1 : Real.Gamma (5 / 2) = 3 / 2 * Real.Gamma (3 / 2) := by
    rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num)]
  have h2 : Real.Gamma (3 / 2) = 1 / 2 * Real.Gamma (1 / 2) := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num)]
  rw [h1, h2, Real.Gamma_one_half_eq]; ring

lemma volume_ball_E3 : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1)).toReal = 4 * Real.pi / 3 := by
  rw [EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin]
  norm_num
  rw [gamma_five_half]
  rw [ENNReal.toReal_ofReal (by positivity)]
  have hp : 0 < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have : √Real.pi ^ 3 = Real.pi * √Real.pi := by
    rw [pow_succ, Real.sq_sqrt Real.pi_pos.le]
  rw [this]; field_simp

lemma integral_radial_E3 (f : ℝ → ℝ) :
    ∫ x : EuclideanSpace ℝ (Fin 3), f ‖x‖ = 4 * Real.pi * ∫ y in Ioi (0 : ℝ), y ^ 2 * f y := by
  rw [integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin 3))) f]
  simp only [finrank_euclideanSpace, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat]
  rw [Measure.real, volume_ball_E3]
  norm_num
  ring

lemma integral_fin3 (g : ℝ → ℝ) :
    ∫ x : Fin 3 → ℝ, g (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) =
      4 * Real.pi * ∫ y in Ioi (0 : ℝ), y ^ 2 * g (y ^ 2) := by
  rw [← integral_radial_E3 (fun y => g (y ^ 2))]
  have hmp := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)
  rw [← hmp.integral_comp' ]
  congr 1
  funext x
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_succ]
  rw [Real.sq_sqrt (by positivity)]; ring_nf

lemma symm_fin4 (t : ℝ) (x : Fin 3 → ℝ) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).symm (t, x) 0 = t ∧
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).symm (t, x) 1 = x 0 ∧
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).symm (t, x) 2 = x 1 ∧
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).symm (t, x) 3 = x 2 := by
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply]
  exact ⟨rfl, rfl⟩

lemma integral_fin4 (Φ : ℝ → ℝ → ℝ)
    (hint : Integrable (fun p : Fin 4 → ℝ => Φ (p 0) (p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2))) :
    ∫ p : Fin 4 → ℝ, Φ (p 0) (p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2) =
      ∫ t : ℝ, 4 * Real.pi * ∫ y in Ioi (0 : ℝ), y ^ 2 * Φ t (y ^ 2) := by
  have hmp : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0) volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0
  have hfun : (fun q : ℝ × (Fin 3 → ℝ) => Φ q.1 (q.2 0 ^ 2 + q.2 1 ^ 2 + q.2 2 ^ 2)) =
      (fun p : Fin 4 → ℝ => Φ (p 0) (p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2)) ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).symm := by
    funext q
    obtain ⟨h0, h1, h2, h3⟩ := symm_fin4 q.1 q.2
    simp only [Function.comp, h0, h1, h2, h3]
  have hint' : Integrable (fun q : ℝ × (Fin 3 → ℝ) => Φ q.1 (q.2 0 ^ 2 + q.2 1 ^ 2 + q.2 2 ^ 2)) := by
    rw [hfun]
    exact hmp.symm.integrable_comp_emb ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).symm.measurableEmbedding) |>.2 hint
  have h1 : ∫ p : Fin 4 → ℝ, Φ (p 0) (p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2) =
      ∫ q : ℝ × (Fin 3 → ℝ), Φ q.1 (q.2 0 ^ 2 + q.2 1 ^ 2 + q.2 2 ^ 2) := by
    rw [hfun]
    exact (hmp.symm.integral_comp' (fun p : Fin 4 → ℝ => Φ (p 0) (p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2))).symm
  rw [h1, Measure.volume_eq_prod, integral_prod _ hint']
  congr 1
  funext t
  exact integral_fin3 (fun s => Φ t s)

lemma mem_diamond3 (p : Fin 4 → ℝ) : p ∈ diamond 3 ↔
    0 ≤ p 0 ∧ p 0 ≤ 1 ∧ p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 ≤ p 0 ^ 2 ∧
      p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 ≤ (1 - p 0) ^ 2 := by
  show coneLE 0 p ∧ coneLE p (diamondTop 3) ↔ _
  rw [coneLE_iff_spatial, coneLE_iff_spatial]
  have h1 : spatialSq (p - 0) = p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 := by rw [spatialSq_four]; simp
  have h2 : spatialSq (diamondTop 3 - p) = p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 := by
    rw [spatialSq_four]; simp [diamondTop]
  rw [h1, h2]
  simp only [Pi.sub_apply, Pi.zero_apply, sub_zero, diamondTop, Pi.single_eq_same]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩
    exact ⟨a, by linarith, b, d⟩
  · rintro ⟨a, b, c, d⟩
    exact ⟨⟨a, c⟩, ⟨by linarith, d⟩⟩

/-- The slice function of the diamond: `g t s` when `(t, s)` is the time and the squared spatial
length of a point of the diamond, and `0` otherwise. -/
noncomputable def phiD (g : ℝ → ℝ → ℝ) (t s : ℝ) : ℝ :=
  if 0 ≤ t ∧ t ≤ 1 ∧ s ≤ t ^ 2 ∧ s ≤ (1 - t) ^ 2 then g t s else 0

lemma phiD_eq (g : ℝ → ℝ → ℝ) (p : Fin 4 → ℝ) :
    phiD g (p 0) (p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2) =
      (diamond 3).indicator (fun p : Fin 4 → ℝ => g (p 0) (p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2)) p := by
  unfold phiD
  by_cases h : p ∈ diamond 3
  · rw [Set.indicator_of_mem h]
    split_ifs with hc
    · rfl
    · exact absurd ((mem_diamond3 p).1 h) hc
  · rw [Set.indicator_of_notMem h]
    split_ifs with hc
    · exact absurd ((mem_diamond3 p).2 hc) h
    · rfl

lemma diamond3_compact : IsCompact (diamond 3) := by
  refine IsCompact.of_isClosed_subset (isCompact_univ_pi fun _ => isCompact_Icc (a := (-1 : ℝ)) (b := 1))
    (diamond_isClosed 3) (diamond_subset_box 3)

lemma phiD_integrable {g : ℝ → ℝ → ℝ} (hg : Continuous (Function.uncurry g)) :
    Integrable (fun p : Fin 4 → ℝ => phiD g (p 0) (p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2)) := by
  simp_rw [phiD_eq]
  rw [integrable_indicator_iff (diamond_measurableSet 3)]
  refine ContinuousOn.integrableOn_compact diamond3_compact ?_
  have : Continuous fun p : Fin 4 → ℝ => g (p 0) (p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2) :=
    hg.comp (by fun_prop : Continuous fun p : Fin 4 → ℝ => (p 0, p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2))
  exact this.continuousOn

lemma slice_inner (g : ℝ → ℝ → ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∫ y in Ioi (0 : ℝ), y ^ 2 * phiD g t (y ^ 2) =
      ∫ y in (0 : ℝ)..(min t (1 - t)), y ^ 2 * g t (y ^ 2) := by
  have hm : 0 ≤ min t (1 - t) := le_min ht0 (by linarith)
  have h1 : ∀ y ∈ Ioi (0 : ℝ), y ^ 2 * phiD g t (y ^ 2) =
      Set.indicator (Iic (min t (1 - t))) (fun y => y ^ 2 * g t (y ^ 2)) y := by
    intro y hy
    have hy0 : 0 < y := hy
    unfold phiD
    by_cases h : y ≤ min t (1 - t)
    · rw [Set.indicator_of_mem (mem_Iic.2 h)]
      have hc : 0 ≤ t ∧ t ≤ 1 ∧ y ^ 2 ≤ t ^ 2 ∧ y ^ 2 ≤ (1 - t) ^ 2 :=
        ⟨ht0, ht1, pow_le_pow_left₀ hy0.le (h.trans (min_le_left _ _)) 2,
          pow_le_pow_left₀ hy0.le (h.trans (min_le_right _ _)) 2⟩
      simp only [hc, and_self, ite_true]
    · rw [Set.indicator_of_notMem (by simpa using h)]
      have hc : ¬ (0 ≤ t ∧ t ≤ 1 ∧ y ^ 2 ≤ t ^ 2 ∧ y ^ 2 ≤ (1 - t) ^ 2) := by
        rintro ⟨_, _, h3, h4⟩
        apply h
        apply le_min
        · nlinarith [hy0, ht0]
        · nlinarith [hy0, ht1]
      simp only [hc, ite_false, mul_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi h1, integral_indicator measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic, intervalIntegral.integral_of_le hm]
  congr 2
  ext y; simp [and_comm]

lemma outer_formula {g : ℝ → ℝ → ℝ} (hg : Continuous (Function.uncurry g)) :
    ∫ p : Fin 4 → ℝ, phiD g (p 0) (p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2) =
      4 * Real.pi * ∫ t in (0 : ℝ)..1, ∫ y in (0 : ℝ)..(min t (1 - t)), y ^ 2 * g t (y ^ 2) := by
  rw [integral_fin4 (phiD g) (phiD_integrable hg), integral_const_mul]
  congr 1
  have hzero : ∀ t ∉ Icc (0 : ℝ) 1, ∫ y in Ioi (0 : ℝ), y ^ 2 * phiD g t (y ^ 2) = 0 := by
    intro t ht
    have : ∀ y : ℝ, phiD g t (y ^ 2) = 0 := by
      intro y; unfold phiD
      have hc : ¬ (0 ≤ t ∧ t ≤ 1 ∧ y ^ 2 ≤ t ^ 2 ∧ y ^ 2 ≤ (1 - t) ^ 2) := by
        rintro ⟨a, b, _⟩; exact ht ⟨a, b⟩
      simp only [hc, ite_false]
    simp [this]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero, intervalIntegral.integral_of_le zero_le_one,
    integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
  exact slice_inner g ht.1.le ht.2

lemma inner_poly (c m : ℝ) :
    ∫ y in (0 : ℝ)..m, y ^ 2 * (c - y ^ 2) ^ 2 = c ^ 2 * m ^ 3 / 3 - 2 * c * m ^ 5 / 5 + m ^ 7 / 7 := by
  have : ∀ y : ℝ, y ^ 2 * (c - y ^ 2) ^ 2 = c ^ 2 * y ^ 2 - 2 * c * y ^ 4 + y ^ 6 := by intro y; ring
  simp_rw [this]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  · simp [integral_pow]; ring
  all_goals first | exact (by fun_prop : Continuous fun y : ℝ => _).intervalIntegrable _ _

lemma split_half (h : ℝ → ℝ → ℝ) (hc : Continuous fun t : ℝ => h t (min t (1 - t))) :
    ∫ t in (0 : ℝ)..1, h t (min t (1 - t)) =
      (∫ t in (0 : ℝ)..(1 / 2), h t t) + ∫ t in (1 / 2 : ℝ)..1, h t (1 - t) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1 / 2) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  congr 1
  · refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le (by norm_num)] at ht
    simp only [min_eq_left (show t ≤ 1 - t by linarith [ht.2])]
  · refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le (by norm_num)] at ht
    simp only [min_eq_right (show 1 - t ≤ t by linarith [ht.1])]

lemma volume_diamond3_real : (volume (diamond 3)).toReal = Real.pi / 24 := by
  have h1 : (volume (diamond 3)).toReal = ∫ p : Fin 4 → ℝ, (diamond 3).indicator (fun _ => (1 : ℝ)) p := by
    rw [show (diamond 3).indicator (fun _ => (1 : ℝ)) = (diamond 3).indicator (1 : (Fin 4 → ℝ) → ℝ) from rfl,
      integral_indicator_one (diamond_measurableSet 3), Measure.real]
  have h2 : ∫ p : Fin 4 → ℝ, (diamond 3).indicator (fun _ => (1 : ℝ)) p =
      ∫ p : Fin 4 → ℝ, phiD (fun _ _ => 1) (p 0) (p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2) := by
    congr 1; funext p; rw [phiD_eq]
  rw [h1, h2, outer_formula (g := fun _ _ => 1) (by fun_prop)]
  have : ∀ m : ℝ, ∫ y in (0 : ℝ)..m, y ^ 2 * (1 : ℝ) = m ^ 3 / 3 := by
    intro m; simp [integral_pow]; norm_num
  simp_rw [this]
  rw [split_half (fun _ m => m ^ 3 / 3) (by fun_prop)]
  have e2 : ∫ t in (1 / 2 : ℝ)..1, (1 - t) ^ 3 / 3 = 1 / 192 := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ 3) 1]
    simp [integral_pow]; norm_num
  have e1 : ∫ t in (0 : ℝ)..(1 / 2), t ^ 3 / 3 = 1 / 192 := by
    rw [intervalIntegral.integral_div]; simp [integral_pow]; norm_num
  rw [e1, e2]; ring

lemma integral_tau4_real :
    ∫ p : Fin 4 → ℝ, (diamond 3).indicator
        (fun p : Fin 4 → ℝ => ((1 - p 0) ^ 2 - (p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2)) ^ 2) p =
      Real.pi / 480 := by
  have h2 : ∫ p : Fin 4 → ℝ, (diamond 3).indicator
        (fun p : Fin 4 → ℝ => ((1 - p 0) ^ 2 - (p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2)) ^ 2) p =
      ∫ p : Fin 4 → ℝ, phiD (fun t s => ((1 - t) ^ 2 - s) ^ 2) (p 0) (p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2) := by
    congr 1; funext p; rw [phiD_eq]
  rw [h2, outer_formula (g := fun t s => ((1 - t) ^ 2 - s) ^ 2) (by fun_prop)]
  simp only [inner_poly]
  rw [split_half (fun t m => ((1 - t) ^ 2) ^ 2 * m ^ 3 / 3 - 2 * (1 - t) ^ 2 * m ^ 5 / 5 + m ^ 7 / 7)
    (by fun_prop)]
  have e1 : ∫ t in (0 : ℝ)..(1 / 2), (((1 - t) ^ 2) ^ 2 * t ^ 3 / 3 - 2 * (1 - t) ^ 2 * t ^ 5 / 5 + t ^ 7 / 7) =
      13 / 26880 := by
    have : ∀ t : ℝ, ((1 - t) ^ 2) ^ 2 * t ^ 3 / 3 - 2 * (1 - t) ^ 2 * t ^ 5 / 5 + t ^ 7 / 7 =
        8 / 105 * t ^ 7 - 8 / 15 * t ^ 6 + 8 / 5 * t ^ 5 - 4 / 3 * t ^ 4 + 1 / 3 * t ^ 3 := by
      intro t; ring
    simp_rw [this]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_sub, intervalIntegral.integral_add,
      intervalIntegral.integral_sub, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    · simp [integral_pow]; norm_num
    all_goals first | exact (by fun_prop : Continuous fun y : ℝ => _).intervalIntegrable _ _
  have e2 : ∫ t in (1 / 2 : ℝ)..1, (((1 - t) ^ 2) ^ 2 * (1 - t) ^ 3 / 3 - 2 * (1 - t) ^ 2 * (1 - t) ^ 5 / 5 +
      (1 - t) ^ 7 / 7) = 1 / 26880 := by
    have : ∀ t : ℝ, ((1 - t) ^ 2) ^ 2 * (1 - t) ^ 3 / 3 - 2 * (1 - t) ^ 2 * (1 - t) ^ 5 / 5 +
        (1 - t) ^ 7 / 7 = 8 / 105 * (1 - t) ^ 7 := by intro t; ring
    simp_rw [this]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ 7) 1]
    simp [integral_pow]; norm_num
  rw [e1, e2]; ring

lemma volume_above (p : Fin 4 → ℝ) (hp : p ∈ diamond 3) :
    MeasureTheory.volume {q : Fin 4 → ℝ | coneLE p q ∧ coneLE q (diamondTop 3)} =
      ENNReal.ofReal (((1 - p 0) ^ 2 - (p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2)) ^ 2) *
        MeasureTheory.volume (diamond 3) := by
  have hset : {q : Fin 4 → ℝ | coneLE p q ∧ coneLE q (diamondTop 3)} =
      (fun q => q + (-p)) ⁻¹' intervalSet (diamondTop 3 - p) := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, intervalSet]
    have e1 : q + -p - 0 = q - p := by simp [sub_eq_add_neg]
    have e2 : diamondTop 3 - p - (q + -p) = diamondTop 3 - q := by abel
    simp only [coneLE, e1, e2]
  rw [hset, measure_preimage_add_right]
  have hF : Fut (diamondTop 3 - p) := by
    rw [Fut_iff_coneLE]; exact hp.2
  rw [volume_interval_all (by norm_num) hF]
  have h0 : (diamondTop 3 - p) 0 = 1 - p 0 := by simp [diamondTop]
  have hs : spatialSq (diamondTop 3 - p) = p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 := by
    rw [spatialSq_four]; simp [diamondTop]
  have hx : 0 ≤ (1 - p 0) ^ 2 - (p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2) := by
    have := hF.2; rw [h0, hs] at this; linarith
  rw [h0, hs]
  congr 2
  rw [show (3 + 1 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hx]

lemma slice_measure (p : Fin 4 → ℝ) (hp : p ∈ diamond 3) :
    (MeasureTheory.volume.restrict (diamond 3)) {q : Fin 4 → ℝ | coneLT p q} =
      ENNReal.ofReal (((1 - p 0) ^ 2 - (p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2)) ^ 2) *
        MeasureTheory.volume (diamond 3) := by
  have hm : MeasurableSet {q : Fin 4 → ℝ | coneLT p q} := by
    have : {q : Fin 4 → ℝ | coneLT p q} = {q | coneLE p q} ∩ {q | p ≠ q} := rfl
    rw [this]
    refine MeasurableSet.inter ?_ ?_
    · have : {q : Fin 4 → ℝ | coneLE p q} = {q | 0 ≤ (q - p) 0} ∩
          {q | minkowskiForm (4 : ℕ) (q - p) (q - p) ≤ 0} := rfl
      rw [this]
      simp only [minkowskiForm_apply]
      exact (isClosed_le (by fun_prop) (by fun_prop)).measurableSet.inter
        (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
    · exact (measurableSet_singleton p).compl.congr (by ext q; simp [eq_comm])
  rw [Measure.restrict_apply hm]
  have hset : {q : Fin 4 → ℝ | coneLT p q} ∩ diamond 3 =
      {q : Fin 4 → ℝ | coneLE p q ∧ coneLE q (diamondTop 3)} \ {p} := by
    ext q
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, coneLT, diamond, Set.mem_sdiff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨h1, h4⟩, fun h => h2 h.symm⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, fun h => h3 h.symm⟩, coneLE_trans hp.1 h1, h2⟩
  rw [hset, measure_sdiff_null (measure_singleton p), volume_above p hp]

lemma coneLT_measurable3 : MeasurableSet {p : (Fin 4 → ℝ) × (Fin 4 → ℝ) | coneLT p.1 p.2} :=
  coneLT_measurableSet 3

/-- **The Myrheim–Meyer probability in four dimensions**: two uniform points of the causal diamond of
`ℝ^{3+1}` are related with probability `1/20`. -/
theorem relProb_three_eq : relProb 3 = 1 / 20 := by
  rw [relProb_eq]
  unfold diamondMeasure regionMeasure ProbabilityTheory.cond
  set V := MeasureTheory.volume (diamond 3) with hV
  have hVr : V = ENNReal.ofReal (Real.pi / 24) := by
    rw [hV, ← ENNReal.ofReal_toReal (volume_diamond_lt_top 3).ne, volume_diamond3_real]
  rw [Measure.prod_smul_left, Measure.prod_smul_right]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Measure.prod_apply coneLT_measurable3]
  have hint : ∀ p ∈ diamond 3, (MeasureTheory.volume.restrict (diamond 3))
      (Prod.mk p ⁻¹' {q : (Fin 4 → ℝ) × (Fin 4 → ℝ) | coneLT q.1 q.2}) =
      ENNReal.ofReal (((1 - p 0) ^ 2 - (p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2)) ^ 2) * V := fun p hp =>
    slice_measure p hp
  rw [setLIntegral_congr_fun (diamond_measurableSet 3) hint]
  have hgc : Continuous fun p : Fin 4 → ℝ => ((1 - p 0) ^ 2 - (p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2)) ^ 2 := by
    fun_prop
  have hI : ∫⁻ p in diamond 3, ENNReal.ofReal (((1 - p 0) ^ 2 - (p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2)) ^ 2) =
      ENNReal.ofReal (Real.pi / 480) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hgc.continuousOn.integrableOn_compact diamond3_compact)
      (Filter.Eventually.of_forall fun p => sq_nonneg _)]
    congr 1
    rw [← integral_tau4_real, integral_indicator (diamond_measurableSet 3)]
  rw [lintegral_mul_const _ (hgc.measurable.ennreal_ofReal), hI, hVr]
  have hpos : (0 : ℝ) < Real.pi / 24 := by positivity
  rw [← mul_assoc, ← mul_assoc, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal hpos.le, ENNReal.toReal_ofReal (by positivity)]
  field_simp
  ring

/-- **Expected number of relations in `3 + 1` dimensions**: `n` uniform points of the causal diamond
have `n (n - 1) / 20` pairs `x ≺ y` in expectation (the case `D = 4` of the Myrheim–Meyer count). -/
theorem expected_relations_diamond_three (n : ℕ) :
    ∫ ω, (relCount {p : (Fin 4 → ℝ) × (Fin 4 → ℝ) | coneLT p.1 p.2} ω : ℝ)
        ∂Measure.pi (fun _ : Fin n => diamondMeasure 3) = (n : ℝ) * (n - 1) / 20 := by
  rw [expected_relations_diamond, relProb_three_eq]; ring

end Lightlike.CausalSets
