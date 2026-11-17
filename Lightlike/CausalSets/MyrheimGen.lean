import Lightlike.CausalSets.IntervalVolume
import Lightlike.CausalSets.BetaReal
import Lightlike.CausalSets.Myrheim

/-!
# The Myrheim–Meyer relation probability in every dimension

Two independent uniform points of the causal diamond of Minkowski space `ℝ^{d+1}` are related with
probability `Γ(D + 1) Γ(D / 2) / (4 Γ(3 D / 2))` in the dimension `D = d + 1` (`myrheimMeyer_eq`), so
`n` uniform points have `n (n - 1)` times this many relations in expectation
(`expected_relations_diamond`).

**The proof.** The pairs `p ≺ q` of the diamond are counted as `∫_{p ∈ D} vol J⁺(p) ∩ D`, and the volume
of the causal interval from `p` to the top of the diamond is the volume of the unit diamond `V` times
the power `d + 1` of the proper time (`Lightlike/CausalSets/IntervalVolume.lean`), so the probability is
`∫_D τ^(d+1) / V`. Both integrals are radial: the polar-coordinate formula of `ℝ^d` gives the volume of
the diamond, `V = ω_d 2^(-d) / (d + 1)`, and `∫_D τ^(d+1) = d ω_d K` with `K` the integral of
`r^(d-1) (t² - r²)^((d+1)/2)` over the half diamond. In the light-cone coordinates `u = t - r`,
`v = t + r` the half diamond is the triangle `0 ≤ u ≤ v ≤ 1`, and the substitution `u = v s` turns `K`
into a Beta integral, `K = 2^(-d) B((d + 3) / 2, d) / (2 d + 2)`. The ratio is `(d / 2) B((d + 3) / 2, d)`,
which is the Gamma expression. The case `d = 0` (time only) is the probability `1/2` that two uniform
points of an interval are ordered. This is part of a bridge between Lorentzian geometry and causal sets.

## References

* J. Myrheim, *Statistical geometry*, CERN preprint TH-2538 (1978).
* D. A. Meyer, *The dimension of causal sets*, PhD thesis, MIT (1988).
* S. Surya, *The causal set approach to the problem of quantum gravity*, Living Reviews in
  Relativity 22 (2019), section 2.
-/

open MeasureTheory Set
open Lightlike

namespace Lightlike.CausalSets

variable {d : ℕ}

/-- The volume of the unit ball of Euclidean space `ℝ^d`, `π^(d/2) / Γ(d/2 + 1)`. -/
noncomputable def ballVol (d : ℕ) : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal

lemma integral_fin_gen (hd : 0 < d) (g : ℝ → ℝ) :
    ∫ x : Fin d → ℝ, g (∑ i, x i ^ 2) = d * ballVol d * ∫ y in Ioi (0 : ℝ), y ^ (d - 1) * g (y ^ 2) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have h1 := integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin d))) (fun y => g (y ^ 2))
  have hmp := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)
  rw [← hmp.integral_comp']
  have h2 : ∀ x : EuclideanSpace ℝ (Fin d), g (∑ i, ((MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm x) i ^ 2) =
      g (‖x‖ ^ 2) := by
    intro x
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    simp
  simp only [h2]
  rw [h1]
  simp only [finrank_euclideanSpace, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul, Measure.real, ballVol]
  ring

lemma symm_fin (t : ℝ) (x : Fin d → ℝ) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm (t, x) 0 = t ∧
    ∀ i : Fin d, (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm (t, x) i.succ = x i := by
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply]

lemma integral_fin_succ (hd : 0 < d) (Φ : ℝ → ℝ → ℝ)
    (hint : Integrable (fun p : Fin (d + 1) → ℝ => Φ (p 0) (spatialSq p))) :
    ∫ p : Fin (d + 1) → ℝ, Φ (p 0) (spatialSq p) =
      ∫ t : ℝ, d * ballVol d * ∫ y in Ioi (0 : ℝ), y ^ (d - 1) * Φ t (y ^ 2) := by
  have hmp : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0) volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
  have hfun : (fun q : ℝ × (Fin d → ℝ) => Φ q.1 (∑ i, q.2 i ^ 2)) =
      (fun p : Fin (d + 1) → ℝ => Φ (p 0) (spatialSq p)) ∘
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm := by
    funext q
    obtain ⟨h0, h1⟩ := symm_fin q.1 q.2
    simp only [Function.comp, h0, spatialSq_eq_sum, h1]
  have hint' : Integrable (fun q : ℝ × (Fin d → ℝ) => Φ q.1 (∑ i, q.2 i ^ 2)) := by
    rw [hfun]
    exact hmp.symm.integrable_comp_emb
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm.measurableEmbedding) |>.2 hint
  have h1 : ∫ p : Fin (d + 1) → ℝ, Φ (p 0) (spatialSq p) =
      ∫ q : ℝ × (Fin d → ℝ), Φ q.1 (∑ i, q.2 i ^ 2) := by
    rw [hfun]
    exact (hmp.symm.integral_comp' (fun p : Fin (d + 1) → ℝ => Φ (p 0) (spatialSq p))).symm
  rw [h1, Measure.volume_eq_prod, integral_prod _ hint']
  congr 1
  funext t
  exact integral_fin_gen hd (fun s => Φ t s)

lemma mem_diamond_gen (p : Fin (d + 1) → ℝ) : p ∈ diamond d ↔
    0 ≤ p 0 ∧ p 0 ≤ 1 ∧ spatialSq p ≤ p 0 ^ 2 ∧ spatialSq p ≤ (1 - p 0) ^ 2 := by
  show coneLE 0 p ∧ coneLE p (diamondTop d) ↔ _
  rw [coneLE_iff_spatial, coneLE_iff_spatial]
  have h1 : spatialSq (p - 0) = spatialSq p := by simp
  have h2 : spatialSq (diamondTop d - p) = spatialSq p := by
    simp [spatialSq_eq_sum, diamondTop, Fin.succ_ne_zero]
  rw [h1, h2]
  simp only [Pi.sub_apply, Pi.zero_apply, sub_zero, diamondTop, Pi.single_eq_same]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨c, e⟩⟩
    exact ⟨a, by linarith, b, e⟩
  · rintro ⟨a, b, c, e⟩
    exact ⟨⟨a, c⟩, ⟨by linarith, e⟩⟩

/-- The slice function of the diamond: `g t s` when `(t, s)` is the time and the squared spatial
length of a point of the diamond, and `0` otherwise. -/
noncomputable def phiD (g : ℝ → ℝ → ℝ) (t s : ℝ) : ℝ :=
  if 0 ≤ t ∧ t ≤ 1 ∧ s ≤ t ^ 2 ∧ s ≤ (1 - t) ^ 2 then g t s else 0

lemma phiD_eq (g : ℝ → ℝ → ℝ) (p : Fin (d + 1) → ℝ) :
    phiD g (p 0) (spatialSq p) = (diamond d).indicator (fun p : Fin (d + 1) → ℝ => g (p 0) (spatialSq p)) p := by
  unfold phiD
  by_cases h : p ∈ diamond d
  · rw [Set.indicator_of_mem h]
    split_ifs with hc
    · rfl
    · exact absurd ((mem_diamond_gen p).1 h) hc
  · rw [Set.indicator_of_notMem h]
    split_ifs with hc
    · exact absurd ((mem_diamond_gen p).2 hc) h
    · rfl

lemma diamond_compact (d : ℕ) : IsCompact (diamond d) := by
  refine IsCompact.of_isClosed_subset
    (isCompact_univ_pi fun _ => isCompact_Icc (a := (-1 : ℝ)) (b := 1))
    (diamond_isClosed d) (diamond_subset_box d)

lemma continuous_spatialSq : Continuous fun p : Fin (d + 1) → ℝ => spatialSq p := by
  simp only [spatialSq_eq_sum]; fun_prop

lemma phiD_integrable {g : ℝ → ℝ → ℝ} (hg : ContinuousOn (Function.uncurry g) (univ : Set (ℝ × ℝ))) :
    Integrable (fun p : Fin (d + 1) → ℝ => phiD g (p 0) (spatialSq p)) := by
  simp_rw [phiD_eq]
  rw [integrable_indicator_iff (diamond_measurableSet d)]
  refine ContinuousOn.integrableOn_compact (diamond_compact d) ?_
  have : Continuous fun p : Fin (d + 1) → ℝ => (p 0, spatialSq p) :=
    (by fun_prop : Continuous fun p : Fin (d + 1) → ℝ => p 0).prodMk continuous_spatialSq
  exact (hg.comp this.continuousOn (fun _ _ => mem_univ _))

lemma slice_inner (g : ℝ → ℝ → ℝ) (d : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∫ y in Ioi (0 : ℝ), y ^ (d - 1) * phiD g t (y ^ 2) =
      ∫ y in (0 : ℝ)..(min t (1 - t)), y ^ (d - 1) * g t (y ^ 2) := by
  have hm : 0 ≤ min t (1 - t) := le_min ht0 (by linarith)
  have h1 : ∀ y ∈ Ioi (0 : ℝ), y ^ (d - 1) * phiD g t (y ^ 2) =
      Set.indicator (Iic (min t (1 - t))) (fun y => y ^ (d - 1) * g t (y ^ 2)) y := by
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

lemma outer_formula (hd : 0 < d) {g : ℝ → ℝ → ℝ} (hg : ContinuousOn (Function.uncurry g) (univ : Set (ℝ × ℝ))) :
    ∫ p : Fin (d + 1) → ℝ, phiD g (p 0) (spatialSq p) =
      d * ballVol d * ∫ t in (0 : ℝ)..1, ∫ y in (0 : ℝ)..(min t (1 - t)), y ^ (d - 1) * g t (y ^ 2) := by
  rw [integral_fin_succ hd (phiD g) (phiD_integrable hg), integral_const_mul]
  congr 1
  have hzero : ∀ t ∉ Icc (0 : ℝ) 1, ∫ y in Ioi (0 : ℝ), y ^ (d - 1) * phiD g t (y ^ 2) = 0 := by
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
  exact slice_inner g d ht.1.le ht.2

/-- The integrand of the proper-time integral over the diamond in the coordinates `(t, r)` of time
and spatial radius: `r^(d-1) (t² - r²)^((d+1)/2)` on the half diamond `0 ≤ r ≤ min(t, 1 - t)`. -/
noncomputable def Ghat (d : ℕ) (q : ℝ × ℝ) : ℝ :=
  if 0 ≤ q.1 ∧ q.1 ≤ 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ q.1 ∧ q.2 ≤ 1 - q.1 then
    q.2 ^ (d - 1) * (q.1 ^ 2 - q.2 ^ 2) ^ (((d : ℝ) + 1) / 2) else 0

/-- The light-cone change of coordinates `(u, v) ↦ ((u + v) / 2, (v - u) / 2)`, from `u = t - r`,
`v = t + r` back to time and radius. -/
noncomputable def lcMap : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ where
  toFun q := ((q.1 + q.2) / 2, (q.2 - q.1) / 2)
  map_add' x y := by ext <;> simp <;> ring
  map_smul' c x := by ext <;> simp <;> ring

lemma Ghat_lcMap (d : ℕ) (q : ℝ × ℝ) :
    Ghat d (lcMap q) = if 0 ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.2 ≤ 1 then
      ((q.2 - q.1) / 2) ^ (d - 1) * (q.1 * q.2) ^ (((d : ℝ) + 1) / 2) else 0 := by
  unfold Ghat
  simp only [lcMap, LinearMap.coe_mk, AddHom.coe_mk]
  have hv : ((q.1 + q.2) / 2) ^ 2 - ((q.2 - q.1) / 2) ^ 2 = q.1 * q.2 := by ring
  rw [hv]
  by_cases h : 0 ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.2 ≤ 1
  · have h' : 0 ≤ (q.1 + q.2) / 2 ∧ (q.1 + q.2) / 2 ≤ 1 ∧ 0 ≤ (q.2 - q.1) / 2 ∧
        (q.2 - q.1) / 2 ≤ (q.1 + q.2) / 2 ∧ (q.2 - q.1) / 2 ≤ 1 - (q.1 + q.2) / 2 := by
      refine ⟨by linarith [h.1, h.2.1], by linarith [h.1, h.2.2], by linarith [h.2.1], by linarith [h.1], by linarith [h.2.2]⟩
    simp only [h', h, if_true, and_self]
  · have h' : ¬ (0 ≤ (q.1 + q.2) / 2 ∧ (q.1 + q.2) / 2 ≤ 1 ∧ 0 ≤ (q.2 - q.1) / 2 ∧
        (q.2 - q.1) / 2 ≤ (q.1 + q.2) / 2 ∧ (q.2 - q.1) / 2 ≤ 1 - (q.1 + q.2) / 2) := by
      rintro ⟨a, b, c, e, f⟩
      exact h ⟨by linarith, by linarith, by linarith⟩
    simp only [h', h, if_false]

lemma lintegral_half {f : ℝ → ENNReal} (hf : Measurable f) (v : ℝ) :
    ∫⁻ u : ℝ, f ((u + v) / 2) = 2 * ∫⁻ t : ℝ, f t := by
  have h1 : ∫⁻ u : ℝ, f ((u + v) / 2) = ∫⁻ u : ℝ, (fun w => f (w / 2)) (u + v) := rfl
  rw [h1, lintegral_add_right_eq_self (fun w => f (w / 2)) v]
  have h2 := Real.map_volume_mul_left (a := (1 / 2 : ℝ)) (by norm_num)
  have h3 : ∫⁻ u : ℝ, f (u / 2) = ∫⁻ u : ℝ, f ((1 / 2 : ℝ) * u) := by
    congr 1; funext u; congr 1; ring
  rw [h3, ← lintegral_map hf (measurable_const_mul (1 / 2 : ℝ)), h2, lintegral_smul_measure]
  simp

lemma Ghat_measurable (d : ℕ) : Measurable (Ghat d) := by
  unfold Ghat
  refine Measurable.ite ?_ ?_ measurable_const
  · refine MeasurableSet.inter (measurableSet_le measurable_const measurable_fst) ?_
    refine MeasurableSet.inter (measurableSet_le measurable_fst measurable_const) ?_
    refine MeasurableSet.inter (measurableSet_le measurable_const measurable_snd) ?_
    exact MeasurableSet.inter (measurableSet_le measurable_snd measurable_fst)
      (measurableSet_le measurable_snd (measurable_const.sub measurable_fst))
  · fun_prop

lemma Lval_eq (d : ℕ) :
    ∫⁻ t : ℝ, ∫⁻ r : ℝ, ENNReal.ofReal (Ghat d (t, r)) =
      2⁻¹ * ∫⁻ v : ℝ, ∫⁻ u : ℝ, ENNReal.ofReal (Ghat d (lcMap (u, v))) := by
  have hmeas : Measurable fun q : ℝ × ℝ => ENNReal.ofReal (Ghat d q) :=
    (Ghat_measurable d).ennreal_ofReal
  have h1 : ∀ t : ℝ, ∫⁻ r : ℝ, ENNReal.ofReal (Ghat d (t, r)) =
      ∫⁻ v : ℝ, ENNReal.ofReal (Ghat d (t, v - t)) := by
    intro t
    have := lintegral_add_right_eq_self (μ := volume) (fun r : ℝ => ENNReal.ofReal (Ghat d (t, r))) (-t)
    simpa [sub_eq_add_neg] using this.symm
  simp_rw [h1]
  have hm2 : Measurable fun q : ℝ × ℝ => ENNReal.ofReal (Ghat d (q.1, q.2 - q.1)) :=
    hmeas.comp (by fun_prop)
  rw [lintegral_lintegral_swap hm2.aemeasurable]
  have h3 : ∀ v : ℝ, ∫⁻ t : ℝ, ENNReal.ofReal (Ghat d (t, v - t)) =
      2⁻¹ * ∫⁻ u : ℝ, ENNReal.ofReal (Ghat d (lcMap (u, v))) := by
    intro v
    have hf : Measurable fun t : ℝ => ENNReal.ofReal (Ghat d (t, v - t)) :=
      hmeas.comp (by fun_prop)
    have := lintegral_half hf v
    have e : ∀ u : ℝ, ENNReal.ofReal (Ghat d (lcMap (u, v))) =
        ENNReal.ofReal (Ghat d ((u + v) / 2, v - (u + v) / 2)) := by
      intro u; simp only [lcMap, LinearMap.coe_mk, AddHom.coe_mk]; congr 3; ring
    simp_rw [e, this]
    rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
  simp_rw [h3]
  rw [lintegral_const_mul']
  · simp

/-- The exponent `(d + 1) / 2` of the proper time in the interval volume. -/
noncomputable abbrev kk (d : ℕ) : ℝ := ((d : ℝ) + 1) / 2

lemma inner_eval (hd : 0 < d) {v : ℝ} (hv : 0 < v) :
    ∫ u in (0 : ℝ)..v, ((v - u) / 2) ^ (d - 1) * (u * v) ^ (kk d) =
      (1 / 2) ^ (d - 1) * (Real.Gamma (kk d + 1) * Real.Gamma d / Real.Gamma (kk d + 1 + d)) * v ^ (2 * d + 1) := by
  have hk : 0 < kk d := by unfold kk; positivity
  have hB := real_beta (a := kk d + 1) (b := (d : ℝ)) (by linarith) (by exact_mod_cast hd)
  -- scaling u = v s
  have hsc := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1)
    (fun u : ℝ => ((v - u) / 2) ^ (d - 1) * (u * v) ^ (kk d)) hv.ne'
  simp only [mul_zero, mul_one, smul_eq_mul] at hsc
  have h2k : v ^ (2 * kk d) = v ^ (d + 1) := by
    have : 2 * kk d = ((d + 1 : ℕ) : ℝ) := by unfold kk; push_cast; ring
    rw [this, Real.rpow_natCast]
  have hs1 : ∀ s ∈ Set.uIcc (0 : ℝ) 1, ((v - v * s) / 2) ^ (d - 1) * ((v * s) * v) ^ (kk d) =
      (1 / 2) ^ (d - 1) * v ^ (d - 1) * v ^ (d + 1) * (s ^ (kk d) * (1 - s) ^ (d - 1)) := by
    intro s hs
    rw [Set.uIcc_of_le zero_le_one] at hs
    have e1 : ((v - v * s) / 2) ^ (d - 1) = (1 / 2) ^ (d - 1) * v ^ (d - 1) * (1 - s) ^ (d - 1) := by
      rw [show (v - v * s) / 2 = (1 / 2) * v * (1 - s) by ring, mul_pow, mul_pow]
    have e2 : ((v * s) * v) ^ (kk d) = v ^ (d + 1) * s ^ (kk d) := by
      rw [show (v * s) * v = v ^ 2 * s by ring, Real.mul_rpow (by positivity) hs.1, ← h2k,
        Real.rpow_mul hv.le, Real.rpow_two]
    rw [e1, e2]; ring
  rw [intervalIntegral.integral_congr hs1, intervalIntegral.integral_const_mul] at hsc
  have hBc : ∫ s in (0 : ℝ)..1, s ^ (kk d) * (1 - s) ^ (d - 1) =
      Real.Gamma (kk d + 1) * Real.Gamma d / Real.Gamma (kk d + 1 + d) := by
    rw [← hB]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le zero_le_one] at hs
    rw [add_sub_cancel_right, show ((d : ℝ) - 1) = ((d - 1 : ℕ) : ℝ) by rw [Nat.cast_sub hd]; simp,
      Real.rpow_natCast]
  rw [hBc] at hsc
  have hv0 : v ≠ 0 := hv.ne'
  have : ∫ u in (0 : ℝ)..v, ((v - u) / 2) ^ (d - 1) * (u * v) ^ (kk d) =
      v * ((1 / 2) ^ (d - 1) * v ^ (d - 1) * v ^ (d + 1) *
        (Real.Gamma (kk d + 1) * Real.Gamma d / Real.Gamma (kk d + 1 + d))) := by
    rw [hsc]; field_simp
  rw [this]
  have hp : v * (v ^ (d - 1) * v ^ (d + 1)) = v ^ (2 * d + 1) := by
    rw [← pow_add, ← pow_succ']
    congr 1; omega
  calc _ = (1 / 2) ^ (d - 1) * (Real.Gamma (kk d + 1) * Real.Gamma d / Real.Gamma (kk d + 1 + d)) *
        (v * (v ^ (d - 1) * v ^ (d + 1))) := by ring
    _ = _ := by rw [hp]


lemma fv_nonneg {v u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) v) (hv : 0 ≤ v) (d : ℕ) :
    0 ≤ ((v - u) / 2) ^ (d - 1) * (u * v) ^ (kk d) := by
  have h1 : 0 ≤ (v - u) / 2 := by linarith [hu.2]
  have h2 : 0 ≤ u * v := mul_nonneg hu.1 hv
  exact mul_nonneg (pow_nonneg h1 _) (Real.rpow_nonneg h2 _)

lemma inner_lintegral (hd : 0 < d) {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) :
    ∫⁻ u : ℝ, ENNReal.ofReal (Ghat d (lcMap (u, v))) =
      ENNReal.ofReal ((1 / 2) ^ (d - 1) * (Real.Gamma (kk d + 1) * Real.Gamma d / Real.Gamma (kk d + 1 + d)) *
        v ^ (2 * d + 1)) := by
  rw [← inner_eval hd hv]
  have h1 : ∀ u : ℝ, ENNReal.ofReal (Ghat d (lcMap (u, v))) =
      Set.indicator (Set.Icc (0 : ℝ) v)
        (fun u => ENNReal.ofReal (((v - u) / 2) ^ (d - 1) * (u * v) ^ (kk d))) u := by
    intro u
    rw [Ghat_lcMap]
    by_cases h : 0 ≤ u ∧ u ≤ v ∧ v ≤ 1
    · rw [Set.indicator_of_mem (show u ∈ Set.Icc (0 : ℝ) v from ⟨h.1, h.2.1⟩)]
      simp [h]
    · rw [Set.indicator_of_notMem]
      · simp [h]
      · rintro ⟨a, b⟩; exact h ⟨a, b, hv1⟩
  simp_rw [h1]
  rw [lintegral_indicator measurableSet_Icc, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hv.le]
  · have : Continuous fun u : ℝ => ((v - u) / 2) ^ (d - 1) * (u * v) ^ (kk d) := by
      have hk : 0 ≤ kk d := by unfold kk; positivity
      exact (by fun_prop : Continuous fun u : ℝ => ((v - u) / 2) ^ (d - 1)).mul
        ((Real.continuous_rpow_const hk).comp (by fun_prop))
    exact this.integrableOn_Icc
  · exact (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun u hu => fv_nonneg hu hv.le d)

lemma inner_lintegral_zero {v : ℝ} (hv : v < 0 ∨ 1 < v) (d : ℕ) :
    ∫⁻ u : ℝ, ENNReal.ofReal (Ghat d (lcMap (u, v))) = 0 := by
  have : ∀ u : ℝ, ENNReal.ofReal (Ghat d (lcMap (u, v))) = 0 := by
    intro u
    rw [Ghat_lcMap]
    have h : ¬ (0 ≤ u ∧ u ≤ v ∧ v ≤ 1) := by
      rintro ⟨a, b, c⟩
      rcases hv with hv | hv <;> linarith
    simp [h]
  simp [this]

lemma Rval_eq (hd : 0 < d) :
    ∫⁻ v : ℝ, ∫⁻ u : ℝ, ENNReal.ofReal (Ghat d (lcMap (u, v))) =
      ENNReal.ofReal ((1 / 2) ^ (d - 1) * (Real.Gamma (kk d + 1) * Real.Gamma d / Real.Gamma (kk d + 1 + d)) *
        (1 / (2 * d + 2))) := by
  set c := (1 / 2 : ℝ) ^ (d - 1) * (Real.Gamma (kk d + 1) * Real.Gamma d / Real.Gamma (kk d + 1 + d)) with hc
  have hX : ∀ v : ℝ, v ≠ 0 → ∫⁻ u : ℝ, ENNReal.ofReal (Ghat d (lcMap (u, v))) =
      Set.indicator (Set.Ioc (0 : ℝ) 1) (fun v => ENNReal.ofReal (c * v ^ (2 * d + 1))) v := by
    intro v hv0
    by_cases hv : 0 < v ∧ v ≤ 1
    · rw [Set.indicator_of_mem (show v ∈ Set.Ioc (0 : ℝ) 1 from hv)]
      exact inner_lintegral hd hv.1 hv.2
    · rw [Set.indicator_of_notMem (show v ∉ Set.Ioc (0 : ℝ) 1 from hv)]
      apply inner_lintegral_zero
      by_contra hcon
      simp only [not_or, not_lt] at hcon
      exact hv ⟨lt_of_le_of_ne hcon.1 (Ne.symm hv0), hcon.2⟩
  have hae : ∀ᵐ v ∂(volume : Measure ℝ), v ≠ 0 := by
    simp [ae_iff]
  rw [lintegral_congr_ae (hae.mono hX), lintegral_indicator measurableSet_Ioc,
    ← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_const_mul, integral_pow]
    have : ((2 * d + 1 : ℕ) : ℝ) + 1 = 2 * d + 2 := by push_cast; ring
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at this ⊢
    norm_num
    exact Or.inl this
  · exact (by fun_prop : Continuous fun v : ℝ => c * v ^ (2 * d + 1)).integrableOn_Ioc
  · have hc0 : 0 ≤ c := by
      have hk : 0 < kk d := by unfold kk; positivity
      have h1 := Real.Gamma_pos_of_pos (show 0 < kk d + 1 by linarith)
      have h2 := Real.Gamma_pos_of_pos (show (0 : ℝ) < d by exact_mod_cast hd)
      have h3 := Real.Gamma_pos_of_pos (show 0 < kk d + 1 + d by positivity)
      rw [hc]; positivity
    exact (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun v hv => by
      have := hv.1; positivity)

/-- The radial and time integral of the proper time to the origin over the half diamond. -/
noncomputable def KG (d : ℕ) : ℝ :=
  ∫ t in (0 : ℝ)..1, ∫ y in (0 : ℝ)..(min t (1 - t)), y ^ (d - 1) * (t ^ 2 - y ^ 2) ^ (kk d)

lemma contK (d : ℕ) (t : ℝ) : Continuous fun y : ℝ => y ^ (d - 1) * (t ^ 2 - y ^ 2) ^ (kk d) := by
  have hk : 0 ≤ kk d := by unfold kk; positivity
  exact (by fun_prop : Continuous fun y : ℝ => y ^ (d - 1)).mul
    ((Real.continuous_rpow_const hk).comp (by fun_prop))

lemma inner_Ghat (d : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∫⁻ r : ℝ, ENNReal.ofReal (Ghat d (t, r)) =
      ENNReal.ofReal (∫ y in (0 : ℝ)..(min t (1 - t)), y ^ (d - 1) * (t ^ 2 - y ^ 2) ^ (kk d)) := by
  have hm : 0 ≤ min t (1 - t) := le_min ht0 (by linarith)
  have h1 : ∀ r : ℝ, ENNReal.ofReal (Ghat d (t, r)) =
      Set.indicator (Set.Icc (0 : ℝ) (min t (1 - t)))
        (fun y => ENNReal.ofReal (y ^ (d - 1) * (t ^ 2 - y ^ 2) ^ (kk d))) r := by
    intro r
    unfold Ghat
    by_cases h : 0 ≤ r ∧ r ≤ min t (1 - t)
    · rw [Set.indicator_of_mem (show r ∈ Set.Icc (0 : ℝ) (min t (1 - t)) from h)]
      have hc : 0 ≤ t ∧ t ≤ 1 ∧ 0 ≤ r ∧ r ≤ t ∧ r ≤ 1 - t :=
        ⟨ht0, ht1, h.1, h.2.trans (min_le_left _ _), h.2.trans (min_le_right _ _)⟩
      simp [hc]
    · rw [Set.indicator_of_notMem (show r ∉ Set.Icc (0 : ℝ) (min t (1 - t)) from h)]
      have hc : ¬ (0 ≤ t ∧ t ≤ 1 ∧ 0 ≤ r ∧ r ≤ t ∧ r ≤ 1 - t) := by
        rintro ⟨_, _, a, b, c⟩
        exact h ⟨a, le_min b c⟩
      simp [hc]
  simp_rw [h1]
  rw [lintegral_indicator measurableSet_Icc, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hm]
  · exact (contK d t).integrableOn_Icc
  · refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun y hy => ?_)
    have h2 : y ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hy.1 (hy.2.trans (min_le_left _ _)) 2
    exact mul_nonneg (pow_nonneg hy.1 _) (Real.rpow_nonneg (by linarith) _)

lemma inner_Ghat_zero (d : ℕ) {t : ℝ} (ht : t ∉ Set.Icc (0 : ℝ) 1) :
    ∫⁻ r : ℝ, ENNReal.ofReal (Ghat d (t, r)) = 0 := by
  have : ∀ r : ℝ, ENNReal.ofReal (Ghat d (t, r)) = 0 := by
    intro r
    unfold Ghat
    have hc : ¬ (0 ≤ t ∧ t ≤ 1 ∧ 0 ≤ r ∧ r ≤ t ∧ r ≤ 1 - t) := by
      rintro ⟨a, b, _⟩; exact ht ⟨a, b⟩
    simp [hc]
  simp [this]

lemma Lval_real (d : ℕ) :
    ∫⁻ t : ℝ, ∫⁻ r : ℝ, ENNReal.ofReal (Ghat d (t, r)) = ENNReal.ofReal (KG d) := by
  have h1 : ∀ t : ℝ, ∫⁻ r : ℝ, ENNReal.ofReal (Ghat d (t, r)) =
      Set.indicator (Set.Icc (0 : ℝ) 1) (fun t => ENNReal.ofReal
        (∫ y in (0 : ℝ)..(min t (1 - t)), y ^ (d - 1) * (t ^ 2 - y ^ 2) ^ (kk d))) t := by
    intro t
    by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
    · rw [Set.indicator_of_mem ht]; exact inner_Ghat d ht.1 ht.2
    · rw [Set.indicator_of_notMem ht]; exact inner_Ghat_zero d ht
  simp_rw [h1]
  have hk : 0 ≤ kk d := by unfold kk; positivity
  have hjoint : Continuous (Function.uncurry fun (t y : ℝ) => y ^ (d - 1) * (t ^ 2 - y ^ 2) ^ (kk d)) := by
    have : Continuous fun q : ℝ × ℝ => q.2 ^ (d - 1) * (q.1 ^ 2 - q.2 ^ 2) ^ (kk d) :=
      (by fun_prop : Continuous fun q : ℝ × ℝ => q.2 ^ (d - 1)).mul
        ((Real.continuous_rpow_const hk).comp (by fun_prop))
    exact this
  have hF : Continuous fun t : ℝ => ∫ y in (0 : ℝ)..(min t (1 - t)), y ^ (d - 1) * (t ^ 2 - y ^ 2) ^ (kk d) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hjoint (by fun_prop)
  rw [lintegral_indicator measurableSet_Icc, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [KG, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  · exact hF.integrableOn_Icc
  · refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun t ht => ?_)
    have hm : 0 ≤ min t (1 - t) := le_min ht.1 (by linarith [ht.2])
    refine intervalIntegral.integral_nonneg hm fun y hy => ?_
    have h2 : y ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hy.1 (hy.2.trans (min_le_left _ _)) 2
    exact mul_nonneg (pow_nonneg hy.1 _) (Real.rpow_nonneg (by linarith) _)

/-- The Beta factor `B = Γ(k+1) Γ(d) / Γ(k+1+d)` with `k = (d+1)/2`. -/
noncomputable def betaK (d : ℕ) : ℝ := Real.Gamma (kk d + 1) * Real.Gamma d / Real.Gamma (kk d + 1 + d)

lemma betaK_pos (hd : 0 < d) : 0 < betaK d := by
  have hk : 0 < kk d := by unfold kk; positivity
  unfold betaK
  have h1 := Real.Gamma_pos_of_pos (show 0 < kk d + 1 by linarith)
  have h2 := Real.Gamma_pos_of_pos (show (0 : ℝ) < d by exact_mod_cast hd)
  have h3 := Real.Gamma_pos_of_pos (show 0 < kk d + 1 + d by positivity)
  positivity

lemma KG_eq (hd : 0 < d) : KG d = (1 / 2) ^ d * betaK d / (2 * d + 2) := by
  have h1 := Lval_eq d
  rw [Lval_real, Rval_eq hd] at h1
  have hpos : 0 ≤ (1 / 2 : ℝ) ^ (d - 1) * betaK d * (1 / (2 * d + 2)) := by
    have := betaK_pos hd; positivity
  have h2 : (2⁻¹ : ENNReal) * ENNReal.ofReal ((1 / 2 : ℝ) ^ (d - 1) * betaK d * (1 / (2 * d + 2))) =
      ENNReal.ofReal ((1 / 2) ^ d * betaK d / (2 * d + 2)) := by
    rw [show (2⁻¹ : ENNReal) = ENNReal.ofReal (1 / 2) by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]; simp, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]; field_simp
  have h3 : ENNReal.ofReal (KG d) = ENNReal.ofReal ((1 / 2) ^ d * betaK d / (2 * d + 2)) := by
    have h1' : ENNReal.ofReal (KG d) =
        2⁻¹ * ENNReal.ofReal ((1 / 2 : ℝ) ^ (d - 1) * betaK d * (1 / (2 * d + 2))) := by
      unfold betaK; exact h1
    rw [h1', h2]
  have hq : 0 < (1 / 2 : ℝ) ^ d * betaK d / (2 * d + 2) := by
    have := betaK_pos hd; positivity
  rcases le_or_gt 0 (KG d) with h | h
  · exact (ENNReal.ofReal_eq_ofReal_iff h hq.le).1 h3
  · rw [ENNReal.ofReal_of_nonpos h.le] at h3
    exact absurd h3.symm (ENNReal.ofReal_pos.2 hq).ne'

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

/-- The volume of the diamond, from the radial formula. -/
lemma volume_diamond_real (hd : 0 < d) :
    (volume (diamond d)).toReal = ballVol d * (1 / 2) ^ d / (d + 1) := by
  have h1 : (volume (diamond d)).toReal = ∫ p : Fin (d + 1) → ℝ, (diamond d).indicator (fun _ => (1 : ℝ)) p := by
    rw [show (diamond d).indicator (fun _ => (1 : ℝ)) = (diamond d).indicator (1 : (Fin (d + 1) → ℝ) → ℝ) from rfl,
      integral_indicator_one (diamond_measurableSet d), Measure.real]
  have h2 : ∫ p : Fin (d + 1) → ℝ, (diamond d).indicator (fun _ => (1 : ℝ)) p =
      ∫ p : Fin (d + 1) → ℝ, phiD (fun _ _ => 1) (p 0) (spatialSq p) := by
    congr 1; funext p; rw [phiD_eq]
  rw [h1, h2, outer_formula hd (g := fun _ _ => 1) (by fun_prop)]
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hin : ∀ m : ℝ, ∫ y in (0 : ℝ)..m, y ^ (d - 1) * (1 : ℝ) = m ^ d / d := by
    intro m
    simp only [mul_one, integral_pow]
    have hc : ((d - 1 : ℕ) : ℝ) + 1 = d := by rw [Nat.cast_sub hd]; simp
    rw [Nat.sub_add_cancel hd, hc, zero_pow hd.ne', sub_zero]
  simp_rw [hin]
  rw [split_half (fun _ m => m ^ d / d) (by fun_prop)]
  have e1 : ∫ t in (0 : ℝ)..(1 / 2), t ^ d / d = (1 / 2) ^ (d + 1) / ((d + 1) * d) := by
    rw [intervalIntegral.integral_div]; simp [integral_pow]; field_simp
  have e2 : ∫ t in (1 / 2 : ℝ)..1, (1 - t) ^ d / d = (1 / 2) ^ (d + 1) / ((d + 1) * d) := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ d) 1]
    simp [integral_pow]; field_simp; rw [← mul_pow]; norm_num
  rw [e1, e2]
  field_simp
  ring

lemma Ktop_eq (d : ℕ) :
    ∫ t in (0 : ℝ)..1, ∫ y in (0 : ℝ)..(min t (1 - t)), y ^ (d - 1) * ((1 - t) ^ 2 - y ^ 2) ^ (kk d) = KG d := by
  unfold KG
  have := intervalIntegral.integral_comp_sub_left
    (fun t : ℝ => ∫ y in (0 : ℝ)..(min t (1 - t)), y ^ (d - 1) * (t ^ 2 - y ^ 2) ^ (kk d)) (a := 0) (b := 1) 1
  simp only [sub_self, sub_zero] at this
  rw [← this]
  refine intervalIntegral.integral_congr fun t _ => ?_
  show _ = ∫ y in (0 : ℝ)..(min (1 - t) (1 - (1 - t))), y ^ (d - 1) * ((1 - t) ^ 2 - y ^ 2) ^ (kk d)
  rw [show 1 - (1 - t) = t by ring, min_comm]

lemma tau_integral (hd : 0 < d) :
    ∫ p : Fin (d + 1) → ℝ, (diamond d).indicator
        (fun p : Fin (d + 1) → ℝ => ((1 - p 0) ^ 2 - spatialSq p) ^ (kk d)) p =
      d * ballVol d * KG d := by
  have hk : 0 ≤ kk d := by unfold kk; positivity
  have h2 : ∫ p : Fin (d + 1) → ℝ, (diamond d).indicator
        (fun p : Fin (d + 1) → ℝ => ((1 - p 0) ^ 2 - spatialSq p) ^ (kk d)) p =
      ∫ p : Fin (d + 1) → ℝ, phiD (fun t s => ((1 - t) ^ 2 - s) ^ (kk d)) (p 0) (spatialSq p) := by
    congr 1; funext p; rw [phiD_eq]
  rw [h2, outer_formula hd (g := fun t s => ((1 - t) ^ 2 - s) ^ (kk d))
    ((Real.continuous_rpow_const hk).comp (by fun_prop)).continuousOn, Ktop_eq]

lemma sqrt_pow_eq_rpow {x : ℝ} (hx : 0 ≤ x) (d : ℕ) : √x ^ (d + 1) = x ^ (kk d) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1; unfold kk; push_cast; ring

lemma volume_above (hd : 0 < d) (p : Fin (d + 1) → ℝ) (hp : p ∈ diamond d) :
    MeasureTheory.volume {q : Fin (d + 1) → ℝ | coneLE p q ∧ coneLE q (diamondTop d)} =
      ENNReal.ofReal (((1 - p 0) ^ 2 - spatialSq p) ^ (kk d)) * MeasureTheory.volume (diamond d) := by
  have hset : {q : Fin (d + 1) → ℝ | coneLE p q ∧ coneLE q (diamondTop d)} =
      (fun q => q + (-p)) ⁻¹' intervalSet (diamondTop d - p) := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, intervalSet]
    have e1 : q + -p - 0 = q - p := by simp [sub_eq_add_neg]
    have e2 : diamondTop d - p - (q + -p) = diamondTop d - q := by abel
    simp only [coneLE, e1, e2]
  rw [hset, measure_preimage_add_right]
  have hF : Fut (diamondTop d - p) := by
    rw [Fut_iff_coneLE]; exact hp.2
  rw [volume_interval_all hd hF]
  have h0 : (diamondTop d - p) 0 = 1 - p 0 := by simp [diamondTop]
  have hs : spatialSq (diamondTop d - p) = spatialSq p := by
    simp [spatialSq_eq_sum, diamondTop, Fin.succ_ne_zero]
  have hx : 0 ≤ (1 - p 0) ^ 2 - spatialSq p := by
    have := hF.2; rw [h0, hs] at this; linarith
  rw [h0, hs, sqrt_pow_eq_rpow hx]

lemma slice_measure (hd : 0 < d) (p : Fin (d + 1) → ℝ) (hp : p ∈ diamond d) :
    (MeasureTheory.volume.restrict (diamond d)) {q : Fin (d + 1) → ℝ | coneLT p q} =
      ENNReal.ofReal (((1 - p 0) ^ 2 - spatialSq p) ^ (kk d)) * MeasureTheory.volume (diamond d) := by
  have hm : MeasurableSet {q : Fin (d + 1) → ℝ | coneLT p q} := by
    have : {q : Fin (d + 1) → ℝ | coneLT p q} = {q | coneLE p q} ∩ {q | p ≠ q} := rfl
    rw [this]
    refine MeasurableSet.inter ?_ ?_
    · have : {q : Fin (d + 1) → ℝ | coneLE p q} = {q | 0 ≤ (q - p) 0} ∩
          {q | minkowskiForm (d + 1) (q - p) (q - p) ≤ 0} := rfl
      rw [this]
      simp only [minkowskiForm_apply]
      exact (isClosed_le (by fun_prop) (by fun_prop)).measurableSet.inter
        (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
    · exact (measurableSet_singleton p).compl.congr (by ext q; simp [eq_comm])
  rw [Measure.restrict_apply hm]
  have hset : {q : Fin (d + 1) → ℝ | coneLT p q} ∩ diamond d =
      {q : Fin (d + 1) → ℝ | coneLE p q ∧ coneLE q (diamondTop d)} \ {p} := by
    ext q
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, coneLT, diamond, Set.mem_sdiff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨h1, h4⟩, fun h => h2 h.symm⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, fun h => h3 h.symm⟩, coneLE_trans hp.1 h1, h2⟩
  rw [hset, measure_sdiff_null (measure_singleton p), volume_above hd p hp]

lemma ballVol_pos (hd : 0 < d) : 0 < ballVol d := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  unfold ballVol
  exact ENNReal.toReal_pos (Metric.measure_ball_pos volume _ one_pos).ne' (measure_ball_lt_top).ne

/-- **The related-pair probability in terms of the Beta factor**: for `d ≥ 1`, two uniform points of
the causal diamond of `ℝ^{d+1}` are related with probability `(d / 2) B((d + 3) / 2, d)`. -/
theorem relProb_beta (hd : 0 < d) : relProb d = d / 2 * betaK d := by
  rw [relProb_eq]
  unfold diamondMeasure regionMeasure ProbabilityTheory.cond
  set V := MeasureTheory.volume (diamond d) with hV
  have hVfin : V ≠ ⊤ := (volume_diamond_lt_top d).ne
  have hVr : V = ENNReal.ofReal (ballVol d * (1 / 2) ^ d / (d + 1)) := by
    rw [← volume_diamond_real hd, ENNReal.ofReal_toReal hVfin]
  rw [Measure.prod_smul_left, Measure.prod_smul_right]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Measure.prod_apply (coneLT_measurableSet d)]
  have hint : ∀ p ∈ diamond d, (MeasureTheory.volume.restrict (diamond d))
      (Prod.mk p ⁻¹' {q : (Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ) | coneLT q.1 q.2}) =
      ENNReal.ofReal (((1 - p 0) ^ 2 - spatialSq p) ^ (kk d)) * V := fun p hp =>
    slice_measure hd p hp
  rw [setLIntegral_congr_fun (diamond_measurableSet d) hint]
  have hk : 0 ≤ kk d := by unfold kk; positivity
  have hgc : Continuous fun p : Fin (d + 1) → ℝ => ((1 - p 0) ^ 2 - spatialSq p) ^ (kk d) :=
    (Real.continuous_rpow_const hk).comp (by
      have := (continuous_spatialSq (d := d))
      fun_prop)
  have hI : ∫⁻ p in diamond d, ENNReal.ofReal (((1 - p 0) ^ 2 - spatialSq p) ^ (kk d)) =
      ENNReal.ofReal (d * ballVol d * KG d) := by
    have hnn : ∀ p ∈ diamond d, 0 ≤ ((1 - p 0) ^ 2 - spatialSq p) ^ (kk d) := by
      intro p hp
      obtain ⟨a, b, c, e⟩ := (mem_diamond_gen p).1 hp
      exact Real.rpow_nonneg (by linarith) _
    rw [← tau_integral hd, ← ofReal_integral_eq_lintegral_ofReal]
    · congr 1
      rw [integral_indicator (diamond_measurableSet d)]
    · exact hgc.continuousOn.integrableOn_compact (diamond_compact d)
    · exact (ae_restrict_iff' (diamond_measurableSet d)).2 (Filter.Eventually.of_forall hnn)
  rw [lintegral_mul_const _ hgc.measurable.ennreal_ofReal, hI, hVr]
  have hω := ballVol_pos hd
  have hB := betaK_pos hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hpos : 0 < ballVol d * (1 / 2) ^ d / (d + 1) := by positivity
  have hK := KG_eq hd
  have hK0 : 0 ≤ KG d := by rw [hK]; positivity
  rw [← mul_assoc, ← mul_assoc, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal hpos.le, ENNReal.toReal_ofReal (by positivity)]
  rw [hK]
  field_simp

theorem relProb_gamma (hd : 0 < d) :
    relProb d = Real.Gamma ((d : ℝ) + 2) * Real.Gamma (((d : ℝ) + 1) / 2) /
      (4 * Real.Gamma (3 * ((d : ℝ) + 1) / 2)) := by
  rw [relProb_beta hd]
  unfold betaK
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have e1 : kk d + 1 = ((d : ℝ) + 1) / 2 + 1 := by unfold kk; ring
  have e2 : kk d + 1 + d = 3 * ((d : ℝ) + 1) / 2 := by unfold kk; ring
  have g1 : Real.Gamma (((d : ℝ) + 1) / 2 + 1) = ((d : ℝ) + 1) / 2 * Real.Gamma (((d : ℝ) + 1) / 2) :=
    Real.Gamma_add_one (by positivity)
  have g2 : Real.Gamma ((d : ℝ) + 1) = d * Real.Gamma d := Real.Gamma_add_one hdpos.ne'
  have g3 : Real.Gamma ((d : ℝ) + 2) = ((d : ℝ) + 1) * Real.Gamma ((d : ℝ) + 1) := by
    rw [show (d : ℝ) + 2 = (d + 1) + 1 by ring]; exact Real.Gamma_add_one (by positivity)
  have hG := Real.Gamma_pos_of_pos (show 0 < 3 * ((d : ℝ) + 1) / 2 by positivity)
  rw [e1, e2, g1, g3, g2]
  field_simp
  ring

lemma coneLE_zero_iff (x y : Fin 1 → ℝ) : coneLE x y ↔ x 0 ≤ y 0 := by
  rw [coneLE_iff_spatial]
  simp [spatialSq]
  intro _; positivity

lemma diamond_zero : diamond 0 = (MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' Set.Icc (0 : ℝ) 1 := by
  ext x
  show coneLE 0 x ∧ coneLE x (diamondTop 0) ↔ _
  rw [coneLE_zero_iff, coneLE_zero_iff]
  simp [diamondTop, MeasurableEquiv.funUnique]

lemma relProb_zero : relProb 0 = 1 / 2 := by
  set e := MeasurableEquiv.funUnique (Fin 1) ℝ with he
  have hmp : MeasurePreserving e volume volume := volume_preserving_funUnique (Fin 1) ℝ
  rw [relProb_eq]
  have hV : volume (diamond 0) = 1 := by
    rw [diamond_zero, hmp.measure_preimage_equiv]; simp
  have hmapD : (diamondMeasure 0).map e = volume.restrict (Set.Icc (0 : ℝ) 1) := by
    unfold diamondMeasure regionMeasure ProbabilityTheory.cond
    rw [hV, Measure.map_smul, diamond_zero, ← Measure.restrict_map e.measurable measurableSet_Icc, hmp.map_eq]
    simp
    exact e.measurable.aemeasurable
  have hset : {p : (Fin (0 + 1) → ℝ) × (Fin (0 + 1) → ℝ) | coneLT p.1 p.2} =
      (Prod.map e e) ⁻¹' ({q : ℝ × ℝ | q.1 ≤ q.2} \ {q | q.1 = q.2}) := by
    ext p
    simp only [coneLT, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_sdiff, Prod.map_fst, Prod.map_snd,
      coneLE_zero_iff]
    have h1 : (p.1 ≠ p.2) ↔ ¬ e p.1 = e p.2 := by rw [e.injective.eq_iff]
    rw [h1]
    rfl
  have hS : MeasurableSet ({q : ℝ × ℝ | q.1 ≤ q.2} \ {q | q.1 = q.2}) :=
    (measurableSet_le measurable_fst measurable_snd).diff (measurableSet_eq_fun measurable_fst measurable_snd)
  rw [hset, ← Measure.map_apply (e.measurable.prodMap e.measurable) hS,
    ← Measure.map_prod_map _ _ e.measurable e.measurable, hmapD]
  have : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := ⟨by simp⟩
  rw [measure_sdiff_null (prod_diag_null _), prod_le_half]
  norm_num

/-- **The Myrheim–Meyer relation probability in every dimension**: two independent uniform points of
the causal diamond of `ℝ^{d+1}` are related, `x ≺ y`, with probability
`Γ(D + 1) Γ(D / 2) / (4 Γ(3 D / 2))` in the dimension `D = d + 1`. For `d = 0` the value is `1/2`;
for `d ≥ 1` it follows from the Beta-integral form `relProb_beta`. Scope: the statement is proved for
the causal order `coneLE` of Minkowski space and the uniform measure on the diamond; the comparison of
the formula with the sources is pending (they have not been read at a location). -/
theorem myrheimMeyer_eq (d : ℕ) :
    relProb d = Real.Gamma ((d : ℝ) + 2) * Real.Gamma (((d : ℝ) + 1) / 2) /
      (4 * Real.Gamma (3 * ((d : ℝ) + 1) / 2)) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [relProb_zero]
    have h2 : Real.Gamma (((0 : ℕ) : ℝ) + 2) = 1 := by norm_num
    have h3 : Real.Gamma (3 * (((0 : ℕ) : ℝ) + 1) / 2) = 1 / 2 * Real.Gamma (1 / 2) := by
      rw [show 3 * (((0 : ℕ) : ℝ) + 1) / 2 = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num)]
    rw [h2, h3, show (((0 : ℕ) : ℝ) + 1) / 2 = 1 / 2 by norm_num]
    have : 0 < Real.Gamma (1 / 2) := Real.Gamma_pos_of_pos (by norm_num)
    field_simp
    norm_num
  · exact relProb_gamma hd

end Lightlike.CausalSets
