import Lightlike.CausalSets.Myrheim

/-!
# A wrong model for the relation count: the rectangle

Two uniform points of the rectangle `[0, 1] × [0, 2]` of `ℝ^{1+1}` (first coordinate time, extent
`1`; second coordinate space, extent `2`) satisfy `x ≺ y` with probability `7/48`
(`rectangle_relProb_eq`), not the `1/4` of the causal diamond (`relProb_one`): the count of
relations depends on the region, so the diamond value is a property of the diamond.

The proof integrates the band `|x' - x| ≤ s` over the space pair (its area in `[0, 2]²` is
`4 s - s²`), then over the time pair with `s = t' - t`, where `∫∫ (4 s - s²) = 7/12`; dividing by
the squared area `4` of the rectangle gives `7/48`. It uses the product decomposition of a pair
of points into time pair and space pair. The task `T-CS2-P3` states the same
theorem and is closed by it.

## References

* S. Surya, *The causal set approach to the problem of quantum gravity*, Living Reviews in
  Relativity 22 (2019), section 2.
-/

open MeasureTheory Set
open Lightlike

namespace Lightlike.CausalSets

/-- The length of `[0, 2] ∩ [x - s, x + s]` (as a formula): the width of the band `|x' - x| ≤ s`
at the point `x` of the interval `[0, 2]`. -/
noncomputable def rectBand (s x : ℝ) : ℝ := min 2 (x + s) - max 0 (x - s)

lemma bandG_int {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : ∫ x in (0:ℝ)..2, rectBand s x = 4 * s - s ^ 2 := by
  have h1 : ∫ x in (0:ℝ)..s, rectBand s x = ∫ x in (0:ℝ)..s, (x + s) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le hs0] at hx
    simp only [rectBand]
    rw [min_eq_right (by linarith [hx.2]), max_eq_left (by linarith [hx.2])]; ring
  have h2 : ∫ x in s..(2 - s), rectBand s x = ∫ x in s..(2 - s), (2 * s) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le (by linarith)] at hx
    simp only [rectBand]
    rw [min_eq_right (by linarith [hx.2]), max_eq_right (by linarith [hx.1])]; ring
  have h3 : ∫ x in (2 - s)..2, rectBand s x = ∫ x in (2 - s)..2, (2 + s - x) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le (by linarith)] at hx
    simp only [rectBand]
    rw [min_eq_left (by linarith [hx.1]), max_eq_right (by linarith [hx.1])]; ring
  have hc : Continuous (rectBand s) := by unfold rectBand; fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := s) (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _),
    ← intervalIntegral.integral_add_adjacent_intervals (a := s) (b := 2 - s) (c := 2) (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _), h1, h2, h3]
  have h4 : ∫ x in (2 - s)..2, (2 + s - x) = (2 + s) * s - (4 - (2 - s) ^ 2) / 2 := by
    rw [intervalIntegral.integral_sub (by simp) (by simp)]; simp [integral_id]; ring
  rw [h4]; simp [integral_id]; ring

lemma bandG_nonneg {s x : ℝ} (hs : 0 ≤ s) (hx : x ∈ Icc (0:ℝ) 2) : 0 ≤ rectBand s x := by
  unfold rectBand
  apply sub_nonneg.2
  apply max_le <;> apply le_min <;> linarith [hx.1, hx.2]

lemma band_measure {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ((volume.restrict (Icc (0:ℝ) 2)).prod (volume.restrict (Icc (0:ℝ) 2)))
      {q : ℝ × ℝ | |q.2 - q.1| ≤ s} = ENNReal.ofReal (4 * s - s ^ 2) := by
  have hm : MeasurableSet {q : ℝ × ℝ | |q.2 - q.1| ≤ s} :=
    measurableSet_le (by fun_prop) measurable_const
  rw [Measure.prod_apply hm]
  have hpre : ∀ x : ℝ, Prod.mk x ⁻¹' {q : ℝ × ℝ | |q.2 - q.1| ≤ s} = Icc (x - s) (x + s) := by
    intro x; ext y
    simp only [mem_preimage, mem_setOf_eq, mem_Icc, abs_le]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  simp_rw [hpre]
  have hval : ∀ x ∈ Icc (0:ℝ) 2, (volume.restrict (Icc (0:ℝ) 2)) (Icc (x - s) (x + s)) =
      ENNReal.ofReal (rectBand s x) := by
    intro x hx
    rw [Measure.restrict_apply measurableSet_Icc, Icc_inter_Icc, Real.volume_Icc]
    congr 1
    unfold rectBand
    rw [max_comm 0 (x - s), min_comm 2 (x + s)]
  rw [setLIntegral_congr_fun measurableSet_Icc hval]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num), bandG_int hs0 hs1]
  · exact (by unfold rectBand; fun_prop : Continuous (rectBand s)).integrableOn_Icc
  · exact (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun x hx => bandG_nonneg hs0 hx)

/-- The integrand over the time pair `(t, t')` of the `1 × 2` rectangle: the measure of the band
`|x' - x| ≤ t' - t` when `t ≤ t'`, and `0` otherwise. -/
noncomputable def rectTimeF (q : ℝ × ℝ) : ENNReal :=
  if q.1 ≤ q.2 then ENNReal.ofReal (4 * (q.2 - q.1) - (q.2 - q.1) ^ 2) else 0

lemma inner_time {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ∫⁻ t' in Icc (0:ℝ) 1, rectTimeF (t, t') = ENNReal.ofReal (2 * (1 - t) ^ 2 - (1 - t) ^ 3 / 3) := by
  have h1 : ∀ t' : ℝ, rectTimeF (t, t') = Set.indicator (Ici t)
      (fun t' => ENNReal.ofReal (4 * (t' - t) - (t' - t) ^ 2)) t' := by
    intro t'; unfold rectTimeF; by_cases h : t ≤ t' <;> simp [h]
  simp_rw [h1]
  rw [lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
  have hset : Ici t ∩ Icc (0:ℝ) 1 = Icc t 1 := by
    ext y; simp only [mem_inter_iff, mem_Ici, mem_Icc]; constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith [ht.1], h2⟩
  rw [hset, ← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht.2]
    have := intervalIntegral.integral_comp_sub_right (fun s : ℝ => 4 * s - s ^ 2) (a := t) (b := 1) t
    simp only [sub_self] at this
    rw [this, intervalIntegral.integral_sub ((by fun_prop : Continuous fun x : ℝ => 4 * x).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun x : ℝ => x ^ 2).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, integral_id, integral_pow]
    ring
  · exact (by fun_prop : Continuous fun y : ℝ => 4 * (y - t) - (y - t) ^ 2).integrableOn_Icc
  · refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun y hy => ?_)
    show 0 ≤ 4 * (y - t) - (y - t) ^ 2
    nlinarith [hy.1, hy.2, ht.1, ht.2]

lemma timeF_measurable : Measurable rectTimeF := by
  unfold rectTimeF
  exact Measurable.ite (measurableSet_le measurable_fst measurable_snd)
    (by fun_prop : Measurable fun q : ℝ × ℝ => ENNReal.ofReal (4 * (q.2 - q.1) - (q.2 - q.1) ^ 2))
    measurable_const

lemma outer_time :
    ∫⁻ q, rectTimeF q ∂((volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict (Icc (0:ℝ) 1))) =
      ENNReal.ofReal (7 / 12) := by
  rw [lintegral_prod _ timeF_measurable.aemeasurable]
  rw [setLIntegral_congr_fun measurableSet_Icc (fun t ht => inner_time ht)]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
    have := intervalIntegral.integral_comp_sub_left (fun u : ℝ => 2 * u ^ 2 - u ^ 3 / 3) (a := 0) (b := 1) 1
    simp only [sub_self, sub_zero] at this
    rw [this, intervalIntegral.integral_sub ((by fun_prop : Continuous fun x : ℝ => 2 * x ^ 2).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun x : ℝ => x ^ 3 / 3).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_div, integral_pow, integral_pow]
    norm_num
  · exact (by fun_prop : Continuous fun t : ℝ => 2 * (1 - t) ^ 2 - (1 - t) ^ 3 / 3).integrableOn_Icc
  · refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun t ht => ?_)
    show 0 ≤ 2 * (1 - t) ^ 2 - (1 - t) ^ 3 / 3
    nlinarith [ht.1, ht.2, sq_nonneg (1 - t), mul_nonneg (sub_nonneg.2 ht.2) (sq_nonneg (1 - t))]


/-- The weak causal relation `x ≼ y` in the coordinates `((t, t'), (x, x'))` of a pair of points. -/
def rectE : Set ((ℝ × ℝ) × (ℝ × ℝ)) := {w | w.1.1 ≤ w.1.2 ∧ |w.2.2 - w.2.1| ≤ w.1.2 - w.1.1}

lemma rectE_measure :
    (((volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict (Icc (0:ℝ) 1))).prod
      ((volume.restrict (Icc (0:ℝ) 2)).prod (volume.restrict (Icc (0:ℝ) 2)))) rectE =
      ENNReal.ofReal (7 / 12) := by
  have hE : MeasurableSet rectE := by
    refine MeasurableSet.inter (s₁ := {w : (ℝ × ℝ) × (ℝ × ℝ) | w.1.1 ≤ w.1.2})
      (s₂ := {w : (ℝ × ℝ) × (ℝ × ℝ) | |w.2.2 - w.2.1| ≤ w.1.2 - w.1.1}) ?_ ?_
    · exact measurableSet_le (f := fun w : (ℝ × ℝ) × (ℝ × ℝ) => w.1.1) (g := fun w => w.1.2)
        (by fun_prop) (by fun_prop)
    · exact measurableSet_le (f := fun w : (ℝ × ℝ) × (ℝ × ℝ) => |w.2.2 - w.2.1|)
        (g := fun w => w.1.2 - w.1.1) (by fun_prop) (by fun_prop)
  rw [Measure.prod_apply hE, ← outer_time]
  have hae : ∀ᵐ q ∂((volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict (Icc (0:ℝ) 1))),
      q.1 ∈ Icc (0:ℝ) 1 ∧ q.2 ∈ Icc (0:ℝ) 1 := by
    have h1 := (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Icc (0:ℝ) 1))
      (ν := volume.restrict (Icc (0:ℝ) 1))).ae (ae_restrict_mem measurableSet_Icc)
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := volume.restrict (Icc (0:ℝ) 1))
      (ν := volume.restrict (Icc (0:ℝ) 1))).ae (ae_restrict_mem measurableSet_Icc)
    filter_upwards [h1, h2] with q a b using ⟨a, b⟩
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with q hq
  by_cases h : q.1 ≤ q.2
  · have hsec : Prod.mk q ⁻¹' rectE = {u : ℝ × ℝ | |u.2 - u.1| ≤ q.2 - q.1} := by
      ext u; simp [rectE, h]
    rw [hsec, band_measure (by linarith) (by linarith [hq.1.1, hq.2.2])]
    simp [rectTimeF, h]
  · have hsec : Prod.mk q ⁻¹' rectE = ∅ := by
      ext u; simp [rectE, h]
    rw [hsec]; simp [rectTimeF, h]

/-- The factor measures of the rectangle `[0, 1] × [0, 2]`: Lebesgue measure on each side. -/
noncomputable def rectρ : Fin 2 → Measure ℝ := fun i => volume.restrict (![Icc (0:ℝ) 1, Icc (0:ℝ) 2] i)

/-- The rectangle `[0, 1] × [0, 2]` of `ℝ^{1+1}`: time extent `1`, space extent `2`. -/
def rectSet : Set (Fin 2 → ℝ) := {x | x 0 ∈ Icc (0:ℝ) 1 ∧ x 1 ∈ Icc (0:ℝ) 2}

instance (i : Fin 2) : IsFiniteMeasure (rectρ i) := by
  fin_cases i
  · exact (inferInstance : IsFiniteMeasure (volume.restrict (Icc (0:ℝ) 1)))
  · exact (inferInstance : IsFiniteMeasure (volume.restrict (Icc (0:ℝ) 2)))

lemma rectSet_eq : rectSet = Set.pi univ ![Icc (0:ℝ) 1, Icc (0:ℝ) 2] := by
  ext x; simp [rectSet, Fin.forall_fin_two]

lemma volume_rectSet : volume rectSet = 2 := by
  rw [rectSet_eq, volume_pi_pi]; simp [Fin.prod_univ_two]

lemma regionMeasure_rect : regionMeasure rectSet = (2 : ENNReal)⁻¹ • Measure.pi rectρ := by
  unfold regionMeasure ProbabilityTheory.cond
  rw [volume_rectSet, rectSet_eq]
  congr 1
  exact Measure.restrict_pi_pi (fun _ : Fin 2 => (volume : Measure ℝ)) ![Icc (0:ℝ) 1, Icc (0:ℝ) 2]

lemma rect_diag : ((Measure.pi rectρ).prod (Measure.pi rectρ))
    {q : (Fin 2 → ℝ) × (Fin 2 → ℝ) | q.1 = q.2} = 0 := by
  have hm : MeasurableSet {q : (Fin 2 → ℝ) × (Fin 2 → ℝ) | q.1 = q.2} :=
    isClosed_diagonal.measurableSet
  rw [Measure.prod_apply hm]
  have : ∀ a : Fin 2 → ℝ, Measure.pi rectρ (Prod.mk a ⁻¹' {q : (Fin 2 → ℝ) × (Fin 2 → ℝ) | q.1 = q.2}) = 0 := by
    intro a
    have : Prod.mk a ⁻¹' {q : (Fin 2 → ℝ) × (Fin 2 → ℝ) | q.1 = q.2} = {a} := by
      ext b; simp [eq_comm]
    rw [this, Measure.pi_singleton]
    exact Finset.prod_eq_zero (Finset.mem_univ 0) (by simp [rectρ])
  simp only [this, lintegral_zero]

lemma rect_E : ((Measure.pi rectρ).prod (Measure.pi rectρ))
    {q : (Fin 2 → ℝ) × (Fin 2 → ℝ) | coneLE q.1 q.2} = ENNReal.ofReal (7 / 12) := by
  have hmp := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin 2) rectρ rectρ
  have h1 := hmp.measure_preimage_equiv {q : (Fin 2 → ℝ) × (Fin 2 → ℝ) | coneLE q.1 q.2}
  rw [← h1]
  have hmp2 := measurePreserving_piFinTwo (fun i : Fin 2 => (rectρ i).prod (rectρ i))
  have hpre : (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin 2)) ⁻¹'
      {q : (Fin 2 → ℝ) × (Fin 2 → ℝ) | coneLE q.1 q.2} =
      (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ × ℝ)) ⁻¹' rectE := by
    ext z
    have e1 : (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin 2) z) =
        (fun i => (z i).1, fun i => (z i).2) := rfl
    have e2 : (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ × ℝ)) z = (z 0, z 1) := rfl
    simp only [mem_preimage, mem_setOf_eq, e1, e2, rectE]
    rw [coneLE_iff_spatial, spatialSq_one]
    simp only [Pi.sub_apply]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, abs_le.2 (abs_le_of_sq_le_sq' h2 h1)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, sq_le_sq' (abs_le.1 h2).1 (abs_le.1 h2).2⟩
  rw [hpre, hmp2.measure_preimage_equiv]
  exact rectE_measure

/-- The related-pair probability of the rectangle is `7/48`. -/
lemma regionRelProb_rect : regionRelProb rectSet = 7 / 48 := by
  unfold regionRelProb
  rw [regionMeasure_rect, Measure.prod_smul_left, Measure.prod_smul_right]
  have hT : {p : (Fin 2 → ℝ) × (Fin 2 → ℝ) | coneLT p.1 p.2} =
      {q : (Fin 2 → ℝ) × (Fin 2 → ℝ) | coneLE q.1 q.2} \ {q | q.1 = q.2} := by
    ext q; simp [coneLT]
  rw [hT]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [measure_sdiff_null rect_diag, rect_E]
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num)]
  have : ((2 : ENNReal)⁻¹).toReal = 1 / 2 := by simp
  rw [this]; norm_num

/-- **Wrong model: a rectangle instead of the diamond.** Two uniform points of the rectangle
`[0, 1] × [0, 2]` of `ℝ^{1+1}` (first coordinate time, extent `1`; second coordinate space, extent
`2`) are related with probability `7/48`, not the `1/4` of the diamond (`relProb_one`). -/
theorem rectangle_relProb_eq :
    regionRelProb {x : Fin 2 → ℝ | x 0 ∈ Set.Icc (0 : ℝ) 1 ∧ x 1 ∈ Set.Icc (0 : ℝ) 2} = 7 / 48 ∧
      regionRelProb {x : Fin 2 → ℝ | x 0 ∈ Set.Icc (0 : ℝ) 1 ∧ x 1 ∈ Set.Icc (0 : ℝ) 2} ≠ relProb 1 := by
  have h : {x : Fin 2 → ℝ | x 0 ∈ Set.Icc (0 : ℝ) 1 ∧ x 1 ∈ Set.Icc (0 : ℝ) 2} = rectSet := rfl
  rw [h, regionRelProb_rect, relProb_one]
  norm_num

end Lightlike.CausalSets
