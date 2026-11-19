import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Integrals over the unit cube

The uniform (Lebesgue) measure `cube ι` on `[0, 1]^ι`, the product of the uniform measures `unif` on `[0, 1]`.
Integrating one coordinate at a time (`integral_cube_update`), ties between coordinates have measure zero
(`cube_eq_null`), so the cube splits according to which coordinate of a finite set is the smallest
(`integral_eq_sum_argmin`), and the part where a given coordinate `e` is the smallest of `e` and a set `F` is the
integral over `0 ≤ w_e ≤ min_{m ∈ F} w_m` (`integral_indicator_argmin`).
-/

open MeasureTheory Set Function

namespace Lightlike.FieldTheory.Forest

/-- The uniform measure on `[0, 1]`. -/
noncomputable abbrev unif : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

instance : IsProbabilityMeasure unif := ⟨by simp [unif]⟩

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- **The uniform measure on the cube** `[0, 1]^ι`. -/
noncomputable abbrev cube : Measure (ι → ℝ) := Measure.pi fun _ => unif

variable {ι}

omit [DecidableEq ι] in
lemma cube_eq_restrict :
    cube ι = (Measure.pi fun _ : ι => (volume : Measure ℝ)).restrict (univ.pi fun _ => Icc (0 : ℝ) 1) :=
  (Measure.restrict_pi_pi (μ := fun _ : ι => (volume : Measure ℝ)) (fun _ => Icc (0 : ℝ) 1)).symm

omit [DecidableEq ι] in
lemma ae_cube_mem : ∀ᵐ y ∂cube ι, ∀ i, y i ∈ Icc (0 : ℝ) 1 := by
  rw [cube_eq_restrict]
  filter_upwards [ae_restrict_mem (MeasurableSet.univ_pi fun _ => measurableSet_Icc)] with y hy i
  exact hy i (mem_univ i)

/-- `(y, s) ↦ y` with the coordinate `l` replaced by `s` carries `cube × unif` to `cube`. -/
lemma measurePreserving_update (l : ι) :
    MeasurePreserving (fun p : (ι → ℝ) × ℝ => update p.1 l p.2) ((cube ι).prod unif) (cube ι) := by
  refine ⟨measurable_update', ?_⟩
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply measurable_update' (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (ι → ℝ) × ℝ => update p.1 l p.2) ⁻¹' (univ.pi s) = univ.pi (update s l univ) ×ˢ s l := by
    ext ⟨y, t⟩
    simp only [mem_preimage, mem_univ_pi, mem_prod]
    constructor
    · intro h
      refine ⟨fun i => ?_, by simpa using h l⟩
      by_cases hi : i = l
      · subst hi; simp
      · simpa [update_of_ne hi] using h i
    · rintro ⟨h1, h2⟩ i
      by_cases hi : i = l
      · subst hi; simpa using h2
      · simpa [update_of_ne hi] using h1 i
  rw [hpre, Measure.prod_prod, Measure.pi_pi, ← Finset.prod_erase_mul _ _ (Finset.mem_univ l),
    ← Finset.prod_erase_mul _ (fun i => unif (s i)) (Finset.mem_univ l)]
  congr 1
  · rw [update_self, measure_univ, mul_one]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [update_of_ne (Finset.ne_of_mem_erase hi)]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [DecidableEq ι] [NormedSpace ℝ V] in
/-- Continuous functions are integrable over the cube. -/
lemma integrable_cube_of_continuous {f : (ι → ℝ) → V} (hf : Continuous f) : Integrable f (cube ι) := by
  rw [cube_eq_restrict]
  exact hf.continuousOn.integrableOn_compact (isCompact_univ_pi fun _ => isCompact_Icc)

/-- Integrating out one coordinate keeps integrability. -/
lemma integrable_inner (l : ι) {f : (ι → ℝ) → V} (hf : Integrable f (cube ι)) :
    Integrable (fun y => ∫ s, f (update y l s) ∂unif) (cube ι) := by
  have hmp := measurePreserving_update (ι := ι) l
  have hf' : Integrable (f ∘ fun p : (ι → ℝ) × ℝ => update p.1 l p.2) ((cube ι).prod unif) :=
    (hmp.integrable_comp hf.aestronglyMeasurable).2 hf
  exact hf'.integral_prod_left

/-- **Fubini in one coordinate**: integrate the coordinate `l` first. -/
lemma integral_cube_update (l : ι) {f : (ι → ℝ) → V} (hf : Integrable f (cube ι)) :
    ∫ w, f w ∂cube ι = ∫ y, ∫ s, f (update y l s) ∂unif ∂cube ι := by
  have hmp := measurePreserving_update (ι := ι) l
  have hf' : Integrable (f ∘ fun p : (ι → ℝ) × ℝ => update p.1 l p.2) ((cube ι).prod unif) :=
    (hmp.integrable_comp hf.aestronglyMeasurable).2 hf
  conv_lhs => rw [← hmp.map_eq]
  rw [integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hf.aestronglyMeasurable)]
  exact integral_prod _ hf'

/-- **Ties have measure zero.** -/
lemma cube_eq_null {a b : ι} (hab : a ≠ b) : cube ι {w | w a = w b} = 0 := by
  have hmp := measurePreserving_update (ι := ι) a
  have hm : MeasurableSet {w : ι → ℝ | w a = w b} :=
    measurableSet_eq_fun (measurable_pi_apply a) (measurable_pi_apply b)
  rw [← hmp.measure_preimage hm.nullMeasurableSet]
  have hpre : (fun p : (ι → ℝ) × ℝ => update p.1 a p.2) ⁻¹' {w | w a = w b} = {p | p.2 = p.1 b} := by
    ext p; simp [update_of_ne hab.symm]
  have hms : MeasurableSet {p : (ι → ℝ) × ℝ | p.2 = p.1 b} :=
    measurableSet_eq_fun measurable_snd ((measurable_pi_apply b).comp measurable_fst)
  rw [hpre, Measure.prod_apply hms]
  simp

/-- The smallest coordinate of `y` on `F` (`1` for empty `F`). -/
noncomputable def minF (F : Finset ι) (y : ι → ℝ) : ℝ := if h : F.Nonempty then F.inf' h y else 1

omit [Fintype ι] [DecidableEq ι] in
lemma minF_le {F : Finset ι} {y : ι → ℝ} {m : ι} (hm : m ∈ F) : minF F y ≤ y m := by
  rw [minF, dite_eq_left ⟨m, hm⟩]
  exact Finset.inf'_le _ hm

omit [Fintype ι] [DecidableEq ι] in
lemma lt_minF_iff {F : Finset ι} {y : ι → ℝ} {s : ℝ} (hF : F.Nonempty) : s < minF F y ↔ ∀ m ∈ F, s < y m := by
  rw [minF, dite_eq_left hF, Finset.lt_inf'_iff]

omit [Fintype ι] [DecidableEq ι] in
lemma minF_mem_Icc {F : Finset ι} {y : ι → ℝ} (hy : ∀ i, y i ∈ Icc (0 : ℝ) 1) : minF F y ∈ Icc (0 : ℝ) 1 := by
  by_cases hF : F.Nonempty
  · obtain ⟨m, -, he⟩ := F.exists_mem_eq_inf' hF y
    rw [minF, dite_eq_left hF, he]
    exact hy m
  · rw [minF, dite_eq_right hF]; exact ⟨zero_le_one, le_rfl⟩

omit [Fintype ι] [DecidableEq ι] in
lemma continuous_minF (F : Finset ι) : Continuous (minF F) := by
  by_cases hF : F.Nonempty
  · have : minF F = fun y => F.inf' hF fun i => y i := funext fun y => dite_eq_left hF
    rw [this]
    exact Continuous.finset_inf'_apply hF fun i _ => continuous_apply i
  · have : minF F = fun _ => 1 := funext fun y => dite_eq_right hF
    rw [this]; exact continuous_const

omit [Fintype ι] in
lemma minF_update {F : Finset ι} {e : ι} (he : e ∉ F) (y : ι → ℝ) (s : ℝ) : minF F (update y e s) = minF F y := by
  unfold minF
  split_ifs with hF
  · exact Finset.inf'_congr hF rfl fun m hm => update_of_ne (by rintro rfl; exact he hm) s y
  · rfl

omit [Fintype ι] in
/-- With a new coordinate `e` set to `s ≤ min_F y`, the smallest coordinate on `{e} ∪ F` is `s`. -/
lemma minF_insert_update {F : Finset ι} {e : ι} (he : e ∉ F) {y : ι → ℝ} {s : ℝ} (hs : s ≤ minF F y) :
    minF (insert e F) (update y e s) = s := by
  rw [minF, dite_eq_left (Finset.insert_nonempty e F)]
  apply le_antisymm
  · calc _ ≤ update y e s e := Finset.inf'_le _ (Finset.mem_insert_self e F)
      _ = s := update_self _ _ _
  · refine Finset.le_inf' _ _ fun m hm => ?_
    rcases Finset.mem_insert.1 hm with rfl | hm'
    · rw [update_self]
    · rw [update_of_ne (by rintro rfl; exact he hm')]
      exact hs.trans (minF_le hm')

omit [Fintype ι] [DecidableEq ι] in
lemma measurableSet_lt_all (F : Finset ι) (e : ι) : MeasurableSet {w : ι → ℝ | ∀ m ∈ F, w e < w m} := by
  have : {w : ι → ℝ | ∀ m ∈ F, w e < w m} = ⋂ m ∈ F, {w | w e < w m} := by ext w; simp
  rw [this]
  exact MeasurableSet.biInter F.countable_toSet fun m _ =>
    measurableSet_lt (measurable_pi_apply e) (measurable_pi_apply m)

omit [Fintype ι] [DecidableEq ι] in
lemma measurableSet_argmin (F : Finset ι) (l : ι) :
    MeasurableSet {w : ι → ℝ | ∀ m ∈ F, m ≠ l → w l < w m} := by
  have : {w : ι → ℝ | ∀ m ∈ F, m ≠ l → w l < w m} = ⋂ m ∈ F, ⋂ (_ : m ≠ l), {w | w l < w m} := by
    ext w; simp
  rw [this]
  exact MeasurableSet.biInter F.countable_toSet fun m _ =>
    MeasurableSet.iInter fun _ => measurableSet_lt (measurable_pi_apply l) (measurable_pi_apply m)

/-- **The cube splits according to the smallest coordinate of a nonempty finite set.** -/
lemma integral_eq_sum_argmin {F : Finset ι} (hF : F.Nonempty) {G : (ι → ℝ) → V} (hG : Integrable G (cube ι)) :
    ∫ w, G w ∂cube ι = ∑ l ∈ F, ∫ w, indicator {w | ∀ m ∈ F, m ≠ l → w l < w m} G w ∂cube ι := by
  rw [← integral_finsetSum _ fun l _ => hG.indicator (measurableSet_argmin F l)]
  refine integral_congr_ae ?_
  have hnull : ∀ᵐ w ∂cube ι, ∀ a b : ι, a ≠ b → w a ≠ w b := by
    refine ae_all_iff.2 fun a => ae_all_iff.2 fun b => ?_
    by_cases hab : a = b
    · exact Filter.Eventually.of_forall fun _ h => absurd hab h
    · filter_upwards [measure_eq_zero_iff_ae_notMem.1 (cube_eq_null hab)] with w hw _
      exact hw
  filter_upwards [hnull] with w hw
  obtain ⟨l₀, hl₀, hmin⟩ := F.exists_min_image w hF
  have hA : ∀ l ∈ F, (w ∈ {w : ι → ℝ | ∀ m ∈ F, m ≠ l → w l < w m}) ↔ l = l₀ := by
    intro l hl
    constructor
    · intro h
      by_contra hne
      exact absurd (h l₀ hl₀ (Ne.symm hne)) (not_lt.2 (hmin l hl))
    · rintro rfl m hm hml
      exact lt_of_le_of_ne (hmin m hm) (hw _ _ (Ne.symm hml))
  rw [Finset.sum_eq_single l₀ (fun l hl hne => indicator_of_notMem (fun h => hne ((hA l hl).1 h)) _)
    (fun h => absurd hl₀ h), indicator_of_mem ((hA l₀ hl₀).2 rfl)]

/-- The inner integral over `w_e` of the part where `e` is the smallest coordinate of `{e} ∪ F` is the integral over
`0 ≤ w_e ≤ min_{m ∈ F} w_m`. -/
lemma inner_ae_eq {F : Finset ι} {e : ι} (he : e ∉ F) (K : (ι → ℝ) → V) :
    (fun y => ∫ s, indicator {w | ∀ m ∈ F, w e < w m} K (update y e s) ∂unif) =ᵐ[cube ι]
      fun y => ∫ s in (0 : ℝ)..minF F y, K (update y e s) := by
  filter_upwards [ae_cube_mem] with y hy
  have hm := minF_mem_Icc (F := F) hy
  by_cases hF : F.Nonempty
  · have hset : ∀ s : ℝ, (update y e s ∈ {w : ι → ℝ | ∀ m ∈ F, w e < w m}) ↔ s ∈ Iio (minF F y) := by
      intro s
      simp only [mem_ofPred_eq, update_self, mem_Iio]
      rw [lt_minF_iff hF]
      exact forall₂_congr fun m hm => by rw [update_of_ne (by rintro rfl; exact he hm)]
    have h1 : (fun s => indicator {w : ι → ℝ | ∀ m ∈ F, w e < w m} K (update y e s)) =
        indicator (Iio (minF F y)) fun s => K (update y e s) := by
      funext s
      by_cases hs : s ∈ Iio (minF F y)
      · rw [indicator_of_mem ((hset s).2 hs), indicator_of_mem hs]
      · rw [indicator_of_notMem (fun h => hs ((hset s).1 h)), indicator_of_notMem hs]
    have h2 : Iio (minF F y) ∩ Icc (0 : ℝ) 1 = Ico 0 (minF F y) := by
      ext s; simp only [mem_inter_iff, mem_Iio, mem_Icc, mem_Ico]
      constructor
      · rintro ⟨h, h0, -⟩; exact ⟨h0, h⟩
      · rintro ⟨h0, h⟩; exact ⟨h, h0, (h.le.trans hm.2)⟩
    show ∫ s, indicator {w : ι → ℝ | ∀ m ∈ F, w e < w m} K (update y e s) ∂unif = _
    rw [h1, integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio, h2,
      integral_Ico_eq_integral_Ioc, intervalIntegral.integral_of_le hm.1]
  · rw [Finset.not_nonempty_iff_eq_empty] at hF
    subst hF
    have h1 : (fun s => indicator {w : ι → ℝ | ∀ m ∈ (∅ : Finset ι), w e < w m} K (update y e s)) =
        fun s => K (update y e s) := by
      funext s; rw [indicator_of_mem (by simp)]
    show ∫ s, indicator {w : ι → ℝ | ∀ m ∈ (∅ : Finset ι), w e < w m} K (update y e s) ∂unif = _
    rw [h1, show minF (∅ : Finset ι) y = 1 by simp [minF], intervalIntegral.integral_of_le zero_le_one,
      ← integral_Icc_eq_integral_Ioc]

lemma integrable_argmin {F : Finset ι} {e : ι} (he : e ∉ F) {K : (ι → ℝ) → V} (hK : Integrable K (cube ι)) :
    Integrable (fun y => ∫ s in (0 : ℝ)..minF F y, K (update y e s)) (cube ι) :=
  (integrable_inner e (hK.indicator (measurableSet_lt_all F e))).congr (inner_ae_eq he K)

/-- **The part of the cube where `e` is the smallest coordinate** of `{e} ∪ F` is the integral over
`0 ≤ w_e ≤ min_{m ∈ F} w_m`. -/
lemma integral_indicator_argmin {F : Finset ι} {e : ι} (he : e ∉ F) {K : (ι → ℝ) → V}
    (hK : Integrable K (cube ι)) :
    ∫ w, indicator {w | ∀ m ∈ F, w e < w m} K w ∂cube ι =
      ∫ y, (∫ s in (0 : ℝ)..minF F y, K (update y e s)) ∂cube ι := by
  rw [integral_cube_update e (hK.indicator (measurableSet_lt_all F e))]
  exact integral_congr_ae (inner_ae_eq he K)

omit [DecidableEq ι] in
/-- **Restricting to the coordinates in `F`** carries the cube `[0, 1]^ι` to the cube `[0, 1]^F`. -/
lemma measurePreserving_restrictF (F : Finset ι) :
    MeasurePreserving (fun w : ι → ℝ => fun l : F => w l) (cube ι) (Measure.pi fun _ : F => unif) := by
  classical
  have h1 := measurePreserving_piEquivPiSubtypeProd (μ := fun _ : ι => unif) (fun l => l ∈ F)
  have h3 := (measurePreserving_fst (ν := Measure.pi fun _ : {l // l ∉ F} => unif)).comp h1
  convert h3
  rfl

/-- The extension of `h : F → ℝ` by `0`. -/
noncomputable def extendF (F : Finset ι) (h : F → ℝ) : ι → ℝ := fun l => if hl : l ∈ F then h ⟨l, hl⟩ else 0

omit [Fintype ι] in
lemma extendF_apply {F : Finset ι} (h : F → ℝ) {l : ι} (hl : l ∈ F) : extendF F h l = h ⟨l, hl⟩ := by
  simp [extendF, hl]

omit [Fintype ι] in
lemma continuous_extendF (F : Finset ι) : Continuous (extendF F) := by
  refine continuous_pi fun l => ?_
  by_cases hl : l ∈ F
  · simp only [extendF, hl, dite_eq_left]; exact continuous_apply _
  · simp only [extendF, hl, dite_eq_right, not_false_eq_true]; exact continuous_const

end Lightlike.FieldTheory.Forest
