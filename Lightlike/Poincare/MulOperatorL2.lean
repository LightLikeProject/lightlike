import Lightlike.Poincare.Imprimitivity

/-!
# Multiplication by bounded measurable functions on `L²`

For a measurable `h : X → ℂ` with `|h| ≤ 1`, multiplication by `h` is a bounded operator `mulOp h` of `L²(μ; E)`
(`coeFn_mulOp`). It is multiplicative (`mulOp_mul`), `mulOp (1 − h) = 1 − mulOp h` (`mulOp_one_sub`), it agrees with
`bcfMul` on bounded continuous functions (`mulOp_eq_bcfMul`), and if `h_k → h` pointwise then `mulOp h_k → mulOp h`
strongly (`tendsto_mulOp`, dominated convergence).

Supporting results for the irreducibility of the one-particle representations; no catalogue entry.
-/

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped InnerProductSpace

namespace Lightlike.Poincare

noncomputable section

variable {X E : Type*} [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma memLp_mulOp {h : X → ℂ} (hm : Measurable h) (hb : ∀ x, ‖h x‖ ≤ 1) (f : Lp E 2 μ) :
    MemLp (fun x => h x • f x) 2 μ :=
  (Lp.memLp f).of_le_mul (c := 1) (hm.aestronglyMeasurable.smul (Lp.aestronglyMeasurable f))
    (Filter.Eventually.of_forall fun x => by
      rw [norm_smul]; exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _))

/-- Multiplication by a measurable function bounded by `1`. -/
def mulOp (h : X → ℂ) (hm : Measurable h) (hb : ∀ x, ‖h x‖ ≤ 1) : Lp E 2 μ →L[ℂ] Lp E 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_mulOp hm hb f).toLp _
      map_add' := fun f g => by
        apply Lp.ext
        filter_upwards [(memLp_mulOp (μ := μ) hm hb (f + g)).coeFn_toLp, Lp.coeFn_add f g,
          Lp.coeFn_add ((memLp_mulOp (μ := μ) hm hb f).toLp _) ((memLp_mulOp (μ := μ) hm hb g).toLp _),
          (memLp_mulOp (μ := μ) hm hb f).coeFn_toLp, (memLp_mulOp (μ := μ) hm hb g).coeFn_toLp]
          with x h1 h2 h3 h4 h5
        rw [h1, h3, Pi.add_apply, h4, h5, h2, Pi.add_apply, smul_add]
      map_smul' := fun c f => by
        apply Lp.ext
        filter_upwards [(memLp_mulOp (μ := μ) hm hb (c • f)).coeFn_toLp, Lp.coeFn_smul c f,
          Lp.coeFn_smul c ((memLp_mulOp (μ := μ) hm hb f).toLp _), (memLp_mulOp (μ := μ) hm hb f).coeFn_toLp]
          with x h1 h2 h3 h4
        rw [h1, RingHom.id_apply, h3, Pi.smul_apply, h4, h2, Pi.smul_apply, smul_comm] }
    1 (fun f => by
      change ‖(memLp_mulOp (μ := μ) hm hb f).toLp _‖ ≤ 1 * ‖f‖
      rw [Lp.norm_toLp, Lp.norm_def, one_mul]
      have hfg : ∀ᵐ x ∂μ, ‖h x • (f : X → E) x‖ ≤ 1 * ‖(f : X → E) x‖ :=
        Filter.Eventually.of_forall fun x => by
          rw [norm_smul]; exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)
      have h' := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (memLp_mulOp (μ := μ) hm hb f).aestronglyMeasurable hfg 2
      rw [ENNReal.ofReal_one, one_mul] at h'
      exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) h')

lemma coeFn_mulOp {h : X → ℂ} (hm : Measurable h) (hb : ∀ x, ‖h x‖ ≤ 1) (f : Lp E 2 μ) :
    (mulOp (μ := μ) h hm hb f : X → E) =ᵐ[μ] fun x => h x • f x :=
  (memLp_mulOp hm hb f).coeFn_toLp

lemma mulOp_mul {h h' : X → ℂ} (hm : Measurable h) (hb : ∀ x, ‖h x‖ ≤ 1) (hm' : Measurable h')
    (hb' : ∀ x, ‖h' x‖ ≤ 1) (f : Lp E 2 μ) :
    mulOp (μ := μ) (fun x => h x * h' x) (hm.mul hm') (fun x => by
      show ‖h x * h' x‖ ≤ 1
      rw [norm_mul]; exact mul_le_one₀ (hb x) (norm_nonneg _) (hb' x)) f =
      mulOp h hm hb (mulOp h' hm' hb' f) := by
  apply Lp.ext
  filter_upwards [coeFn_mulOp (h := fun x => h x * h' x) (μ := μ) (E := E) (hm.mul hm') (fun x => by
      show ‖h x * h' x‖ ≤ 1
      rw [norm_mul]; exact mul_le_one₀ (hb x) (norm_nonneg _) (hb' x)) f,
    coeFn_mulOp (μ := μ) hm hb (mulOp h' hm' hb' f), coeFn_mulOp (μ := μ) hm' hb' f] with x h1 h2 h3
  rw [h1, h2, h3, mul_smul]

lemma mulOp_one_sub {h : X → ℂ} (hm : Measurable h) (hb : ∀ x, ‖h x‖ ≤ 1) (hb' : ∀ x, ‖1 - h x‖ ≤ 1)
    (f : Lp E 2 μ) :
    mulOp (μ := μ) (fun x => 1 - h x) (measurable_const.sub hm) hb' f = f - mulOp h hm hb f := by
  apply Lp.ext
  filter_upwards [coeFn_mulOp (h := fun x => 1 - h x) (μ := μ) (E := E) (measurable_const.sub hm) hb' f,
    Lp.coeFn_sub f (mulOp h hm hb f),
    coeFn_mulOp (μ := μ) hm hb f] with x h1 h2 h3
  rw [h1, h2, Pi.sub_apply, h3, sub_smul, one_smul]

lemma mulOp_eq_bcfMul [TopologicalSpace X] [OpensMeasurableSpace X] [SecondCountableTopologyEither X ℂ]
    (g : X →ᵇ ℂ) (hb : ∀ x, ‖g x‖ ≤ 1) (f : Lp E 2 μ) :
    mulOp (μ := μ) g g.continuous.measurable hb f = bcfMul g f := by
  apply Lp.ext
  filter_upwards [coeFn_mulOp (μ := μ) g.continuous.measurable hb f, coeFn_bcfMul (μ := μ) g f] with x h1 h2
  rw [h1, h2]

/-- **Strong convergence**: if `h_k → h` pointwise (all bounded by `1`), then `h_k f → h f` in `L²`. -/
lemma tendsto_mulOp {h : ℕ → X → ℂ} (hm : ∀ k, Measurable (h k)) (hb : ∀ k x, ‖h k x‖ ≤ 1)
    {h₀ : X → ℂ} (hm₀ : Measurable h₀) (hb₀ : ∀ x, ‖h₀ x‖ ≤ 1) (hlim : ∀ x, Tendsto (fun k => h k x) atTop (𝓝 (h₀ x)))
    (f : Lp E 2 μ) :
    Tendsto (fun k => mulOp (μ := μ) (h k) (hm k) (hb k) f) atTop (𝓝 (mulOp h₀ hm₀ hb₀ f)) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have hfm := Lp.aestronglyMeasurable f
  set G : ℕ → X → E := fun k x => h k x • f x - h₀ x • f x
  have hcongr : ∀ k : ℕ, eLpNorm (⇑(mulOp (μ := μ) (h k) (hm k) (hb k) f) - ⇑(mulOp (μ := μ) h₀ hm₀ hb₀ f)) 2 μ =
      eLpNorm (G k) 2 μ := fun k => eLpNorm_congr_ae ((coeFn_mulOp (hm k) (hb k) f).sub (coeFn_mulOp hm₀ hb₀ f))
  simp only [hcongr]
  have hGm : ∀ k, AEStronglyMeasurable (G k) μ := fun k =>
    ((hm k).aestronglyMeasurable.smul hfm).sub (hm₀.aestronglyMeasurable.smul hfm)
  have hl : Tendsto (fun k : ℕ => ∫⁻ x, ‖G k x‖ₑ ^ (2 : ℝ) ∂μ) atTop (𝓝 (∫⁻ _, 0 ∂μ)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence' (fun x => (2 * ‖f x‖ₑ) ^ (2 : ℝ)) ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun k => ((hGm k).enorm.pow_const _)
    · refine Filter.Eventually.of_forall fun k => Filter.Eventually.of_forall fun x => ?_
      refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      refine (enorm_sub_le).trans ?_
      have hle : ∀ c : ℂ, ‖c‖ ≤ 1 → ‖c • f x‖ₑ ≤ ‖f x‖ₑ := fun c hc => by
        rw [enorm_smul]
        calc ‖c‖ₑ * ‖f x‖ₑ ≤ 1 * ‖f x‖ₑ := by
              gcongr
              rw [← ofReal_norm, ← ENNReal.ofReal_one]
              exact ENNReal.ofReal_le_ofReal hc
          _ = ‖f x‖ₑ := one_mul _
      calc _ ≤ ‖f x‖ₑ + ‖f x‖ₑ := add_le_add (hle _ (hb k x)) (hle _ (hb₀ x))
        _ = 2 * ‖f x‖ₑ := by ring
    · have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
        (Lp.memLp f).eLpNorm_lt_top
      simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
      rw [lintegral_const_mul' _ _ (by simp)]
      exact ENNReal.mul_ne_top (by simp) (by simpa using h.ne)
    · refine Filter.Eventually.of_forall fun x => ?_
      have h1 := (((hlim x).smul_const (f x)).sub_const (h₀ x • f x))
      rw [sub_self] at h1
      have h' := ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto _).comp
        ((continuous_enorm.tendsto _).comp h1)
      rw [enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num)] at h'
      exact h'
  rw [lintegral_zero] at hl
  have hl2 := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp hl
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at hl2
  refine hl2.congr' (Filter.Eventually.of_forall fun k => ?_)
  simp only [Function.comp_apply]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by simp) (hGm k)]
  norm_num

/-! ## Indicators -/

omit [MeasurableSpace X] in
lemma norm_indicator_one_le (S : Set X) (x : X) : ‖S.indicator (fun _ => (1 : ℂ)) x‖ ≤ 1 := by
  by_cases h : x ∈ S <;> simp [h]

/-- Multiplication by the indicator of a measurable set. -/
def indL2 (S : Set X) (hS : MeasurableSet S) : Lp E 2 μ →L[ℂ] Lp E 2 μ :=
  mulOp (S.indicator fun _ => (1 : ℂ)) (measurable_const.indicator hS) (norm_indicator_one_le S)

lemma indL2_congr {S S' : Set X} (h : S = S') (hS : MeasurableSet S) (hS' : MeasurableSet S') :
    indL2 (μ := μ) (E := E) S hS = indL2 S' hS' := by
  subst h; rfl

lemma coeFn_indL2 {S : Set X} (hS : MeasurableSet S) (f : Lp E 2 μ) :
    (indL2 (μ := μ) S hS f : X → E) =ᵐ[μ] S.indicator f := by
  filter_upwards [coeFn_mulOp (μ := μ) (measurable_const.indicator hS) (norm_indicator_one_le S) f] with x hx
  change (mulOp (μ := μ) _ _ _ f : X → E) x = _
  rw [hx]
  by_cases h : x ∈ S <;> simp [h]

lemma indL2_compl {S : Set X} (hS : MeasurableSet S) (f : Lp E 2 μ) :
    indL2 (μ := μ) Sᶜ hS.compl f = f - indL2 S hS f := by
  apply Lp.ext
  filter_upwards [coeFn_indL2 (μ := μ) hS.compl f, Lp.coeFn_sub f (indL2 (μ := μ) S hS f),
    coeFn_indL2 (μ := μ) hS f] with x h1 h2 h3
  rw [h1, h2, Pi.sub_apply, h3]
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_notMem (show x ∉ Sᶜ from fun h => h hx), Set.indicator_of_mem hx, sub_self]
  · rw [Set.indicator_of_mem (show x ∈ Sᶜ from hx), Set.indicator_of_notMem hx, sub_zero]

lemma indL2_inter {S T : Set X} (hS : MeasurableSet S) (hT : MeasurableSet T) (f : Lp E 2 μ) :
    indL2 (μ := μ) (S ∩ T) (hS.inter hT) f = indL2 S hS (indL2 T hT f) := by
  apply Lp.ext
  filter_upwards [coeFn_indL2 (μ := μ) (hS.inter hT) f, coeFn_indL2 (μ := μ) hS (indL2 (μ := μ) T hT f),
    coeFn_indL2 (μ := μ) hT f] with x h1 h2 h3
  rw [h1, h2]
  by_cases hxS : x ∈ S <;> by_cases hxT : x ∈ T <;> simp [Set.indicator, hxS, hxT, h3]

lemma indL2_empty (f : Lp E 2 μ) : indL2 (μ := μ) (∅ : Set X) MeasurableSet.empty f = 0 := by
  apply Lp.ext
  filter_upwards [coeFn_indL2 (μ := μ) MeasurableSet.empty f, Lp.coeFn_zero E 2 μ] with x h1 h2
  rw [h1, h2]
  simp

/-- If the measurable sets `S_k` increase to `S`, then `1_{S_k} f → 1_S f`. -/
lemma tendsto_indL2_iUnion {S : ℕ → Set X} (hS : ∀ k, MeasurableSet (S k)) (hmono : Monotone S)
    (f : Lp E 2 μ) :
    Tendsto (fun k => indL2 (μ := μ) (S k) (hS k) f) atTop (𝓝 (indL2 (⋃ k, S k) (MeasurableSet.iUnion hS) f)) := by
  refine tendsto_mulOp (μ := μ) _ (fun k => norm_indicator_one_le (S k)) _ (norm_indicator_one_le _) (fun x => ?_) f
  by_cases hx : x ∈ ⋃ k, S k
  · obtain ⟨k₀, hk₀⟩ := Set.mem_iUnion.1 hx
    rw [Set.indicator_of_mem hx]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop k₀] with k hk
    rw [Set.indicator_of_mem (hmono hk hk₀)]
  · rw [Set.indicator_of_notMem hx]
    refine tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun k => ?_)
    dsimp only
    rw [Set.indicator_of_notMem (fun h => hx (Set.mem_iUnion.2 ⟨k, h⟩))]

end

end Lightlike.Poincare
