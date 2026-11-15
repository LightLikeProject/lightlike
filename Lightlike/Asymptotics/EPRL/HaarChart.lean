import Lightlike.Asymptotics.EPRL.HaarGraph
import Lightlike.Asymptotics.EPRL.GaugeFix

/-!
# Haar measure of `SU(2)^4` in the gnomonic chart on `ℝ¹²`

`integral_haar_gnomonic` (`HaarGraph.lean`) writes the Haar integral over one factor of `SU(2)` as
an integral over `ℝ³` with the density `1/(2π²(1+|q|²)²)`. Here the four factors of `SU(2)^4` are
taken together: for a continuous `f` supported where each factor lies in the translated open
hemisphere `p_a · hemiSU`,

`∫ f dHaar = ∫_{ℝ¹²} (∏_a ρ(q_a)) f(p_a γ(q_a)) dq`,

with the coordinates `q_a = (q_{3a}, q_{3a+1}, q_{3a+2})` as in the chart of `Amplitude.lean`
(`integral_haar4_chart`). The steps are: the product of the one-factor densities is the density of
the product measure (`pi_withDensity`), the product of the hemisphere restrictions is the
push-forward by the product chart, and `ℝ³ × ℝ³ × ℝ³ × ℝ³` is `ℝ¹²` with Lebesgue measure
(`measurePreserving_reshape`).
-/

open MeasureTheory Complex Finset Set
open scoped ENNReal

namespace Lightlike.Asymptotics.EPRL

open Lightlike.Spin4

local instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
local instance : SecondCountableTopology SU2 :=
  TopologicalSpace.Subtype.secondCountableTopology _

/-! ## Reshaping `ℝ³ × ℝ³ × ℝ³ × ℝ³` into `ℝ¹²` -/

/-- The index equivalence `Fin 4 × Fin 3 ≃ Fin 12` of the chart. -/
def fpf : Fin 4 × Fin 3 ≃ Fin 12 := finProdFinEquiv

/-- `Fin 4 → Fin 3 → ℝ` read as `Fin 12 → ℝ` through `finProdFinEquiv`. -/
def reshapeEquiv : (Fin 4 → Fin 3 → ℝ) ≃ (Fin 12 → ℝ) where
  toFun Y i := Y (fpf.symm i).1 (fpf.symm i).2
  invFun q a k := q (fpf (a, k))
  left_inv Y := by funext a k; simp
  right_inv q := by funext i; simp

/-- `reshapeEquiv` as a measurable equivalence. -/
noncomputable def reshape : (Fin 4 → Fin 3 → ℝ) ≃ᵐ (Fin 12 → ℝ) where
  toEquiv := reshapeEquiv
  measurable_toFun := by
    refine Measurable.of_eval fun i => ?_
    exact (measurable_pi_apply (fpf.symm i).2).comp (measurable_pi_apply (fpf.symm i).1)
  measurable_invFun := by
    refine Measurable.of_eval fun a => Measurable.of_eval fun k => ?_
    exact measurable_pi_apply _

lemma reshape_symm_apply (q : Fin 12 → ℝ) (a : Fin 4) (k : Fin 3) :
    reshape.symm q a k = q (fpf (a, k)) := rfl

/-- **Lebesgue measure on `(ℝ³)⁴` is Lebesgue measure on `ℝ¹²`.** -/
theorem measurePreserving_reshape : MeasurePreserving reshape volume volume := by
  refine ⟨reshape.measurable, ?_⟩
  symm
  refine (Measure.pi_eq (μ := fun _ : Fin 12 => (volume : Measure ℝ)) fun s hs => ?_)
  rw [MeasurableEquiv.map_apply]
  have : reshape ⁻¹' (Set.univ.pi s) =
      Set.univ.pi (fun a : Fin 4 => Set.univ.pi fun k : Fin 3 =>
        s (fpf (a, k))) := by
    ext Y
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h a k
      have := h (fpf (a, k))
      simpa [reshape, reshapeEquiv] using this
    · intro h i
      have := h (fpf.symm i).1 (fpf.symm i).2
      simpa [reshape, reshapeEquiv] using this
  rw [this]
  have hv : (volume : Measure (Fin 4 → Fin 3 → ℝ)) = Measure.pi fun _ => volume := rfl
  rw [hv, Measure.pi_pi]
  have hv3 : (volume : Measure (Fin 3 → ℝ)) = Measure.pi fun _ => volume := rfl
  simp_rw [hv3, Measure.pi_pi]
  rw [← Fintype.prod_prod_type' (fun a k => volume (s (fpf (a, k))))]
  exact Equiv.prod_comp fpf (fun i => volume (s i))

/-! ## The product density -/

/-- The product of the gnomonic Haar densities of the four factors. -/
noncomputable def haarDensity4 (Y : Fin 4 → Fin 3 → ℝ) : ℝ := ∏ a, haarDensity (Y a)

lemma haarDensity4_pos (Y : Fin 4 → Fin 3 → ℝ) : 0 < haarDensity4 Y :=
  prod_pos fun a _ => haarDensity_pos (Y a)

lemma measurable_haarDensity4 : Measurable haarDensity4 := by
  unfold haarDensity4
  exact Finset.measurable_prod _ fun a _ => measurable_haarDensity.comp (measurable_pi_apply a)

/-- **The integral of a product of functions of single coordinates** over a finite product
measure is the product of the integrals. -/
theorem lintegral_pi_prod {α : Type*} [MeasurableSpace α] :
    ∀ (n : ℕ) (μ : Fin n → Measure α) [∀ i, SigmaFinite (μ i)] (f : Fin n → α → ℝ≥0∞),
      (∀ i, Measurable (f i)) →
      ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ x, f i x ∂μ i := by
  intro n
  induction n with
  | zero => intro μ _ f _; simp
  | succ n ih =>
    intro μ _ f hf
    have hmp := measurePreserving_piFinSuccAbove (α := fun _ : Fin (n + 1) => α) μ 0
    have hmeas : Measurable fun x : Fin (n + 1) → α => ∏ i, f i (x i) :=
      Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
    have h1 : ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ =
        ∫⁻ p, (f 0 p.1 * ∏ j : Fin n, f j.succ (p.2 j))
          ∂((μ 0).prod (Measure.pi fun j => μ (Fin.succAbove 0 j))) := by
      rw [← hmp.lintegral_comp_emb (MeasurableEquiv.piFinSuccAbove _ 0).measurableEmbedding]
      refine lintegral_congr fun x => ?_
      simp [MeasurableEquiv.piFinSuccAbove, Fin.prod_univ_succ, Fin.tail]
    rw [h1, lintegral_prod_mul (f := f 0) (g := fun y : Fin n → α => ∏ j, f j.succ (y j))
      (hf 0).aemeasurable
      (Finset.measurable_prod _ fun j _ => (hf j.succ).comp (measurable_pi_apply j)).aemeasurable,
      Fin.prod_univ_succ]
    congr 1
    exact ih (fun j => μ (Fin.succAbove 0 j)) (fun j => f j.succ) (fun j => hf j.succ)

/-- **A product of measures with density has the product density.** -/
theorem pi_withDensity :
    (Measure.pi fun _ : Fin 4 =>
        (volume : Measure (Fin 3 → ℝ)).withDensity fun q => ENNReal.ofReal (haarDensity q)) =
      (volume : Measure (Fin 4 → Fin 3 → ℝ)).withDensity
        fun Y => ENNReal.ofReal (haarDensity4 Y) := by
  refine Measure.pi_eq (μ := fun _ : Fin 4 =>
    (volume : Measure (Fin 3 → ℝ)).withDensity fun q => ENNReal.ofReal (haarDensity q)) fun s hs => ?_
  have hset : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  rw [withDensity_apply _ hset, ← lintegral_indicator hset]
  have hind : ∀ Y : Fin 4 → Fin 3 → ℝ,
      (Set.univ.pi s).indicator (fun Y => ENNReal.ofReal (haarDensity4 Y)) Y =
        ∏ a, (s a).indicator (fun q => ENNReal.ofReal (haarDensity q)) (Y a) := by
    intro Y
    by_cases h : Y ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem h]
      simp only [Set.mem_pi, Set.mem_univ, true_implies] at h
      unfold haarDensity4
      rw [ENNReal.ofReal_prod_of_nonneg fun a _ => (haarDensity_pos (Y a)).le]
      exact prod_congr rfl fun a _ => (Set.indicator_of_mem (h a) (fun q => ENNReal.ofReal (haarDensity q))).symm
    · rw [Set.indicator_of_notMem h]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at h
      obtain ⟨a, ha⟩ := h
      symm
      exact prod_eq_zero (Finset.mem_univ a) (Set.indicator_of_notMem ha _)
  simp_rw [hind]
  have hv : (volume : Measure (Fin 4 → Fin 3 → ℝ)) = Measure.pi fun _ => volume := rfl
  rw [hv, lintegral_pi_prod 4 (fun _ => volume)
    (fun a (q : Fin 3 → ℝ) => (s a).indicator (fun q => ENNReal.ofReal (haarDensity q)) q)
    (fun a => measurable_haarDensity.ennreal_ofReal.indicator (hs a))]
  refine prod_congr rfl fun a _ => ?_
  rw [withDensity_apply _ (hs a), lintegral_indicator (hs a)]

/-! ## The chart integral -/

/-- **Haar integration on `SU(2)^4` in the product chart.** For a measurable `f` supported where
every factor `(p a)⁻¹ Y a` lies in the open hemisphere, the integral against the Haar measure is
the integral over `ℝ¹²` against the product density, with `Y a = p a · γ(q_a)`. -/
theorem integral_haar4_chart (p : Fin 4 → SU2) (f : (Fin 4 → SU2) → ℂ) (hf : Measurable f)
    (hsupp : ∀ Y, f Y ≠ 0 → ∀ a, (p a)⁻¹ * Y a ∈ hemiSU) :
    ∫ Y, f Y ∂(haarN 4) =
      ∫ q : Fin 12 → ℝ, haarDensity4 (reshape.symm q) •
        f (fun a => p a * gammaSU (reshape.symm q a)) := by
  have hH : MeasurableSet hemiSU :=
    measurableSet_lt measurable_const
      (Complex.measurable_re.comp ((measurable_pi_apply 0).comp (measurable_pi_apply 0 |>.comp
        measurable_subtype_coe)))
  -- translate by `p`
  have hmp : MeasurePreserving (fun Z : Fin 4 → SU2 => fun a => p a * Z a) (haarN 4) (haarN 4) :=
    measurePreserving_pi _ _ (fun a => measurePreserving_mul_left haarSU2 (p a))
  have hmeq : MeasurableEmbedding (fun Z : Fin 4 → SU2 => fun a => p a * Z a) :=
    (MeasurableEquiv.piCongrRight fun a => MeasurableEquiv.mulLeft (p a)).measurableEmbedding
  have h1 : ∫ Y, f Y ∂(haarN 4) = ∫ Z, f (fun a => p a * Z a) ∂(haarN 4) :=
    (hmp.integral_comp hmeq f).symm
  set g : (Fin 4 → SU2) → ℂ := fun Z => f (fun a => p a * Z a) with hg
  have hgc : Measurable g :=
    hf.comp (Measurable.of_eval fun a => measurable_const.mul (measurable_pi_apply a))
  have hgs : ∀ Z, g Z ≠ 0 → Z ∈ Set.univ.pi fun _ : Fin 4 => hemiSU := by
    intro Z hZ a _
    have := hsupp _ hZ a
    simpa using this
  have h2 : ∫ Z, g Z ∂(haarN 4) = ∫ Z, g Z ∂((haarN 4).restrict (Set.univ.pi fun _ : Fin 4 => hemiSU)) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (fun Z hZ => by
      by_contra h; exact hZ (hgs Z h))).symm
  have hr : (haarN 4).restrict (Set.univ.pi fun _ : Fin 4 => hemiSU) =
      Measure.pi fun _ : Fin 4 => haarSU2.restrict hemiSU := by
    unfold haarN; exact Measure.restrict_pi_pi _ _
  have hmap : (Measure.pi fun _ : Fin 4 => haarSU2.restrict hemiSU) =
      (volume.withDensity fun Y : Fin 4 → Fin 3 → ℝ => ENNReal.ofReal (haarDensity4 Y)).map
        (fun Y a => gammaSU (Y a)) := by
    simp_rw [haarSU2_restrict_hemi]
    have : ∀ _ : Fin 4, SigmaFinite
        (volume.withDensity fun q : Fin 3 → ℝ => ENNReal.ofReal (haarDensity q)) := fun _ => by
      infer_instance
    have : SigmaFinite (Measure.map gammaSU
        (volume.withDensity fun q : Fin 3 → ℝ => ENNReal.ofReal (haarDensity q))) := by
      rw [← haarSU2_restrict_hemi]; infer_instance
    rw [← pi_withDensity]
    exact (Measure.pi_map_pi (μ := fun _ : Fin 4 =>
      (volume : Measure (Fin 3 → ℝ)).withDensity fun q => ENNReal.ofReal (haarDensity q))
      (f := fun _ => gammaSU) (fun _ => measurable_gammaSU.aemeasurable)).symm
  have hgm : Measurable fun Y : Fin 4 → Fin 3 → ℝ => fun a => gammaSU (Y a) :=
    Measurable.of_eval fun a => measurable_gammaSU.comp (measurable_pi_apply a)
  rw [h1, h2, hr, hmap, integral_map hgm.aemeasurable hgc.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_haarDensity4.ennreal_ofReal) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have hcongr : ∀ Y : Fin 4 → Fin 3 → ℝ,
      (ENNReal.ofReal (haarDensity4 Y)).toReal • g (fun a => gammaSU (Y a)) =
        haarDensity4 Y • f (fun a => p a * gammaSU (Y a)) := fun Y => by
    simp [hg, ENNReal.toReal_ofReal (haarDensity4_pos Y).le]
  simp_rw [hcongr]
  have hres := measurePreserving_reshape.integral_comp reshape.measurableEmbedding
    (fun q : Fin 12 → ℝ => haarDensity4 (reshape.symm q) •
      f (fun a => p a * gammaSU (reshape.symm q a)))
  simpa using hres

end Lightlike.Asymptotics.EPRL
