import Mathlib
import Lightlike.PL.Schoenflies.DiscForm

/-!
# The Alexander (cone) extension of a homeomorphism of the circle to the disc

Row G3-188, milestone PL5 (third pass).  A homeomorphism of the unit circle `circ` extends to a homeomorphism
of the closed unit disc `disc` by coning: `x ↦ |x| · φ (x / |x|)`.  This is the tool that lets the
polygonal Schoenflies maps of two polygons be glued along a prescribed boundary homeomorphism.

* `circle_homeo_extends`: every homeomorphism `φ : circ ≃ₜ circ` extends to a homeomorphism `disc ≃ₜ disc`.
-/

namespace Lightlike.PL.Schoenflies

open Set Filter Topology

/-- The Euclidean norm on `ℝ × ℝ`. -/
noncomputable def rad (x : ℝ × ℝ) : ℝ := Real.sqrt (x.1 ^ 2 + x.2 ^ 2)

lemma continuous_rad : Continuous rad := by unfold rad; fun_prop

lemma rad_nonneg (x : ℝ × ℝ) : 0 ≤ rad x := Real.sqrt_nonneg _

lemma rad_zero : rad 0 = 0 := by simp [rad]

lemma rad_eq_zero_iff {x : ℝ × ℝ} : rad x = 0 ↔ x = 0 := by
  unfold rad
  rw [Real.sqrt_eq_zero (by positivity)]
  constructor
  · intro h
    have h1 : x.1 = 0 := by nlinarith [sq_nonneg x.1, sq_nonneg x.2]
    have h2 : x.2 = 0 := by nlinarith [sq_nonneg x.1, sq_nonneg x.2]
    exact Prod.ext h1 h2
  · rintro rfl; simp

lemma rad_smul {t : ℝ} (ht : 0 ≤ t) (x : ℝ × ℝ) : rad (t • x) = t * rad x := by
  unfold rad
  have : (t • x).1 ^ 2 + (t • x).2 ^ 2 = t ^ 2 * (x.1 ^ 2 + x.2 ^ 2) := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  rw [this, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht]

lemma mem_circ_iff {x : ℝ × ℝ} : x ∈ circ ↔ rad x = 1 := by
  unfold rad circ
  rw [Set.mem_ofPred_eq, Real.sqrt_eq_one]

lemma mem_disc_iff {x : ℝ × ℝ} : x ∈ disc ↔ rad x ≤ 1 := by
  unfold rad disc
  rw [Set.mem_ofPred_eq, Real.sqrt_le_iff]
  constructor
  · intro h; exact ⟨zero_le_one, by simpa using h⟩
  · rintro ⟨-, h⟩; simpa using h

lemma circ_subset_disc : circ ⊆ disc := fun _ hx => by
  rw [mem_circ_iff] at hx; rw [mem_disc_iff]; exact hx.le

lemma norm_le_rad (w : ℝ × ℝ) : ‖w‖ ≤ rad w := by
  rw [Prod.norm_def, max_le_iff]
  constructor
  · rw [Real.norm_eq_abs]; exact Real.abs_le_sqrt (by nlinarith [sq_nonneg w.2])
  · rw [Real.norm_eq_abs]; exact Real.abs_le_sqrt (by nlinarith [sq_nonneg w.1])

/-- The cone of a map `g` of the plane: `x ↦ |x| • g (x / |x|)`, and `0 ↦ 0`. -/
noncomputable def coneMap (g : ℝ × ℝ → ℝ × ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  if x = 0 then 0 else rad x • g ((rad x)⁻¹ • x)

lemma unit_mem_circ {x : ℝ × ℝ} (hx : x ≠ 0) : (rad x)⁻¹ • x ∈ circ := by
  have hr : 0 < rad x := lt_of_le_of_ne (rad_nonneg x) (fun h => hx (rad_eq_zero_iff.1 h.symm))
  rw [mem_circ_iff, rad_smul (inv_nonneg.2 hr.le), inv_mul_cancel₀ hr.ne']

lemma rad_coneMap {g : ℝ × ℝ → ℝ × ℝ} (hg : MapsTo g circ circ) (x : ℝ × ℝ) :
    rad (coneMap g x) = rad x := by
  by_cases hx : x = 0
  · simp [coneMap, hx, rad_zero]
  · have hr : 0 ≤ rad x := rad_nonneg x
    simp only [coneMap, hx, if_false]
    rw [rad_smul hr, mem_circ_iff.1 (hg (unit_mem_circ hx)), mul_one]

lemma continuous_coneMap {g : ℝ × ℝ → ℝ × ℝ} (hg : ContinuousOn g circ) (hm : MapsTo g circ circ) :
    Continuous (coneMap g) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    have h0 : coneMap g 0 = 0 := by simp [coneMap]
    rw [ContinuousAt, h0, tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun y => ?_)
      (by simpa [rad_zero] using continuous_rad.tendsto 0)
    calc ‖coneMap g y‖ ≤ rad (coneMap g y) := norm_le_rad _
      _ = rad y := rad_coneMap hm y
  · have hU : ContinuousOn (fun y => rad y • g ((rad y)⁻¹ • y)) {y : ℝ × ℝ | y ≠ 0} := by
      refine continuous_rad.continuousOn.smul (hg.comp ?_ ?_)
      · refine ContinuousOn.smul (ContinuousOn.inv₀ continuous_rad.continuousOn ?_) continuousOn_id
        intro y hy h; exact hy (rad_eq_zero_iff.1 h)
      · intro y hy; exact unit_mem_circ hy
    have hopen : IsOpen {y : ℝ × ℝ | y ≠ 0} := isOpen_ne
    refine (hU.continuousAt (hopen.mem_nhds hx)).congr ?_
    filter_upwards [hopen.mem_nhds hx] with y hy
    simp only [coneMap, if_neg (show y ≠ 0 from hy)]

lemma coneMap_coneMap {g h : ℝ × ℝ → ℝ × ℝ} (hg : MapsTo g circ circ)
    (hgh : ∀ z ∈ circ, h (g z) = z) (x : ℝ × ℝ) : coneMap h (coneMap g x) = x := by
  by_cases hx : x = 0
  · simp [coneMap, hx]
  · have hr : 0 < rad x := lt_of_le_of_ne (rad_nonneg x) (fun h => hx (rad_eq_zero_iff.1 h.symm))
    have hne : coneMap g x ≠ 0 := by
      intro h0
      have := rad_coneMap hg x
      rw [h0, rad_zero] at this
      exact hx (rad_eq_zero_iff.1 this.symm)
    have hrad := rad_coneMap hg x
    have e1 : coneMap g x = rad x • g ((rad x)⁻¹ • x) := by simp [coneMap, hx]
    have e2 : (rad (coneMap g x))⁻¹ • coneMap g x = g ((rad x)⁻¹ • x) := by
      rw [hrad, e1, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    have e3 : coneMap h (coneMap g x) = rad (coneMap g x) • h ((rad (coneMap g x))⁻¹ • coneMap g x) :=
      if_neg hne
    rw [e3, e2, hgh _ (unit_mem_circ hx), hrad, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]

open scoped Classical in
/-- A homeomorphism of the circle, as a map of the plane (zero off the circle). -/
noncomputable def circExt (ψ : circ ≃ₜ circ) (z : ℝ × ℝ) : ℝ × ℝ :=
  if hz : z ∈ circ then ((ψ ⟨z, hz⟩ : circ) : ℝ × ℝ) else 0

lemma circExt_apply (ψ : circ ≃ₜ circ) (z : circ) : circExt ψ z = ((ψ z : circ) : ℝ × ℝ) := by
  simp [circExt]

lemma mapsTo_circExt (ψ : circ ≃ₜ circ) : MapsTo (circExt ψ) circ circ := by
  intro z hz
  have := circExt_apply ψ ⟨z, hz⟩
  simp only at this
  rw [this]
  exact (ψ ⟨z, hz⟩).2

lemma continuousOn_circExt (ψ : circ ≃ₜ circ) : ContinuousOn (circExt ψ) circ := by
  rw [continuousOn_iff_continuous_domRestrict]
  have : circ.domRestrict (circExt ψ) = fun z : circ => ((ψ z : circ) : ℝ × ℝ) := by
    funext z; exact circExt_apply ψ z
  rw [this]
  exact continuous_subtype_val.comp ψ.continuous

lemma circExt_symm (ψ : circ ≃ₜ circ) {z : ℝ × ℝ} (hz : z ∈ circ) :
    circExt ψ.symm (circExt ψ z) = z := by
  have h1 := circExt_apply ψ ⟨z, hz⟩
  simp only at h1
  rw [h1, circExt_apply ψ.symm (ψ ⟨z, hz⟩)]
  simp

lemma rad_le_one_of_mem_disc {x : ℝ × ℝ} (hx : x ∈ disc) : rad x ≤ 1 := mem_disc_iff.1 hx

/-- **Alexander's cone extension.**  Every homeomorphism of the unit circle extends to a homeomorphism of the
closed unit disc (by `x ↦ |x| φ (x / |x|)`). -/
theorem circle_homeo_extends (φ : circ ≃ₜ circ) :
    ∃ Φ : disc ≃ₜ disc, ∀ z : circ, ((Φ ⟨z, circ_subset_disc z.2⟩ : disc) : ℝ × ℝ) = φ z := by
  have hmem : ∀ (ψ : circ ≃ₜ circ) (x : disc), coneMap (circExt ψ) x ∈ disc := fun ψ x => by
    rw [mem_disc_iff, rad_coneMap (mapsTo_circExt ψ)]
    exact mem_disc_iff.1 x.2
  have hcont : ∀ ψ : circ ≃ₜ circ, Continuous fun x : disc => (⟨coneMap (circExt ψ) x, hmem ψ x⟩ : disc) :=
    fun ψ => ((continuous_coneMap (continuousOn_circExt ψ) (mapsTo_circExt ψ)).comp
      continuous_subtype_val).subtype_mk _
  refine ⟨⟨⟨fun x => ⟨coneMap (circExt φ) x, hmem φ x⟩, fun x => ⟨coneMap (circExt φ.symm) x, hmem φ.symm x⟩,
    fun x => ?_, fun x => ?_⟩, hcont φ, hcont φ.symm⟩, fun z => ?_⟩
  · exact Subtype.ext (coneMap_coneMap (mapsTo_circExt φ) (fun w hw => circExt_symm φ hw) x)
  · exact Subtype.ext (coneMap_coneMap (mapsTo_circExt φ.symm) (fun w hw => by
      simpa using circExt_symm φ.symm hw) x)
  · have hz := mem_circ_iff.1 z.2
    have hz0 : (z : ℝ × ℝ) ≠ 0 := fun h => by rw [h, rad_zero] at hz; exact zero_ne_one hz
    show coneMap (circExt φ) z = φ z
    simp only [coneMap, if_neg hz0, hz, inv_one, one_smul]
    rw [circExt_apply φ z]

end Lightlike.PL.Schoenflies
