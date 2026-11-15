import Lightlike.Spin4.SO4
import Lightlike.Spin4.Haar
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The Haar measure of SU(2) as the surface measure of the 3-sphere

`SU(2)` is the group of unit quaternions, the unit sphere of `ℍ ≅ ℝ⁴` (`Lightlike.Spin4.quatEquiv`).
Left multiplication by a unit quaternion is a linear isometry of `ℍ`, so it preserves Lebesgue
measure and the cone measure `toSphere` of the sphere. This file proves that invariance
(`map_mulLeft_toSphere`), the first step towards identifying the Haar measure of `SU(2)` with the
normalised surface measure and computing its density in a chart.
-/

open Quaternion MeasureTheory Set Metric Pointwise ENNReal

namespace Lightlike.Asymptotics.EPRL

/-- The Borel σ-algebra on the real quaternions. -/
noncomputable local instance : MeasurableSpace ℍ[ℝ] := borel ℍ[ℝ]
local instance : BorelSpace ℍ[ℝ] := ⟨rfl⟩

/-- **Left multiplication by a unit quaternion** as a linear isometry of `ℍ`. -/
noncomputable def mulLeftIso (q : ℍ[ℝ]) (hq : ‖q‖ = 1) : ℍ[ℝ] ≃ₗᵢ[ℝ] ℍ[ℝ] where
  toFun x := q * x
  invFun x := q⁻¹ * x
  map_add' x y := mul_add q x y
  map_smul' c x := mul_smul_comm c q x
  left_inv x := inv_mul_cancel_left₀ (norm_ne_zero_iff.mp (by rw [hq]; exact one_ne_zero)) x
  right_inv x := mul_inv_cancel_left₀ (norm_ne_zero_iff.mp (by rw [hq]; exact one_ne_zero)) x
  norm_map' x := by simp [norm_mul, hq]

@[simp] lemma mulLeftIso_apply (q : ℍ[ℝ]) (hq : ‖q‖ = 1) (x : ℍ[ℝ]) :
    mulLeftIso q hq x = q * x := rfl

/-- Left multiplication by a unit quaternion preserves the norm, hence the unit sphere. -/
noncomputable def sphereMulLeft (q : ℍ[ℝ]) (hq : ‖q‖ = 1) :
    sphere (0 : ℍ[ℝ]) 1 → sphere (0 : ℍ[ℝ]) 1 :=
  fun x => ⟨q * x, by simp [norm_mul, hq]⟩

/-- **Lebesgue measure is invariant** under left multiplication by a unit quaternion. -/
theorem measurePreserving_mulLeft (q : ℍ[ℝ]) (hq : ‖q‖ = 1) :
    MeasurePreserving (fun x : ℍ[ℝ] => q * x) volume volume :=
  (mulLeftIso q hq).measurePreserving

/-- Left multiplication by a unit quaternion is continuous on the sphere. -/
lemma continuous_sphereMulLeft (q : ℍ[ℝ]) (hq : ‖q‖ = 1) :
    Continuous (sphereMulLeft q hq) :=
  Continuous.subtype_mk (continuous_const.mul continuous_subtype_val) _

/-- Volume of the image of a set under left multiplication by a unit quaternion. -/
lemma volume_image_mulLeft (q : ℍ[ℝ]) (hq : ‖q‖ = 1) (A : Set ℍ[ℝ]) :
    volume ((fun x => q * x) '' A) = volume A := by
  have h := (mulLeftIso q hq).symm.measurePreserving
  have he := (mulLeftIso q hq).symm.toHomeomorph.measurableEmbedding
  have e : (fun x => q * x) '' A = (mulLeftIso q hq).symm ⁻¹' A := by
    rw [← LinearIsometryEquiv.image_eq_preimage_symm]; rfl
  rw [e]
  exact h.measure_preimage_emb he A

/-- **The cone measure of the 3-sphere is invariant** under left multiplication by a unit
quaternion. -/
theorem map_sphereMulLeft_toSphere (q : ℍ[ℝ]) (hq : ‖q‖ = 1) :
    Measure.map (sphereMulLeft q hq) (volume : Measure ℍ[ℝ]).toSphere
      = (volume : Measure ℍ[ℝ]).toSphere := by
  have hqi : ‖q⁻¹‖ = 1 := by simp [hq]
  ext s hs
  have hm : Measurable (sphereMulLeft q hq) := (continuous_sphereMulLeft q hq).measurable
  rw [Measure.map_apply hm hs, Measure.toSphere_apply' _ (hm hs), Measure.toSphere_apply' _ hs]
  congr 1
  have himg : ((↑) '' (sphereMulLeft q hq ⁻¹' s) : Set ℍ[ℝ])
      = (fun x => q⁻¹ * x) '' ((↑) '' s) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨q * x, ⟨⟨q * x, by simp [norm_mul, hq]⟩, hx, rfl⟩, by
        simp [← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mp (by rw [hq]; exact one_ne_zero))]⟩
    · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨⟨q⁻¹ * w, by simp [norm_mul, hqi]⟩, ?_, rfl⟩
      show sphereMulLeft q hq _ ∈ s
      convert hw using 1
      apply Subtype.ext
      simp [sphereMulLeft, ← mul_assoc,
        mul_inv_cancel₀ (norm_ne_zero_iff.mp (by rw [hq]; exact one_ne_zero))]
  rw [himg]
  have hsm : Ioo (0 : ℝ) 1 • ((fun x => q⁻¹ * x) '' ((↑) '' s : Set ℍ[ℝ]))
      = (fun x => q⁻¹ * x) '' (Ioo (0 : ℝ) 1 • ((↑) '' s : Set ℍ[ℝ])) := by
    ext y
    simp only [Set.mem_image]
    constructor
    · rintro ⟨c, hc, _, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨c • z, ⟨c, hc, z, hz, rfl⟩, by simp⟩
    · rintro ⟨_, ⟨c, hc, z, hz, rfl⟩, rfl⟩
      exact ⟨c, hc, q⁻¹ * z, ⟨z, hz, rfl⟩, by simp⟩
  rw [hsm]
  rw [volume_image_mulLeft q⁻¹ hqi]

/-! ## The sphere as SU(2) -/

open Lightlike Lightlike.Spin4 in
/-- A unit quaternion has `normSq = 1`. -/
lemma normSq_of_mem_sphere (x : sphere (0 : ℍ[ℝ]) 1) : Quaternion.normSq (x : ℍ[ℝ]) = 1 := by
  have h : ‖(x : ℍ[ℝ])‖ = 1 := by simpa using x.2
  rw [Quaternion.normSq_eq_norm_mul_self, h, one_mul]

open Lightlike Lightlike.Spin4 in
/-- The unit sphere of `ℍ` as `SU(2)`: `x ↦ toMat x`. -/
noncomputable def sphereToSU2 (x : sphere (0 : ℍ[ℝ]) 1) : SU2 :=
  ⟨toMat (x : ℍ[ℝ]), toMat_mem_SU2 ⟨x, mem_unitary_of_normSq (normSq_of_mem_sphere x)⟩⟩

open Lightlike Lightlike.Spin4 in
lemma continuous_sphereToSU2 : Continuous sphereToSU2 := by
  refine Continuous.subtype_mk ?_ _
  exact (LinearMap.continuous_of_finiteDimensional (toMat : ℍ[ℝ] →ₐ[ℝ] _).toLinearMap).comp
    continuous_subtype_val

open Lightlike Lightlike.Spin4 in
lemma sphereToSU2_mul (p x : sphere (0 : ℍ[ℝ]) 1) :
    sphereToSU2 ⟨p * x, by simp [norm_mul, show ‖(p : ℍ[ℝ])‖ = 1 by simpa using p.2,
      show ‖(x : ℍ[ℝ])‖ = 1 by simpa using x.2]⟩ = sphereToSU2 p * sphereToSU2 x :=
  Subtype.ext (map_mul toMat (p : ℍ[ℝ]) x)

open Lightlike Lightlike.Spin4 in
lemma sphereToSU2_bijective : Function.Bijective sphereToSU2 := by
  constructor
  · intro x y h
    exact Subtype.ext (toMat_injective (congrArg Subtype.val h))
  · intro g
    obtain ⟨q, hq⟩ := exists_toMat_eq g
    have hn : ‖(q : ℍ[ℝ])‖ = 1 := by
      have := normSq_unitary q
      rw [Quaternion.normSq_eq_norm_mul_self] at this
      nlinarith [norm_nonneg (q : ℍ[ℝ])]
    exact ⟨⟨q, by simpa using hn⟩, Subtype.ext hq⟩

/-! ## The cone measure on SU(2) is the Haar measure -/

local instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
local instance : SecondCountableTopology SU2 := TopologicalSpace.Subtype.secondCountableTopology _

open Lightlike Lightlike.Spin4 in
/-- The surface measure of the 3-sphere, transported to `SU(2)`. -/
noncomputable def coneSU2 : Measure SU2 :=
  Measure.map sphereToSU2 (volume : Measure ℍ[ℝ]).toSphere

open Lightlike Lightlike.Spin4 in
/-- `sphereToSU2` as a homeomorphism (compact to Hausdorff). -/
noncomputable def sphereHomeo : sphere (0 : ℍ[ℝ]) 1 ≃ₜ SU2 :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ sphereToSU2_bijective) continuous_sphereToSU2

open Lightlike Lightlike.Spin4 in
instance : IsFiniteMeasure coneSU2 := by unfold coneSU2; infer_instance

open Lightlike Lightlike.Spin4 in
instance : coneSU2.IsOpenPosMeasure := by
  refine ⟨fun U hU hne => ?_⟩
  unfold coneSU2
  have hm : Measurable sphereToSU2 := continuous_sphereToSU2.measurable
  rw [Measure.map_apply hm hU.measurableSet]
  exact ne_of_gt <| (hU.preimage continuous_sphereToSU2).measure_pos (volume : Measure ℍ[ℝ]).toSphere (by
    obtain ⟨g, hg⟩ := hne
    obtain ⟨x, hx⟩ := sphereToSU2_bijective.2 g
    exact ⟨x, by simpa [hx] using hg⟩)

open Lightlike Lightlike.Spin4 in
instance : coneSU2.IsMulLeftInvariant := by
  refine ⟨fun g => ?_⟩
  obtain ⟨p, rfl⟩ := sphereToSU2_bijective.2 g
  have hm : Measurable sphereToSU2 := continuous_sphereToSU2.measurable
  have hmul : Measurable (fun h : SU2 => sphereToSU2 p * h) :=
    (continuous_const.mul continuous_id).measurable
  unfold coneSU2
  rw [Measure.map_map hmul hm]
  have hc : ((fun h : SU2 => sphereToSU2 p * h) ∘ sphereToSU2)
      = sphereToSU2 ∘ sphereMulLeft p (by simpa using p.2) := by
    funext x
    exact (sphereToSU2_mul p x).symm
  rw [hc, ← Measure.map_map hm (continuous_sphereMulLeft p (by simpa using p.2)).measurable,
    map_sphereMulLeft_toSphere]

open Lightlike Lightlike.Spin4 in
instance : haarSU2.IsHaarMeasure := by unfold haarSU2; infer_instance

open Lightlike Lightlike.Spin4 in
/-- **The Haar measure of SU(2) is the normalised surface measure of the 3-sphere.** -/
theorem haarSU2_eq_cone : haarSU2 = (coneSU2 univ)⁻¹ • coneSU2 := by
  have h := Measure.isMulLeftInvariant_eq_smul coneSU2 haarSU2
  have hne : coneSU2 univ ≠ 0 := (isOpen_univ.measure_pos _ univ_nonempty).ne'
  generalize Measure.haarScalarFactor coneSU2 haarSU2 = c at h
  have h2 : coneSU2 univ = (c : ENNReal) := by
    have := congrArg (fun m => m univ) h
    simpa using this
  rw [h2] at hne ⊢
  rw [h]
  have hc : (c : ENNReal) ≠ 0 := hne
  ext t ht
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.smul_def]
  rw [← mul_assoc, ENNReal.inv_mul_cancel hc ENNReal.coe_ne_top, one_mul]

/-- **Total mass of the cone measure**: `toSphere univ = 4 * vol(B⁴) = 2π²`. -/
theorem toSphere_univ_quat :
    (volume : Measure ℍ[ℝ]).toSphere univ = ENNReal.ofReal (2 * Real.pi ^ 2) := by
  have h4 : Module.finrank ℝ ℍ[ℝ] = 4 := Quaternion.finrank_eq_four
  have hk : Module.finrank ℝ ℍ[ℝ] = 2 * 2 := by rw [h4]
  rw [Measure.toSphere_apply_univ, InnerProductSpace.volume_ball_of_dim_even hk, h4]
  simp only [ENNReal.ofReal_one, one_pow, one_mul, Nat.factorial]
  rw [show ((4 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 4 by simp, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  norm_num
  ring

open Lightlike Lightlike.Spin4 in
theorem coneSU2_univ : coneSU2 univ = ENNReal.ofReal (2 * Real.pi ^ 2) := by
  unfold coneSU2
  rw [Measure.map_apply continuous_sphereToSU2.measurable MeasurableSet.univ, preimage_univ,
    toSphere_univ_quat]

open Lightlike Lightlike.Spin4 in
/-- **The Haar probability measure of SU(2) is the surface measure divided by `2π²`.** -/
theorem haarSU2_eq_cone_div :
    haarSU2 = (ENNReal.ofReal (2 * Real.pi ^ 2))⁻¹ • coneSU2 := by
  rw [← coneSU2_univ]; exact haarSU2_eq_cone

end Lightlike.Asymptotics.EPRL
