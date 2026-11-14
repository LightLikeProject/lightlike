module

public import Lightlike.Lorentz.SL2C

/-!
# The Möbius action of SL(2,ℂ) on ℂ and its change of variables

For `g = [[a, b], [c, d]] ∈ SL(2,ℂ)` the principal series acts on functions on `ℂ` through the
Möbius map of the transpose `gᵀ`,

  `mob g z = (a z + c) / (b z + d)`,   with denominator `den g z = b z + d`.

This is the affine chart `ζ = (z, 1)` of the linear action `ζ ↦ gᵀ ζ` on `ℂ²`:
`gᵀ (z, 1) = den g z • (mob g z, 1)` (`transpose_mulVec_chart`). It is a right action:
`mob (g h) = mob h ∘ mob g` (`mob_mul`), and `den` is a cocycle,
`den (g h) z = den g z * den h (mob g z)` (`den_mul`).

## Main results

* `hasDerivAt_mob`: the complex derivative of `mob g` is `1 / (den g z)²` (because `det g = 1`).
* `lintegral_mob`: **change of variables**,
  `∫⁻ w, f w = ∫⁻ z, (‖den g z‖ ^ 4)⁻¹ * f (mob g z)` for every `f : ℂ → ℝ≥0∞`. The real Jacobian
  of a holomorphic map is `|f'|²`, here `‖den g z‖⁻⁴`.
* `quasiMeasurePreserving_mob`: preimages of Lebesgue-null sets are null, so `mob g` acts on
  almost-everywhere classes.

The exceptional set `{z | den g z = 0}` has at most one point (`den_eq_zero_subsingleton`) and is
Lebesgue-null; Lean's junk value `x / 0 = 0` is used there and nowhere else.

References: the Möbius action of SL(2,ℂ) on the Riemann sphere and its Jacobian `|bz+d|⁻⁴` are
in A. W. Knapp, *Representation Theory of Semisimple Groups* (Princeton, 1986), Chapter II, and
W. Rühl, *The Lorentz Group and Harmonic Analysis* (Benjamin, 1970).
-/

@[expose] public section

open MeasureTheory Matrix Complex
open scoped ENNReal

namespace Lightlike.Lorentz

/-- The denominator `den g z = b z + d` of the Möbius map of `gᵀ`, for `g = [[a, b], [c, d]]`. -/
def den (g : SL2C) (z : ℂ) : ℂ := g 0 1 * z + g 1 1

/-- The numerator `num g z = a z + c`. -/
def num (g : SL2C) (z : ℂ) : ℂ := g 0 0 * z + g 1 0

/-- **The Möbius map of `gᵀ`**: `z ↦ (a z + c) / (b z + d)` for `g = [[a, b], [c, d]]`. -/
noncomputable def mob (g : SL2C) (z : ℂ) : ℂ := num g z / den g z

lemma mob_def (g : SL2C) (z : ℂ) : mob g z = num g z / den g z := rfl

@[simp] lemma den_one (z : ℂ) : den 1 z = 1 := by simp [den]
@[simp] lemma num_one (z : ℂ) : num 1 z = z := by simp [num]
@[simp] lemma mob_one (z : ℂ) : mob 1 z = z := by simp [mob]

/-- The affine chart: `gᵀ (z, 1) = den g z • (mob g z, 1)` whenever `den g z ≠ 0`. -/
lemma transpose_mulVec_chart (g : SL2C) {z : ℂ} (hz : den g z ≠ 0) :
    (g : Matrix (Fin 2) (Fin 2) ℂ)ᵀ *ᵥ ![z, 1] = den g z • ![mob g z, 1] := by
  have hz' : g 0 1 * z + g 1 1 ≠ 0 := hz
  have hz'' : z * g 0 1 + g 1 1 ≠ 0 := by rwa [mul_comm]
  ext i; fin_cases i
  · simp [mulVec, dotProduct, Fin.sum_univ_two, mob, num, den]; field_simp
  · simp [mulVec, dotProduct, Fin.sum_univ_two, den]

/-- The numerator is a cocycle in the same way as the denominator. -/
lemma num_mul (g h : SL2C) {z : ℂ} (hz : den g z ≠ 0) :
    num (g * h) z = den g z * num h (mob g z) := by
  have hz' : g 0 1 * z + g 1 1 ≠ 0 := hz
  simp only [num, den, mob, Matrix.SpecialLinearGroup.coe_mul, mul_apply, Fin.sum_univ_two]
  field_simp; ring

/-- **Cocycle identity** `den (g h) z = den g z · den h (mob g z)`. -/
lemma den_mul (g h : SL2C) {z : ℂ} (hz : den g z ≠ 0) :
    den (g * h) z = den g z * den h (mob g z) := by
  have hz' : g 0 1 * z + g 1 1 ≠ 0 := hz
  simp only [num, den, mob, Matrix.SpecialLinearGroup.coe_mul, mul_apply, Fin.sum_univ_two]
  field_simp; ring

/-- **Right action** `mob (g h) = mob h ∘ mob g` (off the pole of `mob g`). -/
lemma mob_mul (g h : SL2C) {z : ℂ} (hz : den g z ≠ 0) :
    mob (g * h) z = mob h (mob g z) := by
  rw [mob, num_mul g h hz, den_mul g h hz, mul_div_mul_left _ _ hz, ← mob_def]

/-- Off the pole, `mob g⁻¹` undoes `mob g`, and the image avoids the pole of `mob g⁻¹`. -/
lemma den_inv_mob_ne_zero (g : SL2C) {z : ℂ} (hz : den g z ≠ 0) : den g⁻¹ (mob g z) ≠ 0 := by
  have h := den_mul g g⁻¹ hz
  rw [mul_inv_cancel, den_one] at h
  exact right_ne_zero_of_mul (h ▸ one_ne_zero)

lemma mob_inv_mob (g : SL2C) {z : ℂ} (hz : den g z ≠ 0) : mob g⁻¹ (mob g z) = z := by
  rw [← mob_mul g g⁻¹ hz, mul_inv_cancel, mob_one]

lemma mob_mob_inv (g : SL2C) {w : ℂ} (hw : den g⁻¹ w ≠ 0) : mob g (mob g⁻¹ w) = w := by
  simpa using mob_inv_mob g⁻¹ hw

lemma den_mob_inv_ne_zero (g : SL2C) {w : ℂ} (hw : den g⁻¹ w ≠ 0) : den g (mob g⁻¹ w) ≠ 0 := by
  simpa using den_inv_mob_ne_zero g⁻¹ hw

/-- The pole set `{z | den g z = 0}` has at most one point. -/
lemma den_eq_zero_subsingleton (g : SL2C) : {z : ℂ | den g z = 0}.Subsingleton := by
  intro z hz w hw
  simp only [Set.mem_ofPred_eq, den] at hz hw
  by_cases hb : g 0 1 = 0
  · have hdet := SL2C.det_eq g
    rw [hb] at hz hdet
    simp only [zero_mul, zero_add] at hz
    rw [hz] at hdet; simp at hdet
  · have : g 0 1 * (z - w) = 0 := by linear_combination hz - hw
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hb)

/-- The pole set is Lebesgue-null. -/
lemma volume_den_eq_zero (g : SL2C) : volume {z : ℂ | den g z = 0} = 0 :=
  (den_eq_zero_subsingleton g).measure_zero _

/-- Almost every point is off the pole. -/
lemma ae_den_ne_zero (g : SL2C) : ∀ᵐ z ∂(volume : Measure ℂ), den g z ≠ 0 := by
  rw [ae_iff]; simpa using volume_den_eq_zero g

lemma continuous_den (g : SL2C) : Continuous (den g) := by unfold den; fun_prop
lemma continuous_num (g : SL2C) : Continuous (num g) := by unfold num; fun_prop

lemma measurable_mob (g : SL2C) : Measurable (mob g) :=
  (continuous_num g).measurable.div (continuous_den g).measurable

lemma isOpen_den_ne_zero (g : SL2C) : IsOpen {z : ℂ | den g z ≠ 0} :=
  isOpen_ne_fun (continuous_den g) continuous_const

/-- `mob g` is continuous off its pole. -/
lemma continuousAt_mob (g : SL2C) {z : ℂ} (hz : den g z ≠ 0) : ContinuousAt (mob g) z :=
  (continuous_num g).continuousAt.div (continuous_den g).continuousAt hz

/-- **The derivative of the Möbius map** is `1 / (den g z)²`, because `det g = 1`. -/
lemma hasDerivAt_mob (g : SL2C) {z : ℂ} (hz : den g z ≠ 0) :
    HasDerivAt (mob g) (1 / den g z ^ 2) z := by
  have hn : HasDerivAt (num g) (g 0 0) z := by
    have := ((hasDerivAt_id' z).const_mul (g 0 0)).add_const (g 1 0)
    rw [mul_one] at this; exact this
  have hd : HasDerivAt (den g) (g 0 1) z := by
    have := ((hasDerivAt_id' z).const_mul (g 0 1)).add_const (g 1 1)
    rw [mul_one] at this; exact this
  have := hn.div hd hz
  convert this using 2
  · rfl
  · have hdet := SL2C.det_eq g
    unfold num den
    linear_combination -hdet

/-- The real Jacobian determinant of multiplication by `c` on `ℂ = ℝ²` is `|c|²`. -/
lemma det_smul_one (c : ℂ) : ((c • (1 : ℂ →L[ℝ] ℂ)) : ℂ →L[ℝ] ℂ).det = Complex.normSq c := by
  have : (c • (1 : ℂ →L[ℝ] ℂ)).toLinearMap = LinearMap.mulLeft ℝ c := by
    ext w; simp
  show LinearMap.det (c • (1 : ℂ →L[ℝ] ℂ)).toLinearMap = _
  rw [this, ← Algebra.norm_complex_apply, Algebra.norm_apply]; rfl

/-- The Jacobian of `mob g`: `|det D(mob g)(z)| = ‖den g z‖⁻⁴`. -/
lemma abs_det_mob (g : SL2C) (z : ℂ) :
    |((1 / den g z ^ 2) • (1 : ℂ →L[ℝ] ℂ)).det| = (‖den g z‖ ^ 4)⁻¹ := by
  rw [det_smul_one, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
  rw [norm_div, norm_one, norm_pow]; ring

/-- The image of the domain `{den g ≠ 0}` under `mob g` is `{den g⁻¹ ≠ 0}`. -/
lemma image_mob (g : SL2C) :
    mob g '' {z | den g z ≠ 0} = {w | den g⁻¹ w ≠ 0} := by
  ext w; constructor
  · rintro ⟨z, hz, rfl⟩; exact den_inv_mob_ne_zero g hz
  · intro hw; exact ⟨mob g⁻¹ w, den_mob_inv_ne_zero g hw, mob_mob_inv g hw⟩

/-- **Change of variables for the Möbius map**:
`∫⁻ w, f w = ∫⁻ z, ‖den g z‖⁻⁴ · f (mob g z)` for every `f : ℂ → ℝ≥0∞`. -/
theorem lintegral_mob (g : SL2C) (f : ℂ → ℝ≥0∞) :
    ∫⁻ w, f w = ∫⁻ z, ENNReal.ofReal ((‖den g z‖ ^ 4)⁻¹) * f (mob g z) := by
  have hs : MeasurableSet {z : ℂ | den g z ≠ 0} := (isOpen_den_ne_zero g).measurableSet
  have hf' : ∀ z ∈ {z : ℂ | den g z ≠ 0},
      HasFDerivWithinAt (mob g) ((1 / den g z ^ 2) • (1 : ℂ →L[ℝ] ℂ)) {z | den g z ≠ 0} z :=
    fun z hz => (hasDerivAt_mob g hz).complexToReal_fderiv.hasFDerivWithinAt
  have hinj : Set.InjOn (mob g) {z : ℂ | den g z ≠ 0} := by
    intro z hz w hw h
    rw [← mob_inv_mob g hz, ← mob_inv_mob g hw, h]
  have key := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hf' hinj f
  rw [image_mob] at key
  simp only [abs_det_mob] at key
  rwa [Measure.restrict_eq_self_of_ae_mem (s := {w | den g⁻¹ w ≠ 0}) (ae_den_ne_zero g⁻¹),
    Measure.restrict_eq_self_of_ae_mem (s := {z | den g z ≠ 0}) (ae_den_ne_zero g)] at key

/-- **`mob g` is quasi-measure-preserving**: the preimage of a Lebesgue-null set is null. -/
theorem quasiMeasurePreserving_mob (g : SL2C) :
    QuasiMeasurePreserving (mob g) volume volume := by
  refine ⟨measurable_mob g, Measure.AbsolutelyContinuous.mk fun A hA hA0 => ?_⟩
  rw [Measure.map_apply (measurable_mob g) hA]
  have key := lintegral_mob g⁻¹ ((mob g ⁻¹' A).indicator 1)
  rw [lintegral_indicator_one (measurable_mob g hA)] at key
  rw [key]
  have hae : ∀ᵐ z ∂(volume : Measure ℂ),
      ENNReal.ofReal ((‖den g⁻¹ z‖ ^ 4)⁻¹) * (mob g ⁻¹' A).indicator 1 (mob g⁻¹ z) =
        A.indicator (fun z => ENNReal.ofReal ((‖den g⁻¹ z‖ ^ 4)⁻¹)) z := by
    filter_upwards [ae_den_ne_zero g⁻¹] with z hz
    classical
    rw [Set.indicator_apply, Set.indicator_apply, Set.mem_preimage, mob_mob_inv g hz]
    split_ifs <;> simp
  rw [lintegral_congr_ae hae, lintegral_indicator hA, setLIntegral_measure_zero _ _ hA0]

/-- Composition with `mob g` respects almost-everywhere equality. -/
lemma ae_eq_comp_mob (g : SL2C) {f f' : ℂ → ℂ} (h : f =ᵐ[volume] f') :
    f ∘ mob g =ᵐ[volume] f' ∘ mob g :=
  (quasiMeasurePreserving_mob g).ae_eq_comp h

end Lightlike.Lorentz
