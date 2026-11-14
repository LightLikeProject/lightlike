module

public import Lightlike.Lorentz.SL2R
public import Lightlike.Lorentz.WeightedComp

/-!
# The principal series of SL(2,ℝ) on L²(ℝ)

For `ε ∈ ℤ` (only its parity matters) and `ν ∈ ℝ` the principal series `P^{ε,iν}` of `SL(2,ℝ)`
acts on `L²(ℝ)` by

  `(π(g) f)(x) = m(b x + d) · f((a x + c) / (b x + d))`,   `g = [[a, b], [c, d]]`,

with the multiplier `m(t) = |t|^{iν - 1} sgn(t)^ε`. As for `SL(2,ℂ)` (`PrincipalSeries.lean`),
this is the affine chart `x ↦ (x, 1)` of the action `F ↦ F ∘ gᵀ` on functions on `ℝ² ∖ 0` that
are homogeneous of degree `iν - 1` and parity `ε`. The usual form
`(π'(g) f)(x) = |-c x + a|^{-1-iν} sgn(-c x + a)^ε f((d x - b)/(-c x + a))` (Knapp, Ch. II §5)
uses `g⁻¹` in place of `gᵀ`; since `(gᵀ)⁻¹ = w g w⁻¹` with `w = [[0, 1], [-1, 0]]`, the two are
equivalent through an inner automorphism (and `ν ↦ -ν`), so characters and the Plancherel measure
agree.

## Main results

* `mob g x = (a x + c) / (b x + d)` with denominator `den g x = b x + d`: a right action
  (`mob_mul`) with cocycle `den_mul`; derivative `1 / den²` (`hasDerivAt_mob`); change of
  variables `lintegral_mob`; quasi-measure-preserving (`quasiMeasurePreserving_mob`).
* `mult_mul`: `m` is a character of `ℝ^×`; `norm_mult`: `|m(t)| = |t|⁻¹` for real `ν`, and
  `norm_mult_complex`: `|m(t)| = |t|^{-1 - Im ν}` in general.
* `principalSeries ε ν : ContRepresentation ℂ SL2R (L²(ℝ))`, multiplicative
  (`principalSeries_mul`, `principalSeries_one`), unitary (`principalSeries_norm`,
  `principalSeries_inner`, `principalSeries_mem_unitary`) and strongly continuous
  (`continuous_principalSeries`, `continuous_principalSeries_action`).

The pole `{x | den g x = 0}` has at most one point; Lean's junk value `x / 0 = 0` is used there
and nowhere else.

References: A. W. Knapp, *Representation Theory of Semisimple Groups* (Princeton, 1986),
Ch. II §5 and Ch. VII; S. Lang, *SL₂(ℝ)* (Springer, 1985), Ch. III; G. B. Folland, *A Course in
Abstract Harmonic Analysis* (CRC Press, 1995), Ch. 3 (strong continuity).
-/

@[expose] public section

open MeasureTheory Matrix Complex Filter Topology Metric
open scoped ENNReal ComplexConjugate InnerProductSpace

noncomputable section

namespace Lightlike.Lorentz.SL2R

/-! ## The real Möbius map of `gᵀ` -/

/-- The denominator `den g x = b x + d` of the Möbius map of `gᵀ`, for `g = [[a, b], [c, d]]`. -/
def den (g : SL2R) (x : ℝ) : ℝ := g 0 1 * x + g 1 1

/-- The numerator `num g x = a x + c`. -/
def num (g : SL2R) (x : ℝ) : ℝ := g 0 0 * x + g 1 0

/-- **The Möbius map of `gᵀ`** on `ℝ`: `x ↦ (a x + c) / (b x + d)`. -/
def mob (g : SL2R) (x : ℝ) : ℝ := num g x / den g x

lemma mob_def (g : SL2R) (x : ℝ) : mob g x = num g x / den g x := rfl

@[simp] lemma den_one (x : ℝ) : den 1 x = 1 := by simp [den]
@[simp] lemma num_one (x : ℝ) : num 1 x = x := by simp [num]
@[simp] lemma mob_one (x : ℝ) : mob 1 x = x := by simp [mob]

/-- The numerator is a cocycle in the same way as the denominator. -/
lemma num_mul (g h : SL2R) {x : ℝ} (hx : den g x ≠ 0) :
    num (g * h) x = den g x * num h (mob g x) := by
  have hx' : g 0 1 * x + g 1 1 ≠ 0 := hx
  simp only [num, den, mob, Matrix.SpecialLinearGroup.coe_mul, mul_apply, Fin.sum_univ_two]
  field_simp; ring

/-- **Cocycle identity** `den (g h) x = den g x · den h (mob g x)`. -/
lemma den_mul (g h : SL2R) {x : ℝ} (hx : den g x ≠ 0) :
    den (g * h) x = den g x * den h (mob g x) := by
  have hx' : g 0 1 * x + g 1 1 ≠ 0 := hx
  simp only [num, den, mob, Matrix.SpecialLinearGroup.coe_mul, mul_apply, Fin.sum_univ_two]
  field_simp; ring

/-- **Right action** `mob (g h) = mob h ∘ mob g` (off the pole of `mob g`). -/
lemma mob_mul (g h : SL2R) {x : ℝ} (hx : den g x ≠ 0) :
    mob (g * h) x = mob h (mob g x) := by
  rw [mob, num_mul g h hx, den_mul g h hx, mul_div_mul_left _ _ hx, ← mob_def]

lemma den_inv_mob_ne_zero (g : SL2R) {x : ℝ} (hx : den g x ≠ 0) : den g⁻¹ (mob g x) ≠ 0 := by
  have h := den_mul g g⁻¹ hx
  rw [mul_inv_cancel, den_one] at h
  exact right_ne_zero_of_mul (h ▸ one_ne_zero)

lemma mob_inv_mob (g : SL2R) {x : ℝ} (hx : den g x ≠ 0) : mob g⁻¹ (mob g x) = x := by
  rw [← mob_mul g g⁻¹ hx, mul_inv_cancel, mob_one]

lemma mob_mob_inv (g : SL2R) {y : ℝ} (hy : den g⁻¹ y ≠ 0) : mob g (mob g⁻¹ y) = y := by
  simpa using mob_inv_mob g⁻¹ hy

lemma den_mob_inv_ne_zero (g : SL2R) {y : ℝ} (hy : den g⁻¹ y ≠ 0) : den g (mob g⁻¹ y) ≠ 0 := by
  simpa using den_inv_mob_ne_zero g⁻¹ hy

/-- The pole set `{x | den g x = 0}` has at most one point. -/
lemma den_eq_zero_subsingleton (g : SL2R) : {x : ℝ | den g x = 0}.Subsingleton := by
  intro x hx y hy
  simp only [Set.mem_ofPred_eq, den] at hx hy
  by_cases hb : g 0 1 = 0
  · have hdet := det_eq g
    rw [hb] at hx hdet
    simp only [zero_mul, zero_add] at hx
    rw [hx] at hdet; simp at hdet
  · have : g 0 1 * (x - y) = 0 := by linear_combination hx - hy
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hb)

/-- The pole set is Lebesgue-null. -/
lemma volume_den_eq_zero (g : SL2R) : volume {x : ℝ | den g x = 0} = 0 :=
  (den_eq_zero_subsingleton g).measure_zero _

/-- Almost every point is off the pole. -/
lemma ae_den_ne_zero (g : SL2R) : ∀ᵐ x ∂(volume : Measure ℝ), den g x ≠ 0 := by
  rw [ae_iff]; simpa using volume_den_eq_zero g

lemma continuous_den (g : SL2R) : Continuous (den g) := by unfold den; fun_prop
lemma continuous_num (g : SL2R) : Continuous (num g) := by unfold num; fun_prop

lemma measurable_mob (g : SL2R) : Measurable (mob g) :=
  (continuous_num g).measurable.div (continuous_den g).measurable

lemma isOpen_den_ne_zero (g : SL2R) : IsOpen {x : ℝ | den g x ≠ 0} :=
  isOpen_ne_fun (continuous_den g) continuous_const

/-- **The derivative of the real Möbius map** is `1 / (den g x)²`, because `det g = 1`. -/
lemma hasDerivAt_mob (g : SL2R) {x : ℝ} (hx : den g x ≠ 0) :
    HasDerivAt (mob g) (1 / den g x ^ 2) x := by
  have hn : HasDerivAt (num g) (g 0 0) x := by
    have := ((hasDerivAt_id' x).const_mul (g 0 0)).add_const (g 1 0)
    rw [mul_one] at this; exact this
  have hd : HasDerivAt (den g) (g 0 1) x := by
    have := ((hasDerivAt_id' x).const_mul (g 0 1)).add_const (g 1 1)
    rw [mul_one] at this; exact this
  have := hn.div hd hx
  convert this using 2
  · rfl
  · have hdet := det_eq g
    unfold num den
    linear_combination -hdet

/-- The image of the domain `{den g ≠ 0}` under `mob g` is `{den g⁻¹ ≠ 0}`. -/
lemma image_mob (g : SL2R) :
    mob g '' {x | den g x ≠ 0} = {y | den g⁻¹ y ≠ 0} := by
  ext y; constructor
  · rintro ⟨x, hx, rfl⟩; exact den_inv_mob_ne_zero g hx
  · intro hy; exact ⟨mob g⁻¹ y, den_mob_inv_ne_zero g hy, mob_mob_inv g hy⟩

/-- **Change of variables for the real Möbius map**:
`∫⁻ y, f y = ∫⁻ x, (den g x)⁻² · f (mob g x)` for every `f : ℝ → ℝ≥0∞`. -/
theorem lintegral_mob (g : SL2R) (f : ℝ → ℝ≥0∞) :
    ∫⁻ y, f y = ∫⁻ x, ENNReal.ofReal ((den g x ^ 2)⁻¹) * f (mob g x) := by
  have hs : MeasurableSet {x : ℝ | den g x ≠ 0} := (isOpen_den_ne_zero g).measurableSet
  have hf' : ∀ x ∈ {x : ℝ | den g x ≠ 0},
      HasDerivWithinAt (mob g) (1 / den g x ^ 2) {x | den g x ≠ 0} x :=
    fun x hx => (hasDerivAt_mob g hx).hasDerivWithinAt
  have hinj : Set.InjOn (mob g) {x : ℝ | den g x ≠ 0} := by
    intro x hx y hy h
    rw [← mob_inv_mob g hx, ← mob_inv_mob g hy, h]
  have key := lintegral_image_eq_lintegral_abs_deriv_mul hs hf' hinj f
  rw [image_mob] at key
  have habs : ∀ x, |1 / den g x ^ 2| = (den g x ^ 2)⁻¹ := fun x => by
    rw [one_div, abs_of_nonneg (by positivity)]
  simp only [habs] at key
  rwa [Measure.restrict_eq_self_of_ae_mem (s := {y | den g⁻¹ y ≠ 0}) (ae_den_ne_zero g⁻¹),
    Measure.restrict_eq_self_of_ae_mem (s := {x | den g x ≠ 0}) (ae_den_ne_zero g)] at key

/-- **`mob g` is quasi-measure-preserving**: the preimage of a Lebesgue-null set is null. -/
theorem quasiMeasurePreserving_mob (g : SL2R) :
    QuasiMeasurePreserving (mob g) volume volume := by
  refine ⟨measurable_mob g, Measure.AbsolutelyContinuous.mk fun A hA hA0 => ?_⟩
  rw [Measure.map_apply (measurable_mob g) hA]
  have key := lintegral_mob g⁻¹ ((mob g ⁻¹' A).indicator 1)
  rw [lintegral_indicator_one (measurable_mob g hA)] at key
  rw [key]
  have hae : ∀ᵐ x ∂(volume : Measure ℝ),
      ENNReal.ofReal ((den g⁻¹ x ^ 2)⁻¹) * (mob g ⁻¹' A).indicator 1 (mob g⁻¹ x) =
        A.indicator (fun x => ENNReal.ofReal ((den g⁻¹ x ^ 2)⁻¹)) x := by
    filter_upwards [ae_den_ne_zero g⁻¹] with x hx
    classical
    rw [Set.indicator_apply, Set.indicator_apply, Set.mem_preimage, mob_mob_inv g hx]
    split_ifs <;> simp
  rw [lintegral_congr_ae hae, lintegral_indicator hA, setLIntegral_measure_zero _ _ hA0]

/-- Composition with `mob g` respects almost-everywhere equality. -/
lemma ae_eq_comp_mob (g : SL2R) {f f' : ℝ → ℂ} (h : f =ᵐ[volume] f') :
    f ∘ mob g =ᵐ[volume] f' ∘ mob g :=
  (quasiMeasurePreserving_mob g).ae_eq_comp h

/-! ## The multiplier -/

/-- **The multiplier** `m(t) = |t|^{iν - 1} sgn(t)^ε` of the principal series `P^{ε,iν}`.
Defined for every complex `ν` so that non-unitary parameters can be tested; the unitary
principal series uses real `ν`. -/
def mult (ε : ℤ) (ν : ℂ) (t : ℝ) : ℂ :=
  ((|t| : ℝ) : ℂ) ^ (I * ν - 1) * ((t / |t| : ℝ) : ℂ) ^ ε

/-- The sign `t / |t|` has absolute value one. -/
lemma norm_phase {t : ℝ} (ht : t ≠ 0) : ‖((t / |t| : ℝ) : ℂ)‖ = 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_abs, div_self (abs_ne_zero.mpr ht)]

@[simp] lemma mult_one (ε : ℤ) (ν : ℂ) : mult ε ν 1 = 1 := by
  simp [mult]

/-- **The multiplier is a character** of `ℝ^×`: `m(s t) = m(s) m(t)`. -/
theorem mult_mul (ε : ℤ) (ν : ℂ) (s t : ℝ) : mult ε ν (s * t) = mult ε ν s * mult ε ν t := by
  simp only [mult, abs_mul, Complex.ofReal_mul]
  rw [Complex.mul_cpow_ofReal_nonneg (abs_nonneg s) (abs_nonneg t), mul_div_mul_comm,
    Complex.ofReal_mul, mul_zpow]
  ring

/-- For real `ν`, `|m(t)| = |t|⁻¹`. -/
theorem norm_mult (ε : ℤ) (ν : ℝ) {t : ℝ} (ht : t ≠ 0) : ‖mult ε ν t‖ = |t|⁻¹ := by
  have hpos : 0 < |t| := abs_pos.mpr ht
  rw [mult, norm_mul, norm_zpow, norm_phase ht, _root_.one_zpow, mul_one,
    Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  have : (I * (ν : ℂ) - 1).re = -1 := by simp
  rw [this, Real.rpow_neg_one]

/-- For complex `ν`, `|m(t)| = |t|^{-1 - Im ν}`: unitarity fails when `Im ν ≠ 0`. -/
theorem norm_mult_complex (ε : ℤ) (ν : ℂ) {t : ℝ} (ht : t ≠ 0) :
    ‖mult ε ν t‖ = |t| ^ (-1 - ν.im) := by
  have hpos : 0 < |t| := abs_pos.mpr ht
  rw [mult, norm_mul, norm_zpow, norm_phase ht, _root_.one_zpow, mul_one,
    Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  congr 1; simp; ring

/-- The multiplier is continuous on `ℝ^×`. -/
lemma continuousAt_mult (ε : ℤ) (ν : ℂ) {t : ℝ} (ht : t ≠ 0) : ContinuousAt (mult ε ν) t := by
  have habs : Continuous fun t : ℝ => ((|t| : ℝ) : ℂ) := by fun_prop
  have h1 : ContinuousAt (fun t : ℝ => ((|t| : ℝ) : ℂ) ^ (I * ν - 1)) t :=
    ContinuousAt.cpow (f := fun t : ℝ => ((|t| : ℝ) : ℂ)) habs.continuousAt continuousAt_const
      (Complex.ofReal_mem_slitPlane.mpr (abs_pos.mpr ht))
  have h2 : ContinuousAt (fun t : ℝ => ((t / |t| : ℝ) : ℂ)) t :=
    Complex.continuous_ofReal.continuousAt.comp (f := fun t : ℝ => t / |t|)
      (continuousAt_id.div continuous_abs.continuousAt (abs_ne_zero.mpr ht))
  have h3 : ContinuousAt (fun t : ℝ => ((t / |t| : ℝ) : ℂ) ^ ε) t :=
    h2.zpow₀ ε (Or.inl (Complex.ofReal_ne_zero.mpr (div_ne_zero ht (abs_ne_zero.mpr ht))))
  exact h1.mul h3

lemma measurable_mult (ε : ℤ) (ν : ℂ) : Measurable (mult ε ν) := by
  unfold mult; fun_prop

/-! ## The principal series -/

/-- The Hilbert space `L²(ℝ)` of the principal series of `SL(2,ℝ)`. -/
abbrev L2R := Lp ℂ 2 (volume : Measure ℝ)

/-- **The principal-series action on functions**: `(act g f)(x) = m(den g x) · f(mob g x)`. -/
def act (ε : ℤ) (ν : ℂ) (g : SL2R) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x => mult ε ν (den g x) * f (mob g x)

/-- `|m(den g x)|² = (den g x)⁻²` off the pole. -/
lemma enorm_mult_den_sq (ε : ℤ) (ν : ℝ) (g : SL2R) {x : ℝ} (hx : den g x ≠ 0) :
    ‖mult ε ν (den g x)‖ₑ ^ (2 : ℝ) = ENNReal.ofReal ((den g x ^ 2)⁻¹) := by
  rw [← ofReal_norm, norm_mult ε ν hx, ENNReal.ofReal_rpow_of_nonneg (by positivity)
    zero_le_two]
  congr 1
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, inv_pow, sq_abs]

/-- **The L² identity** behind unitarity: `∫⁻ |act g f|² = ∫⁻ |f|²` for every `f`. -/
theorem lintegral_act (ε : ℤ) (ν : ℝ) (g : SL2R) (f : ℝ → ℂ) :
    ∫⁻ x, ‖mult ε ν (den g x) * f (mob g x)‖ₑ ^ (2 : ℝ) = ∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) := by
  rw [lintegral_mob g (fun y => ‖f y‖ₑ ^ (2 : ℝ))]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_den_ne_zero g] with x hx
  rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ zero_le_two, enorm_mult_den_sq ε ν g hx]

lemma aestronglyMeasurable_mult_den (ε : ℤ) (ν : ℂ) (g : SL2R) :
    AEStronglyMeasurable (fun x => mult ε ν (den g x)) volume :=
  ((measurable_mult ε ν).comp (continuous_den g).measurable).aestronglyMeasurable

/-- The operator `π(g)` as a linear isometry of `L²(ℝ)`. -/
def piIso (ε : ℤ) (ν : ℝ) (g : SL2R) : L2R →ₗᵢ[ℂ] L2R :=
  weightedCompL2 volume (fun x => mult ε ν (den g x)) (mob g)
    (aestronglyMeasurable_mult_den ε ν g) (quasiMeasurePreserving_mob g)
    (fun f _ => lintegral_act ε ν g f)

lemma coeFn_piIso (ε : ℤ) (ν : ℝ) (g : SL2R) (f : L2R) :
    piIso ε ν g f =ᵐ[volume] act ε ν g f :=
  coeFn_weightedCompL2 _ _ _ _ _ _ f

lemma piIso_one (ε : ℤ) (ν : ℝ) (f : L2R) : piIso ε ν 1 f = f := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_piIso ε ν 1 f] with x hx
  rw [hx]; simp [act]

lemma piIso_mul (ε : ℤ) (ν : ℝ) (g h : SL2R) (f : L2R) :
    piIso ε ν (g * h) f = piIso ε ν g (piIso ε ν h f) := by
  rw [Lp.ext_iff]
  have h1 := coeFn_piIso ε ν (g * h) f
  have h2 := coeFn_piIso ε ν g (piIso ε ν h f)
  have h3 := ae_eq_comp_mob g (coeFn_piIso ε ν h f)
  filter_upwards [h1, h2, h3, ae_den_ne_zero g] with x hx1 hx2 hx3 hg
  rw [hx1, hx2]
  simp only [Function.comp_apply] at hx3
  simp only [act]
  rw [hx3]
  simp only [act]
  rw [den_mul g h hg, mult_mul, mob_mul g h hg]; ring

/-- **The unitary principal series** `P^{ε,iν}` of `SL(2,ℝ)` on `L²(ℝ)`. -/
def principalSeries (ε : ℤ) (ν : ℝ) : ContRepresentation ℂ SL2R L2R :=
  .ofMonoidHom
    { toFun := fun g => (piIso ε ν g).toContinuousLinearMap
      map_one' := by ext1 f; exact piIso_one ε ν f
      map_mul' := fun g h => by ext1 f; exact piIso_mul ε ν g h f }

lemma principalSeries_apply (ε : ℤ) (ν : ℝ) (g : SL2R) (f : L2R) :
    principalSeries ε ν g f = piIso ε ν g f := rfl

/-- The principal series acts by the explicit formula, almost everywhere. -/
theorem coeFn_principalSeries (ε : ℤ) (ν : ℝ) (g : SL2R) (f : L2R) :
    principalSeries ε ν g f =ᵐ[volume] fun x => mult ε ν (den g x) * f (mob g x) :=
  coeFn_piIso ε ν g f

/-- `π(g h) = π(g) π(h)`. -/
theorem principalSeries_mul (ε : ℤ) (ν : ℝ) (g h : SL2R) :
    principalSeries ε ν (g * h) = principalSeries ε ν g * principalSeries ε ν h :=
  map_mul _ g h

/-- `π(1) = 1`. -/
theorem principalSeries_one (ε : ℤ) (ν : ℝ) : principalSeries ε ν 1 = 1 :=
  map_one _

/-- **Unitarity (norm form):** `‖π(g) f‖ = ‖f‖`. -/
theorem principalSeries_norm (ε : ℤ) (ν : ℝ) (g : SL2R) (f : L2R) :
    ‖principalSeries ε ν g f‖ = ‖f‖ :=
  (piIso ε ν g).norm_map f

/-- **Unitarity:** `π(g)` preserves the inner product of `L²(ℝ)`. -/
theorem principalSeries_inner (ε : ℤ) (ν : ℝ) (g : SL2R) (f f' : L2R) :
    ⟪principalSeries ε ν g f, principalSeries ε ν g f'⟫_ℂ = ⟪f, f'⟫_ℂ :=
  (piIso ε ν g).inner_map_map f f'

/-- **Each `π(g)` is a unitary operator** (inverse and adjoint `π(g⁻¹)`). -/
theorem principalSeries_mem_unitary (ε : ℤ) (ν : ℝ) (g : SL2R) :
    principalSeries ε ν g ∈ unitary (L2R →L[ℂ] L2R) :=
  mem_unitary_of_inner _ (principalSeries_inner ε ν) g

/-! ## Strong continuity

The proof is that of `Continuity.lean` for `SL(2,ℂ)`: matrix coefficients of continuous compactly
supported functions are continuous at `1` by dominated convergence; unitarity turns this into
`π(g) φ → φ`; density of `C_c` in `L²` and an `ε/3` argument extend it to all of `L²(ℝ)`. The
last two steps are the generic lemmas `continuous_of_dense_coeff` and `continuous_action_of_norm`
of `WeightedComp.lean`, shared with the discrete series. -/

section Continuity

variable (ε : ℤ) (ν : ℝ)

lemma continuous_entry (i j : Fin 2) :
    Continuous fun g : SL2R => (g : Matrix (Fin 2) (Fin 2) ℝ) i j :=
  continuous_subtype_val.matrix_elem i j

lemma continuous_den_left (x : ℝ) : Continuous fun g : SL2R => den g x :=
  ((continuous_entry 0 1).mul continuous_const).add (continuous_entry 1 1)

lemma continuous_num_left (x : ℝ) : Continuous fun g : SL2R => num g x :=
  ((continuous_entry 0 0).mul continuous_const).add (continuous_entry 1 0)

/-- The integrand of the matrix coefficient `⟪π(g) φ, φ⟫`. -/
def coeffIntegrand (φ : ℝ → ℂ) (g : SL2R) (x : ℝ) : ℂ :=
  conj (mult ε ν (den g x) * φ (mob g x)) * φ x

/-- The matrix coefficient of a function in `L²` as an explicit integral. -/
lemma inner_eq_integral (φ : ℝ → ℂ) (hφ : MemLp φ 2 volume) (g : SL2R) :
    ⟪principalSeries ε ν g (hφ.toLp φ), hφ.toLp φ⟫_ℂ = ∫ x, coeffIntegrand ε ν φ g x := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  have h1 := coeFn_principalSeries ε ν g (hφ.toLp φ)
  have h2 := MemLp.coeFn_toLp hφ
  have h3 := ae_eq_comp_mob g h2
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  simp only [Function.comp_apply] at hx3
  rw [hx1, hx2, hx3, coeffIntegrand, RCLike.inner_apply, mul_comm]

/-- **Step 1.** For continuous compactly supported `φ`, `g ↦ ⟪π(g) φ, φ⟫` is continuous at `1`. -/
theorem continuousAt_inner_one (φ : ℝ → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    ContinuousAt (fun g => ∫ x, coeffIntegrand ε ν φ g x) 1 := by
  obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hφc
  obtain ⟨R, hR⟩ := hφc.isCompact.isBounded.subset_closedBall 0
  set δ : ℝ := 1 / (4 * (|R| + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  -- Near the identity, `|b| < δ` and `|d - 1| < 1/4`.
  have hb : ∀ᶠ g : SL2R in 𝓝 1, |g 0 1| < δ :=
    ((continuous_entry 0 1).abs.continuousAt).eventually_lt
      (continuousAt_const (y := δ)) (by simpa using hδpos)
  have hd : ∀ᶠ g : SL2R in 𝓝 1, |g 1 1 - 1| < 1 / 4 :=
    (((continuous_entry 1 1).sub continuous_const).abs.continuousAt).eventually_lt
      (continuousAt_const (y := (1 / 4 : ℝ))) (by norm_num)
  refine continuousAt_of_dominated (bound := fun x => 2 * C * ‖φ x‖) ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun g => ?_
    refine (Continuous.measurable (by fun_prop : Continuous fun w : ℂ => conj w)).comp_aemeasurable
      ?_ |>.aestronglyMeasurable.mul hφ.aestronglyMeasurable
    exact ((measurable_mult ε ν).comp (continuous_den g).measurable).aemeasurable.mul
      (hφ.measurable.comp (measurable_mob g)).aemeasurable
  · filter_upwards [hb, hd] with g hbg hdg
    refine Eventually.of_forall fun x => ?_
    by_cases hx : φ x = 0
    · simp [coeffIntegrand, hx]
    · have hxK : x ∈ Metric.closedBall (0 : ℝ) R := hR (subset_tsupport _ hx)
      have hxR : |x| ≤ |R| := by
        have := mem_closedBall_zero_iff.mp hxK
        rw [Real.norm_eq_abs] at this
        exact this.trans (le_abs_self R)
      have hden : |den g x - 1| ≤ 1 / 2 := by
        have e : den g x - 1 = g 0 1 * x + (g 1 1 - 1) := by simp only [den]; ring
        rw [e]
        calc |g 0 1 * x + (g 1 1 - 1)| ≤ |g 0 1| * |x| + |g 1 1 - 1| :=
              (abs_add_le _ _).trans (by rw [abs_mul])
          _ ≤ δ * (|R| + 1) + 1 / 4 :=
              add_le_add (mul_le_mul hbg.le (by linarith) (abs_nonneg _) hδpos.le) hdg.le
          _ = 1 / 2 := by rw [hδ]; field_simp; norm_num
      have hden' : 1 / 2 ≤ den g x := by linarith [(abs_le.mp hden).1]
      have hpos : 0 < den g x := by linarith
      have hm : ‖mult ε ν (den g x)‖ ≤ 2 := by
        rw [norm_mult ε ν hpos.ne', abs_of_pos hpos]
        calc (den g x)⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := by gcongr
          _ = 2 := by norm_num
      have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC x)
      rw [coeffIntegrand, norm_mul, RCLike.norm_conj, norm_mul]
      exact mul_le_mul_of_nonneg_right (mul_le_mul hm (hC _) (norm_nonneg _) (by norm_num))
        (norm_nonneg _)
  · exact ((hφ.integrable_of_hasCompactSupport hφc).norm.const_mul (2 * C))
  · refine Eventually.of_forall fun x => ?_
    have h1 : den (1 : SL2R) x ≠ 0 := by simp
    have hd : ContinuousAt (fun g : SL2R => den g x) 1 := (continuous_den_left x).continuousAt
    have hm : ContinuousAt (fun g : SL2R => mult ε ν (den g x)) 1 :=
      ContinuousAt.comp (f := fun g : SL2R => den g x) (continuousAt_mult ε ν h1) hd
    have hmob : ContinuousAt (fun g : SL2R => mob g x) 1 :=
      ((continuous_num_left x).continuousAt).div hd h1
    have hφm : ContinuousAt (fun g : SL2R => φ (mob g x)) 1 :=
      hφ.continuousAt.comp hmob
    exact ((Complex.continuous_conj.continuousAt).comp (hm.mul hφm)).mul continuousAt_const

/-- **Step 2.** The matrix coefficient of the class of a continuous compactly supported `φ` is
continuous at `1`. -/
theorem continuousAt_coeff_of_compactSupport {F : L2R} {φ : ℝ → ℂ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hF : F =ᵐ[volume] φ) :
    ContinuousAt (fun g => ⟪principalSeries ε ν g F, F⟫_ℂ) 1 := by
  have hφ2 : MemLp φ 2 volume := (Lp.memLp F).ae_eq hF
  have hFe : F = hφ2.toLp φ := Lp.ext (hF.trans (MemLp.coeFn_toLp hφ2).symm)
  rw [hFe]
  simpa only [← inner_eq_integral ε ν φ hφ2] using continuousAt_inner_one ε ν φ hφ hφc

/-- **Strong continuity of the principal series**: `g ↦ π(g) f` is continuous for every
`f ∈ L²(ℝ)`, by density of `C_c` classes (`continuous_of_dense_coeff`). -/
theorem continuous_principalSeries (f : L2R) :
    Continuous fun g => principalSeries ε ν g f :=
  continuous_of_dense_coeff (principalSeries ε ν) (principalSeries_norm ε ν)
    (dense_hasCompactSupport_L2 volume)
    (fun _ ⟨_, hφ, hφc, hF⟩ => continuousAt_coeff_of_compactSupport ε ν hφ hφc hF) f

/-- **Step 3.** For every `f ∈ L²(ℝ)`, `π(g) f → f` as `g → 1`. -/
theorem tendsto_one (f : L2R) : Tendsto (fun g => principalSeries ε ν g f) (𝓝 1) (𝓝 f) := by
  have := (continuous_principalSeries ε ν f).tendsto 1
  rwa [principalSeries_one, one_apply_eq_self] at this

/-- **Joint continuity of the action** `(g, f) ↦ π(g) f` on `SL(2,ℝ) × L²(ℝ)`. -/
theorem continuous_principalSeries_action :
    Continuous fun p : SL2R × L2R => principalSeries ε ν p.1 p.2 :=
  continuous_action_of_norm (principalSeries ε ν) (principalSeries_norm ε ν)
    (continuous_principalSeries ε ν)

end Continuity

end Lightlike.Lorentz.SL2R
