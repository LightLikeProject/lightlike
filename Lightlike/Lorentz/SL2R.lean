module

public import Mathlib

/-!
# The group SL(2,ℝ), its Iwasawa chart and its Haar measure

`SL(2,ℝ)` is Mathlib's `Matrix.SpecialLinearGroup (Fin 2) ℝ`, acting on the upper half-plane `ℍ`
by Möbius transformations (`UpperHalfPlane.SLAction`). This file sets up the harmonic analysis
used for its representations and its Plancherel formula (milestone HA3).

* **Topology:** `SL(2,ℝ)` is closed in `ℝ⁴`, hence locally compact, second countable and
  Hausdorff.
* **Rotations:** `rot θ = [[cos θ, sin θ], [−sin θ, cos θ]]`, the maximal compact subgroup
  `K = SO(2)`. `rot` is a homomorphism from `(ℝ, +)` with period `2π`; the stabiliser of
  `i ∈ ℍ` is exactly `{rot θ}` (`eq_rot_of_smul_I`).
* **Iwasawa chart:** `iwasawa (z, θ) = g_z · rot θ` with `g_z = UpperHalfPlane.toSL2R z`, the
  upper triangular matrix sending `i` to `z`. Every `g` is `iwasawa (g • i, θ)` for some `θ`
  (`exists_iwasawa`), and left multiplication acts as
  `h · iwasawa (z, θ) = iwasawa (h • z, θ + α)` (`mul_iwasawa`).
* **Haar measure:** `haarR` is the image under the Iwasawa chart of `μ_ℍ ⊗ dθ` on
  `ℍ × (0, 2π]`, where `μ_ℍ = dx dy / y²` is Mathlib's `SL(2,ℝ)`-invariant measure on `ℍ` and
  `dθ` is Lebesgue measure on `(0, 2π]`. It is
  left-invariant (`haarR` is `IsMulLeftInvariant`), finite on compact sets, and nonzero, hence a
  Haar measure; `SL(2,ℝ)` is unimodular, being perfect (`isPerfect`).

In this normalisation `∫_G f = ∫_ℍ ∫_0^{2π} f(g_z rot θ) dθ dμ_ℍ(z)`.

References: A. W. Knapp, *Representation Theory of Semisimple Groups* (Princeton, 1986),
Ch. II §1 and §5; S. Lang, *SL₂(ℝ)* (Springer, 1985), Ch. III.
-/

@[expose] public section

open MeasureTheory Matrix Topology UpperHalfPlane
open scoped ENNReal NNReal

noncomputable section

namespace Lightlike.Lorentz

/-- The group `SL(2,ℝ)` of real `2 × 2` matrices of determinant one. -/
abbrev SL2R := Matrix.SpecialLinearGroup (Fin 2) ℝ

namespace SL2R

/-- `SL(2,ℝ)` is locally compact: it is closed in the space of matrices. -/
instance instLocallyCompactSpace : LocallyCompactSpace SL2R :=
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℝ))
  Matrix.SpecialLinearGroup.isClosedEmbedding_val.locallyCompactSpace

/-- `SL(2,ℝ)` is second countable, as a subspace of `ℝ⁴`. -/
instance instSecondCountableTopology : SecondCountableTopology SL2R :=
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℝ))
  Matrix.SpecialLinearGroup.isClosedEmbedding_val.isInducing.secondCountableTopology

/-- `SL(2,ℝ)` is Hausdorff. -/
instance instT2Space : T2Space SL2R :=
  Matrix.SpecialLinearGroup.isClosedEmbedding_val.isEmbedding.t2Space

/-- The Borel σ-algebra on `SL(2,ℝ)`. -/
instance instMeasurableSpace : MeasurableSpace SL2R := borel SL2R

instance instBorelSpace : BorelSpace SL2R := ⟨rfl⟩

/-- The element `[[a, b], [c, d]]` of `SL(2,ℝ)`, given `ad − bc = 1`. -/
def mk (a b c d : ℝ) (h : a * d - b * c = 1) : SL2R :=
  ⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; exact h⟩

@[simp] lemma coe_mk (a b c d : ℝ) (h : a * d - b * c = 1) :
    (mk a b c d h : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; c, d] := rfl

/-- The determinant identity `g₀₀ g₁₁ − g₀₁ g₁₀ = 1`. -/
lemma det_eq (g : SL2R) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := g.2
  rwa [Matrix.det_fin_two] at h

/-- Two elements of `SL(2,ℝ)` with the same four entries are equal. -/
lemma ext_of_entries {g h : SL2R} (h00 : g 0 0 = h 0 0) (h01 : g 0 1 = h 0 1)
    (h10 : g 1 0 = h 1 0) (h11 : g 1 1 = h 1 1) : g = h := by
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

/-- The upper unipotent `n_t = [[1, t], [0, 1]]`. -/
def upper (t : ℝ) : SL2R := mk 1 t 0 1 (by ring)

/-- The lower unipotent `[[1, 0], [t, 1]]`. -/
def lower (t : ℝ) : SL2R := mk 1 0 t 1 (by ring)

/-- The diagonal element `diag(a, a⁻¹)`, `a ≠ 0`. -/
def diagSL (a : ℝ) (ha : a ≠ 0) : SL2R := mk a 0 0 a⁻¹ (by field_simp; ring)

/-- The rotation `k_θ = [[cos θ, sin θ], [−sin θ, cos θ]]`. -/
def rot (θ : ℝ) : SL2R :=
  mk (Real.cos θ) (Real.sin θ) (-Real.sin θ) (Real.cos θ)
    (by nlinarith [Real.sin_sq_add_cos_sq θ])

@[simp] lemma coe_rot (θ : ℝ) :
    (rot θ : Matrix (Fin 2) (Fin 2) ℝ) =
      !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] := rfl

/-- `rot` is a homomorphism from `(ℝ, +)`. -/
lemma rot_add (θ φ : ℝ) : rot (θ + φ) = rot θ * rot φ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add] <;> ring

@[simp] lemma rot_zero : rot 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- `rot` has period `2π`. -/
lemma rot_periodic : Function.Periodic rot (2 * Real.pi) := fun θ => by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

lemma continuous_rot : Continuous rot := by
  refine Continuous.subtype_mk ?_ _
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

/-! ## Perfectness and unimodularity -/

/-- `n_t` is the commutator of `diag(2, ½)` and `n_{t/3}`. -/
lemma upper_eq_commutator (t : ℝ) :
    upper t = diagSL 2 two_ne_zero * upper (t / 3) * (diagSL 2 two_ne_zero)⁻¹ *
      (upper (t / 3))⁻¹ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upper, diagSL, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The lower unipotent is the commutator of `diag(½, 2)` and `[[1, 0], [t/3, 1]]`. -/
lemma lower_eq_commutator (t : ℝ) :
    lower t = (diagSL 2 two_ne_zero)⁻¹ * lower (t / 3) * diagSL 2 two_ne_zero *
      (lower (t / 3))⁻¹ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lower, diagSL, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- An element with `c ≠ 0` is a product `n_x · n̄_c · n_y` of unipotents. -/
lemma eq_upper_lower_upper (g : SL2R) (hc : g 1 0 ≠ 0) :
    g = upper ((g 0 0 - 1) / g 1 0) * lower (g 1 0) * upper ((g 1 1 - 1) / g 1 0) := by
  have hdet := det_eq g
  refine ext_of_entries ?_ ?_ ?_ ?_ <;>
    simp [upper, lower, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
    nlinarith [hdet]

/-- A homomorphism to a commutative monoid is trivial on commutators. -/
lemma map_commutator {M : Type*} [CommMonoid M] (χ : SL2R →* M) (x y : SL2R) :
    χ (x * y * x⁻¹ * y⁻¹) = 1 := by
  have hx : χ x * χ x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hy : χ y * χ y⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  simp only [map_mul]
  calc χ x * χ y * χ x⁻¹ * χ y⁻¹ = (χ x * χ x⁻¹) * (χ y * χ y⁻¹) := by ac_rfl
    _ = 1 := by rw [hx, hy, one_mul]

/-- **SL(2,ℝ) is perfect**, in the form used here: every homomorphism to a commutative monoid is
trivial. -/
theorem isPerfect {M : Type*} [CommMonoid M] (χ : SL2R →* M) (g : SL2R) : χ g = 1 := by
  have hU : ∀ t, χ (upper t) = 1 := fun t => by
    rw [upper_eq_commutator, map_commutator]
  have hL : ∀ t, χ (lower t) = 1 := fun t => by
    rw [lower_eq_commutator, mul_assoc, mul_assoc, ← mul_assoc (lower (t / 3)), ← mul_assoc,
      ← mul_assoc]
    have := map_commutator χ (diagSL 2 two_ne_zero)⁻¹ (lower (t / 3))
    rwa [inv_inv] at this
  have h3 : ∀ g : SL2R, g 1 0 ≠ 0 → χ g = 1 := fun g hc => by
    rw [eq_upper_lower_upper g hc]; simp [hU, hL]
  by_cases hc : g 1 0 = 0
  · have hdet := det_eq g
    have ha : g 0 0 ≠ 0 := by
      intro h; rw [h, hc] at hdet; simp at hdet
    have h' : (lower 1 * g) 1 0 ≠ 0 := by
      simpa [lower, Matrix.mul_apply, Fin.sum_univ_two, hc] using ha
    have : g = lower (-1) * (lower 1 * g) := by
      rw [← mul_assoc]
      have : lower (-1) * lower 1 = 1 := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [lower, Matrix.mul_apply, Fin.sum_univ_two]
      rw [this, one_mul]
    rw [this, map_mul, hL, h3 _ h', one_mul]
  · exact h3 g hc

/-! ## Haar measure and unimodularity -/

/-- **The Haar measure of SL(2,ℝ)**: Mathlib's left Haar measure (normalised on a fixed compact
set; Haar measures are unique up to a positive factor). -/
def haar : Measure SL2R := Measure.haar

instance : haar.IsHaarMeasure := by unfold haar; infer_instance

/-- The modular character of `SL(2,ℝ)` is trivial. -/
theorem modularCharacter_eq_one (g : SL2R) : Measure.modularCharacter g = 1 :=
  isPerfect _ g

/-- **SL(2,ℝ) is unimodular:** its left Haar measure is also right-invariant. -/
theorem haar_isMulRightInvariant : haar.IsMulRightInvariant := by
  constructor
  intro g
  rw [Measure.map_right_mul_eq_modularCharacterFun_smul haar g]
  have : Measure.modularCharacterFun g = 1 := modularCharacter_eq_one g
  rw [this, one_smul]

instance : haar.IsMulRightInvariant := haar_isMulRightInvariant

/-! ## The stabiliser of `i` and the Iwasawa decomposition -/

/-- The Möbius action of `SL(2,ℝ)` on `ℍ` in coordinates. -/
lemma coe_smul (g : SL2R) (z : ℍ) :
    ((g • z : ℍ) : ℂ) = (g 0 0 * (z : ℂ) + g 0 1) / (g 1 0 * (z : ℂ) + g 1 1) := by
  rw [coe_specialLinearGroup_apply]; rfl

/-- The denominator `c z + d` does not vanish on `ℍ`. -/
lemma denom_ne_zero' (g : SL2R) (z : ℍ) : (g 1 0 * (z : ℂ) + g 1 1) ≠ 0 :=
  UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ g) z

/-- Rotations fix `i`. -/
@[simp] lemma rot_smul_I (θ : ℝ) : rot θ • UpperHalfPlane.I = UpperHalfPlane.I := by
  ext
  have h := denom_ne_zero' (rot θ) UpperHalfPlane.I
  rw [coe_smul, div_eq_iff h]
  simp only [rot, coe_mk, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one, UpperHalfPlane.coe_I]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **The stabiliser of `i` is `SO(2)`**: if `g • i = i` then `g = rot θ` for some `θ`. -/
theorem eq_rot_of_smul_I {g : SL2R} (hg : g • UpperHalfPlane.I = UpperHalfPlane.I) :
    ∃ θ, g = rot θ := by
  have h := congrArg (fun z : ℍ => (z : ℂ)) hg
  simp only [coe_smul, UpperHalfPlane.coe_I] at h
  rw [div_eq_iff (by simpa using denom_ne_zero' g UpperHalfPlane.I)] at h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp at hre him
  -- `b = -c` and `a = d`, so `(a, b)` is a unit vector
  have hab : g 0 0 ^ 2 + g 0 1 ^ 2 = 1 := by
    linear_combination det_eq g + g 0 0 * him + g 0 1 * hre
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = ⟨g 0 0, g 0 1⟩ := ⟨_, rfl⟩
  have hwre : w.re = g 0 0 := by rw [hw]
  have hwim : w.im = g 0 1 := by rw [hw]
  have hnorm : ‖w‖ = 1 := by
    have h2 : ‖w‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hwre, hwim]; linear_combination hab
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg w) two_ne_zero).1 h2
  have hw0 : w ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hnorm; exact zero_ne_one hnorm
  have hc : Real.cos (Complex.arg w) = g 0 0 := by rw [Complex.cos_arg hw0, hnorm, div_one, hwre]
  have hs : Real.sin (Complex.arg w) = g 0 1 := by rw [Complex.sin_arg, hnorm, div_one, hwim]
  refine ⟨Complex.arg w, ext_of_entries ?_ ?_ ?_ ?_⟩
  · simp [rot, hc]
  · simp [rot, hs]
  · simp [rot, hs]; linarith
  · simp [rot, hc]; linarith

/-- **Iwasawa decomposition** `G = N A K`: every `g` is `g_z · rot θ` with `z = g • i`. -/
theorem exists_iwasawa (g : SL2R) : ∃ θ, g = (g • UpperHalfPlane.I).toSL2R * rot θ := by
  obtain ⟨θ, hθ⟩ := eq_rot_of_smul_I (g := (g • UpperHalfPlane.I).toSL2R⁻¹ * g) (by
    rw [mul_smul, inv_smul_eq_iff, toSL2R_smul_I])
  exact ⟨θ, by rw [← hθ, mul_inv_cancel_left]⟩

/-- The Iwasawa chart `(z, θ) ↦ g_z · rot θ`. -/
def iwasawa (p : ℍ × ℝ) : SL2R := p.1.toSL2R * rot p.2

lemma continuous_iwasawa : Continuous iwasawa :=
  (continuous_toSL2R.comp continuous_fst).mul (continuous_rot.comp continuous_snd)

lemma measurable_iwasawa : Measurable iwasawa := continuous_iwasawa.measurable

@[simp] lemma iwasawa_smul_I (p : ℍ × ℝ) : iwasawa p • UpperHalfPlane.I = p.1 := by
  rw [iwasawa, mul_smul, rot_smul_I, toSL2R_smul_I]

/-- Left multiplication in the Iwasawa chart: `h · g_z · rot θ = g_{h z} · rot (α + θ)`, where
the angle `α` depends on `h` and `z` only. -/
theorem mul_iwasawa (h : SL2R) (z : ℍ) :
    ∃ α : ℝ, ∀ θ, h * iwasawa (z, θ) = iwasawa (h • z, α + θ) := by
  obtain ⟨α, hα⟩ := exists_iwasawa (h * z.toSL2R)
  rw [mul_smul, toSL2R_smul_I] at hα
  refine ⟨α, fun θ => ?_⟩
  simp only [iwasawa, rot_add, ← mul_assoc]
  rw [← hα]

/-! ## The Haar measure in the Iwasawa chart -/

/-- **The Haar measure in the Iwasawa chart**: the image of `μ_ℍ ⊗ dθ|_{(0, 2π]}` under
`(z, θ) ↦ g_z · rot θ`, with `μ_ℍ = dx dy / y²`. -/
def haarR : Measure SL2R :=
  ((volume : Measure ℍ).prod (volume.restrict (Set.Ioc 0 (2 * Real.pi)))).map iwasawa

/-- Integrals against `haarR` in the chart. -/
lemma lintegral_haarR {F : SL2R → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ g, F g ∂haarR =
      ∫⁻ z : ℍ, ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), F (z.toSL2R * rot θ) := by
  rw [haarR, lintegral_map hF measurable_iwasawa,
    lintegral_prod (fun p => F (iwasawa p)) (hF.comp measurable_iwasawa).aemeasurable]
  rfl

/-- Rotation invariance of `dθ` on a period: `∫_0^{2π} F(rot (α + θ)) dθ = ∫_0^{2π} F(rot θ) dθ`
for every `F`, measurable or not. -/
lemma lintegral_rot_add (F : SL2R → ℝ≥0∞) (α : ℝ) :
    ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), F (rot (α + θ)) =
      ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), F (rot θ) := by
  have : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  let f : AddCircle (2 * Real.pi) → ℝ≥0∞ := fun x => F (rot_periodic.lift x)
  have h1 := AddCircle.lintegral_preimage (2 * Real.pi) 0 f
  have h2 := AddCircle.lintegral_preimage (2 * Real.pi) 0
    (fun x => f ((α : AddCircle (2 * Real.pi)) + x))
  rw [zero_add] at h1 h2
  have e1 : ∀ θ : ℝ, f θ = F (rot θ) := fun θ => rfl
  have e2 : ∀ θ : ℝ, f ((α : AddCircle (2 * Real.pi)) + θ) = F (rot (α + θ)) := fun θ => by
    rw [← AddCircle.coe_add]; rfl
  simp only [e1] at h1
  simp only [e2] at h2
  rw [h1, h2]
  exact lintegral_add_left_eq_self f (α : AddCircle (2 * Real.pi))

/-- `SL(2,ℝ)` preserves `μ_ℍ`, from Mathlib's `GL(2,ℝ)`-invariance. -/
instance : SMulInvariantMeasure SL2R ℍ volume :=
  ⟨fun g _ hs => SMulInvariantMeasure.measure_preimage_smul
    (Matrix.SpecialLinearGroup.mapGL ℝ g) hs⟩

/-- **`haarR` is left-invariant.** -/
instance : haarR.IsMulLeftInvariant := by
  refine ⟨fun h => Measure.ext fun A hA => ?_⟩
  have hA' : MeasurableSet ((h * ·) ⁻¹' A) := measurable_const_mul h hA
  rw [Measure.map_apply (measurable_const_mul h) hA, ← lintegral_indicator_one hA',
    ← lintegral_indicator_one hA, lintegral_haarR (measurable_one.indicator hA'),
    lintegral_haarR (measurable_one.indicator hA)]
  set G : ℍ → ℝ≥0∞ := fun w =>
    ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), A.indicator 1 (w.toSL2R * rot θ)
  have key : ∀ z : ℍ, ∫⁻ θ in Set.Ioc 0 (2 * Real.pi),
      ((h * ·) ⁻¹' A).indicator 1 (z.toSL2R * rot θ) = G (h • z) := fun z => by
    obtain ⟨α, hα⟩ := mul_iwasawa h z
    have : ∀ θ, ((h * ·) ⁻¹' A).indicator (1 : SL2R → ℝ≥0∞) (z.toSL2R * rot θ) =
        (fun g => A.indicator 1 ((h • z).toSL2R * g)) (rot (α + θ)) := fun θ => by
      have e := hα θ
      simp only [iwasawa] at e
      show _ = A.indicator 1 ((h • z).toSL2R * rot (α + θ))
      rw [← e]; rfl
    simp only [this]
    exact lintegral_rot_add (fun g => A.indicator 1 ((h • z).toSL2R * g)) α
  simp only [key]
  exact ((measurePreserving_smul h (volume : Measure ℍ)).lintegral_map_equiv G
    (MeasurableEquiv.smul h)).symm

/-- `μ_ℍ` is not the zero measure: its density `y⁻²` is positive and `ℍ` is open in `ℂ`. -/
lemma volume_upperHalfPlane_ne_zero : (volume : Measure ℍ) ≠ 0 := by
  intro h0
  have hc : Continuous fun z : ℍ => ((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2 : ℝ≥0) := by
    refine .pow (.div₀ continuous_const ?_ ?_) _
    · exact UpperHalfPlane.continuous_im.subtype_mk _
    · exact fun x ↦ NNReal.ne_iff.mp x.im_ne_zero
  have hU : (volume : Measure ℍ) Set.univ = 0 := by rw [h0]; rfl
  rw [UpperHalfPlane.volume_def,
    withDensity_apply_eq_zero' hc.measurable.coe_nnreal_ennreal.aemeasurable] at hU
  have hset : {x : ℍ | (((1 / NNReal.mk x.im x.im_pos.le : ℝ≥0) ^ 2 : ℝ≥0) : ℝ≥0∞) ≠ 0} ∩
      Set.univ = Set.univ := by
    refine Set.eq_univ_of_forall fun z => ⟨?_, trivial⟩
    simp only [Set.mem_ofPred_eq, ne_eq, ENNReal.coe_eq_zero, pow_eq_zero_iff two_ne_zero,
      one_div, inv_eq_zero]
    exact NNReal.ne_iff.mp z.im_ne_zero
  rw [hset, UpperHalfPlane.measurableEmbedding_coe.comap_apply] at hU
  have hopen : IsOpen (UpperHalfPlane.coe '' Set.univ) :=
    UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ isOpen_univ
  exact (hopen.measure_pos volume
    ⟨_, Set.mem_image_of_mem _ (Set.mem_univ UpperHalfPlane.I)⟩).ne' hU

/-- The image of `haarR` on `ℍ = G/K` is `2π μ_ℍ`: `haarR {g | g • i ∈ S} = 2π μ_ℍ(S)`. -/
theorem haarR_preimage_smul_I {S : Set ℍ} (hS : MeasurableSet S) :
    haarR ((fun g : SL2R => g • UpperHalfPlane.I) ⁻¹' S) =
      volume S * ENNReal.ofReal (2 * Real.pi) := by
  have hm : Measurable fun g : SL2R => g • UpperHalfPlane.I :=
    (continuous_id.smul continuous_const).measurable
  rw [haarR, Measure.map_apply measurable_iwasawa (hm hS), ← Set.preimage_comp]
  have : (fun g : SL2R => g • UpperHalfPlane.I) ∘ iwasawa = Prod.fst :=
    funext iwasawa_smul_I
  rw [this, ← Set.prod_univ, Measure.prod_prod]
  simp [Real.volume_Ioc]

/-- `haarR` is finite on compact sets: a compact `K` lies in `{g | g • i ∈ K • i}`. -/
instance : IsFiniteMeasureOnCompacts haarR := by
  refine ⟨fun K hK => ?_⟩
  have hc : Continuous fun g : SL2R => g • UpperHalfPlane.I := continuous_id.smul continuous_const
  have hS : IsCompact ((fun g : SL2R => g • UpperHalfPlane.I) '' K) := hK.image hc
  calc haarR K ≤ haarR ((fun g : SL2R => g • UpperHalfPlane.I) ⁻¹'
          ((fun g : SL2R => g • UpperHalfPlane.I) '' K)) :=
        measure_mono (Set.subset_preimage_image _ _)
    _ = volume ((fun g : SL2R => g • UpperHalfPlane.I) '' K) * ENNReal.ofReal (2 * Real.pi) :=
        haarR_preimage_smul_I hS.measurableSet
    _ < ⊤ := ENNReal.mul_lt_top hS.measure_lt_top ENNReal.ofReal_lt_top

/-- The chart measure is not zero. -/
theorem haarR_ne_zero : haarR ≠ 0 := by
  intro h
  have h2 := haarR_preimage_smul_I (S := Set.univ) MeasurableSet.univ
  rw [h, Measure.coe_zero, Pi.zero_apply, eq_comm, mul_eq_zero] at h2
  rcases h2 with h2 | h2
  · exact volume_upperHalfPlane_ne_zero (Measure.measure_univ_eq_zero.1 h2)
  · exact (ENNReal.ofReal_pos.2 Real.two_pi_pos).ne' h2

/-- **Uniqueness**: the chart measure is a multiple of Mathlib's Haar measure. -/
theorem haarR_eq_smul : haarR = Measure.haarScalarFactor haarR haar • haar :=
  Measure.isMulLeftInvariant_eq_smul _ _

/-- The scalar factor between `haarR` and `haar` is nonzero. -/
theorem haarScalarFactor_haarR_ne_zero : Measure.haarScalarFactor haarR haar ≠ 0 := by
  intro h; apply haarR_ne_zero; rw [haarR_eq_smul, h, zero_smul]

/-- **`haarR` is a Haar measure** of `SL(2,ℝ)`. -/
instance isHaarMeasure_haarR : haarR.IsHaarMeasure := by
  rw [haarR_eq_smul]; exact Measure.IsHaarMeasure.nnreal_smul _ haarScalarFactor_haarR_ne_zero

/-- `haarR` is also right-invariant (`SL(2,ℝ)` is unimodular). -/
instance : haarR.IsMulRightInvariant := by
  rw [haarR_eq_smul]; infer_instance

/-- **Integration in the Iwasawa chart**:
`∫_G f = ∫_ℍ ∫_0^{2π} f(g_z rot θ) dθ dμ_ℍ(z)` for integrable `f`. -/
theorem integral_haarR {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : SL2R → E}
    (hf : Integrable f haarR) :
    ∫ g, f g ∂haarR = ∫ z : ℍ, ∫ θ in Set.Ioc 0 (2 * Real.pi), f (z.toSL2R * rot θ) := by
  unfold haarR at hf ⊢
  have hf' := (integrable_map_measure hf.aestronglyMeasurable
    measurable_iwasawa.aemeasurable).1 hf
  rw [integral_map measurable_iwasawa.aemeasurable hf.aestronglyMeasurable,
    integral_prod (fun p => f (iwasawa p)) hf']
  rfl

end SL2R

end Lightlike.Lorentz
