module

public import Mathlib
public import Lightlike.SU2.SpinRep

/-!
# The group SL(2,ℂ) and its Haar measure

`SL(2,ℂ)` is Mathlib's `Matrix.SpecialLinearGroup (Fin 2) ℂ`, with the subspace topology from
`Matrix (Fin 2) (Fin 2) ℂ` (Mathlib provides the topological-group structure). This file adds what
harmonic analysis on it needs:

* **Topology:** `SL(2,ℂ)` is a closed subset of `ℂ⁴`, hence locally compact, second countable and
  Hausdorff (`instLocallyCompactSpace`, `instSecondCountableTopology`); it is not compact
  (`instNoncompactSpace`).
* **Haar measure:** `haar` is Mathlib's left Haar measure on the Borel σ-algebra.
* **Unimodularity:** `haar` is also right-invariant (`haar_isMulRightInvariant`). The modular
  character is a homomorphism to the commutative monoid `ℝ≥0`, so it is trivial on commutators, and
  every element of `SL(2,ℂ)` is a product of commutators (`isPerfect`): every unipotent matrix is
  one commutator (`upper_eq_commutator`, `lower_eq_commutator`), and every element is a product of
  at most four unipotents (`eq_upper_lower_upper`).
* **Infinite volume:** `haar univ = ∞` (`haar_univ`), in contrast to the compact group `SU(2)`.
* **SU(2) as a subgroup:** `ofSU2 : SU2 →* SL2C`, injective and continuous.

References: G. B. Folland, *A Course in Abstract Harmonic Analysis* (CRC Press, 1995), §2.4
(modular function, unimodularity); A. W. Knapp, *Representation Theory of Semisimple Groups*
(Princeton, 1986), Chapter II (SL(2,ℂ)).
-/

@[expose] public section

open MeasureTheory Matrix Topology

namespace Lightlike.Lorentz

/-- The group `SL(2,ℂ)` of complex `2 × 2` matrices of determinant one. -/
abbrev SL2C := Matrix.SpecialLinearGroup (Fin 2) ℂ

namespace SL2C

/-- `SL(2,ℂ)` is locally compact: it is a closed subset of the finite-dimensional space of
matrices. -/
instance instLocallyCompactSpace : LocallyCompactSpace SL2C :=
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℂ))
  Matrix.SpecialLinearGroup.isClosedEmbedding_val.locallyCompactSpace

/-- `SL(2,ℂ)` is second countable, as a subspace of `ℂ⁴`. -/
instance instSecondCountableTopology : SecondCountableTopology SL2C :=
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))
  Matrix.SpecialLinearGroup.isClosedEmbedding_val.isInducing.secondCountableTopology

/-- `SL(2,ℂ)` is Hausdorff. -/
instance instT2Space : T2Space SL2C :=
  Matrix.SpecialLinearGroup.isClosedEmbedding_val.isEmbedding.t2Space

/-- The Borel σ-algebra on `SL(2,ℂ)`. -/
noncomputable instance instMeasurableSpace : MeasurableSpace SL2C := borel SL2C

instance instBorelSpace : BorelSpace SL2C := ⟨rfl⟩

/-- An element of `SL(2,ℂ)` from its four entries and a proof that the determinant is one. -/
noncomputable def mk (a b c d : ℂ) (h : a * d - b * c = 1) : SL2C :=
  ⟨!![a, b; c, d], by rw [det_fin_two_of]; exact h⟩

@[simp] lemma coe_mk (a b c d : ℂ) (h : a * d - b * c = 1) :
    ((mk a b c d h : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) = !![a, b; c, d] := rfl

/-- The determinant identity of an element, entrywise. -/
lemma det_eq (g : SL2C) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have := g.2; rwa [det_fin_two] at this

/-- Two elements are equal when their entries are. -/
lemma ext' {g h : SL2C} (h00 : g 0 0 = h 0 0) (h01 : g 0 1 = h 0 1) (h10 : g 1 0 = h 1 0)
    (h11 : g 1 1 = h 1 1) : g = h := by
  ext i j; fin_cases i <;> fin_cases j <;> assumption

/-! ## Perfectness: every element is a product of commutators -/

/-- The upper unipotent `[[1, t], [0, 1]]`. -/
noncomputable def upper (t : ℂ) : SL2C := mk 1 t 0 1 (by ring)
/-- The lower unipotent `[[1, 0], [t, 1]]`. -/
noncomputable def lower (t : ℂ) : SL2C := mk 1 0 t 1 (by ring)
/-- The diagonal element `diag(a, a⁻¹)`. -/
noncomputable def diagSL (a : ℂ) (ha : a ≠ 0) : SL2C := mk a 0 0 a⁻¹ (by field_simp; ring)

lemma sqrt2_ne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.mpr two_pos).ne'

lemma sqrt2_sq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt zero_le_two]; norm_num

/-- `[[1, t], [0, 1]]` is the commutator of `diag(√2, 1/√2)` and `[[1, t], [0, 1]]`. -/
lemma upper_eq_commutator (t : ℂ) :
    upper t = diagSL _ sqrt2_ne * upper t * (diagSL _ sqrt2_ne)⁻¹ * (upper t)⁻¹ := by
  have h2 := sqrt2_sq
  have hne := sqrt2_ne
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, upper, diagSL,
    coe_mk, adjugate_fin_two_of]
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]
  field_simp
  linear_combination (-t) * h2

/-- `[[1, 0], [t, 1]]` is the commutator of `diag(√2, 1/√2)` and `[[1, 0], [-2t, 1]]`. -/
lemma lower_eq_commutator (t : ℂ) :
    lower t = diagSL _ sqrt2_ne * lower (-2 * t) * (diagSL _ sqrt2_ne)⁻¹ * (lower (-2 * t))⁻¹ := by
  have h2 := sqrt2_sq
  have hne := sqrt2_ne
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, lower, diagSL,
    coe_mk, adjugate_fin_two_of]
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]
  field_simp
  linear_combination (-t) * h2

/-- If the lower-left entry is nonzero, `g` is a product of three unipotents:
`g = [[1, (a-1)/c], [0, 1]] · [[1, 0], [c, 1]] · [[1, (d-1)/c], [0, 1]]`. -/
lemma eq_upper_lower_upper (g : SL2C) (hc : g 1 0 ≠ 0) :
    g = upper ((g 0 0 - 1) / g 1 0) * lower (g 1 0) * upper ((g 1 1 - 1) / g 1 0) := by
  have hdet := det_eq g
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, upper, lower, coe_mk]
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two] <;> field_simp <;>
    first | ring1 | linear_combination hdet | linear_combination (-1 : ℂ) * hdet

/-- A homomorphism from `SL(2,ℂ)` to a commutative monoid is trivial on commutators. -/
lemma map_commutator {M : Type*} [CommMonoid M] (χ : SL2C →* M) (x y : SL2C) :
    χ (x * y * x⁻¹ * y⁻¹) = 1 := by
  have hx : χ x * χ x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hy : χ y * χ y⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  simp only [map_mul]
  calc χ x * χ y * χ x⁻¹ * χ y⁻¹ = (χ x * χ x⁻¹) * (χ y * χ y⁻¹) := by
        ac_rfl
    _ = 1 := by rw [hx, hy, one_mul]

/-- **SL(2,ℂ) is perfect**, in the form used here: every homomorphism to a commutative monoid is
trivial. -/
theorem isPerfect {M : Type*} [CommMonoid M] (χ : SL2C →* M) (g : SL2C) : χ g = 1 := by
  have hU : ∀ t, χ (upper t) = 1 := fun t => by rw [upper_eq_commutator, map_commutator]
  have hL : ∀ t, χ (lower t) = 1 := fun t => by rw [lower_eq_commutator, map_commutator]
  have h3 : ∀ g : SL2C, g 1 0 ≠ 0 → χ g = 1 := fun g hc => by
    rw [eq_upper_lower_upper g hc]; simp [hU, hL]
  by_cases hc : g 1 0 = 0
  · -- `lower 1 * g` has lower-left entry `g 0 0 ≠ 0`.
    have hdet := det_eq g
    have ha : g 0 0 ≠ 0 := by
      intro h; rw [h, hc] at hdet; simp at hdet
    have h' : (lower 1 * g) 1 0 ≠ 0 := by
      simp only [Matrix.SpecialLinearGroup.coe_mul, lower, coe_mk]
      simpa [mul_apply, Fin.sum_univ_two, hc] using ha
    have : g = lower (-1) * (lower 1 * g) := by
      rw [← mul_assoc]
      have : lower (-1) * lower 1 = 1 := by
        ext i j
        simp only [Matrix.SpecialLinearGroup.coe_mul, lower, coe_mk]
        fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]
      rw [this, one_mul]
    rw [this, map_mul, hL, h3 _ h', one_mul]
  · exact h3 g hc

/-! ## Haar measure and unimodularity -/

/-- **The Haar measure of SL(2,ℂ)**: Mathlib's left Haar measure (normalised on a fixed compact
set; Haar measures are unique up to a positive factor). -/
noncomputable def haar : Measure SL2C := Measure.haar

instance : haar.IsHaarMeasure := by unfold haar; infer_instance

instance : haar.InnerRegular := by unfold haar; infer_instance

/-- The modular character of `SL(2,ℂ)` is trivial. -/
theorem modularCharacter_eq_one (g : SL2C) : Measure.modularCharacter g = 1 :=
  isPerfect _ g

/-- **SL(2,ℂ) is unimodular:** its left Haar measure is also right-invariant. -/
theorem haar_isMulRightInvariant : haar.IsMulRightInvariant := by
  constructor
  intro g
  rw [Measure.map_right_mul_eq_modularCharacterFun_smul haar g]
  have : Measure.modularCharacterFun g = 1 := modularCharacter_eq_one g
  rw [this, one_smul]

instance : haar.IsMulRightInvariant := haar_isMulRightInvariant

/-- `SL(2,ℂ)` is not compact: the entries of `diag(t, 1/t)` are unbounded. -/
instance instNoncompactSpace : NoncompactSpace SL2C := by
  constructor
  intro h
  have hc : IsCompact (Set.range fun g : SL2C => (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) := by
    rw [← Set.image_univ]
    exact h.image (continuous_subtype_val.matrix_elem 0 0)
  obtain ⟨C, hC⟩ := hc.isBounded.exists_norm_le
  have hpos : (0 : ℝ) < |C| + 1 := by positivity
  have hne : (((|C| + 1 : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have := hC _ ⟨diagSL _ hne, rfl⟩
  simp only [diagSL, coe_mk, of_apply, cons_val', cons_val_zero, empty_val', cons_val_fin_one,
    Complex.norm_real, Real.norm_eq_abs] at this
  rw [abs_of_pos hpos] at this
  linarith [le_abs_self C]

/-- **SL(2,ℂ) has infinite Haar volume** (unlike `SU(2)`). -/
theorem haar_univ : haar Set.univ = ⊤ :=
  measure_univ_of_isMulLeftInvariant haar

/-- Compact sets have finite Haar measure. -/
theorem haar_lt_top_of_isCompact {K : Set SL2C} (hK : IsCompact K) : haar K < ⊤ :=
  hK.measure_lt_top

/-- Nonempty open sets have positive Haar measure. -/
theorem haar_pos_of_isOpen {U : Set SL2C} (hU : IsOpen U) (hne : U.Nonempty) : 0 < haar U :=
  hU.measure_pos haar hne

/-! ## SU(2) inside SL(2,ℂ) -/

/-- The inclusion `SU(2) → SL(2,ℂ)`. -/
def ofSU2 : Lightlike.SU2 →* SL2C where
  toFun u := ⟨u.1, (Matrix.mem_specialUnitaryGroup_iff.mp u.2).2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] lemma coe_ofSU2 (u : Lightlike.SU2) :
    ((ofSU2 u : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) = (u : Matrix (Fin 2) (Fin 2) ℂ) := rfl

lemma ofSU2_injective : Function.Injective ofSU2 := fun u v h => by
  apply Subtype.ext
  have := congrArg (fun g : SL2C => (g : Matrix (Fin 2) (Fin 2) ℂ)) h
  simpa using this

lemma continuous_ofSU2 : Continuous ofSU2 := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val

end SL2C

end Lightlike.Lorentz
