module

public import Mathlib
public import Lightlike.Lorentz.PoincareIrreps.Massless
public import Lightlike.Lorentz.PoincareIrreps.Poincare

/-!
# Orbits of the Lorentz group on momentum space (Wigner's orbit types), row G1-055, pass 4

Beyond the done-when of HA6, which treats one orbit of each type (rest, light-like, tachyonic),
Wigner's classification rests on the fact that these orbits exhaust momentum space: two momenta lie
in the same `SL(2,ℂ)`-orbit iff they have the same `p²` (= `det`) and, when `p² ≥ 0`, the same sign
of the energy. This file proves the transitivity statements one orbit type at a time.

* `smul_tachMom_apply`: the entries of `A • tachMom m`.
* `exists_smul_tachMom_of_pos`: a Hermitian matrix with `det = -m²` (`m > 0`), `P₀₀ > 0`, is in the
  orbit of `tachMom m`.
* `neg_tachMom_eq_smul`, `exists_smul_tachMom_of_neg`: the same for `P₀₀ < 0`, via `-tachMom m`.

* `exists_smul_tachMom`: every `P` with `det P = -m²` is in the orbit of `tachMom m` (the case
  `P₀₀ = 0` is handled by an upper unipotent shear, `exists_upper_smul_pos`).

* `exists_smul_restMom_of_neg`: the negative-energy mass shell is the orbit of `restMom (-m)`.
* `exists_smul_neg_lightMom`: the negative light cone is the orbit of `-lightMom 1`.

Reference: E. Wigner (1939); S. Weinberg, *The Quantum Theory of Fields I* (1995), Chapter 2.
No equation numbers are claimed.
-/

@[expose] public section

open Matrix

namespace Lightlike.Lorentz.WignerOrbits

open Lightlike.Lorentz Lightlike.Lorentz.Poincare

/-- The entries of `A (m diag(1,-1)) A†`: `m (A_{i0} conj(A_{j0}) - A_{i1} conj(A_{j1}))`. -/
lemma smul_tachMom_apply (A : SL2C) (m : ℝ) (i j : Fin 2) :
    ((A • tachMom m : Herm2) : Matrix (Fin 2) (Fin 2) ℂ) i j =
      (m : ℂ) * (A i 0 * (starRingEnd ℂ) (A j 0) - A i 1 * (starRingEnd ℂ) (A j 1)) := by
  rw [coe_smul]
  simp [tachMom, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  ring

/-- **A tachyonic momentum with positive `P₀₀` lies in the orbit of `tachMom m`.** If
`det P = -m²` (`m > 0`) and `P₀₀ > 0`, then `P = A (m diag(1,-1)) A†` for some `A ∈ SL(2,ℂ)`. -/
theorem exists_smul_tachMom_of_pos {m : ℝ} (hm : 0 < m) {P : Herm2}
    (hd : P.1.det = ((-(m ^ 2) : ℝ) : ℂ)) (ha : 0 < (P.1 0 0).re) :
    ∃ A : SL2C, A • tachMom m = P := by
  obtain ⟨h00, h11, h10⟩ := Lightlike.Lorentz.Poincare.herm_entries P
  set a := (P.1 0 0).re with hadef
  set d := (P.1 1 1).re with hddef
  set b := P.1 0 1 with hb
  have hdet : (a : ℂ) * d - (starRingEnd ℂ) b * b = ((-(m ^ 2) : ℝ) : ℂ) := by
    rw [Matrix.det_fin_two, h00, h11, h10, ← hb] at hd
    linear_combination hd
  have hq : 0 < a / m := div_pos ha hm
  set r : ℝ := Real.sqrt (a / m) with hrdef
  have hr0 : r ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  have hr2 : r * r = a / m := Real.mul_self_sqrt hq.le
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr0
  have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hrc2 : (r : ℂ) * r * m = a := by
    have : ((r * r * m : ℝ) : ℂ) = (a : ℂ) := by
      rw [hr2]; push_cast; field_simp
    simpa using this
  refine ⟨SL2C.mk r 0 (r * (starRingEnd ℂ) b / a) (r : ℂ)⁻¹ (by field_simp; ring), ?_⟩
  apply Subtype.ext
  ext i j
  rw [smul_tachMom_apply]
  have hcr : (starRingEnd ℂ) (r : ℂ) = r := Complex.conj_ofReal r
  fin_cases i <;> fin_cases j
  · simp [h00, hcr]
    linear_combination hrc2
  · simp [hcr, ← hb]
    field_simp
    linear_combination (b) * hrc2
  · simp [hcr, h10]
    field_simp
    linear_combination ((starRingEnd ℂ) b) * hrc2
  · simp [hcr, h11]
    field_simp
    have hdet' := hdet
    push_cast at hdet'
    rw [← hrc2] at hdet' ⊢
    linear_combination (-((m : ℂ) * (r : ℂ) ^ 4)) * hdet'

/-- The rotation `S = [[0,-1],[1,0]]` sends `tachMom m` to `-tachMom m`. -/
lemma neg_tachMom_eq_smul (m : ℝ) :
    ∃ S : SL2C, S • tachMom m = -tachMom m := by
  refine ⟨SL2C.mk 0 (-1) 1 0 (by simp), ?_⟩
  apply Subtype.ext
  rw [coe_smul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SL2C.mk, tachMom, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]

/-- **A tachyonic momentum with negative `P₀₀` lies in the orbit of `tachMom m`.** -/
theorem exists_smul_tachMom_of_neg {m : ℝ} (hm : 0 < m) {P : Herm2}
    (hd : P.1.det = ((-(m ^ 2) : ℝ) : ℂ)) (ha : (P.1 0 0).re < 0) :
    ∃ A : SL2C, A • tachMom m = P := by
  have hd' : (-P).1.det = ((-(m ^ 2) : ℝ) : ℂ) := by
    rw [coe_neg_herm, Matrix.det_neg]
    simpa using hd
  have ha' : 0 < ((-P).1 0 0).re := by
    rw [coe_neg_herm]; simpa using ha
  obtain ⟨A, hA⟩ := exists_smul_tachMom_of_pos hm hd' ha'
  obtain ⟨S, hS⟩ := neg_tachMom_eq_smul m
  refine ⟨A * S, ?_⟩
  rw [mul_smul, hS, smul_neg, hA, neg_neg]

/-- The `(0,0)` entry of `upper z • P`: `P₀₀ + z P₁₀ + z̄ (P₀₁ + z P₁₁)`. -/
lemma upper_smul_apply_zero (z : ℂ) (P : Herm2) :
    ((SL2C.upper z • P : Herm2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 =
      P.1 0 0 + z * P.1 1 0 + (starRingEnd ℂ) z * (P.1 0 1 + z * P.1 1 1) := by
  rw [coe_smul]
  simp [SL2C.upper, SL2C.mk, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
    Matrix.vecMul, dotProduct]
  ring

/-- A tachyonic momentum with `P₀₀ = 0` can be moved by an upper triangular unipotent element to
one with `P₀₀ > 0`. -/
lemma exists_upper_smul_pos {m : ℝ} (hm : 0 < m) {P : Herm2}
    (hd : P.1.det = ((-(m ^ 2) : ℝ) : ℂ)) (ha : (P.1 0 0).re = 0) :
    ∃ z : ℂ, 0 < (((SL2C.upper z • P : Herm2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re := by
  obtain ⟨h00, h11, h10⟩ := Lightlike.Lorentz.Poincare.herm_entries P
  set d := (P.1 1 1).re with hddef
  set b := P.1 0 1 with hb
  have h00' : P.1 0 0 = 0 := by rw [h00, ha]; simp
  have hdet : -((starRingEnd ℂ) b * b) = ((-(m ^ 2) : ℝ) : ℂ) := by
    rw [Matrix.det_fin_two, h00', h11, h10, ← hb] at hd
    linear_combination hd
  have hn : Complex.normSq b = m ^ 2 := by
    have h1 : (starRingEnd ℂ) b * b = ((Complex.normSq b : ℝ) : ℂ) := by
      rw [mul_comm]; exact Complex.mul_conj b
    rw [h1] at hdet
    have h2 : ((Complex.normSq b : ℝ) : ℂ) = ((m ^ 2 : ℝ) : ℂ) := by
      push_cast at hdet ⊢
      linear_combination -hdet
    exact_mod_cast h2
  have hnpos : 0 < Complex.normSq b := by rw [hn]; positivity
  set t : ℝ := 1 / (1 + |d|) with htdef
  have hden : 0 < 1 + |d| := by positivity
  have ht : 0 < t := by positivity
  have htd : 0 < 2 + t * d := by
    have h1 : t * |d| ≤ 1 := by
      rw [htdef, one_div, inv_mul_le_iff₀ hden]; linarith
    have h2 : -(t * |d|) ≤ t * d := by
      have := neg_abs_le d
      nlinarith
    linarith
  refine ⟨(t : ℂ) * b, ?_⟩
  rw [upper_smul_apply_zero, h00', h10, h11, ← hb]
  have e : (0 : ℂ) + (t : ℂ) * b * (starRingEnd ℂ) b +
      (starRingEnd ℂ) ((t : ℂ) * b) * (b + (t : ℂ) * b * (d : ℂ)) =
      ((t * Complex.normSq b * (2 + t * d) : ℝ) : ℂ) := by
    have h1 : b * (starRingEnd ℂ) b = ((Complex.normSq b : ℝ) : ℂ) := Complex.mul_conj b
    simp only [map_mul, Complex.conj_ofReal]
    push_cast
    linear_combination (↑t * (2 + ↑t * (d : ℂ))) * h1
  rw [e, Complex.ofReal_re]
  positivity

/-- **Every tachyonic momentum lies in the orbit of `tachMom m`.** If `det P = -m²` with `m > 0`,
then `P = A (m diag(1,-1)) A†` for some `A ∈ SL(2,ℂ)`; the sign of the energy plays no role. -/
theorem exists_smul_tachMom {m : ℝ} (hm : 0 < m) {P : Herm2}
    (hd : P.1.det = ((-(m ^ 2) : ℝ) : ℂ)) :
    ∃ A : SL2C, A • tachMom m = P := by
  rcases lt_trichotomy (P.1 0 0).re 0 with h | h | h
  · exact exists_smul_tachMom_of_neg hm hd h
  · obtain ⟨z, hz⟩ := exists_upper_smul_pos hm hd h
    have hd' : (SL2C.upper z • P : Herm2).1.det = ((-(m ^ 2) : ℝ) : ℂ) := by
      rw [det_smul]; exact hd
    obtain ⟨A, hA⟩ := exists_smul_tachMom_of_pos hm hd' hz
    refine ⟨(SL2C.upper z)⁻¹ * A, ?_⟩
    rw [mul_smul, hA, inv_smul_smul]
  · exact exists_smul_tachMom_of_pos hm hd h

/-- `restMom (-m) = -restMom m`. -/
lemma restMom_neg (m : ℝ) : restMom (-m) = -restMom m := by
  apply Subtype.ext
  rw [coe_neg_herm]
  simp [restMom]

/-- **The negative-energy mass shell is one orbit.** If `det P = m²` (`m > 0`) and `tr P < 0`, then
`P = A (-m · 1) A†` for some `A ∈ SL(2,ℂ)`. -/
theorem exists_smul_restMom_of_neg {m : ℝ} (hm : 0 < m) {P : Herm2}
    (hd : P.1.det = ((m ^ 2 : ℝ) : ℂ)) (ht : P.1.trace.re < 0) :
    ∃ A : SL2C, A • restMom (-m) = P := by
  have hmem : (-P) ∈ massShell m := by
    refine ⟨?_, ?_⟩
    · rw [coe_neg_herm, Matrix.det_neg]
      simpa using hd
    · rw [coe_neg_herm, Matrix.trace_neg]
      simpa using ht
  refine ⟨boost hm ⟨-P, hmem⟩, ?_⟩
  rw [restMom_neg, smul_neg, boost_smul_rest hm ⟨-P, hmem⟩, neg_neg]

/-- **The negative light cone (without apex) is one orbit.** If `det P = 0` and `tr P < 0`, then
`P = A (-lightMom 1) A†` for some `A ∈ SL(2,ℂ)`. -/
theorem exists_smul_neg_lightMom {P : Herm2}
    (hd : P.1.det = 0) (ht : P.1.trace.re < 0) :
    ∃ A : SL2C, A • (-lightMom 1) = P := by
  have hmem : (-P) ∈ lightCone := by
    refine ⟨?_, ?_⟩
    · rw [coe_neg_herm, Matrix.det_neg]
      simp [hd]
    · rw [coe_neg_herm, Matrix.trace_neg]
      simpa using ht
  obtain ⟨A, hA⟩ := exists_smul_lightMom hmem
  refine ⟨A, ?_⟩
  rw [smul_neg, hA, neg_neg]

end Lightlike.Lorentz.WignerOrbits

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Lorentz.HARow055.exists_smul_neg_lightMom := _root_.Lightlike.Lorentz.WignerOrbits.exists_smul_neg_lightMom
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Lorentz.HARow055.exists_smul_restMom_of_neg := _root_.Lightlike.Lorentz.WignerOrbits.exists_smul_restMom_of_neg
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Lorentz.HARow055.exists_smul_tachMom := _root_.Lightlike.Lorentz.WignerOrbits.exists_smul_tachMom
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Lorentz.HARow055.exists_smul_tachMom_of_neg := _root_.Lightlike.Lorentz.WignerOrbits.exists_smul_tachMom_of_neg
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Lorentz.HARow055.exists_smul_tachMom_of_pos := _root_.Lightlike.Lorentz.WignerOrbits.exists_smul_tachMom_of_pos
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Lorentz.HARow055.exists_upper_smul_pos := _root_.Lightlike.Lorentz.WignerOrbits.exists_upper_smul_pos
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Lorentz.HARow055.neg_tachMom_eq_smul := _root_.Lightlike.Lorentz.WignerOrbits.neg_tachMom_eq_smul
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Lorentz.HARow055.restMom_neg := _root_.Lightlike.Lorentz.WignerOrbits.restMom_neg
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Lorentz.HARow055.smul_tachMom_apply := _root_.Lightlike.Lorentz.WignerOrbits.smul_tachMom_apply
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Lorentz.HARow055.upper_smul_apply_zero := _root_.Lightlike.Lorentz.WignerOrbits.upper_smul_apply_zero
