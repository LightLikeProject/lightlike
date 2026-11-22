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

Reference: E. Wigner (1939); S. Weinberg, *The Quantum Theory of Fields I* (1995), Chapter 2.
No equation numbers are claimed.
-/

@[expose] public section

open Matrix

namespace Lightlike.Lorentz.HARow055

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

end Lightlike.Lorentz.HARow055
