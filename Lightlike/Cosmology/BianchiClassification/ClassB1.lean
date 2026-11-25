import Lightlike.Cosmology.BianchiClassification.ClassA

/-!
# Class B, part 1: sign changes and the rotation in the plane of `a`

For a diagonal `n` we collect the isomorphisms needed to bring `a` to the form `(0, 0, α)`:
the sign changes `a ↦ (a₀, -a₁, -a₂)` and `n ↦ -n, a ↦ -a` (both instances of
`bracketIso_diagonal_scale`), and the rotation about the first axis which turns
`a = (0, a₁, a₂)` into `(0, 0, √(a₁²+a₂²))` and fixes `diag(1,0,0)`.

## Main results

* `Lightlike.Rows.G1_039.bracketIso_flip12`, `bracketIso_neg`
* `Lightlike.Rows.G1_039.bracketIso_rotate`

## References

* heinzle-uggla-2009a (Section 3)
-/

namespace Lightlike.Rows.G1_039

open Matrix

/-- The class B normal forms `(n, α)` with `a = (0, 0, α)`: `V` (`n = 0`), `IV` (`n = diag(1,0,0)`),
`VI_h` (`n = diag(1,-1,0)`) and `VII_h` (`n = diag(1,1,0)`), the last two with `α > 0`. -/
def ClassBNormal (t : Fin 3 → ℝ) (α : ℝ) : Prop :=
  (t = ![0, 0, 0] ∧ α = 1) ∨ (t = ![1, 0, 0] ∧ α = 1) ∨ (t = ![1, -1, 0] ∧ 0 < α) ∨
    (t = ![1, 1, 0] ∧ 0 < α)

/-- Reversing the signs of the last two basis vectors keeps the diagonal `n`. -/
theorem bracketIso_flip12 (l : Fin 3 → ℝ) (a : V3) :
    BracketIso (diagonal l) a (diagonal l) ![a 0, -a 1, -a 2] := by
  have h := bracketIso_diagonal_scale l a ![1, -1, -1] (by intro i; fin_cases i <;> simp)
  have e1 : (fun i => l i * (![1, -1, -1] : Fin 3 → ℝ) i ^ 2 /
      ((![1, -1, -1] : Fin 3 → ℝ) 0 * (![1, -1, -1] : Fin 3 → ℝ) 1 *
        (![1, -1, -1] : Fin 3 → ℝ) 2)) = l := by
    ext i; fin_cases i <;> simp
  have e2 : (fun i => a i / (![1, -1, -1] : Fin 3 → ℝ) i) = ![a 0, -a 1, -a 2] := by
    ext i; fin_cases i <;> simp [div_neg]
  rwa [e1, e2] at h

/-- Changing the sign of all basis vectors: `n ↦ -n`, `a ↦ -a`. -/
theorem bracketIso_neg (l : Fin 3 → ℝ) (a : V3) :
    BracketIso (diagonal l) a (diagonal fun i => -l i) fun i => -a i := by
  have h := bracketIso_diagonal_scale l a ![-1, -1, -1] (by intro i; fin_cases i <;> simp)
  have e1 : (fun i => l i * (![-1, -1, -1] : Fin 3 → ℝ) i ^ 2 /
      ((![-1, -1, -1] : Fin 3 → ℝ) 0 * (![-1, -1, -1] : Fin 3 → ℝ) 1 *
        (![-1, -1, -1] : Fin 3 → ℝ) 2)) = fun i => -l i := by
    ext i; fin_cases i <;> simp [div_neg]
  have e2 : (fun i => a i / (![-1, -1, -1] : Fin 3 → ℝ) i) = fun i => -a i := by
    ext i; fin_cases i <;> simp [div_neg]
  rwa [e1, e2] at h

/-- Rotation about the first axis taking `(0, a₁, a₂)` to `(0, 0, √(a₁²+a₂²))`; it fixes
`diag(1,0,0)`. -/
theorem bracketIso_rotate (a : V3) (h0 : a 0 = 0) (hne : a 1 ≠ 0 ∨ a 2 ≠ 0) :
    BracketIso (diagonal ![1, 0, 0]) a (diagonal ![1, 0, 0])
      ![0, 0, Real.sqrt (a 1 ^ 2 + a 2 ^ 2)] := by
  have hpos : 0 < a 1 ^ 2 + a 2 ^ 2 := by
    rcases hne with h | h
    · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg (a 2)]
    · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg (a 1)]
  set r := Real.sqrt (a 1 ^ 2 + a 2 ^ 2) with hr
  have hrpos : 0 < r := Real.sqrt_pos.mpr hpos
  have hr2 : r ^ 2 = a 1 ^ 2 + a 2 ^ 2 := Real.sq_sqrt hpos.le
  set c := a 2 / r with hc
  set s := a 1 / r with hs
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    rw [hc, hs, div_pow, div_pow, ← add_div, add_comm, ← hr2]
    exact div_self (by positivity)
  set P : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, c, -s; 0, s, c] with hP
  have hdet : P.det = 1 := by
    rw [hP, Matrix.det_fin_three]
    simp
    nlinarith [hcs]
  have hinv : P⁻¹ = Pᵀ := by
    apply Matrix.inv_eq_right_inv
    rw [hP]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith [hcs]
  have h := bracketIso_transform (diagonal ![1, 0, 0]) a P (by rw [hdet]; exact one_ne_zero)
  have e1 : (P.det)⁻¹ • (P * diagonal ![1, 0, 0] * Pᵀ) = diagonal ![1, 0, 0] := by
    rw [hdet, hP]
    ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.smul_apply,
      Matrix.diagonal_apply]
    fin_cases i <;> fin_cases j <;> simp
  have e2 : (P⁻¹)ᵀ.mulVec a = ![0, 0, r] := by
    rw [hinv, Matrix.transpose_transpose, hP]
    ext i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h0]
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h0, hc, hs]
      field_simp
      ring
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h0, hc, hs]
      field_simp
      nlinarith [hr2]
  rwa [e1, e2] at h

end Lightlike.Rows.G1_039
