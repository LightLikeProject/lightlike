import Lightlike.Asymptotics.Orientation
import Lightlike.Asymptotics.Tests
import Lightlike.Asymptotics.ContourTests
import Lightlike.Asymptotics.ClosingTests

/-!
# Trust checks for the orientation of the descent contour

* **Known value.** For the regular unit tetrahedron (`Aᵢ = 3`, saddle `s = 11/3 + i √2/6`),
  `s − 3 = 2/3 + i √2/6`, `‖s − 3‖² = 1/2` and `(s − 3)⁴ = 17/324 + i 14√2/81`, so
  `saddleDir² = −i (s − 3)⁴/‖s − 3‖⁴ = (56√2 − 17 i)/81` (`saddleDir_sq_regular`), a unit
  vector, as `norm_saddleDir` says.
* **Wrong input fails.** Without the shift by `−π/4`, `w = exp(i Σᵢ arg(s − Aᵢ)/2)` has
  `b w² = −i ‖b‖`: it points along a ridge, not a valley (`IsEuclid.saddleCoeff_mul_sq_ne`).
  The opposite root `−saddleDir` satisfies `b u² = −‖b‖` as well but has negative real part
  (`IsEuclid.re_neg_saddleDir_neg`), so the square identity alone does not fix the orientation;
  `IsEuclid.exists_contour` does.
* **Non-vacuity.** For the regular tetrahedron the oriented contour exists, with the path along
  `+saddleDir` landing beyond `Bₖ = 4` and the one along `−saddleDir` in `(0, 3)`
  (`exists_contour_regular`).
* **Junk values.** For `l = 0` all `Aᵢ`, `Bₖ` vanish and Lean's `1/0 = 0` turns
  `ψ''(z) = 1/z − 4/z + 3/z` into `0`, so `saddleCoeff 0 = 0` (`saddleCoeff_zero`) and
  `b u² = −‖b‖` holds for every `u`. The orientation theorems therefore assume `IsEuclid l`, which
  gives `b ≠ 0` (`IsEuclid.saddleCoeff_ne_zero`).
-/

open Complex Set Filter Topology
open scoped Real

namespace Lightlike.Asymptotics

/-- **Known value**: `saddleDir² = (56√2 − 17 i)/81` for the regular tetrahedron. -/
theorem saddleDir_sq_regular :
    saddleDir (fun _ => 1) ^ 2 = ((56 * √2 / 81 : ℝ) : ℂ) - ((17 / 81 : ℝ) : ℂ) * I := by
  have e := saddleDir_sq_mul_norm (fun _ => 1)
  have hw : ∀ i, saddle (fun _ => (1 : ℝ)) - ((faceSum (fun _ => 1) i : ℝ) : ℂ) =
      ((2 / 3 : ℝ) : ℂ) + ((√2 / 6 : ℝ) : ℂ) * I := by
    intro i
    rw [saddle_regular, faceSum_regular]
    apply Complex.ext <;> simp <;> norm_num
  simp only [hw, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at e
  have hn : ‖(((2 / 3 : ℝ) : ℂ) + ((√2 / 6 : ℝ) : ℂ) * I) ^ 4‖ = 1 / 4 := by
    have h2 : (√2 / 6 : ℝ) ^ 2 = 1 / 18 := by
      rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
    rw [norm_pow, show ∀ x : ℝ, x ^ 4 = (x ^ 2) ^ 2 from fun x => by ring, Complex.sq_norm,
      Complex.normSq_add_mul_I, h2]
    norm_num
  rw [hn] at e
  have hq : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hw2 : (((2 / 3 : ℝ) : ℂ) + ((√2 / 6 : ℝ) : ℂ) * I) ^ 2 = 7 / 18 + 2 * ((√2 : ℝ) : ℂ) / 9 * I := by
    push_cast
    linear_combination (((√2 : ℝ) : ℂ) ^ 2 / 36) * I_sq - (1 / 36) * hq
  have hw4 : (((2 / 3 : ℝ) : ℂ) + ((√2 / 6 : ℝ) : ℂ) * I) ^ 4 = 17 / 324 + 14 * ((√2 : ℝ) : ℂ) / 81 * I := by
    rw [show ∀ x : ℂ, x ^ 4 = (x ^ 2) ^ 2 from fun x => by ring, hw2]
    linear_combination (4 * ((√2 : ℝ) : ℂ) ^ 2 / 81) * I_sq - (4 / 81) * hq
  rw [hw4] at e
  push_cast at e ⊢
  linear_combination 4 * e - (56 * ((√2 : ℝ) : ℂ) / 81) * I_sq

/-- `b exp(i Σᵢ arg(s − Aᵢ)) = −i ‖b‖`. -/
theorem IsEuclid.saddleCoeff_mul_exp_sum_arg {l : Fin 6 → ℝ} (h : IsEuclid l) :
    saddleCoeff l * exp (((∑ i, arg (saddle l - faceSum l i) : ℝ) : ℂ) * I) =
      -I * ‖saddleCoeff l‖ := by
  have h1 := h.mul_saddleDir_sq
  rw [saddleDir_sq] at h1
  linear_combination I * h1 + saddleCoeff l * exp (((∑ i, arg (saddle l - faceSum l i) : ℝ) : ℂ) * I) * I_sq

/-- **Wrong input**: without the shift by `−π/4`, `w = exp(i Σᵢ arg(s − Aᵢ)/2)` is no descent
direction, `b w² ≠ −‖b‖`. -/
theorem IsEuclid.saddleCoeff_mul_sq_ne {l : Fin 6 → ℝ} (h : IsEuclid l) :
    saddleCoeff l * exp ((((∑ i, arg (saddle l - faceSum l i)) / 2 : ℝ) : ℂ) * I) ^ 2 ≠
      -‖saddleCoeff l‖ := by
  have hsq : exp ((((∑ i, arg (saddle l - faceSum l i)) / 2 : ℝ) : ℂ) * I) ^ 2 =
      exp (((∑ i, arg (saddle l - faceSum l i) : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [hsq, h.saddleCoeff_mul_exp_sum_arg]
  intro he
  have := congrArg Complex.im he
  simp at this
  exact h.saddleCoeff_ne_zero this

/-- **Wrong input**: `−saddleDir` also satisfies `b u² = −‖b‖`, but its real part is negative, so
the orientation is not fixed by the square identity. -/
theorem IsEuclid.re_neg_saddleDir_neg {l : Fin 6 → ℝ} (h : IsEuclid l) :
    saddleCoeff l * (-saddleDir l) ^ 2 = -‖saddleCoeff l‖ ∧ (-saddleDir l).re < 0 := by
  refine ⟨by rw [neg_sq]; exact h.mul_saddleDir_sq, ?_⟩
  rw [neg_re]
  linarith [h.re_saddleDir_pos]

/-- **Non-vacuity**: for the regular tetrahedron the oriented contour lands at `x₁ > 4` and at
`x₂ ∈ (0, 3)`. -/
theorem exists_contour_regular : ∃ x₁ x₂ : ℝ, 4 < x₁ ∧ 0 < x₂ ∧ x₂ < 3 := by
  obtain ⟨-, -, -, -, -, -, -, -, x₁, x₂, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨k, hk⟩, h0, i, hi⟩ :=
    isEuclid_regular.exists_contour
  rw [quadSum_regular] at hk
  rw [faceSum_regular] at hi
  exact ⟨x₁, x₂, hk, h0, hi⟩

/-- **Junk value**: for `l = 0` Lean's `1/0 = 0` gives `saddleCoeff 0 = 0`. -/
theorem saddleCoeff_zero : saddleCoeff 0 = 0 := by
  have hA : faceSum 0 = 0 := by funext i; fin_cases i <;> simp [faceSum]
  have hB : quadSum 0 = 0 := by funext k; fin_cases k <;> simp [quadSum]
  simp only [saddleCoeff, d2phaseC, hA, hB, Pi.zero_apply, ofReal_zero, sub_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

end Lightlike.Asymptotics
