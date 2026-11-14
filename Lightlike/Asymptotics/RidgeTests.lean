import Lightlike.Asymptotics.Ridge
import Lightlike.Asymptotics.Tests
import Lightlike.Asymptotics.ContourTests

/-!
# Trust checks for the ridge through the saddle

* **Known values.** For the regular unit tetrahedron (`Aᵢ = 3`, `Bₖ = 4`, saddle
  `s₁ = 11/3 + i √2/6`) the polynomial of `sin_im_dphaseC_vertical` on the line `Re z = 11/3` is
  `C(t) = 16 t² − 8 t + 32/81 = 8 (9t − 4)(18t − 1)/81` (`ridgeCoeffs_regular`,
  `ridgePoly_regular`). Its roots are `t = 1/18 = (Im s₁)²` and `t = 4/9`, and its leading
  coefficient is positive, as the proof of `im_dphaseC_vertical_sign` predicts
  (`ridgePoly_regular_roots`).
* **Wrong input fails.** Without `Σᵢ Aᵢ = Σₖ Bₖ` the `t³` term survives: for `A = (1, 0, 0, 0)`,
  `B = 0` and `x = 0`, `C(t) = −t³` (`ridgePoly_unbalanced`), which is no quadratic
  (`ridgePoly_unbalanced_not_quadratic`). So `ridgePoly_eq` needs the balance.
* **Non-vacuity.** For the regular tetrahedron the point `11/3 + i` lies on the vertical line
  through `s₁` and has `Re ψ > Re ψ(s₁)` (`re_phaseC_vertical_gt_regular`), from
  `IsEuclid.re_phaseC_vertical_gt`.
* **Junk values.** At `z = 0`, Lean's `log 0 = 0` and `arg (−a) = π` for `a > 0` give
  `Im ψ'(0) = −3π` for the regular data (`im_dphaseC_zero_regular`), while the limit along
  `iy`, `y → 0⁺`, is `π/2 − 4π + 3π − 2π = −5π/2`. The continuity and sign statements are made
  only for `y > 0`, where no junk value enters.
-/

open Complex Set Filter Topology
open scoped Real

namespace Lightlike.Asymptotics

/-- **Known value**: the coefficients of `C` for the regular tetrahedron on the line `Re z = 11/3`. -/
theorem ridgeCoeffs_regular :
    ridgeC2 (fun _ => 3) (fun _ => 4) (11 / 3) = 16 ∧
      ridgeC1 (fun _ => 3) (fun _ => 4) (11 / 3) = -8 ∧
      ridgeC0 (fun _ => 3) (fun _ => 4) (11 / 3) = 32 / 81 := by
  simp only [ridgeC2, ridgeC1, ridgeC0, esym1, esym2, esym3, esym4, ridgeNum, ridgeDen,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two]
  norm_num

/-- **Known value**: `C(t) = 8 (9t − 4)(18t − 1)/81` for the regular tetrahedron. -/
theorem ridgePoly_regular (t : ℝ) :
    ridgePoly (fun _ => 3) (fun _ => 4) (11 / 3) t = 8 * (9 * t - 4) * (18 * t - 1) / 81 := by
  have hbal : ∑ _i : Fin 4, (3 : ℝ) = ∑ _k : Fin 3, (4 : ℝ) := by norm_num
  obtain ⟨h2, h1, h0⟩ := ridgeCoeffs_regular
  rw [ridgePoly_eq hbal, h2, h1, h0]
  ring

/-- **Known value**: the roots of `C` for the regular tetrahedron are `(Im s₁)² = 1/18` and `4/9`,
and its leading coefficient is positive. -/
theorem ridgePoly_regular_roots :
    ridgePoly (fun _ => 3) (fun _ => 4) (11 / 3) ((saddle (fun _ => 1)).im ^ 2) = 0 ∧
      ridgePoly (fun _ => 3) (fun _ => 4) (11 / 3) (4 / 9) = 0 ∧
      0 < ridgeC2 (fun _ => 3) (fun _ => 4) (11 / 3) := by
  have hs : (saddle (fun _ => 1)).im ^ 2 = 1 / 18 := by
    rw [saddle_regular]
    show (√2 / 6) ^ 2 = 1 / 18
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [hs, ridgePoly_regular]; norm_num
  · rw [ridgePoly_regular]; norm_num
  · rw [ridgeCoeffs_regular.1]; norm_num

/-- **Wrong input**: for the unbalanced data `A = (1, 0, 0, 0)`, `B = 0`, `x = 0`, the `t³` term
survives and `C(t) = −t³`. -/
theorem ridgePoly_unbalanced (t : ℝ) : ridgePoly ![1, 0, 0, 0] ![0, 0, 0] 0 t = -t ^ 3 := by
  simp only [ridgePoly, esym1, esym2, esym3, esym4, ridgeNum, ridgeDen,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two]
  ring

/-- **Wrong input**: the unbalanced `C(t) = −t³` is not a quadratic in `t`, so the conclusion of
`ridgePoly_eq` fails without `Σᵢ Aᵢ = Σₖ Bₖ`. -/
theorem ridgePoly_unbalanced_not_quadratic :
    ¬ ∃ c₂ c₁ c₀ : ℝ, ∀ t, ridgePoly ![1, 0, 0, 0] ![0, 0, 0] 0 t = c₂ * t ^ 2 + c₁ * t + c₀ := by
  rintro ⟨c₂, c₁, c₀, h⟩
  have h0 := h 0
  have h1 := h 1
  have hm := h (-1)
  have h2 := h 2
  simp only [ridgePoly_unbalanced] at h0 h1 hm h2
  norm_num at h0 h1 hm h2
  linarith

/-- **Non-vacuity**: for the regular tetrahedron, the point `11/3 + i` on the vertical line through
the saddle `s₁ = 11/3 + i √2/6` has `Re ψ(11/3 + i) > Re ψ(s₁)`. -/
theorem re_phaseC_vertical_gt_regular :
    (phaseC (fun _ => 3) (fun _ => 4) ⟨11 / 3, √2 / 6⟩).re <
      (phaseC (fun _ => 3) (fun _ => 4) (((11 / 3 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * I)).re := by
  have hne : (1 : ℝ) ≠ (saddle (fun _ => 1)).im := by
    rw [saddle_regular]
    intro h
    change (1 : ℝ) = √2 / 6 at h
    have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith
  have := isEuclid_regular.re_phaseC_vertical_gt one_pos hne
  rw [faceSum_regular, quadSum_regular, saddle_regular] at this
  exact this

/-- **Junk value**: at `z = 0`, `log 0 = 0` and `arg (−a) = π` give `Im ψ'(0) = −3π` for the
regular data, which differs from the limit `−5π/2` along `iy`, `y → 0⁺`. The statements of
`Ridge` are made for `y > 0` only. -/
theorem im_dphaseC_zero_regular : (dphaseC (fun _ => 3) (fun _ => 4) 0).im = -3 * π := by
  have h3 : arg ((0 : ℂ) - ((3 : ℝ) : ℂ)) = π := by
    rw [zero_sub, ← ofReal_neg]; exact arg_ofReal_of_neg (by norm_num)
  have h4 : arg ((0 : ℂ) - ((4 : ℝ) : ℂ)) = π := by
    rw [zero_sub, ← ofReal_neg]; exact arg_ofReal_of_neg (by norm_num)
  rw [im_dphaseC]
  simp only [arg_zero, h3, h4, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

end Lightlike.Asymptotics
