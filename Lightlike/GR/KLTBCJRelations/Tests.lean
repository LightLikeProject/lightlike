import Lightlike.GR.KLTBCJRelations.KLT

/-!
# Numerical checks for the four-point KLT and BCJ relations

Row G3-261 (T-PG7). An explicit conserved four-particle configuration with all angle and square
brackets nonzero:
`λ̃ = (1,0), (0,1), (1,1), (1,-1)` (`cfgLt`), `λ = (-1,-1), (-1,1), (1,0), (0,1)` (`cfgL`).
There `s₁₂ = -2`, `s₁₃ = s₁₄ = 1`, `A[1234] = A[1243] = 1/2`, and

* `cfg_klt`: the KLT relation `klt_four` holds (both sides are `1/2`);
* `cfg_klt_wrong_t`, `cfg_klt_wrong_u`: the relation with `s₁₃` (resp. `s₁₄`) in place of `s₁₂`
  fails (this is the negative trust check of PG7);
* `cfg_bcj_wrong`: the BCJ relation with `s₁₂` in place of `s₁₄`, `s₁₂ A[1234] = s₁₃ A[1243]`,
  fails.
-/

noncomputable section

namespace Lightlike.Rows.G3_261

open Lightlike.SpinorHelicity

/-- Test configuration: square spinors. -/
def cfgL : Fin 4 → Fin 2 → ℂ := ![![-1, -1], ![-1, 1], ![1, 0], ![0, 1]]

/-- Test configuration: angle spinors. -/
def cfgLt : Fin 4 → Fin 2 → ℂ := ![![1, 0], ![0, 1], ![1, 1], ![1, -1]]

/-- The test configuration conserves momentum. -/
theorem cfg_conserved : Conserved cfgL cfgLt := by
  intro a b
  fin_cases a <;> fin_cases b <;> simp [Fin.sum_univ_four, cfgL, cfgLt]

/-- All angle brackets of the test configuration are nonzero. -/
theorem cfg_angle : ∀ a b : Fin 4, a ≠ b → angleBr (cfgLt a) (cfgLt b) ≠ 0 := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp [angleBr_eq, cfgLt] at hab ⊢ <;> norm_num

/-- All square brackets of the test configuration are nonzero. -/
theorem cfg_square : ∀ a b : Fin 4, a ≠ b → squareBr (cfgL a) (cfgL b) ≠ 0 := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp [squareBr_eq, cfgL] at hab ⊢ <;> norm_num

theorem cfg_s12 : sBr cfgL cfgLt 0 1 = -2 := by
  simp [sBr, angleBr_eq, squareBr_eq, cfgL, cfgLt]; norm_num

theorem cfg_s13 : sBr cfgL cfgLt 0 2 = 1 := by
  simp [sBr, angleBr_eq, squareBr_eq, cfgL, cfgLt]

theorem cfg_s14 : sBr cfgL cfgLt 0 3 = 1 := by
  simp [sBr, angleBr_eq, squareBr_eq, cfgL, cfgLt]

theorem cfg_pt1234 : pt1234 cfgLt = 1 / 2 := by
  simp [pt1234, parkeTaylor, cycDen, Fin.prod_univ_four, angleBr_eq, cfgLt]
  norm_num

theorem cfg_pt1243 : pt1243 cfgLt = 1 / 2 := by
  simp [pt1243, parkeTaylor, cycDen, Fin.prod_univ_four, angleBr_eq, cfgLt]
  norm_num

/-- The KLT relation `klt_four` instantiated at the test configuration. -/
theorem cfg_klt :
    bcjNumS cfgL cfgLt ^ 2 / sBr cfgL cfgLt 0 1 + bcjNumT cfgL cfgLt ^ 2 / sBr cfgL cfgLt 0 2 +
        bcjNumU cfgL cfgLt ^ 2 / sBr cfgL cfgLt 0 3 =
      -sBr cfgL cfgLt 0 1 * pt1234 cfgLt * pt1243 cfgLt :=
  klt_four cfg_conserved cfg_angle cfg_square

/-- Both sides of the KLT relation equal `1/2` at the test configuration. -/
theorem cfg_klt_value :
    -sBr cfgL cfgLt 0 1 * pt1234 cfgLt * pt1243 cfgLt = 1 / 2 := by
  rw [cfg_s12, cfg_pt1234, cfg_pt1243]; norm_num

/-- **Negative check**: with `s₁₃` in place of `s₁₂` the KLT relation fails. -/
theorem cfg_klt_wrong_t :
    bcjNumS cfgL cfgLt ^ 2 / sBr cfgL cfgLt 0 1 + bcjNumT cfgL cfgLt ^ 2 / sBr cfgL cfgLt 0 2 +
        bcjNumU cfgL cfgLt ^ 2 / sBr cfgL cfgLt 0 3 ≠
      -sBr cfgL cfgLt 0 2 * pt1234 cfgLt * pt1243 cfgLt := by
  rw [cfg_klt, cfg_s12, cfg_s13, cfg_pt1234, cfg_pt1243]; norm_num

/-- **Negative check**: with `s₁₄` in place of `s₁₂` the KLT relation fails. -/
theorem cfg_klt_wrong_u :
    bcjNumS cfgL cfgLt ^ 2 / sBr cfgL cfgLt 0 1 + bcjNumT cfgL cfgLt ^ 2 / sBr cfgL cfgLt 0 2 +
        bcjNumU cfgL cfgLt ^ 2 / sBr cfgL cfgLt 0 3 ≠
      -sBr cfgL cfgLt 0 3 * pt1234 cfgLt * pt1243 cfgLt := by
  rw [cfg_klt, cfg_s12, cfg_s14, cfg_pt1234, cfg_pt1243]; norm_num

/-- **Negative check**: the BCJ relation with `s₁₂` in place of `s₁₄` fails. -/
theorem cfg_bcj_wrong :
    sBr cfgL cfgLt 0 1 * pt1234 cfgLt ≠ sBr cfgL cfgLt 0 2 * pt1243 cfgLt := by
  rw [cfg_s12, cfg_s13, cfg_pt1234, cfg_pt1243]; norm_num

end Lightlike.Rows.G3_261
