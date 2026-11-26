module

public import Mathlib
public import Lightlike.Lorentz.SL2RPlancherel.LadderComponents

/-!
# The `L²` norm of the raising operator in the `K × K` components

For `F` of class `C¹` on the entries, `f = F ∘ (entries)` on `SL(2,ℝ)` and `E f = A f + i B f`, where
`A, B` are the right derivatives of `f` in the directions `H, S`, the Plancherel identity in the
`K × K` components (`lintegral_norm_sq_eq_kk`) and the action of `E` on the components
(`kk_ladder_up`) give
`∫ |E f|² d haarR = (2π)² ∫_{ξ>0} sinh ξ ∑_{m,n} |f_{m,n}' − ((n cosh ξ − m)/(2 sinh ξ)) f_{m,n}|² dξ`
(`lintegral_norm_sq_raise`).  Layer 2c-ii of the Plancherel formula on `SL(2,ℝ)`, milestone HA3.
-/

@[expose] public section

open MeasureTheory Set Real Lightlike.Lorentz.SL2RPlancherel

noncomputable section

namespace Lightlike.Lorentz.SL2R

/-- The function `f = F ∘ (entries)` on `SL(2,ℝ)`. -/
def smoothFn (F : Ent → ℂ) (g : SL2R) : ℂ := F (ent (g : Matrix (Fin 2) (Fin 2) ℝ))

/-- The raising operator `A + iB` on `f = F ∘ (entries)`: the right derivative in the direction
`H` plus `i` times that in the direction `S`. -/
def raiseFn (F : Ent → ℂ) (g : SL2R) : ℂ :=
  dF F (g : Matrix (Fin 2) (Fin 2) ℝ) matH + Complex.I * dF F (g : Matrix (Fin 2) (Fin 2) ℝ) matS

lemma continuous_dF_group {F : Ent → ℂ} (hF : ContDiff ℝ 1 F) (X : Matrix (Fin 2) (Fin 2) ℝ) :
    Continuous fun g : SL2R => dF F (g : Matrix (Fin 2) (Fin 2) ℝ) X := by
  unfold dF
  have hc : Continuous fun g : SL2R => ent (g : Matrix (Fin 2) (Fin 2) ℝ) :=
    continuous_pi fun i => continuous_pi fun j =>
      (continuous_apply j).comp ((continuous_apply i).comp
        continuous_subtype_val)
  have hf : Continuous fun g : SL2R => fderiv ℝ F (ent (g : Matrix (Fin 2) (Fin 2) ℝ)) :=
    (hF.continuous_fderiv one_ne_zero).comp hc
  have hx : Continuous fun g : SL2R => ent ((g : Matrix (Fin 2) (Fin 2) ℝ) * X) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [ent, Matrix.mul_apply, Fin.sum_univ_two]
    have hij : ∀ i k : Fin 2, Continuous fun g : SL2R => (g : Matrix (Fin 2) (Fin 2) ℝ) i k :=
      fun i k => (continuous_apply k).comp ((continuous_apply i).comp
        continuous_subtype_val)
    have := hij
    fun_prop
  exact hf.clm_apply hx

lemma continuous_raiseFn {F : Ent → ℂ} (hF : ContDiff ℝ 1 F) : Continuous (raiseFn F) :=
  (continuous_dF_group hF matH).add (continuous_const.mul (continuous_dF_group hF matS))

/-- The `(m, n)`-component of the raising operator, as the ladder expression in the
`(m, n-2)`-component of `f`: `f_{m,n-2}' − (((n-2) cosh ξ − m)/(2 sinh ξ)) f_{m,n-2}`. -/
def raiseComp (F : Ent → ℂ) (n : Fin 2 → ℤ) (ξ : ℝ) : ℂ :=
  deriv (fun ξ => kkCoeff (smoothFn F) ![n 0, n 1 - 2] ξ) ξ -
    ((((n 1 - 2 : ℤ) : ℝ) * Real.cosh ξ - (n 0 : ℝ)) / (2 * Real.sinh ξ) : ℝ) *
      kkCoeff (smoothFn F) ![n 0, n 1 - 2] ξ

lemma kkCoeff_raiseFn (F : Ent → ℂ) (m k : ℤ) (ξ : ℝ) :
    kkCoeff (raiseFn F) ![m, k + 2] ξ =
      ∫ x in box, torusChar m (k + 2) (x 0) (x 1) *
        (dF F (kakM (2 * π * x 0) ξ (2 * π * x 1)) matH +
          Complex.I * dF F (kakM (2 * π * x 0) ξ (2 * π * x 1)) matS) := by
  unfold kkCoeff kkProfile raiseFn torusChar
  simp [Fin.sum_univ_two, kakM]

lemma kkCoeff_smoothFn_eq (F : Ent → ℂ) (m k : ℤ) :
    (fun ξ => kkCoeff (smoothFn F) ![m, k] ξ) = fun ξ => ∫ x in box, kkPhi F m k (x 0, x 1) ξ :=
  funext fun ξ => kkCoeff_eq F m k ξ

/-- Each `K × K` component of the raising operator is the ladder expression `raiseComp`. -/
lemma kkCoeff_raiseFn_eq {F : Ent → ℂ} (hF : ContDiff ℝ 1 F) (n : Fin 2 → ℤ) {ξ : ℝ} (hξ : ξ ≠ 0) :
    kkCoeff (raiseFn F) n ξ = raiseComp F n ξ := by
  have hn : n = ![n 0, (n 1 - 2) + 2] := by
    ext i; fin_cases i <;> simp
  rw [hn]
  have h1 := kk_ladder_up hF (n 0) (n 1 - 2) hξ
  rw [kkCoeff_raiseFn, h1]
  unfold raiseComp
  simp only [kkCoeff_smoothFn_eq]
  simp

/-- **The `L²` norm of the raising operator in the `K × K` components** (layer 2c-ii):
`∫ |E f|² d haarR = (2π)² ∫_{ξ>0} sinh ξ ∑_{m,n} |f_{m,n-2}' − ((n-2) cosh ξ − m)/(2 sinh ξ) f_{m,n-2}|² dξ`
for `f = F ∘ (entries)` with `F` of class `C¹` and `E = A + iB` the right derivative in the
directions `H` and `S`. -/
theorem lintegral_norm_sq_raise {F : Ent → ℂ} (hF : ContDiff ℝ 1 F) :
    ∫⁻ g, ENNReal.ofReal (‖raiseFn F g‖ ^ 2) ∂haarR =
      ∫⁻ ξ in Ioi (0 : ℝ), ENNReal.ofReal (Real.sinh ξ) *
        ENNReal.ofReal ((2 * π) ^ 2 * ∑' n : Fin 2 → ℤ, ‖raiseComp F n ξ‖ ^ 2) := by
  rw [lintegral_norm_sq_eq_kk (continuous_raiseFn hF)]
  refine setLIntegral_congr_fun measurableSet_Ioi fun ξ hξ => ?_
  have hξ0 : ξ ≠ 0 := ne_of_gt hξ
  simp only [kkCoeff_raiseFn_eq hF _ hξ0]

end Lightlike.Lorentz.SL2R
