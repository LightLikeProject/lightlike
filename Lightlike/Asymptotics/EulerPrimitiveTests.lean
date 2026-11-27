import Mathlib
import Lightlike.Asymptotics.EulerPrimitive

/-!
# Tests: the Euler primitive and the radial average

* For the linear `H(v) = v₀` (so `H(0) = 0`), the Euler primitive is `K = H` (`eulerPrimitive_coord`): `DK(v) v = v₀`, as
  `fderiv_eulerPrimitive_apply_self` says.
* The radial average of order `2` of `G(v) = v₀` is `v₀/3` (`radialAverage_two_coord`), and indeed
  `DW(v) v + 2W(v) = v₀/3 + 2v₀/3 = v₀`. A kernel `τᵏ` in place of `τ^{k-1}` would give `v₀/4`, for which
  `v₀/4 + 2v₀/4 ≠ v₀`: caught.
-/

open Set intervalIntegral
open scoped ContDiff
noncomputable section
namespace Lightlike.EulerPrimitiveTests

/-- The derivative of the coordinate function `v ↦ v₀` is the projection. -/
theorem fderiv_coord (w : Fin 1 → ℝ) :
    fderiv ℝ (fun v : Fin 1 → ℝ => v 0) w = (ContinuousLinearMap.proj 0 : (Fin 1 → ℝ) →L[ℝ] ℝ) :=
  (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 1 => ℝ) 0 w).fderiv

/-- **Trust check**: the Euler primitive of the linear `H(v) = v₀` is `H` itself. -/
theorem eulerPrimitive_coord (v : Fin 1 → ℝ) : eulerPrimitive (fun w : Fin 1 → ℝ => w 0) v = v 0 := by
  simp [eulerPrimitive, eulerKernel, fderiv_coord]

/-- The Euler equation holds for `H(v) = v₀`: `DK(v) v = v₀`. -/
example (v : Fin 1 → ℝ) : fderiv ℝ (eulerPrimitive (fun w : Fin 1 → ℝ => w 0)) v v = v 0 :=
  fderiv_eulerPrimitive_apply_self (contDiff_apply ℝ (fun _ : Fin 1 => ℝ) 0) rfl v

/-- **Trust check**: the radial average of order `2` of `v₀` is `v₀/3`. -/
theorem radialAverage_two_coord (v : Fin 1 → ℝ) : radialAverage 2 (fun w : Fin 1 → ℝ => w 0) v = v 0 / 3 := by
  unfold radialAverage
  have h : ∀ τ ∈ uIcc (0 : ℝ) 1, τ ^ (2 - 1) * (τ • v) 0 = v 0 * τ ^ 2 := fun τ _ => by
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [intervalIntegral.integral_congr h, intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

/-- The order-`2` transport equation for `G(v) = v₀`: `DW(v) v + 2 W(v) = v₀`, with `W = v₀/3`. -/
example (v : Fin 1 → ℝ) :
    fderiv ℝ (radialAverage 2 (fun w : Fin 1 → ℝ => w 0)) v v + 2 * radialAverage 2 (fun w : Fin 1 → ℝ => w 0) v =
      v 0 := by
  have := fderiv_radialAverage_apply_self 2 (by norm_num) (contDiff_apply ℝ (fun _ : Fin 1 => ℝ) 0) v
  exact_mod_cast this

/-- The kernel `τᵏ` would give `W = v₀/4` and `W' + 2W = 3v₀/4 ≠ v₀` (for `v₀ = 1`): caught. -/
example : (1 : ℝ) / 4 + 2 * (1 / 4) ≠ 1 := by norm_num

end Lightlike.EulerPrimitiveTests
