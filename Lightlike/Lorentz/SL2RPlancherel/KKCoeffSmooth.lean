import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.ParametricBoxIntegral
import Lightlike.Lorentz.SL2RPlancherel.KKParseval

/-!
# Smoothness of the `K × K` components

A function `f` on `SL(2,ℝ)` that is the restriction of a smooth function `F` of the matrix entries
has smooth `K × K` components: `ξ ↦ kkCoeff f m ξ` is smooth (`contDiff_kkCoeff`), since the entries
of `k_{2πa} a_ξ k_{2πb}` are smooth in `(ξ, a, b)` and the box integral of a jointly smooth function
is smooth (`contDiff_integral_box`).
Layer 2c-v of the Plancherel formula on `SL(2,ℝ)` (a dense class of test functions), milestone HA3.
-/

open MeasureTheory Set Lightlike.Lorentz.SL2R
open scoped ContDiff Real

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The entries of `k_{2πa} a_ξ k_{2πb}` are smooth in `(ξ, (a, b))`. -/
lemma contDiff_polar_entry (i j : Fin 2) :
    ContDiff ℝ ∞ fun p : ℝ × (Fin 2 → ℝ) =>
      (rot (2 * π * p.2 0) * aR p.1 * rot (2 * π * p.2 1)) i j := by
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, aR, diagSL, ← Real.exp_neg] <;> fun_prop

/-- The matrix of `k_{2πa} a_ξ k_{2πb}` is smooth in `(ξ, (a, b))`. -/
lemma contDiff_polar_matrix :
    ContDiff ℝ ∞ fun p : ℝ × (Fin 2 → ℝ) =>
      (fun i j => (rot (2 * π * p.2 0) * aR p.1 * rot (2 * π * p.2 1)) i j :
        Fin 2 → Fin 2 → ℝ) :=
  contDiff_pi.2 fun i => contDiff_pi.2 fun j => contDiff_polar_entry i j

/-- **Smooth `K × K` components**: if `f g = F(g_ij)` with `F` smooth, every `kkCoeff f m` is
smooth. -/
theorem contDiff_kkCoeff {f : SL2R → ℂ} {F : (Fin 2 → Fin 2 → ℝ) → ℂ} (hF : ContDiff ℝ ∞ F)
    (hfF : ∀ g : SL2R, f g = F fun i j => g i j) (m : Fin 2 → ℤ) :
    ContDiff ℝ ∞ (kkCoeff f m) := by
  have hΦ : ContDiff ℝ ∞ (Function.uncurry fun (ξ : ℝ) (x : Fin 2 → ℝ) =>
      Complex.exp (-(2 * π * Complex.I * ∑ i, (m i : ℂ) * (x i : ℂ))) * kkProfile f ξ x) := by
    have h1 : ContDiff ℝ ∞ fun p : ℝ × (Fin 2 → ℝ) =>
        Complex.exp (-(2 * π * Complex.I * ∑ i, (m i : ℂ) * (p.2 i : ℂ))) := by
      simp only [Fin.sum_univ_two]
      have hx : ∀ i, ContDiff ℝ ∞ fun p : ℝ × (Fin 2 → ℝ) => ((p.2 i : ℝ) : ℂ) := fun i =>
        Complex.ofRealCLM.contDiff.comp
          (show ContDiff ℝ ∞ fun p : ℝ × (Fin 2 → ℝ) => p.2 i by fun_prop)
      exact Complex.contDiff_exp.comp ((contDiff_const.mul ((contDiff_const.mul (hx 0)).add
        (contDiff_const.mul (hx 1)))).neg)
    have h2 : ContDiff ℝ ∞ fun p : ℝ × (Fin 2 → ℝ) => kkProfile f p.1 p.2 := by
      have e : (fun p : ℝ × (Fin 2 → ℝ) => kkProfile f p.1 p.2) = fun p =>
          F (fun i j => (rot (2 * π * p.2 0) * aR p.1 * rot (2 * π * p.2 1)) i j) :=
        funext fun p => hfF _
      rw [e]
      exact hF.comp contDiff_polar_matrix
    exact h1.mul h2
  exact contDiff_integral_box hΦ

end Lightlike.Lorentz.SL2RPlancherel
