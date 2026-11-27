import Mathlib
import Lightlike.Geometry.HeatKernel.DiagonalVanishing
import Lightlike.Geometry.HeatKernel.ParamIntegralDeriv

/-!
# Tests: derivatives of functions vanishing on the diagonal; parametric integrals

Non-vacuity of `exists_norm_iteratedFDeriv_comp_diag_add_le` for `Φ(p, w) = p − w` on the line, of
`exists_norm_iteratedFDeriv_quad_diag_le` for `V(p, w) = p − w`, `g = 1` in dimension one, and of
`iteratedFDeriv_integral_eq` for `Φ(q, x) = f(q) x` with a smooth bump `f`. Trust check: the diagonal map has norm
`≤ 1`.
-/

open Set MeasureTheory
open scoped ContDiff
noncomputable section
namespace Lightlike.DiagonalVanishingTests

example : ‖(diagCLM : ℝ →L[ℝ] ℝ × ℝ)‖ ≤ 1 := norm_diagCLM_le

example (ℓ : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ Icc (0 : ℝ) 1, ∀ c : ℝ, ‖c‖ ≤ 1 →
    ‖iteratedFDeriv ℝ ℓ (fun w' : ℝ => (w' + c) - w') w‖ ≤ C * ‖c‖ :=
  exists_norm_iteratedFDeriv_comp_diag_add_le (Φ := fun z : ℝ × ℝ => z.1 - z.2) (by fun_prop) isCompact_Icc
    isOpen_univ (subset_univ _) (fun w _ => sub_self w) 1 ℓ

/-- `V(p, w) = p − w` in dimension one. -/
def Vl : Fin 1 → (Fin 1 → ℝ) × (Fin 1 → ℝ) → ℝ := fun _ z => z.1 0 - z.2 0

/-- The constant metric `1`. -/
def gl : Fin 1 → Fin 1 → (Fin 1 → ℝ) → ℝ := fun _ _ _ => 1

example (ℓ : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ Icc (0 : Fin 1 → ℝ) 1, ∀ c : Fin 1 → ℝ, ‖c‖ ≤ 1 → ∀ m ≤ ℓ,
    ‖iteratedFDeriv ℝ m (fun w' => ∑ i : Fin 1, ∑ j : Fin 1, gl i j (w' + c) *
      (Vl i (w' + c, w') * Vl j (w' + c, w'))) w‖ ≤ C * ‖c‖ ^ 2 :=
  exists_norm_iteratedFDeriv_quad_diag_le (fun _ => by unfold Vl; fun_prop) (fun _ _ => contDiff_const)
    isCompact_Icc isOpen_univ (subset_univ _) (fun _ w _ => by simp [Vl]) 1 ℓ

example (f : ContDiffBump (0 : ℝ)) (m : ℕ) :
    iteratedFDeriv ℝ m (fun x : ℝ => ∫ q : ℝ, f q * x) = fun x => ∫ q : ℝ, iteratedFDeriv ℝ m (fun x => f q * x) x :=
  iteratedFDeriv_integral_eq m (Φ := fun q x => f q * x)
    ((f.contDiff.comp contDiff_fst).mul contDiff_snd) (R := f.rOut) fun q hq x => by
      rw [f.zero_of_le_dist (by rw [dist_zero_right]; exact hq.le), zero_mul]

end Lightlike.DiagonalVanishingTests
