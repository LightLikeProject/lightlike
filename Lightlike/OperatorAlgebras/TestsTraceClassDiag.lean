import Lightlike.OperatorAlgebras.TestsTraceClass
import Lightlike.OperatorAlgebras.HilbertSchmidtBasis
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Trust check: the diagonal operator with eigenvalues `1 / (n + 1)` on `ℓ²(ℕ)`

A bounded diagonal operator on `ℓ²(ℕ)` built from a sequence of norm at most one (Mathlib has no multiplication operator on `lp`), and the
check of the milestone OP6: `D = diag (1 / (n + 1))` is Hilbert-Schmidt (`∑ 1 / (n + 1)² < ∞`) and not trace class (`∑ 1 / (n + 1) = ∞`).
A local construction for this check, not an API.
-/

open scoped InnerProductSpace

namespace Lightlike.OperatorAlgebras.TraceClass

/-- `ℓ²(ℕ)` over `ℂ`. -/
abbrev L2N : Type := lp (fun _ : ℕ => ℂ) 2

/-- **The diagonal operator** `x ↦ (wₙ xₙ)ₙ` for a sequence with `‖wₙ‖ ≤ 1`. -/
noncomputable def diagOp (w : ℕ → ℂ) (hw : ∀ n, ‖w n‖ ≤ 1) : L2N →L[ℂ] L2N :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun n => w n * x n, by
        have hx := lp.memℓp x
        rw [memℓp_gen_iff (by simp)] at hx ⊢
        refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hx
        simp only [ENNReal.toReal_ofNat, norm_mul]
        calc (‖w n‖ * ‖x n‖) ^ (2 : ℝ) = ‖w n‖ ^ (2 : ℝ) * ‖x n‖ ^ (2 : ℝ) := by rw [Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
          _ ≤ 1 * ‖x n‖ ^ (2 : ℝ) := by gcongr; exact (Real.rpow_le_one (norm_nonneg _) (hw n) (by norm_num))
          _ = ‖x n‖ ^ (2 : ℝ) := one_mul _⟩
      map_add' := fun x y => by ext n; simp [mul_add]
      map_smul' := fun c x => by ext n; simp [mul_left_comm] } 1
    (fun x => by
      sorry)

end Lightlike.OperatorAlgebras.TraceClass
