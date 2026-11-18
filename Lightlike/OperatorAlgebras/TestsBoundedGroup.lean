import Lightlike.OperatorAlgebras.BoundedGroup

/-!
# Trust checks for the unitary groups of bounded operators

The Cauchy estimate with `B' = 0` says `‖exp (i t B) y - y‖ ≤ |t| ‖B y‖`: it is the first-order Taylor bound,
which has the right sign convention (`U t = exp (i t B)`, derivative `i B` at `0`) and a nontrivial content
(`B ≠ 0` gives a nonzero bound that shrinks with `t`).
-/

open scoped InnerProductSpace

namespace Lightlike.OperatorAlgebras

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **First-order bound**: `‖exp (i t B) y - y‖ ≤ |t| ‖B y‖` for a self-adjoint bounded `B`. -/
theorem bdU_sub_self_le {B : H →L[ℂ] H} (hB : IsSelfAdjoint B) (t : ℝ) (y : H) :
    ‖bdU B t y - y‖ ≤ |t| * ‖B y‖ := by
  have h := bdU_cauchy hB (IsSelfAdjoint.zero (H →L[ℂ] H)) (Commute.zero_right B) t y
  have h0 : bdU (0 : H →L[ℂ] H) t = 1 := by simp [bdU]
  simpa [h0] using h

end Lightlike.OperatorAlgebras
