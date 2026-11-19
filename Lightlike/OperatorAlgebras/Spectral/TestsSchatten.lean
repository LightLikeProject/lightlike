import Lightlike.OperatorAlgebras.Spectral.SchattenTrace
import Lightlike.OperatorAlgebras.Spectral.SchattenBanach
import Lightlike.OperatorAlgebras.TestsTraceClassDiag

/-!
# Tests for the Schatten classes

* `schattenSum_two_invDiag_lt_top`, `schattenSum_one_invDiag_eq_top`: `diag(1/(n+1))` on `ℓ²(ℕ)` is in `J₂` and not in
  `J₁` (`‖D‖₂² = ∑ 1/(n+1)² < ∞`, `‖D‖₁ = ∑ 1/(n+1) = ∞`), so `J₁ ⊊ J₂`;
* `schattenNorm_zero`: `‖0‖_p = 0`.
-/

open scoped ENNReal

namespace Lightlike.OperatorAlgebras.CompactSpectral

open TraceClass

/-- **`diag(1/(n+1))` is in `J₂`**: it is Hilbert–Schmidt. -/
theorem schattenSum_two_invDiag_lt_top : schattenSum 2 invDiag < ⊤ :=
  (isHilbertSchmidt_iff.mp invDiag_isHilbertSchmidt).2

/-- **`diag(1/(n+1))` is not in `J₁`**: it is compact and not trace class, so `‖D‖₁ = ∞`. -/
theorem schattenSum_one_invDiag_eq_top : schattenSum 1 invDiag = ⊤ := by
  by_contra h
  exact invDiag_not_isTraceClass (isTraceClass_iff.mpr
    ⟨(isHilbertSchmidt_iff.mp invDiag_isHilbertSchmidt).1, lt_top_iff_ne_top.mpr h⟩)

/-- `‖0‖_p = 0` for `p > 0`. -/
theorem schattenNorm_zero {p : ℝ} (hp : 0 < p) : schattenNorm p (0 : L2N →L[ℂ] L2N) = 0 :=
  (schattenNorm_eq_zero_iff hp 0).mpr rfl

end Lightlike.OperatorAlgebras.CompactSpectral
