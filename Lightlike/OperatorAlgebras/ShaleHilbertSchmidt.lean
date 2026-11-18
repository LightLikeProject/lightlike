import Lightlike.OperatorAlgebras.ShaleAlgebra
import Lightlike.OperatorAlgebras.HilbertSchmidtBasis

/-!
# The Hilbert-Schmidt condition on the antilinear part, in one basis

Helper for the necessity part of Shale's criterion (`T-OP2-P6`, `Tasks/OP/T_OP2_P6.lean`). The antilinear part
`β` of a Bogoliubov transformation has the same squared norms as the bounded operator `√(α†α - 1)` (`ShaleAlgebra`),
so by the basis independence of the Hilbert-Schmidt square sum (`HilbertSchmidtBasis`), `∑ᵢ ‖β bᵢ‖² < ∞` in one
Hilbert basis gives `IsHilbertSchmidt β`, which asks for every basis.
-/

universe u

namespace Lightlike.OperatorAlgebras

variable {h : Type u} [NormedAddCommGroup h] [InnerProductSpace ℂ h] [CompleteSpace h]

/-- **Hilbert-Schmidt in one basis**: if `∑ᵢ ‖β bᵢ‖²` converges for one Hilbert basis `b`, the antilinear part
of `T` is Hilbert-Schmidt (for every Hilbert basis). -/
theorem Bogoliubov.isHilbertSchmidt_betaPart (T : Bogoliubov h) {ι : Type u} (b : HilbertBasis ι ℂ h)
    (hb : Summable fun i => ‖T.betaPart (b i)‖ ^ 2) : IsHilbertSchmidt T.betaPart := by
  intro κ c
  have hb' : Summable fun i => ‖CFC.sqrt (ContinuousLinearMap.adjoint T.alphaCLM * T.alphaCLM - 1) (b i)‖ ^ 2 := by
    simpa only [T.norm_sqrt_sq] using hb
  have := hasSum_norm_sq_apply_of_basis b c hb'
  simpa only [T.norm_sqrt_sq] using this.summable

end Lightlike.OperatorAlgebras
