import Lightlike.OperatorAlgebras.KMSInfiniteDimensions.KMSDef
import Lightlike.OperatorAlgebras.GibbsKMS

/-!
# The Gibbs state of a diagonal Hamiltonian satisfies the strip KMS condition

Row G1-053.  The Gibbs functional `gibbs b ev β` on `B(H)`, for a Hamiltonian diagonal in a Hilbert
basis `b` with eigenvalues `ev` and summable Boltzmann weights `exp(-β evₙ)`, together with the
Heisenberg flow `dyn b ev`, satisfies the infinite-dimensional KMS condition `IsKMSFunctional`
(Panangaden, Proposition 5.9 and Definition 5.8).  This shows that the notion of
`Lightlike.OperatorAlgebras.KMSInfiniteDimensions.KMSDef` is satisfied by a genuine infinite-dimensional example, with the
witness function supplied by `GibbsKMS.kmsFun`.
-/

open Complex

namespace Lightlike.OperatorAlgebras.KMSInfiniteDimensions

open Lightlike.OperatorAlgebras

variable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The Gibbs state of a diagonal Hamiltonian with summable Boltzmann weights is KMS** at inverse
temperature `β > 0` for its Heisenberg flow, in the strip form `IsKMSFunctional`. -/
theorem isKMSFunctional_gibbs (b : HilbertBasis ι ℂ H) (ev : ι → ℝ) {β : ℝ} (hβ : 0 < β)
    (hZ : Summable fun n => Real.exp (-(β * ev n))) :
    IsKMSFunctional (GibbsKMS.gibbs b ev β) (GibbsKMS.dyn b ev) β := by
  intro A B
  refine ⟨GibbsKMS.kmsFun b ev β A B, ?_, ?_, ?_, ?_, ?_⟩
  · exact GibbsKMS.continuousOn_kmsFun b ev hβ hZ A B
  · exact GibbsKMS.differentiableOn_kmsFun b ev hβ hZ A B
  · exact ⟨_, fun z hz => GibbsKMS.norm_kmsFun_le b ev hβ hZ A B hz⟩
  · intro t
    exact GibbsKMS.kmsFun_ofReal b ev hβ hZ A B t
  · intro t
    exact GibbsKMS.kmsFun_add_I_mul b ev hβ hZ A B t

end Lightlike.OperatorAlgebras.KMSInfiniteDimensions

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_053.isKMSFunctional_gibbs := _root_.Lightlike.OperatorAlgebras.KMSInfiniteDimensions.isKMSFunctional_gibbs
