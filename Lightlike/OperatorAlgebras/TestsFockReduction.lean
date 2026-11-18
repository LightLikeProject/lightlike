import Lightlike.OperatorAlgebras.FockReduction

/-!
# Trust checks for the cyclic-vector reduction

The identity Bogoliubov transformation is implemented (by the identity), and the vector `Ψ = Ω` has the Gaussian
characteristic function `exp (-‖f‖² / 4)`, which is the Fock expectation; so the reduction recovers the trivial
case in both directions.
-/

open scoped InnerProductSpace

universe u

namespace Lightlike.OperatorAlgebras

variable {h : Type u} [NormedAddCommGroup h] [InnerProductSpace ℂ h]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The identity Bogoliubov transformation. -/
def Bogoliubov.id (h : Type u) [NormedAddCommGroup h] [InnerProductSpace ℂ h] : Bogoliubov h where
  toEquiv := ContinuousLinearEquiv.refl ℝ h
  symp_map _ _ := rfl

/-- **Non-vacuity**: the vacuum is the Gaussian vector of the identity transformation, so the identity is
implemented. -/
theorem implements_id (R : FockRep h K) : Implements R.toCCRRep (Bogoliubov.id h) :=
  (implements_iff_gaussian_vector R (Bogoliubov.id h)).2
    ⟨R.Ω, fun f => R.vacuum_expectation f⟩

end Lightlike.OperatorAlgebras
