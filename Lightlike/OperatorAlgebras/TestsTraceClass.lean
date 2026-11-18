import Lightlike.OperatorAlgebras.TraceClass.RankOnePairing

/-!
# Trust checks for the trace-class layer

Non-vacuity examples for the ported trace-class and Hilbert-Schmidt API (`Lightlike.OperatorAlgebras.TraceClass`): the
hypotheses are satisfiable, and the trace has the expected values on the simplest operators.

Not covered here: the diagonal operator with eigenvalues `1 / n` (Hilbert-Schmidt and not trace class) and a bounded
non-compact operator that is not Hilbert-Schmidt; they need an explicit `ℓ²` and are open checks.
-/

open scoped InnerProductSpace

namespace Lightlike.OperatorAlgebras.TraceClass

/-- **The trace of the rank-one operator on `ℂ`**: `tr (|1⟩⟨1|) = ⟪1, 1⟫ = 1`. -/
theorem trace_rankOne_complex_one :
    trace (InnerProductSpace.rankOne ℂ (1 : ℂ) (1 : ℂ)) (TraceClass.isTraceClass_rankOne 1 1) = 1 := by
  simpa using TraceClass.trace_rankOne (1 : ℂ) (1 : ℂ)

/-- **Every operator on a finite-dimensional space is trace class** (non-vacuity of `IsTraceClass`): the identity of `ℂ`. -/
theorem isTraceClass_id_complex : IsTraceClass (1 : ℂ →L[ℂ] ℂ) :=
  isTraceClass_of_finiteDimensional _

/-- **A product of Hilbert-Schmidt operators is trace class**, instantiated at the identity of `ℂ` (which is
Hilbert-Schmidt): the hypotheses of `isTraceClass_mul_of_isHilbertSchmidt` are satisfiable. -/
theorem isTraceClass_one_mul_one : IsTraceClass ((1 : ℂ →L[ℂ] ℂ) * 1) := by
  have h : HilbertSchmidt.IsHilbertSchmidt (1 : ℂ →L[ℂ] ℂ) := by
    obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ ℂ
    haveI : Finite w := b.orthonormal.linearIndependent.finite
    exact ⟨w, b, Summable.of_finite⟩
  exact isTraceClass_mul_of_isHilbertSchmidt h h

end Lightlike.OperatorAlgebras.TraceClass
