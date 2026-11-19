import Lightlike.OperatorAlgebras.TraceClass.RankOnePairing
import Mathlib.Analysis.PSeries

/-!
# Trust checks for the trace-class layer

Non-vacuity examples for the ported trace-class and Hilbert-Schmidt API (`Lightlike.OperatorAlgebras.TraceClass`): the
hypotheses are satisfiable, and the trace has the expected values on the simplest operators.

Negative control: the identity of an infinite-dimensional Hilbert space is bounded, not compact, and not Hilbert-Schmidt
(`not_isHilbertSchmidt_one`).

Not covered here: the diagonal operator with eigenvalues `1 / n` (Hilbert-Schmidt and not trace class), which needs an
explicit `ℓ²` and a diagonal operator, and a concrete infinite-dimensional space; open checks.
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

/-- **Negative control**: the identity of a Hilbert space that is not finite-dimensional is not Hilbert-Schmidt: in any
Hilbert basis the sum `∑ ‖e_i‖² = ∑ 1` diverges over the infinite index set. -/
theorem not_isHilbertSchmidt_one {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (hinf : ¬ FiniteDimensional ℂ H) : ¬ HilbertSchmidt.IsHilbertSchmidt (1 : H →L[ℂ] H) := by
  intro hHS
  obtain ⟨w, b, hb⟩ := exists_hilbertBasis ℂ H
  have hsum := HilbertSchmidt.summable_norm_sq_apply_of_hilbertBasis w b hHS
  have hnorm : ∀ i : w, ‖(1 : H →L[ℂ] H) (b i)‖ ^ 2 = 1 := fun i => by
    simp [b.orthonormal.1 i]
  simp only [hnorm] at hsum
  have hfin : Finite w := by
    by_contra hw
    have : Infinite w := not_finite_iff_infinite.mp hw
    exact (summable_const_iff (1 : ℝ)).mp hsum |> one_ne_zero
  apply hinf
  have hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range b)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range b)
  have hc : IsClosed (Submodule.span ℂ (Set.range b) : Set H) := Submodule.closed_of_finiteDimensional _
  have hspan : Submodule.span ℂ (Set.range b) = ⊤ := by
    have hd := b.dense_span
    rwa [hc.submodule_topologicalClosure_eq] at hd
  rw [hspan] at hfd
  exact LinearEquiv.finiteDimensional (Submodule.topEquiv (R := ℂ) (M := H))

/-- **The numerical core of the check "the diagonal operator with eigenvalues `1 / n` is Hilbert-Schmidt and not trace class"**:
the squares of the eigenvalues `1 / (n + 1)` are summable, the eigenvalues themselves are not. (The operator form, on an explicit
`ℓ²`, is not in the library yet; in a basis `eₙ` with `D eₙ = (n + 1)⁻¹ eₙ` the first sum is the Hilbert-Schmidt sum and the second
the trace-norm sum.) -/
theorem diag_weights_square_summable_not_summable :
    Summable (fun n : ℕ => (((n : ℝ) + 1)⁻¹) ^ 2) ∧ ¬ Summable (fun n : ℕ => ((n : ℝ) + 1)⁻¹) := by
  constructor
  · have h : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) :=
      (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2))
    simpa [inv_pow, Nat.cast_add] using h
  · intro h
    have h2 : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹) := by simpa [Nat.cast_add] using h
    exact Real.not_summable_natCast_inv ((summable_nat_add_iff 1).mp h2)

end Lightlike.OperatorAlgebras.TraceClass
