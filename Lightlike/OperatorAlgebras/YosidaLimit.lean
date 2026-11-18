import Lightlike.OperatorAlgebras.ResolventIdentity
import Lightlike.OperatorAlgebras.BoundedGroup

/-!
# The strong limit of the approximating unitary groups

Helper lemmas for the task `T-OP1-P2` (Stone's theorem, existence). Let `A` be self-adjoint and
`U_n t = exp (i t A_n)` (`BoundedGroup.lean`) with the commuting bounded self-adjoint approximants `A_n`
(`Yosida.lean`). For `x` in the domain, `‖U_n t x - U_m t x‖ ≤ |t| ‖A_n x - A_m x‖`, and `A_n x` converges, so
`U_n t x` is Cauchy; by density and isometry `U_n t y` is Cauchy for every `y`, and its limit is a unitary
group `U t` with `‖U_n t x - U t x‖ ≤ |t| ‖A_n x - A x‖` on the domain.
-/

open scoped InnerProductSpace LinearPMap Topology
open Filter

namespace Lightlike.OperatorAlgebras

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A : H →ₗ.[ℂ] H}

/-- The approximating unitary `U_n t = exp (i t A_n)`. -/
noncomputable def Un (hA : IsSelfAdjoint A) (n : ℕ) (t : ℝ) : H ≃ₗᵢ[ℂ] H :=
  bdUnitary (approx_isSelfAdjoint hA n) t

lemma Un_apply (hA : IsSelfAdjoint A) (n : ℕ) (t : ℝ) (y : H) :
    Un hA n t y = bdU (approx hA n) t y := rfl

/-- **The Cauchy estimate** for the approximating unitaries on the domain. -/
lemma Un_cauchy (hA : IsSelfAdjoint A) (n m : ℕ) (t : ℝ) (x : A.domain) :
    ‖Un hA n t (x : H) - Un hA m t (x : H)‖ ≤ |t| * ‖approx hA n (x : H) - approx hA m (x : H)‖ := by
  have := bdU_cauchy (approx_isSelfAdjoint hA n) (approx_isSelfAdjoint hA m) (approx_commute hA n m) t (x : H)
  simpa [Un_apply] using this

/-- For `x` in the domain, `U_n t x` is a Cauchy sequence. -/
lemma cauchySeq_Un_domain (hA : IsSelfAdjoint A) (t : ℝ) (x : A.domain) :
    CauchySeq fun n => Un hA n t (x : H) := by
  have hc : CauchySeq fun n => approx hA n (x : H) := (approx_tendsto hA x).cauchySeq
  rw [Metric.cauchySeq_iff] at hc ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hc (ε / (|t| + 1)) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have h1 := Un_cauchy hA m n t x
  have h2 : ‖approx hA m (x : H) - approx hA n (x : H)‖ < ε / (|t| + 1) := by
    have := hN m hm n hn
    rwa [dist_eq_norm] at this
  rw [dist_eq_norm]
  calc ‖Un hA m t (x : H) - Un hA n t (x : H)‖ ≤ |t| * ‖approx hA m (x : H) - approx hA n (x : H)‖ := h1
    _ ≤ |t| * (ε / (|t| + 1)) := by gcongr
    _ < ε := by
      rw [mul_div_assoc']
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg t]

end Lightlike.OperatorAlgebras
