import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Compact operators on a Hilbert space are norm limits of finite-rank operators

For a compact operator `K` of a complex Hilbert space and `ε > 0` there is an operator `F` of finite rank with
`‖K - F‖ ≤ ε` (`exists_finiteRank_approx`): cover the compact closure of the image of the unit ball by finitely many `ε`-balls, and
let `P` be the orthogonal projection onto the span of their centres; `F = P K`. First step towards the duality between the compact
operators and the trace class (`T-OP6-P1`).
-/

open Metric

namespace Lightlike.OperatorAlgebras

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Finite-rank approximation of a compact operator** (norm): `K - P K` is small, `P` the orthogonal projection onto the span
of an `ε`-net of the image of the unit ball. -/
theorem exists_finiteRank_approx (K : H →L[ℂ] H) (hK : IsCompactOperator K) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : H →L[ℂ] H, FiniteDimensional ℂ (LinearMap.range (F : H →ₗ[ℂ] H)) ∧ ‖K - F‖ ≤ ε := by
  have hS := hK.isCompact_closure_image_closedBall 1
  obtain ⟨t, hts, htfin, hcov⟩ := hS.finite_cover_balls hε
  let U : Submodule ℂ H := Submodule.span ℂ t
  haveI : FiniteDimensional ℂ U := FiniteDimensional.span_of_finite ℂ htfin
  let P : H →L[ℂ] H := U.starProjection
  refine ⟨P.comp K, ?_, ?_⟩
  · refine Submodule.finiteDimensional_of_le (S₂ := U) ?_
    rintro _ ⟨x, rfl⟩
    exact U.starProjection_apply_mem (K x)
  · refine ContinuousLinearMap.opNorm_le_of_unit_norm hε.le fun x hx => ?_
    have hxK : K x ∈ closure (K '' closedBall (0 : H) 1) :=
      subset_closure ⟨x, by simp [hx], rfl⟩
    obtain ⟨y, hyt, hy⟩ := Set.mem_iUnion₂.mp (hcov hxK)
    have hyU : y ∈ U := Submodule.subset_span hyt
    have hmin := U.starProjection_minimal (K x)
    have : ‖K x - U.starProjection (K x)‖ ≤ ‖K x - y‖ := by
      rw [hmin]; exact ciInf_le (f := fun w : U => ‖K x - w‖) ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩ (⟨y, hyU⟩ : U)
    calc ‖(K - P.comp K) x‖ = ‖K x - U.starProjection (K x)‖ := by simp [P]
      _ ≤ ‖K x - y‖ := this
      _ ≤ ε := by rw [← dist_eq_norm]; exact (mem_ball.mp hy).le

end Lightlike.OperatorAlgebras
