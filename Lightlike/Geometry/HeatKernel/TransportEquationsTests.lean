import Mathlib
import Lightlike.Geometry.HeatKernel.TransportEquations
import Lightlike.Geometry.HeatKernel.GaussianAnsatzTests

/-!
# Tests: the transport equations on the line

On the line with `σ = y²`, the coefficients `u₀ = 1`, `u_k = 0` (`k ≥ 1`) solve the transport equations to every order
(`isTransport_free`), so `Lightlike.heatOperator_truncated_ansatz` applies (non-vacuity) and its right side
`t^N Δu_N` is `0`: the free heat kernel `(4πt)^{-1/2} e^{-y²/4t}` solves the heat equation exactly. A wrong first
coefficient (`u₀ = 2`, `u₁ = 1`) violates the transport equation of order `1` (`1 + 2·... ≠ 0`): caught.
-/

open Set
open scoped ContDiff
noncomputable section
namespace Lightlike.TransportEquationsTests

open Lightlike.LaplaceBeltramiTests Lightlike.GaussianAnsatzTests

/-- The coefficients of the free heat kernel: `u₀ = 1`, `u_k = 0` for `k ≥ 1`. -/
def uFree : ℕ → (Fin 1 → ℝ) → ℝ := fun k _ => if k = 0 then 1 else 0

theorem coordLaplacian_const (c : ℝ) (y : Fin 1 → ℝ) : coordLaplacian gLine (fun _ => c) y = 0 := by
  have hflux : ∀ i, coordFlux gLine (fun _ => c) i = fun _ => 0 := fun i => by
    funext z; simp [coordFlux, pd_const]
  simp [coordLaplacian, hflux, pd_const]

theorem uFree_const (k : ℕ) : uFree k = fun _ => uFree k 0 := funext fun _ => rfl

/-- **The free coefficients solve the transport equations** to every order. -/
theorem isTransport_free (N : ℕ) : IsTransport gLine univ σLine uFree N := by
  intro k _ y _
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h := transport_free y
    have hu0 : uFree 0 = fun _ => 1 := funext fun _ => by simp [uFree]
    rw [hu0]
    simp only [if_true, CharP.cast_eq_zero, zero_sub, neg_zero]
    linear_combination h
  · have hk0 : k ≠ 0 := hk.ne'
    have hu : uFree k = fun _ => 0 := funext fun _ => by simp [uFree, hk0]
    rw [hu, uFree_const (k - 1), coordLaplacian_const]
    simp [hk0, coordGradPair, pd_const]

/-- Non-vacuity, and the free heat kernel solves the heat equation: the right side `t^N Δu_N` vanishes. -/
example (N : ℕ) {t : ℝ} (ht : 0 < t) (y : Fin 1 → ℝ) :
    ∃ D, HasDerivAt (fun s => heatGaussian 1 (σLine y) s * truncAnsatz uFree N s y) D t ∧
      D + (4 * Real.pi * t) ^ (-((1 : ℕ) : ℝ) / 2) *
          coordLaplacian gLine (fun z => gaussFactor t (σLine z) * truncAnsatz uFree N t z) y = 0 := by
  obtain ⟨D, hD, hDeq⟩ := heatOperator_truncated_ansatz isCoordMetric_gLine
    ((contDiff_apply ℝ (fun _ : Fin 1 => ℝ) 0).mul (contDiff_apply ℝ (fun _ : Fin 1 => ℝ) 0)).contDiffOn
    (fun k => contDiffOn_const) (fun z _ => congrFun eikonal_σLine z) (isTransport_free N) ht (mem_univ y)
  refine ⟨D, hD, hDeq.trans ?_⟩
  rw [coordLaplacian_const]
  ring

/-- A wrong pair `u₀ = 2`, `u₁ = 1` violates the transport equation of order `1`, whose left side is
`0 + (1 - 0) · 1 = 1` while its right side is `-Δu₀ = 0`: caught. -/
example : (0 : ℝ) / 2 + ((1 : ℕ) - ((-2 : ℝ) / 4 + (1 : ℕ) / 2)) * 1 ≠ -0 := by norm_num

end Lightlike.TransportEquationsTests
