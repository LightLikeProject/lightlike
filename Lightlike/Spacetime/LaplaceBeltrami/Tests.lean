import Mathlib
import Lightlike.Spacetime.LaplaceBeltrami.Riemannian

/-!
# Tests: the Laplace–Beltrami operator of Minkowski space

On Minkowski space (`Fin n → ℝ` with its single chart, the identity, and `η = diag(-1, 1, …, 1)`) the coordinate formula
`Δ f = -ρ⁻¹ ∂ᵢ(ρ η^{ij} ∂ⱼ f)` with `ρ = 1` gives `Δ (yᵢ²) = -2 ηᵢᵢ`: `-2` for a space coordinate (the sign convention of
the nonnegative Laplacian, `Δ = -div grad`) and `+2` for the time coordinate. A wrong sign convention (`Δ = +div grad`)
would give `+2` on a space coordinate and is caught.
-/

open Set Manifold Matrix
open scoped ContDiff
noncomputable section
namespace Lightlike.LaplaceBeltramiTests

/-- The partial derivatives of `yᵢ²`. -/
theorem coordPartial_sq {n : ℕ} (i : Fin n) (x₀ : Fin n → ℝ) (y : Fin n → ℝ) (j : Fin n) :
    coordPartial x₀ (fun z : Fin n → ℝ => z i ^ 2) y j = if j = i then 2 * y i else 0 := by
  unfold coordPartial
  rw [extChartAt_model_space_eq_id]
  have hd : HasFDerivAt (fun z : Fin n → ℝ => z i ^ 2)
      (y i • (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ) +
        y i • (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)) y := by
    have h2 : (fun z : Fin n → ℝ => z i ^ 2) = fun z => z i * z i := by funext z; ring
    rw [h2]
    exact (hasFDerivAt_apply i y).mul (hasFDerivAt_apply i y)
  have hcomp : ((fun z : Fin n → ℝ => z i ^ 2) ∘ (PartialEquiv.refl (Fin n → ℝ)).symm) =
      fun z : Fin n → ℝ => z i ^ 2 := by
    funext z; simp
  rw [hcomp, hd.fderiv]
  by_cases hji : j = i
  · subst hji; simp; ring
  · simp [Ne.symm hji, hji]

/-- The coordinate metric of Minkowski space as a nondegenerate metric is `η` in its chart. -/
theorem coordMetric_mink {n : ℕ} (x₀ y : Fin n → ℝ) :
    (NondegMetric.ofLorentzian (minkowskiMetric n)).coordMetric x₀ y = eta n := by
  have := congrFun (minkowski_coordMetric (n := n) x₀) y
  exact this

theorem volDensity_mink {n : ℕ} (x₀ y : Fin n → ℝ) :
    (NondegMetric.ofLorentzian (minkowskiMetric n)).volDensity x₀ y = 1 := by
  unfold NondegMetric.volDensity
  rw [coordMetric_mink, eta, Matrix.det_diagonal, Finset.abs_prod]
  have : ∀ i : Fin n, |etaDiag i| = 1 := fun i => by unfold etaDiag; split_ifs <;> simp
  simp [this]

/-- The flux of `yᵢ²` on Minkowski space: `ρ η^{kj} ∂ⱼ(yᵢ²) = 2 ηᵢᵢ yᵢ` for `k = i`, else `0`. -/
theorem lapFlux_sq {n : ℕ} (i : Fin n) (x₀ : Fin n → ℝ) (k : Fin n) :
    (NondegMetric.ofLorentzian (minkowskiMetric n)).lapFlux x₀ (fun z : Fin n → ℝ => z i ^ 2) k =
      fun y => if k = i then 2 * etaDiag i * y i else 0 := by
  funext y
  unfold NondegMetric.lapFlux
  rw [volDensity_mink, coordMetric_mink, eta_inv, one_mul]
  simp only [coordPartial_sq, eta, Matrix.diagonal_apply]
  by_cases hki : k = i
  · subst hki; simp; ring
  · simp [hki]

/-- **Trust check: `Δ(yᵢ²) = -2 ηᵢᵢ` on Minkowski space.** -/
theorem laplaceBeltrami_sq {n : ℕ} (i : Fin n) (x : Fin n → ℝ) :
    (NondegMetric.ofLorentzian (minkowskiMetric n)).laplaceBeltrami (fun z : Fin n → ℝ => z i ^ 2) x =
      -2 * etaDiag i := by
  unfold NondegMetric.laplaceBeltrami NondegMetric.laplaceCoord
  rw [volDensity_mink]
  simp only [lapFlux_sq]
  have hk : ∀ k : Fin n, fderiv ℝ (fun y : Fin n → ℝ => if k = i then 2 * etaDiag i * y i else 0)
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) (Pi.single k 1) = if k = i then 2 * etaDiag i else 0 := by
    intro k
    by_cases hki : k = i
    · subst hki
      simp only [if_true]
      have : HasFDerivAt (fun y : Fin n → ℝ => 2 * etaDiag k * y k)
          ((2 * etaDiag k) • (ContinuousLinearMap.proj k : (Fin n → ℝ) →L[ℝ] ℝ))
          (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) := (hasFDerivAt_apply k _).const_mul _
      rw [this.fderiv]; simp
    · simp [hki]
  simp only [hk, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- On a space coordinate the Laplacian of `y₁²` is `-2` (nonnegative-Laplacian sign convention). -/
example : (NondegMetric.ofLorentzian (minkowskiMetric 2)).laplaceBeltrami (fun z : Fin 2 → ℝ => z 1 ^ 2) 0 = -2 := by
  rw [laplaceBeltrami_sq]; simp [etaDiag]

/-- A wrong sign convention (`Δ = +div grad`, giving `+2` on a space coordinate) is caught. -/
example : (NondegMetric.ofLorentzian (minkowskiMetric 2)).laplaceBeltrami (fun z : Fin 2 → ℝ => z 1 ^ 2) 0 ≠ 2 := by
  rw [laplaceBeltrami_sq]; simp [etaDiag]; norm_num

/-- Non-vacuity of the chart-independence theorem: its hypotheses hold for Minkowski space and `y₀²`. -/
example (x : Fin 2 → ℝ) :
    (NondegMetric.ofLorentzian (minkowskiMetric 2)).laplaceBeltrami (fun z : Fin 2 → ℝ => z 0 ^ 2) x =
      (NondegMetric.ofLorentzian (minkowskiMetric 2)).laplaceCoord 0 (fun z : Fin 2 → ℝ => z 0 ^ 2)
        (extChartAt 𝓘(ℝ, Fin 2 → ℝ) (0 : Fin 2 → ℝ) x) :=
  NondegMetric.laplaceBeltrami_eq_coord _ (by
    have : ContDiff ℝ ∞ (fun z : Fin 2 → ℝ => z 0 ^ 2) := by fun_prop
    exact this.contMDiff) 0 (by simp)

end Lightlike.LaplaceBeltramiTests
