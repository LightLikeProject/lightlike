import Mathlib
import Lightlike.Geometry.HeatKernel.TransportEquations

/-!
# The heat operator on the cut-off ansatz

For a coordinate metric `g` on an open `U ⊆ ℝⁿ`, a smooth world function `σ` with the eikonal equation on `U`,
coefficients `u_k` solving the transport equations to order `N` on `U`, and a smooth cutoff `θ : ℝⁿ → ℝ`, the heat
operator applied to the cut-off ansatz `θ · (4πt)^{-n/2} e^{-σ/4t} Σ_{k≤N} tᵏ u_k` is
(`heatOperator_cutoff_ansatz`)

`θ (4πt)^{-n/2} e^{-σ/4t} t^N Δu_N + (4πt)^{-n/2} (Φ Δθ − 2 g⁻¹(dθ, dΦ))`,   `Φ = e^{-σ/4t} Σ tᵏ u_k`:

the error `t^N Δu_N` of the truncated ansatz (`heatOperator_truncated_ansatz`) times the cutoff, plus terms that
involve only the derivatives of `θ` (`IsCoordMetric.coordLaplacian_mul`). Where `θ ≡ 1` near `y` those terms vanish
(`cutoff_terms_eq_zero_of_eventuallyEq_one`); elsewhere they are small through the Gaussian factor.
-/

open Set Filter Real
open scoped ContDiff Topology

noncomputable section

namespace Lightlike

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- **The heat operator on the cut-off ansatz.** -/
theorem heatOperator_cutoff_ansatz (hg : IsCoordMetric g U) {σ : (Fin n → ℝ) → ℝ} {u : ℕ → (Fin n → ℝ) → ℝ}
    (hσ : ContDiffOn ℝ ∞ σ U) (hu : ∀ k, ContDiffOn ℝ ∞ (u k) U) (heik : ∀ z ∈ U, coordGradPair g σ σ z = 4 * σ z)
    {N : ℕ} (htr : IsTransport g U σ u N) {θ : (Fin n → ℝ) → ℝ} (hθ : ContDiff ℝ ∞ θ) {t : ℝ} (ht : 0 < t)
    {y : Fin n → ℝ} (hy : y ∈ U) :
    ∃ D, HasDerivAt (fun s => θ y * (heatGaussian n (σ y) s * truncAnsatz u N s y)) D t ∧
      D + (4 * π * t) ^ (-(n : ℝ) / 2) *
          coordLaplacian g (fun z => θ z * (gaussFactor t (σ z) * truncAnsatz u N t z)) y =
        θ y * (heatGaussian n (σ y) t * (t ^ N * coordLaplacian g (u N) y)) +
          (4 * π * t) ^ (-(n : ℝ) / 2) *
            (gaussFactor t (σ y) * truncAnsatz u N t y * coordLaplacian g θ y -
              2 * coordGradPair g θ (fun z => gaussFactor t (σ z) * truncAnsatz u N t z) y) := by
  obtain ⟨D, hD, hDeq⟩ := heatOperator_truncated_ansatz hg hσ hu heik htr ht hy
  have hΦ : ContDiffOn ℝ ∞ (fun z => gaussFactor t (σ z) * truncAnsatz u N t z) U :=
    ((contDiff_gaussFactor t).comp_contDiffOn hσ).mul (ContDiffOn.sum fun k _ => contDiffOn_const.mul (hu k))
  refine ⟨θ y * D, hD.const_mul (θ y), ?_⟩
  rw [hg.coordLaplacian_mul hθ.contDiffOn hΦ hy]
  have hDeq' := congrArg (fun z => θ y * z) hDeq
  linear_combination hDeq'

/-- **Where the cutoff is `1` near `y`, its terms vanish**: `Δθ(y) = 0` and `g⁻¹(dθ, dΦ)(y) = 0`. -/
theorem cutoff_terms_eq_zero_of_eventuallyEq_one {θ Φ : (Fin n → ℝ) → ℝ} {y : Fin n → ℝ}
    (h1 : θ =ᶠ[𝓝 y] fun _ => 1) :
    coordLaplacian g θ y = 0 ∧ coordGradPair g θ Φ y = 0 := by
  have hpd : ∀ i, pd i θ y = 0 := fun i => by rw [pd_congr h1 i, pd_const]
  refine ⟨?_, ?_⟩
  · unfold coordLaplacian
    have hflux : ∀ i, coordFlux g θ i =ᶠ[𝓝 y] fun _ => 0 := fun i => by
      have h1' : ∀ᶠ z in 𝓝 y, θ =ᶠ[𝓝 z] fun _ => 1 := h1.eventuallyEq_nhds
      filter_upwards [h1'] with z hz
      simp [coordFlux, pd_congr hz, pd_const]
    simp [pd_congr (hflux _), pd_const]
  · simp [coordGradPair, hpd]

/-- **The cross term of the cutoff, expanded**: `g⁻¹(dθ, d(e^{-σ/4t} U)) = e^{-σ/4t} (g⁻¹(dθ, dU) − U g⁻¹(dθ, dσ)/4t)`. -/
theorem coordGradPair_gauss_mul {θ σ V : (Fin n → ℝ) → ℝ} {y : Fin n → ℝ} (hσ : DifferentiableAt ℝ σ y)
    (hV : DifferentiableAt ℝ V y) (t : ℝ) :
    coordGradPair g θ (fun z => gaussFactor t (σ z) * V z) y =
      gaussFactor t (σ y) * (coordGradPair g θ V y - V y * coordGradPair g θ σ y / (4 * t)) := by
  have he : DifferentiableAt ℝ (fun z => gaussFactor t (σ z)) y :=
    ((contDiff_gaussFactor t).differentiable (by simp) _).comp y hσ
  have hpe : ∀ j, pd j (fun z => gaussFactor t (σ z)) y = -(gaussFactor t (σ y)) / (4 * t) * pd j σ y := by
    intro j
    have h := (hasDerivAt_gaussFactor t (σ y)).comp_hasFDerivAt y hσ.hasFDerivAt
    unfold pd
    show fderiv ℝ (gaussFactor t ∘ σ) y _ = _
    rw [h.fderiv]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hpd : ∀ j, pd j (fun z => gaussFactor t (σ z) * V z) y =
      -(gaussFactor t (σ y)) / (4 * t) * pd j σ y * V y + gaussFactor t (σ y) * pd j V y := by
    intro j
    rw [pd_mul (f₁ := fun z => gaussFactor t (σ z)) (f₂ := V) he hV, hpe]
  unfold coordGradPair
  simp only [hpd, Finset.mul_sum, Finset.sum_div, mul_sub, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Lightlike
