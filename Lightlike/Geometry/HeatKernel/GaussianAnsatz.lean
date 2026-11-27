import Mathlib
import Lightlike.Spacetime.LaplaceBeltrami.CoordCalculus

/-!
# The Laplacian of the Gaussian ansatz `e^{-σ/4t} u`

For a coordinate metric `g` on an open `U ⊆ ℝⁿ` (any signature), a smooth `σ` on `U` satisfying the eikonal equation
`g⁻¹(dσ, dσ) = 4σ` (the world function of `Lightlike.Geodesic.exists_sqDist_eikonal`), a smooth `u` and `t ≠ 0`,

`Δ(e^{-σ/4t} u) = e^{-σ/4t} (Δu - (Δσ / 4t) u - (σ / 4t²) u + g⁻¹(dσ, du) / 2t)`

(`IsCoordMetric.coordLaplacian_gaussian_mul`), with `Δ = -ρ⁻¹ ∂ᵢ(ρ g^{ij} ∂ⱼ)` the nonnegative Laplacian. The term
`(σ / 4t²) u` is cancelled by the time derivative of `(4πt)^{-n/2} e^{-σ/4t}`
(`hasDerivAt_heatGaussian`: `∂ₜ = (σ/4t² - n/2t)` times it), so that the heat operator `∂ₜ + Δ` applied to
`(4πt)^{-n/2} e^{-σ/4t} u` is `(4πt)^{-n/2} e^{-σ/4t}` times
`∂ₜu + Δu + (1/t) (g⁻¹(dσ, du)/2 - (Δσ/4 + n/2) u)` (`heatOperator_gaussian_ansatz`): the transport equations of the
Minakshisundaram–Pleijel parametrix are the vanishing of the coefficients of the powers of `t` in this expression.

## References

* `rosenberg-1997`: S. Rosenberg, *The Laplacian on a Riemannian Manifold* (1997), §3.2, the computation of
  `(∂ₜ + Δ)` of the parametrix leading to the transport equations. Comparison pending (not read at that location).
-/

open Set Filter Real
open scoped ContDiff Topology

noncomputable section

namespace Lightlike

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- The Gaussian factor `s ↦ e^{-s/4t}`. -/
def gaussFactor (t : ℝ) (s : ℝ) : ℝ := Real.exp (-s / (4 * t))

theorem hasDerivAt_gaussFactor (t s : ℝ) :
    HasDerivAt (gaussFactor t) (-(gaussFactor t s) / (4 * t)) s := by
  have h : HasDerivAt (fun s : ℝ => -s / (4 * t)) (-1 / (4 * t)) s := by
    simpa using ((hasDerivAt_id s).neg).div_const (4 * t)
  have := h.exp
  unfold gaussFactor
  convert this using 1
  ring

theorem deriv_gaussFactor (t : ℝ) : deriv (gaussFactor t) = fun s => -(gaussFactor t s) / (4 * t) :=
  funext fun s => (hasDerivAt_gaussFactor t s).deriv

theorem deriv_deriv_gaussFactor (t : ℝ) :
    deriv (deriv (gaussFactor t)) = fun s => gaussFactor t s / (16 * t ^ 2) := by
  rw [deriv_gaussFactor]
  funext s
  have := ((hasDerivAt_gaussFactor t s).neg).div_const (4 * t)
  rw [show (fun s => -gaussFactor t s / (4 * t)) = fun x => (-gaussFactor t) x / (4 * t) from rfl, this.deriv]
  ring

theorem contDiff_gaussFactor (t : ℝ) : ContDiff ℝ ∞ (gaussFactor t) := by
  unfold gaussFactor
  exact Real.contDiff_exp.comp (contDiff_id.neg.div_const _)

/-- The pairing with the differential of `φ ∘ F`: `g⁻¹(d(φ ∘ F), dH) = φ'(F) g⁻¹(dF, dH)`. -/
theorem IsCoordMetric.coordGradPair_comp_left (hg : IsCoordMetric g U) {F H : (Fin n → ℝ) → ℝ}
    (hF : ContDiffOn ℝ ∞ F U) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) {y : Fin n → ℝ} (hy : y ∈ U) :
    coordGradPair g (fun z => φ (F z)) H y = deriv φ (F y) * coordGradPair g F H y := by
  have hpd : ∀ j, pd j (fun z => φ (F z)) y = deriv φ (F y) * pd j F y := by
    intro j
    unfold pd
    rw [show (fun z => φ (F z)) = φ ∘ F from rfl,
      fderiv_comp y ((hφ.differentiable (by simp)) _) (differentiableAt_of_contDiffOn hF hg.isOpen hy)]
    simp
    ring
  unfold coordGradPair
  simp only [hpd, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **The Laplacian of the Gaussian ansatz**: with the eikonal equation `g⁻¹(dσ, dσ) = 4σ`,
`Δ(e^{-σ/4t} u) = e^{-σ/4t} (Δu - (Δσ/4t) u - (σ/4t²) u + g⁻¹(dσ, du)/2t)`. -/
theorem IsCoordMetric.coordLaplacian_gaussian_mul (hg : IsCoordMetric g U) {σ u : (Fin n → ℝ) → ℝ}
    (hσ : ContDiffOn ℝ ∞ σ U) (hu : ContDiffOn ℝ ∞ u U) (heik : coordGradPair g σ σ = fun y => 4 * σ y)
    {t : ℝ} (ht : t ≠ 0) {y : Fin n → ℝ} (hy : y ∈ U) :
    coordLaplacian g (fun z => gaussFactor t (σ z) * u z) y =
      gaussFactor t (σ y) * (coordLaplacian g u y - coordLaplacian g σ y / (4 * t) * u y -
        σ y / (4 * t ^ 2) * u y + coordGradPair g σ u y / (2 * t)) := by
  have hG : ContDiffOn ℝ ∞ (fun z => gaussFactor t (σ z)) U := (contDiff_gaussFactor t).comp_contDiffOn hσ
  rw [hg.coordLaplacian_mul hG hu hy, hg.coordLaplacian_comp hσ (contDiff_gaussFactor t) hy,
    hg.coordGradPair_comp_left hσ (contDiff_gaussFactor t) hy, deriv_deriv_gaussFactor, deriv_gaussFactor]
  have h4 : coordGradPair g σ σ y = 4 * σ y := congrFun heik y
  simp only [h4]
  field_simp
  ring

/-- The heat Gaussian `(4πt)^{-n/2} e^{-s/4t}` as a function of `t > 0`. -/
def heatGaussian (n : ℕ) (s t : ℝ) : ℝ := (4 * π * t) ^ (-(n : ℝ) / 2) * gaussFactor t s

/-- **The time derivative of the heat Gaussian**: `∂ₜ[(4πt)^{-n/2} e^{-s/4t}] = (s/4t² - n/2t) (4πt)^{-n/2} e^{-s/4t}`. -/
theorem hasDerivAt_heatGaussian (n : ℕ) (s : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (heatGaussian n s) ((s / (4 * t ^ 2) - n / (2 * t)) * heatGaussian n s t) t := by
  have h4 : 0 < 4 * π * t := by positivity
  have hp : HasDerivAt (fun t : ℝ => (4 * π * t) ^ (-(n : ℝ) / 2))
      ((-(n : ℝ) / 2) * (4 * π * t) ^ (-(n : ℝ) / 2 - 1) * (4 * π)) t := by
    have hl : HasDerivAt (fun t : ℝ => 4 * π * t) (4 * π) t := by
      simpa using (hasDerivAt_id t).const_mul (4 * π)
    exact (hl.rpow_const (Or.inl h4.ne')).congr_deriv (by ring)
  have he : HasDerivAt (fun t : ℝ => gaussFactor t s) (s / (4 * t ^ 2) * gaussFactor t s) t := by
    have hq : HasDerivAt (fun t : ℝ => -s / (4 * t)) (s / (4 * t ^ 2)) t := by
      have := ((hasDerivAt_id t).const_mul 4).inv (by positivity : (4 : ℝ) * t ≠ 0)
      convert this.const_mul (-s) using 1
      · funext t; simp [div_eq_mul_inv]
      · simp only [id_eq]; field_simp
    unfold gaussFactor
    convert hq.exp using 1
    ring
  have := hp.mul he
  unfold heatGaussian
  convert this using 1
  rw [Real.rpow_sub h4, Real.rpow_one]
  field_simp
  ring

/-- **The heat operator on the Gaussian ansatz**: for `u(t, y)` smooth in `y`, differentiable in `t` with
`∂ₜu(t, y) = u'`, the eikonal equation and `t > 0`, the time derivative `D` of `(4πt)^{-n/2} e^{-σ(y)/4t} u(t, y)` satisfies
`D + (4πt)^{-n/2} Δ(e^{-σ/4t} u)(y) = (4πt)^{-n/2} e^{-σ/4t} (u' + Δu + (g⁻¹(dσ, du)/2 - (Δσ/4 + n/2) u)/t)`. -/
theorem heatOperator_gaussian_ansatz (hg : IsCoordMetric g U) {σ : (Fin n → ℝ) → ℝ} {u : ℝ → (Fin n → ℝ) → ℝ}
    (hσ : ContDiffOn ℝ ∞ σ U) (hu : ∀ s, ContDiffOn ℝ ∞ (u s) U) (heik : coordGradPair g σ σ = fun y => 4 * σ y)
    {t : ℝ} (ht : 0 < t) {y : Fin n → ℝ} (hy : y ∈ U) {u' : ℝ} (hut : HasDerivAt (fun s => u s y) u' t) :
    ∃ D, HasDerivAt (fun s => heatGaussian n (σ y) s * u s y) D t ∧
      D + (4 * π * t) ^ (-(n : ℝ) / 2) * coordLaplacian g (fun z => gaussFactor t (σ z) * u t z) y =
        heatGaussian n (σ y) t * (u' + coordLaplacian g (u t) y +
          (coordGradPair g σ (u t) y / 2 - (coordLaplacian g σ y / 4 + n / 2) * u t y) / t) := by
  refine ⟨_, (hasDerivAt_heatGaussian n (σ y) ht).mul hut, ?_⟩
  rw [hg.coordLaplacian_gaussian_mul hσ (hu t) heik ht.ne' hy]
  unfold heatGaussian
  field_simp
  ring

end Lightlike
