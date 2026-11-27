import Mathlib
import Lightlike.Spacetime.RiemannSymmetry

/-!
# The coordinate Laplace–Beltrami operator on an open set of `ℝⁿ`: product and chain rules

For a coordinate metric `g` on an open `U ⊆ ℝⁿ` (`IsCoordMetric`: smooth, symmetric, invertible) with density
`ρ = √|det g|`:

* `coordGradPair g F H = g^{ij} ∂ᵢF ∂ⱼH` (the pairing of the differentials),
* `coordFlux g F i = ρ g^{ij} ∂ⱼF`,
* `coordLaplacian g F = -ρ⁻¹ ∂ᵢ(ρ g^{ij} ∂ⱼF)` (the nonnegative Laplace–Beltrami operator).

## Main results

* `IsCoordMetric.contDiffOn_coordDensity`, `IsCoordMetric.contDiffOn_coordFlux`,
  `IsCoordMetric.contDiffOn_coordLaplacian`: regularity on `U`.
* `IsCoordMetric.coordLaplacian_mul` (**product rule**): `Δ(FH) = F ΔH + H ΔF - 2 g⁻¹(dF, dH)`.
* `IsCoordMetric.coordLaplacian_comp` (**chain rule**): `Δ(φ ∘ F) = φ'(F) ΔF - φ''(F) g⁻¹(dF, dF)`.

These are the identities from which the Minakshisundaram–Pleijel parametrix `(4πt)^{-n/2} e^{-σ/4t} Σ tᵏ uₖ` is computed:
with the eikonal equation `g⁻¹(dσ, dσ) = 4σ` they turn `(∂ₜ + Δ)` of the parametrix into the transport equations.
-/

open Set Filter Matrix
open scoped ContDiff Topology

noncomputable section

namespace Lightlike

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- The density `√|det g|`. -/
def coordDensity (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) : ℝ := √|(g y).det|

/-- `g^{ij} ∂ᵢF ∂ⱼH`. -/
def coordGradPair (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (F H : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, (g y)⁻¹ i j * pd i F y * pd j H y

/-- The flux `ρ g^{ij} ∂ⱼF` (component `i`). -/
def coordFlux (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (F : (Fin n → ℝ) → ℝ) (i : Fin n) (y : Fin n → ℝ) : ℝ :=
  coordDensity g y * ∑ j, (g y)⁻¹ i j * pd j F y

/-- **The coordinate Laplace–Beltrami operator** `-ρ⁻¹ ∂ᵢ(ρ g^{ij} ∂ⱼF)`. -/
def coordLaplacian (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (F : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ) : ℝ :=
  -(coordDensity g y)⁻¹ * ∑ i, pd i (coordFlux g F i) y

theorem IsCoordMetric.coordDensity_pos (hg : IsCoordMetric g U) {y : Fin n → ℝ} (hy : y ∈ U) :
    0 < coordDensity g y :=
  Real.sqrt_pos.2 (abs_pos.2 (hg.isUnit_det y hy).ne_zero)

/-- The density is smooth on `U`. -/
theorem IsCoordMetric.contDiffOn_coordDensity (hg : IsCoordMetric g U) : ContDiffOn ℝ ∞ (coordDensity g) U := by
  intro y hy
  have hd : ContDiffOn ℝ ∞ (fun y => (g y).det) U := contDiffOn_det_of_entries hg.smooth
  have hne : (g y).det ≠ 0 := (hg.isUnit_det y hy).ne_zero
  rcases hne.lt_or_gt with hneg | hpos
  · have hev : coordDensity g =ᶠ[𝓝[U] y] fun z => √(-(g z).det) := by
      filter_upwards [Filter.Tendsto.eventually (hd.continuousOn y hy) (gt_mem_nhds hneg)] with z hz
      unfold coordDensity; rw [abs_of_neg hz]
    refine ContDiffWithinAt.congr_of_eventuallyEq ?_ hev (by unfold coordDensity; rw [abs_of_neg hneg])
    exact ((hd y hy).neg).sqrt (by simpa using hneg.ne)
  · have hev : coordDensity g =ᶠ[𝓝[U] y] fun z => √((g z).det) := by
      filter_upwards [Filter.Tendsto.eventually (hd.continuousOn y hy) (lt_mem_nhds hpos)] with z hz
      unfold coordDensity; rw [abs_of_pos hz]
    refine ContDiffWithinAt.congr_of_eventuallyEq ?_ hev (by unfold coordDensity; rw [abs_of_pos hpos])
    exact (hd y hy).sqrt hpos.ne'

theorem IsCoordMetric.contDiffOn_coordFlux (hg : IsCoordMetric g U) {F : (Fin n → ℝ) → ℝ}
    (hF : ContDiffOn ℝ ∞ F U) (i : Fin n) : ContDiffOn ℝ ∞ (coordFlux g F i) U :=
  hg.contDiffOn_coordDensity.mul (ContDiffOn.sum fun j _ => (hg.contDiffOn_inv i j).mul (contDiffOn_pd hF hg.isOpen j))

theorem IsCoordMetric.contDiffOn_coordLaplacian (hg : IsCoordMetric g U) {F : (Fin n → ℝ) → ℝ}
    (hF : ContDiffOn ℝ ∞ F U) : ContDiffOn ℝ ∞ (coordLaplacian g F) U :=
  ((hg.contDiffOn_coordDensity.inv fun _ hy => (hg.coordDensity_pos hy).ne').neg).mul
    (ContDiffOn.sum fun i _ => contDiffOn_pd (hg.contDiffOn_coordFlux hF i) hg.isOpen i)

theorem IsCoordMetric.contDiffOn_coordGradPair (hg : IsCoordMetric g U) {F H : (Fin n → ℝ) → ℝ}
    (hF : ContDiffOn ℝ ∞ F U) (hH : ContDiffOn ℝ ∞ H U) : ContDiffOn ℝ ∞ (coordGradPair g F H) U :=
  ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ =>
    ((hg.contDiffOn_inv i j).mul (contDiffOn_pd hF hg.isOpen i)).mul (contDiffOn_pd hH hg.isOpen j)

theorem IsCoordMetric.coordGradPair_comm (hg : IsCoordMetric g U) {y : Fin n → ℝ} (hy : y ∈ U)
    (F H : (Fin n → ℝ) → ℝ) : coordGradPair g F H y = coordGradPair g H F y := by
  unfold coordGradPair
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hg.inv_symm hy j i]; ring

/-- **The product rule**: `Δ(FH) = F ΔH + H ΔF - 2 g⁻¹(dF, dH)` on `U`. -/
theorem IsCoordMetric.coordLaplacian_mul (hg : IsCoordMetric g U) {F H : (Fin n → ℝ) → ℝ}
    (hF : ContDiffOn ℝ ∞ F U) (hH : ContDiffOn ℝ ∞ H U) {y : Fin n → ℝ} (hy : y ∈ U) :
    coordLaplacian g (fun z => F z * H z) y =
      F y * coordLaplacian g H y + H y * coordLaplacian g F y - 2 * coordGradPair g F H y := by
  have hU := hg.isOpen
  -- the flux of the product
  have hflux : ∀ i, coordFlux g (fun z => F z * H z) i =ᶠ[𝓝 y]
      fun z => F z * coordFlux g H i z + H z * coordFlux g F i z := by
    intro i
    filter_upwards [hU.mem_nhds hy] with z hz
    unfold coordFlux
    have hpd : ∀ j, pd j (fun z => F z * H z) z = pd j F z * H z + F z * pd j H z := fun j =>
      pd_mul (differentiableAt_of_contDiffOn hF hU hz) (differentiableAt_of_contDiffOn hH hU hz) j
    simp only [hpd, mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hdF := fun i => differentiableAt_of_contDiffOn (hg.contDiffOn_coordFlux hF i) hU hy
  have hdH := fun i => differentiableAt_of_contDiffOn (hg.contDiffOn_coordFlux hH i) hU hy
  have hFd := differentiableAt_of_contDiffOn hF hU hy
  have hHd := differentiableAt_of_contDiffOn hH hU hy
  have hpdflux : ∀ i, pd i (coordFlux g (fun z => F z * H z) i) y =
      (pd i F y * coordFlux g H i y + F y * pd i (coordFlux g H i) y) +
        (pd i H y * coordFlux g F i y + H y * pd i (coordFlux g F i) y) := by
    intro i
    rw [pd_congr (hflux i) i,
      pd_add (f₁ := fun z => F z * coordFlux g H i z) (f₂ := fun z => H z * coordFlux g F i z)
        (hFd.mul (hdH i)) (hHd.mul (hdF i)),
      pd_mul (f₁ := F) (f₂ := coordFlux g H i) hFd (hdH i), pd_mul (f₁ := H) (f₂ := coordFlux g F i) hHd (hdF i)]
  have hρ := (hg.coordDensity_pos hy).ne'
  unfold coordLaplacian
  simp only [hpdflux, Finset.sum_add_distrib]
  unfold coordGradPair coordFlux
  have hsym : ∀ i j, (g y)⁻¹ i j = (g y)⁻¹ j i := hg.inv_symm hy
  have hcross : ∑ i, pd i H y * (coordDensity g y * ∑ j, (g y)⁻¹ i j * pd j F y) =
      coordDensity g y * ∑ i, ∑ j, (g y)⁻¹ i j * pd i F y * pd j H y := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hsym j i]; ring
  have hcross' : ∑ i, pd i F y * (coordDensity g y * ∑ j, (g y)⁻¹ i j * pd j H y) =
      coordDensity g y * ∑ i, ∑ j, (g y)⁻¹ i j * pd i F y * pd j H y := by
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at *
  rw [hcross, hcross']
  field_simp
  ring

/-- **The chain rule**: for `φ : ℝ → ℝ` smooth, `Δ(φ ∘ F) = φ'(F) ΔF - φ''(F) g⁻¹(dF, dF)` on `U`. -/
theorem IsCoordMetric.coordLaplacian_comp (hg : IsCoordMetric g U) {F : (Fin n → ℝ) → ℝ}
    (hF : ContDiffOn ℝ ∞ F U) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) {y : Fin n → ℝ} (hy : y ∈ U) :
    coordLaplacian g (fun z => φ (F z)) y =
      deriv φ (F y) * coordLaplacian g F y - deriv (deriv φ) (F y) * coordGradPair g F F y := by
  have hU := hg.isOpen
  have hφd : ∀ s, DifferentiableAt ℝ φ s := fun s => (hφ.differentiable (by simp)) s
  have hφ'c : ContDiff ℝ ∞ (deriv φ) := hφ.iterate_deriv 1
  have hφ'd : ∀ s, DifferentiableAt ℝ (deriv φ) s := fun s => (hφ'c.differentiable (by simp)) s
  have hpdc : ∀ {z}, z ∈ U → ∀ j, pd j (fun z => φ (F z)) z = deriv φ (F z) * pd j F z := by
    intro z hz j
    unfold pd
    rw [show (fun z => φ (F z)) = φ ∘ F from rfl, fderiv_comp z (hφd _) (differentiableAt_of_contDiffOn hF hU hz)]
    simp <;> ring
  have hflux : ∀ i, coordFlux g (fun z => φ (F z)) i =ᶠ[𝓝 y] fun z => deriv φ (F z) * coordFlux g F i z := by
    intro i
    filter_upwards [hU.mem_nhds hy] with z hz
    unfold coordFlux
    simp only [hpdc hz, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  have hFd := differentiableAt_of_contDiffOn hF hU hy
  have hdF := fun i => differentiableAt_of_contDiffOn (hg.contDiffOn_coordFlux hF i) hU hy
  have hφ'F : DifferentiableAt ℝ (fun z => deriv φ (F z)) y := (hφ'd _).comp y hFd
  have hpdφ' : ∀ i, pd i (fun z => deriv φ (F z)) y = deriv (deriv φ) (F y) * pd i F y := by
    intro i
    unfold pd
    rw [show (fun z => deriv φ (F z)) = deriv φ ∘ F from rfl, fderiv_comp y (hφ'd _) hFd]
    simp <;> ring
  have hρ := (hg.coordDensity_pos hy).ne'
  unfold coordLaplacian
  have hpd : ∀ i, pd i (coordFlux g (fun z => φ (F z)) i) y =
      deriv (deriv φ) (F y) * pd i F y * coordFlux g F i y + deriv φ (F y) * pd i (coordFlux g F i) y := by
    intro i
    rw [pd_congr (hflux i) i, pd_mul (f₁ := fun z => deriv φ (F z)) (f₂ := coordFlux g F i) hφ'F (hdF i), hpdφ']
  simp only [hpd, Finset.sum_add_distrib]
  have hG : ∑ i, deriv (deriv φ) (F y) * pd i F y * coordFlux g F i y =
      coordDensity g y * (deriv (deriv φ) (F y) * coordGradPair g F F y) := by
    unfold coordFlux coordGradPair
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hG, ← Finset.mul_sum]
  field_simp
  ring

end Lightlike
