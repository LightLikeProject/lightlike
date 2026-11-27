import Mathlib
import Lightlike.Spacetime.LaplaceBeltrami.CoordCalculus
import Lightlike.Spacetime.VariationDet
import Lightlike.Canonical.DensityDeriv
import Lightlike.Regge.Conv3.JetCurvature
import Lightlike.Geometry.HeatKernel.PartialJets

/-!
# Jacobi's formula for the coordinate density

For a coordinate metric `g` on an open `U` (any signature), the partial derivatives of the density `ρ = √|det g|` are
`∂ᵢρ = ρ · ½ tr(g⁻¹ ∂ᵢg)` at every point of `U` (`IsCoordMetric.pd_coordDensity`): the chain rule through the derivative
along lines (`Canonical.pd_comp_line`) and Jacobi's formula along a line (`hasDerivAt_sqrt_abs_det_add_smul`). With it, the coordinate Laplacian takes its non-divergence form
(`IsCoordMetric.coordLaplacian_eq_sum`), whose terms can be differentiated with the Leibniz rule of `PartialJets`.
-/

open Set Filter
open scoped ContDiff Topology

noncomputable section

namespace Lightlike

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- **Jacobi's formula for the density**: `∂ᵢ √|det g| = √|det g| · ½ tr(g⁻¹ ∂ᵢg)` on `U`. -/
theorem IsCoordMetric.pd_coordDensity (hg : IsCoordMetric g U) {y : Fin n → ℝ} (hy : y ∈ U) (i : Fin n) :
    pd i (coordDensity g) y =
      coordDensity g y * ((1 / 2) * ((g y)⁻¹ * Matrix.of fun k l => pd i (fun z => g z k l) y).trace) := by
  set F : (Fin n → Fin n → ℝ) → ℝ := fun M => √|(Matrix.of M).det| with hFdef
  set z : Fin n → Fin n → ℝ := fun k l => g y k l with hz
  have hdet : (Matrix.of z).det ≠ 0 := (hg.isUnit_det y hy).ne_zero
  have hdd : DifferentiableAt ℝ (fun M : Fin n → Fin n → ℝ => (Matrix.of M).det) z :=
    differentiableAt_det_of (f := fun M : Fin n → Fin n → ℝ => Matrix.of M) fun a b => by simp only [Matrix.of_apply]; fun_prop
  have hF : DifferentiableAt ℝ F z := (hdd.abs hdet).sqrt (abs_ne_zero.2 hdet)
  set D : (Fin n → Fin n → ℝ) → ℝ := fun v => (1 / 2) * √|(Matrix.of z).det| * ((Matrix.of z)⁻¹ * Matrix.of v).trace
    with hDdef
  have hD : ∀ v, HasDerivAt (fun t : ℝ => F (z + t • v)) (D v) 0 := fun v =>
    hasDerivAt_sqrt_abs_det_add_smul (Matrix.of z) (Matrix.of v) hdet
  set G : (Fin n → ℝ) → (Fin n → Fin n → ℝ) := fun w k l => g w k l with hGdef
  have hent : ∀ k l, DifferentiableAt ℝ (fun w => g w k l) y := fun k l =>
    ((hg.smooth k l).contDiffAt (hg.isOpen.mem_nhds hy)).differentiableAt (by simp)
  have hGd : HasFDerivAt G (ContinuousLinearMap.pi fun k => ContinuousLinearMap.pi fun l =>
      fderiv ℝ (fun w => g w k l) y) y :=
    hasFDerivAt_pi.2 fun k => hasFDerivAt_pi.2 fun l => (hent k l).hasFDerivAt
  have key := Canonical.pd_comp_line F hF D hD G hGd.differentiableAt rfl i
  have hl : (fun w => F (G w)) = coordDensity g := rfl
  rw [hl] at key
  rw [key, hGd.fderiv]
  simp only [hDdef, coordDensity]
  ring_nf
  rfl

/-- **The coordinate Laplacian in non-divergence form**:
`Δf = -Σᵢ ((∂ᵢρ/ρ) Σⱼ g^{ij} ∂ⱼf + Σⱼ (∂ᵢg^{ij} ∂ⱼf + g^{ij} ∂ᵢ∂ⱼf))` at a point of `U`, for `f` smooth on `U`. -/
theorem IsCoordMetric.coordLaplacian_eq_sum (hg : IsCoordMetric g U) {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) {y : Fin n → ℝ} (hy : y ∈ U) :
    coordLaplacian g f y = -∑ i, (pd i (coordDensity g) y / coordDensity g y * ∑ j, (g y)⁻¹ i j * pd j f y +
      ∑ j, (pd i (fun z => (g z)⁻¹ i j) y * pd j f y + (g y)⁻¹ i j * pd i (pd j f) y)) := by
  have hU := hg.isOpen.mem_nhds hy
  have hρ : DifferentiableAt ℝ (coordDensity g) y :=
    (hg.contDiffOn_coordDensity.contDiffAt hU).differentiableAt (by simp)
  have hH : ∀ i j, DifferentiableAt ℝ (fun z => (g z)⁻¹ i j) y := fun i j =>
    ((Regge.Conv3.cdo_inv g hg i j).contDiffAt hU).differentiableAt (by simp)
  have hfj : ∀ j, DifferentiableAt ℝ (pd j f) y := fun j =>
    ((contDiffOn_pd hf hg.isOpen j).contDiffAt hU).differentiableAt (by simp)
  have hρ0 : coordDensity g y ≠ 0 := (hg.coordDensity_pos hy).ne'
  unfold coordLaplacian coordFlux
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsum : DifferentiableAt ℝ (fun z => ∑ j, (g z)⁻¹ i j * pd j f z) y :=
    DifferentiableAt.fun_sum fun j _ => (hH i j).mul (hfj j)
  rw [pd_mul' i hρ hsum]
  have hps : pd i (fun z => ∑ j, (g z)⁻¹ i j * pd j f z) y =
      ∑ j, (pd i (fun z => (g z)⁻¹ i j) y * pd j f y + (g y)⁻¹ i j * pd i (pd j f) y) := by
    rw [Regge.Conv3.pd_sum Finset.univ (f := fun j z => (g z)⁻¹ i j * pd j f z) i
      (fun j _ => (hH i j).mul (hfj j))]
    exact Finset.sum_congr rfl fun j _ => pd_mul' i (hH i j) (hfj j)
  rw [hps]
  field_simp

end Lightlike
