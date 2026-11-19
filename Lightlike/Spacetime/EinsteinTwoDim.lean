import Lightlike.Spacetime.VariationCritical
import Lightlike.Spacetime.RiemannSymmetry

/-!
# Two dimensions: the Einstein tensor vanishes (GE15 trust check)

For a smooth nondegenerate metric on `ℝ²`, `Ric = ½ R g` (`ricci_two_dim`), so `R^{αβ} - ½ R g^{αβ} = 0` (`einsteinUp_two_dim`) and every
such metric is a critical point of the Einstein-Hilbert action with `Λ = 0` (`isEHCritical_two_dim`): in two dimensions `∫ √g R` is
topological (Gauss-Bonnet), so its variation vanishes. The proof uses only the antisymmetries of the lowered Riemann tensor.

**Limits.** Coordinates on `ℝ²`; the topological invariance itself (the integral over a closed surface) is not proved.
-/

open Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike

section
variable (g : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ) (hg : ∀ a b, ContDiff ℝ ∞ (fun y => g y a b))
    (hgs : ∀ y a b, g y a b = g y b a) (hdet : ∀ x, (g x).det ≠ 0)
include hg hgs hdet

/-- **In two dimensions the Ricci tensor is `½ R g`** for a smooth nondegenerate metric. -/
theorem ricci_two_dim (x : Fin 2 → ℝ) (σ ν : Fin 2) :
    ricci g σ ν x = (1 / 2) * scalarCurvature g x * g x σ ν := by
  have hcm : IsCoordMetric g Set.univ :=
    ⟨isOpen_univ, fun y _ => by ext i j; exact hgs y j i, fun y _ => isUnit_iff_ne_zero.2 (hdet y),
      fun i j => (hg i j).contDiffOn⟩
  set R4 : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ := fun ρ σ μ ν => riemannLower g ρ σ μ ν x with hR4
  have a1 : ∀ ρ σ μ ν, R4 ρ σ μ ν = -R4 σ ρ μ ν := fun ρ σ μ ν => hcm.riemannLower_antisymm_first (Set.mem_univ x) ρ σ μ ν
  have a2 : ∀ ρ σ μ ν, R4 ρ σ μ ν = -R4 ρ σ ν μ := fun ρ σ μ ν => riemannLower_antisymm_last g ρ σ μ ν x
  -- the upper Riemann tensor from the lowered one
  have hG : (g x)⁻¹ * g x = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (hdet x))
  have hg1 : g x * (g x)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hdet x))
  have hT : ((g x)⁻¹)ᵀ = (g x)⁻¹ := by
    have : (g x)ᵀ = g x := by ext i j; exact hgs x j i
    rw [Matrix.transpose_nonsing_inv, this]
  have hGs : ∀ a b, (g x)⁻¹ a b = (g x)⁻¹ b a := by
    intro a b
    simpa [Matrix.transpose_apply] using (congrFun (congrFun hT a) b).symm
  have hup : ∀ ρ σ μ ν, riemann g ρ σ μ ν x = ∑ l, (g x)⁻¹ ρ l * R4 l σ μ ν := by
    intro ρ σ μ ν
    simp only [hR4, riemannLower]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← Finset.sum_mul]
    have : ∀ l, ∑ k, (g x)⁻¹ ρ k * g x k l = if ρ = l then 1 else 0 := by
      intro l
      have := congrFun (congrFun hG ρ) l
      simpa [Matrix.mul_apply, Matrix.one_apply] using this
    simp [this]
  have hGg : ∀ a b, ∑ k, (g x)⁻¹ a k * g x k b = if a = b then 1 else 0 := by
    intro a b
    have := congrFun (congrFun hG a) b
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  have hgG : ∀ a b, ∑ k, g x a k * (g x)⁻¹ k b = if a = b then 1 else 0 := by
    intro a b
    have := congrFun (congrFun hg1 a) b
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  set D : ℝ := R4 0 1 0 1 with hD
  have z00 : ∀ μ ν, R4 0 0 μ ν = 0 := fun μ ν => by have := a1 0 0 μ ν; linarith
  have z11 : ∀ μ ν, R4 1 1 μ ν = 0 := fun μ ν => by have := a1 1 1 μ ν; linarith
  have y0 : ∀ ρ σ, R4 ρ σ 0 0 = 0 := fun ρ σ => by have := a2 ρ σ 0 0; linarith
  have y1 : ∀ ρ σ, R4 ρ σ 1 1 = 0 := fun ρ σ => by have := a2 ρ σ 1 1; linarith
  have c0110 : R4 0 1 1 0 = -D := by have := a2 0 1 0 1; linarith
  have c1001 : R4 1 0 0 1 = -D := by have := a1 0 1 0 1; linarith
  have c1010 : R4 1 0 1 0 = D := by have := a1 0 1 1 0; linarith
  have hric : ∀ σ ν, ricci g σ ν x = ∑ ρ, ∑ l, (g x)⁻¹ ρ l * R4 l σ ρ ν := by
    intro σ ν
    unfold ricci
    exact Finset.sum_congr rfl fun ρ _ => hup ρ σ ρ ν
  have r00 : ricci g 0 0 x = (g x)⁻¹ 1 1 * D := by
    rw [hric]; simp [Fin.sum_univ_two, z00, z11, y0, y1, c1010]
  have r11 : ricci g 1 1 x = (g x)⁻¹ 0 0 * D := by
    rw [hric]; simp [Fin.sum_univ_two, z00, z11, y0, y1, hD]
  have r01 : ricci g 0 1 x = -((g x)⁻¹ 0 1 * D) := by
    rw [hric]; simp [Fin.sum_univ_two, z00, z11, y0, y1, c1001]
  have r10 : ricci g 1 0 x = -((g x)⁻¹ 1 0 * D) := by
    rw [hric]; simp [Fin.sum_univ_two, z00, z11, y0, y1, c0110]
  have hR : scalarCurvature g x = 2 * D * ((g x)⁻¹ 0 0 * (g x)⁻¹ 1 1 - (g x)⁻¹ 0 1 * (g x)⁻¹ 0 1) := by
    unfold scalarCurvature
    simp only [Fin.sum_univ_two, r00, r11, r01, r10]
    rw [hGs 1 0]
    ring
  rw [hR]
  have e00 := hGg 0 0
  have e01 := hGg 0 1
  have e10 := hGg 1 0
  have e11 := hGg 1 1
  simp only [Fin.sum_univ_two, if_true, one_ne_zero, zero_ne_one, if_false] at e00 e01 e10 e11
  have s01 : g x 0 1 = g x 1 0 := hgs x 0 1
  rw [hGs 1 0] at e10 e11
  rw [hGs 1 0] at r10
  fin_cases σ <;> fin_cases ν <;> simp only [Fin.zero_eta, Fin.mk_one, r00, r11, r01, r10]
  · linear_combination (-D * (g x)⁻¹ 1 1) * e00 + (D * (g x)⁻¹ 0 1) * e10
  · linear_combination (-D * (g x)⁻¹ 1 1) * e01 + (D * (g x)⁻¹ 0 1) * e11
  · rw [← s01]
    linear_combination (-D * (g x)⁻¹ 1 1) * e01 + (D * (g x)⁻¹ 0 1) * e11
  · linear_combination (-D * (g x)⁻¹ 0 0) * e11 + (D * (g x)⁻¹ 0 1) * e01


/-- In two dimensions `E^{αβ} = Λ g^{αβ}`: the Einstein tensor vanishes identically. -/
theorem einsteinUp_two_dim (Λ : ℝ) (x : Fin 2 → ℝ) (α β : Fin 2) :
    einsteinUp g Λ x α β = Λ * (g x)⁻¹ α β := by
  have hG : (g x)⁻¹ * g x = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (hdet x))
  have hGg : ∀ a b, ∑ k, (g x)⁻¹ a k * g x k b = if a = b then 1 else 0 := by
    intro a b
    have := congrFun (congrFun hG a) b
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  have hup : ricciUp g x α β = (1 / 2) * scalarCurvature g x * (g x)⁻¹ α β := by
    unfold ricciUp
    simp only [ricci_two_dim g hg hgs hdet x]
    have : ∀ a b, (g x)⁻¹ α a * ((1 / 2) * scalarCurvature g x * g x a b) * (g x)⁻¹ b β =
        ((1 / 2) * scalarCurvature g x) * ((g x)⁻¹ α a * g x a b * (g x)⁻¹ b β) := fun a b => by ring
    simp only [this, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    have h2 : ∀ b, ∑ a, (g x)⁻¹ α a * g x a b * (g x)⁻¹ b β = (if α = b then 1 else 0) * (g x)⁻¹ b β := by
      intro b
      rw [← hGg α b, Finset.sum_mul]
    simp [h2]
  unfold einsteinUp
  rw [hup]; ring

/-- **In two dimensions every smooth nondegenerate metric is a critical point of the Einstein-Hilbert action** (`Λ = 0`):
the variation vanishes (Gauss-Bonnet). -/
theorem isEHCritical_two_dim : IsEHCritical g 0 := by
  refine (isEHCritical_iff g hg hdet hgs 0).2 fun x α β => ?_
  simp [einsteinUp_two_dim g hg hgs hdet]

end

end Lightlike
