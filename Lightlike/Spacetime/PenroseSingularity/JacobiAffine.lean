import Lightlike.Spacetime.PenroseSingularity.FamilyPoint
import Lightlike.Spacetime.PenroseSingularity.IndexForm

/-!
# Combinations of Jacobi fields (G1-012, step D4)

Sums and constant multiples of Jacobi fields are Jacobi fields, and so are `(a + b t) w` for a geodesic with
velocity `w`: along a geodesic `w` and `t w` are Jacobi fields.
-/

open Set Filter Topology

noncomputable section

namespace Lightlike.Penrose

open Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

theorem riemannApply_add_right (x w J K : Fin n → ℝ) :
    riemannApply g x w (J + K) = riemannApply g x w J + riemannApply g x w K := by
  funext i
  simp only [riemannApply, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem riemannApply_smul_right (x w J : Fin n → ℝ) (c : ℝ) :
    riemannApply g x w (c • J) = c • riemannApply g x w J := by
  funext i
  simp only [riemannApply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => by ring

theorem gammaApply_smul_right (x v u : Fin n → ℝ) (c : ℝ) :
    gammaApply g x v (c • u) = c • gammaApply g x v u := by
  funext i
  simp only [gammaApply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem gammaApply_zero_right (x v : Fin n → ℝ) : gammaApply g x v (0 : Fin n → ℝ) = 0 := by
  funext i; simp [gammaApply]

/-- The sum of two Jacobi fields is a Jacobi field. -/
theorem IsJacobiOn.add {γ w J₁ P₁ J₂ P₂ : ℝ → Fin n → ℝ} {I : Set ℝ} (h₁ : IsJacobiOn g γ w J₁ P₁ I)
    (h₂ : IsJacobiOn g γ w J₂ P₂ I) : IsJacobiOn g γ w (J₁ + J₂) (P₁ + P₂) I where
  geodesic := h₁.geodesic
  deriv_field t ht := by
    have := (h₁.deriv_field t ht).add (h₂.deriv_field t ht)
    refine this.congr_deriv ?_
    simp only [Pi.add_apply, gammaApply_add_right]
    abel
  deriv_cov t ht := by
    have := (h₁.deriv_cov t ht).add (h₂.deriv_cov t ht)
    refine this.congr_deriv ?_
    simp only [Pi.add_apply, gammaApply_add_right, riemannApply_add_right]
    abel

/-- A constant multiple of a Jacobi field is a Jacobi field. -/
theorem IsJacobiOn.smul {γ w J P : ℝ → Fin n → ℝ} {I : Set ℝ} (h : IsJacobiOn g γ w J P I) (c : ℝ) :
    IsJacobiOn g γ w (c • J) (c • P) I where
  geodesic := h.geodesic
  deriv_field t ht := by
    have := (h.deriv_field t ht).const_smul c
    refine this.congr_deriv ?_
    simp [gammaApply_smul_right, smul_sub]
  deriv_cov t ht := by
    have := (h.deriv_cov t ht).const_smul c
    refine this.congr_deriv ?_
    simp [gammaApply_smul_right, riemannApply_smul_right, smul_sub, smul_neg]

/-- `R(w, w) w = 0`. -/
theorem riemannApply_self (x w : Fin n → ℝ) : riemannApply g x w w = 0 := by
  funext i
  simp only [riemannApply, Pi.zero_apply]
  refine Finset.sum_eq_zero fun σ _ => ?_
  have h := sum_antisymm_symm (f := fun μ ν => Lightlike.riemann g i σ μ ν x) (c := fun μ ν => w μ * w ν)
    (fun μ ν => Lightlike.riemann_antisymm_last g i σ μ ν x) (fun μ ν => mul_comm _ _)
  calc ∑ μ, ∑ ν, Lightlike.riemann g i σ μ ν x * w σ * w μ * w ν
      = w σ * ∑ μ, ∑ ν, Lightlike.riemann g i σ μ ν x * (w μ * w ν) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ν _ => ?_
        ring
    _ = 0 := by rw [h]; ring

/-- **`(a + b t) w` is a Jacobi field along a geodesic with velocity `w`**, with covariant derivative `b w`. -/
theorem IsJacobiOn.affine_w {γ w : ℝ → Fin n → ℝ} {I : Set ℝ} (hγ : IsGeodesicOn g γ w I) (a b : ℝ) :
    IsJacobiOn g γ w (fun t => (a + b * t) • w t) (fun t => b • w t) I where
  geodesic := hγ
  deriv_field t ht := by
    have h1 : HasDerivAt (fun t : ℝ => a + b * t) b t := by
      simpa using ((hasDerivAt_id t).const_mul b).const_add a
    have := h1.smul (hγ.vel t ht)
    refine this.congr_deriv ?_
    rw [accel_eq_neg_gammaApply, gammaApply_smul_right]
    simp only [smul_neg, smul_sub]
    abel
  deriv_cov t ht := by
    have := (hγ.vel t ht).const_smul b
    refine this.congr_deriv ?_
    rw [accel_eq_neg_gammaApply, riemannApply_smul_right, riemannApply_self, gammaApply_smul_right]
    simp

end Lightlike.Penrose
