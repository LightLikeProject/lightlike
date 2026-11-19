import Lightlike.Spacetime.EHManifold.FRHessianForm

/-!
# Tests for the Hessian form of the `f(R)` first variation

* `covHessUp_const`, `dalembertian_const`: the covariant Hessian and the d'Alembertian of a constant vanish;
* `fR_field_equation_variation_id`: for `f(R) = R` the field-equation form of the variation is the
  Einstein–Hilbert first variation (the Hessian terms drop out because `f' = 1`).

No catalogue entry.
-/

open MeasureTheory Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- The covariant Hessian of a constant vanishes. -/
theorem covHessUp_const (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (a b : Fin n)
    (x : Fin n → ℝ) : covHessUp g (fun _ => c) a b x = 0 := by
  have h0 : ∀ (μ : Fin n) (y : Fin n → ℝ), pd μ (fun _ : Fin n → ℝ => c) y = 0 := fun μ y => by
    simp [pd]
  have hz : ∀ α : Fin n, pd α (fun _ : Fin n → ℝ => (0 : ℝ)) x = 0 := fun α => by simp [pd]
  simp [covHessUp, h0, hz]

/-- The d'Alembertian of a constant vanishes. -/
theorem dalembertian_const (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (x : Fin n → ℝ) :
    dalembertian g (fun _ => c) x = 0 := by
  have h0 : ∀ (μ : Fin n) (y : Fin n → ℝ), pd μ (fun _ : Fin n → ℝ => c) y = 0 := fun μ y => by
    simp [pd]
  have hz : ∀ α : Fin n, pd α (fun _ : Fin n → ℝ => (0 : ℝ)) x = 0 := fun α => by simp [pd]
  simp [dalembertian, h0, hz]

/-- For `f(R) = R` the field-equation form gives the Einstein–Hilbert first variation. -/
theorem fR_field_equation_variation_id (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun y => g y a b)) (hh : ∀ a b, ContDiff ℝ ∞ (fun y => h y a b))
    (hgs : ∀ y a b, g y a b = g y b a) (hhs : ∀ y a b, h y a b = h y b a)
    (hdet : ∀ x, (g x).det ≠ 0) {T : Set (Fin n → ℝ)} (hT : IsCompact T)
    (hsupp : ∀ a b, tsupport (fun y => h y a b) ⊆ T) :
    HasDerivAt (fun t : ℝ => ∫ x in T, fRDensity g h (fun r => r) t x)
      (-∫ x in T, √|(g x).det| * ∑ α, ∑ β, h x α β *
          (ricciUp g x α β - (1 / 2) * scalarCurvature g x * (g x)⁻¹ α β)) 0 := by
  have hd : deriv (fun r : ℝ => r) = fun _ => (1 : ℝ) := by
    funext r
    simp
  have hmain := fR_field_equation_variation g h hg hh hgs hhs hdet (fun r => r) contDiff_id
    (by rw [hd]; exact contDiff_const) hT hsupp
  simp only [hd, covHessUp_const, dalembertian_const, mul_zero, sub_zero, Finset.sum_const_zero,
    integral_zero, add_zero, one_mul] at hmain
  exact hmain

end Lightlike
