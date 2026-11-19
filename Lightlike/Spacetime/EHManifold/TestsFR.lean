import Lightlike.Spacetime.EHManifold.FRParts

/-!
# Tests for the `f(R)` variation

* `fRDensity_id`: for `f(R) = R` the density is the Einstein–Hilbert density without cosmological constant;
* `fR_first_variation_id`: for `f(R) = R`, `fR_first_variation` gives back the Einstein–Hilbert first
  variation `-∫ √|g| (R^{αβ} - ½ R g^{αβ}) h_{αβ}` (the term with `∂ f'(R)` vanishes).

No catalogue entry.
-/

open Matrix Filter Topology MeasureTheory Set Metric
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- **Test:** for `f(R) = R` the `f(R)` density is the Einstein–Hilbert density with `Λ = 0`. -/
theorem fRDensity_id (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (x : Fin n → ℝ) :
    fRDensity g h (fun r => r) t x = lagDensity g h 0 t x := by
  unfold fRDensity lagDensity
  ring

/-- **Test:** for `f(R) = R`, the `f(R)` first variation is the Einstein–Hilbert one. -/
theorem fR_first_variation_id (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
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
  have hmain := fR_first_variation g h hg hh hgs hhs hdet (fun r => r) contDiff_id
    (by rw [hd]; exact contDiff_const) hT hsupp
  have hpd1 : ∀ (ρ : Fin n) (x : Fin n → ℝ), pd ρ (fun _ : Fin n → ℝ => (1 : ℝ)) x = 0 := by
    intro ρ x
    unfold pd
    simp
  simp only [hd, hpd1, mul_zero, Finset.sum_const_zero, integral_zero, sub_zero, one_mul] at hmain
  exact hmain

end Lightlike
