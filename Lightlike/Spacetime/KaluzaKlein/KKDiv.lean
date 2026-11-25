import Lightlike.Spacetime.KaluzaKlein.KKTrace
import Lightlike.Spacetime.KaluzaKlein.KKRicciRef
import Lightlike.Spacetime.ConformalRicci
import Lightlike.Spacetime.VariationInverse

/-!
# The covariant divergence of a gradient (G1-044)

For a coordinate metric `g` and a function `φ`, the covariant divergence of the vector `gradU g φ` is the wave
operator: `Σ_c (∂_c Gᶜ + Γᶜ_{cl} Gˡ) = □φ` (`div_gradU`), with `Gᶜ = gᶜᵈ ∂_d φ`.

Supporting file for the row G1-044 (Kaluza-Klein reduction).
-/

open Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike

namespace KK

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {φ : (Fin n → ℝ) → ℝ} {U : Set (Fin n → ℝ)}
  {p : Fin n → ℝ}

/-- **The covariant divergence of the gradient is the wave operator.** -/
theorem div_gradU (hg : IsCoordMetric g U) (hgs : ∀ y a b, g y a b = g y b a) (hφ : ContDiffOn ℝ ∞ φ U)
    (hp : p ∈ U) :
    ∑ c, (pd c (gradU g φ c) p + ∑ l, christoffel g c c l p * gradU g φ l p) = boxC g φ p := by
  have hdp : ∀ d, DifferentiableAt ℝ (fun y => pd d φ y) p := fun d =>
    differentiableAt_of_contDiffOn (contDiffOn_pd hφ hg.isOpen d) hg.isOpen hp
  have hdi : ∀ a d, DifferentiableAt ℝ (fun y => (g y)⁻¹ a d) p := fun a d =>
    differentiableAt_of_contDiffOn (hg.contDiffOn_inv a d) hg.isOpen hp
  have hdg : ∀ a b, DifferentiableAt ℝ (fun y => g y a b) p := fun a b =>
    differentiableAt_of_contDiffOn (hg.smooth a b) hg.isOpen hp
  have hdet : (g p).det ≠ 0 := (hg.isUnit_det p hp).ne_zero
  have h1 : ∀ c, pd c (gradU g φ c) p = ∑ d, ((-∑ α, (christoffel g c c α p * (g p)⁻¹ α d +
      christoffel g d c α p * (g p)⁻¹ c α)) * pd d φ p + (g p)⁻¹ c d * pd c (fun y => pd d φ y) p) := fun c => by
    unfold gradU
    rw [pd_sum Finset.univ (f := fun d y => (g y)⁻¹ c d * pd d φ y) (fun d _ => (hdi c d).mul (hdp d)) c]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [pd_mul (hdi c d) (hdp d) c, pd_inv_eq g p hgs hdg hdet]
  have Ta : ∑ c, ∑ d, (∑ α, christoffel g c c α p * (g p)⁻¹ α d) * pd d φ p =
      ∑ c, ∑ l, christoffel g c c l p * gradU g φ l p := by
    refine Finset.sum_congr rfl fun c _ => ?_
    unfold gradU
    simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
  have Tb : ∑ c, ∑ d, (∑ α, christoffel g d c α p * (g p)⁻¹ c α) * pd d φ p =
      ∑ k, ∑ b, (g p)⁻¹ k b * ∑ e, christoffel g e k b p * pd e φ p := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun d _ => by ring
  have hS : ∀ c, pd c (gradU g φ c) p = ∑ d, (-(∑ α, christoffel g c c α p * (g p)⁻¹ α d) * pd d φ p) +
      ∑ d, (-(∑ α, christoffel g d c α p * (g p)⁻¹ c α) * pd d φ p) + ∑ d, (g p)⁻¹ c d * pd c (fun y => pd d φ y) p :=
    fun c => by
    rw [h1 c, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.sum_add_distrib]
    ring
  unfold boxC hessC
  simp only [mul_sub, Finset.sum_sub_distrib, hS, neg_mul, Finset.sum_neg_distrib, Finset.sum_add_distrib, Ta, Tb]
  ring

end KK

end Lightlike
