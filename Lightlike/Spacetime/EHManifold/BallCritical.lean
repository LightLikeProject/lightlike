import Lightlike.Spacetime.VariationCritical
import Lightlike.Spacetime.EHManifold.BallVariation

/-!
# The vacuum Einstein equations make the first variation vanish, on a ball

`eh_first_variation_ball_eq_zero`: for a coordinate metric `g` that is smooth, symmetric and nondegenerate on
a ball, if the symmetric part of `R^{αβ} - ½ R g^{αβ} + Λ g^{αβ}` (`einsteinUp g Λ`) vanishes on a compact set
`T` in the smaller concentric ball, then the first variation of the Einstein–Hilbert action over `T` vanishes
for every smooth symmetric perturbation supported in `T`.

This is the direction "Einstein equations ⟹ critical" of `isEHCritical_iff`, for a metric given on a ball.
The converse (a local form of the fundamental lemma) is not proved here.

## References

* S. M. Carroll, *Lecture Notes on General Relativity*, arXiv gr-qc/9712019, chapter 4, eqs. (4.66) and
  (4.67), p. 116.
-/

open Filter Topology Metric MeasureTheory
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ} {c : Fin n → ℝ}

/-- **Solutions of the vacuum Einstein equations are critical**, for a metric given on a ball and
perturbations supported in a compact set of the smaller ball. -/
theorem eh_first_variation_ball_eq_zero (φ : ContDiffBump c)
    (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hg : ∀ a b, ContDiffOn ℝ ∞ (fun y => g y a b) (ball c φ.rOut))
    (hh : ∀ a b, ContDiff ℝ ∞ (fun y => h y a b))
    (hgs : ∀ y ∈ ball c φ.rOut, ∀ a b, g y a b = g y b a) (hhs : ∀ y a b, h y a b = h y b a)
    (hdet : ∀ y ∈ ball c φ.rOut, (g y).det ≠ 0) {T : Set (Fin n → ℝ)} (hT : IsCompact T)
    (hTball : T ⊆ ball c φ.rIn) (hsupp : ∀ a b, tsupport (fun y => h y a b) ⊆ T) (Λ : ℝ)
    (hE : ∀ x ∈ T, ∀ α β, einsteinUp g Λ x α β + einsteinUp g Λ x β α = 0) :
    HasDerivAt (fun t : ℝ => ∫ x in T, lagDensity g h Λ t x) 0 0 := by
  have hmain := eh_first_variation_ball φ g h hg hh hgs hhs hdet hT hTball hsupp Λ
  have hz : ∀ x ∈ T, ∑ α, ∑ β, h x α β *
      (ricciUp g x α β - (1 / 2) * scalarCurvature g x * (g x)⁻¹ α β + Λ * (g x)⁻¹ α β) = 0 := by
    intro x hx
    have hsw : ∑ α, ∑ β, h x α β * einsteinUp g Λ x α β =
        ∑ α, ∑ β, h x α β * einsteinUp g Λ x β α := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
      rw [hhs x β α]
    have h2 : ∑ α, ∑ β, h x α β * einsteinUp g Λ x α β +
        ∑ α, ∑ β, h x α β * einsteinUp g Λ x β α = 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun α _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun β _ => ?_
      rw [← mul_add, hE x hx α β, mul_zero]
    have h3 : ∑ α, ∑ β, h x α β * einsteinUp g Λ x α β = 0 := by
      rw [← hsw] at h2
      linarith
    exact h3
  have hint : ∫ x in T, √|(g x).det| * ∑ α, ∑ β, h x α β *
      (ricciUp g x α β - (1 / 2) * scalarCurvature g x * (g x)⁻¹ α β + Λ * (g x)⁻¹ α β) = 0 := by
    rw [setIntegral_congr_fun hT.measurableSet (g := fun _ => (0 : ℝ)) fun x hx => by
      show √|(g x).det| * ∑ α, ∑ β, h x α β *
        (ricciUp g x α β - (1 / 2) * scalarCurvature g x * (g x)⁻¹ α β + Λ * (g x)⁻¹ α β) = 0
      rw [hz x hx, mul_zero]]
    simp
  rw [hint, neg_zero] at hmain
  exact hmain

end Lightlike
