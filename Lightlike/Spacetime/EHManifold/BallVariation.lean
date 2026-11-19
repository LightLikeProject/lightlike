import Lightlike.Spacetime.VariationIntegral
import Lightlike.Spacetime.EHManifold.Retraction

/-!
# The first variation of the Einstein–Hilbert action for a metric on a ball

`eh_first_variation_ball`: the first variation formula of `eh_first_variation`
(`Lightlike/Spacetime/VariationIntegral.lean`, for a coordinate metric that is smooth and nondegenerate on
all of `ℝⁿ`) holds for a coordinate metric `g` that is smooth, symmetric and nondegenerate only on a ball
`B(c, φ.rOut)`, for perturbations `h` supported in a compact set `T` inside the smaller ball `B(c, φ.rIn)`:

`d/dt ∫_T √|g + t h| (R(g + t h) - 2Λ) = -∫_T √|g| (R^{αβ} - ½ R g^{αβ} + Λ g^{αβ}) h_{αβ}` at `t = 0`.

`eh_first_variation` is the case of a metric on all of `ℝⁿ`. The proof composes `g` with the retraction
`ballRetract φ` and uses that the curvature at a point depends only on the germ of the metric there.

## References

* S. M. Carroll, *Lecture Notes on General Relativity*, arXiv gr-qc/9712019, chapter 4, eqs. (4.54) to
  (4.67), pp. 114 to 116.
-/

open Filter Topology Metric MeasureTheory
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ} {c : Fin n → ℝ}

/-- **The first variation of the Einstein–Hilbert action for a metric given on a ball.** -/
theorem eh_first_variation_ball (φ : ContDiffBump c)
    (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hg : ∀ a b, ContDiffOn ℝ ∞ (fun y => g y a b) (ball c φ.rOut))
    (hh : ∀ a b, ContDiff ℝ ∞ (fun y => h y a b))
    (hgs : ∀ y ∈ ball c φ.rOut, ∀ a b, g y a b = g y b a) (hhs : ∀ y a b, h y a b = h y b a)
    (hdet : ∀ y ∈ ball c φ.rOut, (g y).det ≠ 0) {T : Set (Fin n → ℝ)} (hT : IsCompact T)
    (hTball : T ⊆ ball c φ.rIn) (hsupp : ∀ a b, tsupport (fun y => h y a b) ⊆ T) (Λ : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ x in T, lagDensity g h Λ t x)
      (-∫ x in T, √|(g x).det| * ∑ α, ∑ β, h x α β *
          (ricciUp g x α β - (1 / 2) * scalarCurvature g x * (g x)⁻¹ α β + Λ * (g x)⁻¹ α β)) 0 := by
  obtain ⟨gt, hgt⟩ : ∃ gt : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ,
      gt = fun y => g (ballRetract φ y) := ⟨_, rfl⟩
  have hsm : ∀ a b, ContDiff ℝ ∞ (fun y => gt y a b) := by
    intro a b
    rw [hgt]
    exact contDiff_comp_ballRetract φ hg a b
  have hsym : ∀ y a b, gt y a b = gt y b a := by
    intro y a b
    rw [hgt]
    exact hgs _ (ballRetract_mem φ y) a b
  have hdt : ∀ y, (gt y).det ≠ 0 := by
    intro y
    rw [hgt]
    exact hdet _ (ballRetract_mem φ y)
  have hmain := eh_first_variation gt h hsm hh hsym hhs hdt hT hsupp Λ
  have hev : ∀ x ∈ T, gt =ᶠ[𝓝 x] g := by
    intro x hx
    rw [hgt]
    exact eventuallyEq_comp_ballRetract φ g (hTball hx)
  have hlag : ∀ t : ℝ, ∫ x in T, lagDensity gt h Λ t x = ∫ x in T, lagDensity g h Λ t x := by
    intro t
    refine setIntegral_congr_fun hT.measurableSet fun x hx => ?_
    have he : (fun z => gt z + t • h z) =ᶠ[𝓝 x] fun z => g z + t • h z :=
      (hev x hx).mono fun z hz => by
        show gt z + t • h z = g z + t • h z
        rw [hz]
    show √|(gt x + t • h x).det| * (scalarCurvature (fun z => gt z + t • h z) x - 2 * Λ) =
      √|(g x + t • h x).det| * (scalarCurvature (fun z => g z + t • h z) x - 2 * Λ)
    rw [scalarCurvature_congr he, (hev x hx).eq_of_nhds]
  have hrhs : ∫ x in T, √|(gt x).det| * ∑ α, ∑ β, h x α β *
        (ricciUp gt x α β - (1 / 2) * scalarCurvature gt x * (gt x)⁻¹ α β + Λ * (gt x)⁻¹ α β) =
      ∫ x in T, √|(g x).det| * ∑ α, ∑ β, h x α β *
        (ricciUp g x α β - (1 / 2) * scalarCurvature g x * (g x)⁻¹ α β + Λ * (g x)⁻¹ α β) := by
    refine setIntegral_congr_fun hT.measurableSet fun x hx => ?_
    have hx0 : gt x = g x := (hev x hx).eq_of_nhds
    have hric : ∀ a b, ricci gt a b x = ricci g a b x := fun a b => ricci_congr (hev x hx) a b
    simp only [ricciUp, hx0, hric, scalarCurvature_congr (hev x hx)]
  simp_rw [hlag] at hmain
  rw [hrhs] at hmain
  exact hmain

end Lightlike
