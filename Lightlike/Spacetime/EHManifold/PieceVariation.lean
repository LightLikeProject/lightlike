import Lightlike.Spacetime.VariationIntegral

/-!
# The variation of the Einstein–Hilbert density integrated over a measurable piece

`eh_variation_piece`: for a smooth nondegenerate symmetric coordinate metric `g`, a smooth symmetric
perturbation `h` (no condition on its support), a compact set `T` and a measurable set `A`,

`d/dt ∫_{T ∩ A} √|g_t| (R(g_t) - 2Λ) = ∫_{T ∩ A} (-√|g| (R^{αβ} - ½ R g^{αβ} + Λ g^{αβ}) h_{αβ} + ∂_ρ (√|g| W^ρ))`

at `t = 0`: the Einstein term plus the divergence of the flux `√|g| W^ρ` of the Palatini identity
(`ehFluxDiv`). For a perturbation supported in `T` the divergence integrates to zero over `T`
(`eh_first_variation`); over a piece it does not.

Supporting lemma for perturbations that are not supported in one chart; no catalogue entry.
-/

open Matrix Filter Topology MeasureTheory Set Metric
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- **The divergence of the Palatini flux** `∂_ρ (√|g| W^ρ)` of a perturbation `h` of a coordinate metric
`g`: the part of the first variation of the Einstein–Hilbert density that is a total derivative. -/
def ehFluxDiv (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ ρ, pd ρ (fun y => √|(g y).det| * Wvec g h ρ y) x

variable (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun y => g y a b)) (hh : ∀ a b, ContDiff ℝ ∞ (fun y => h y a b))
    (hgs : ∀ y a b, g y a b = g y b a) (hhs : ∀ y a b, h y a b = h y b a)
    (hdet : ∀ x, (g x).det ≠ 0)
include hg hh hgs hhs hdet

/-- **The variation of the Einstein–Hilbert density over a measurable piece of a compact set.** -/
theorem eh_variation_piece {T : Set (Fin n → ℝ)} (hT : IsCompact T) (A : Set (Fin n → ℝ)) (Λ : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ x in T, lagDensity g h Λ t x ∂(volume.restrict A))
      (∫ x in T, (-√|(g x).det| * ∑ α, ∑ β, h x α β *
          (ricciUp g x α β - (1 / 2) * scalarCurvature g x * (g x)⁻¹ α β + Λ * (g x)⁻¹ α β) +
        ehFluxDiv g h x) ∂(volume.restrict A)) 0 := by
  have hΦc : ∀ x, ContDiffAt ℝ 1 (fun p : ℝ × (Fin n → ℝ) => lagDensity g h Λ p.1 p.2) (0, x) :=
    fun x => contDiffAt_lagDensity g h hg hh Λ 0 x (by simpa using hdet x)
  have hmain := hasDerivAt_integral_family (μ := (volume : Measure (Fin n → ℝ)).restrict A) hT
    (fun p : ℝ × (Fin n → ℝ) => lagDensity g h Λ p.1 p.2) (fun x _ => hΦc x)
  have hder : ∀ x, fderiv ℝ (fun p : ℝ × (Fin n → ℝ) => lagDensity g h Λ p.1 p.2) (0, x) (1, 0) =
      -√|(g x).det| * ∑ α, ∑ β, h x α β *
          (ricciUp g x α β - (1 / 2) * scalarCurvature g x * (g x)⁻¹ α β + Λ * (g x)⁻¹ α β) +
        ehFluxDiv g h x := by
    intro x
    have h1 := hasDerivAt_lagrangian g h hg hh hgs hhs x (hdet x) Λ
    have h2 : HasDerivAt (fun t : ℝ => lagDensity g h Λ t x)
        (fderiv ℝ (fun p : ℝ × (Fin n → ℝ) => lagDensity g h Λ p.1 p.2) (0, x) (1, 0)) 0 := by
      have hd := ((hΦc x).differentiableAt (by simp)).hasFDerivAt
      have hl : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : Fin n → ℝ)) 0 :=
        (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 x)
      exact hd.comp_hasDerivAt (0 : ℝ) hl
    exact h2.unique h1
  have hint : ∫ x in T, fderiv ℝ (fun p : ℝ × (Fin n → ℝ) => lagDensity g h Λ p.1 p.2) (0, x) (1, 0)
        ∂(volume.restrict A) =
      ∫ x in T, (-√|(g x).det| * ∑ α, ∑ β, h x α β *
          (ricciUp g x α β - (1 / 2) * scalarCurvature g x * (g x)⁻¹ α β + Λ * (g x)⁻¹ α β) +
        ehFluxDiv g h x) ∂(volume.restrict A) :=
    setIntegral_congr_fun hT.isClosed.measurableSet fun x _ => hder x
  rw [hint] at hmain
  exact hmain

end Lightlike
