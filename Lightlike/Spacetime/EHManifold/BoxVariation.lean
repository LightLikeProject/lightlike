import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Lightlike.Spacetime.VariationCritical
import Lightlike.Spacetime.EHManifold.PieceVariation

/-!
# The variation of the Einstein–Hilbert action over a coordinate box, with its boundary term

`eh_variation_box`: for a smooth nondegenerate symmetric coordinate metric `g` on `ℝⁿ⁺¹`, a smooth symmetric
perturbation `h` (no condition on its support or on its values at the boundary) and a box `[a, b]`,

`d/dt ∫_{[a,b]} √|g_t| (R(g_t) - 2Λ) = -∫_{[a,b]} √|g| (R^{αβ} - ½ R g^{αβ} + Λ g^{αβ}) h_{αβ}
  + ∑_i (∫_{face x^i = b_i} √|g| W^i - ∫_{face x^i = a_i} √|g| W^i)` at `t = 0`,

with `W^ρ = g^{σν} δΓ^ρ_{σν} - g^{ρσ} δΓ^κ_{κσ}` (`Wvec`). The sum over the faces is the boundary term: the
flux of `√|g| W` through the boundary of the box (the divergence theorem for boxes of Mathlib).

This is the variation (4.2) of Dyer–Hinterbichler without the Gibbons–Hawking–York term, on a coordinate box
and with the boundary integrand written as `√|g| W^ρ n_ρ`; its reduction to `-√|h| h^{αβ} n^μ ∂_μ δg_{αβ}`
when the perturbation vanishes on the boundary is not proved here.

## References

* E. Dyer, K. Hinterbichler, *Boundary Terms, Variational Principles and Higher Derivative Modified Gravity*,
  arXiv:0809.4033, section 4, eq. (4.2), p. 20.
-/

open Matrix Filter Topology MeasureTheory Set Metric
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- **The flux `√|g| W^ρ`** of the Palatini identity: its divergence is the total-derivative part of the
first variation of the Einstein–Hilbert density. -/
def ehFlux (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (ρ : Fin n) (y : Fin n → ℝ) : ℝ :=
  √|(g y).det| * Wvec g h ρ y

variable (g h : (Fin (n + 1) → ℝ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun y => g y a b)) (hh : ∀ a b, ContDiff ℝ ∞ (fun y => h y a b))
    (hgs : ∀ y a b, g y a b = g y b a) (hhs : ∀ y a b, h y a b = h y b a)
    (hdet : ∀ x, (g x).det ≠ 0)
include hg hh hgs hhs hdet

/-- **The variation of the Einstein–Hilbert action over a coordinate box, with the boundary term.** -/
theorem eh_variation_box (a b : Fin (n + 1) → ℝ) (hle : a ≤ b) (Λ : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ x in Icc a b, lagDensity g h Λ t x)
      ((-∫ x in Icc a b, √|(g x).det| * ∑ α, ∑ β, h x α β * einsteinUp g Λ x α β) +
        ∑ i : Fin (n + 1),
          ((∫ y in Icc (a ∘ Fin.succAbove i) (b ∘ Fin.succAbove i),
              ehFlux g h i (Fin.insertNth i (b i) y)) -
            ∫ y in Icc (a ∘ Fin.succAbove i) (b ∘ Fin.succAbove i),
              ehFlux g h i (Fin.insertNth i (a i) y))) 0 := by
  have hT : IsCompact (Icc a b) := isCompact_Icc
  have hmain := eh_variation_piece g h hg hh hgs hhs hdet hT univ Λ
  simp only [Measure.restrict_univ] at hmain
  have hFs : ∀ ρ, ContDiff ℝ ∞ (ehFlux g h ρ) := fun ρ => contDiff_flux g h hg hh hdet ρ
  -- the two parts are continuous, hence integrable on the box
  have hGc : Continuous g := continuous_matrix fun i j => (hg i j).continuous
  have hbulk : Continuous (fun x => -√|(g x).det| * ∑ α, ∑ β, h x α β * einsteinUp g Λ x α β) :=
    ((Real.continuous_sqrt.comp (continuous_abs.comp hGc.matrix_det)).neg).mul
      (continuous_finsetSum _ fun α _ => continuous_finsetSum _ fun β _ =>
        (hh α β).continuous.mul (contDiff_einsteinUp g hg hdet hgs Λ α β).continuous)
  have hdivc : Continuous (ehFluxDiv g h) := by
    unfold ehFluxDiv
    exact continuous_finsetSum _ fun ρ _ => (contDiff_pd (hFs ρ) ρ).continuous
  have hsplit : ∫ x in Icc a b, (-√|(g x).det| * ∑ α, ∑ β, h x α β *
        (ricciUp g x α β - (1 / 2) * scalarCurvature g x * (g x)⁻¹ α β + Λ * (g x)⁻¹ α β) +
        ehFluxDiv g h x) =
      (-∫ x in Icc a b, √|(g x).det| * ∑ α, ∑ β, h x α β * einsteinUp g Λ x α β) +
        ∫ x in Icc a b, ehFluxDiv g h x := by
    rw [← integral_neg]
    have e := integral_add (hbulk.continuousOn.integrableOn_compact hT)
      (hdivc.continuousOn.integrableOn_compact hT)
    rw [← e]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show _ = -(√|(g x).det| * ∑ α, ∑ β, h x α β * einsteinUp g Λ x α β) + ehFluxDiv g h x
    unfold einsteinUp
    ring
  -- the divergence theorem on the box
  have hdiv : ∫ x in Icc a b, ehFluxDiv g h x =
      ∑ i : Fin (n + 1),
        ((∫ y in Icc (a ∘ Fin.succAbove i) (b ∘ Fin.succAbove i),
            ehFlux g h i (Fin.insertNth i (b i) y)) -
          ∫ y in Icc (a ∘ Fin.succAbove i) (b ∘ Fin.succAbove i),
            ehFlux g h i (Fin.insertNth i (a i) y)) := by
    have key := integral_divergence_of_hasFDerivAt_off_countable' a b hle (ehFlux g h)
      (fun i x => fderiv ℝ (ehFlux g h i) x) ∅ countable_empty
      (fun i => (hFs i).continuous.continuousOn)
      (fun x _ i => ((hFs i).differentiable (by simp)).differentiableAt.hasFDerivAt)
      (by
        have : (fun x => ∑ i, fderiv ℝ (ehFlux g h i) x (Pi.single i 1)) = ehFluxDiv g h := rfl
        rw [this]
        exact hdivc.continuousOn.integrableOn_compact hT)
    exact key
  rw [hsplit, hdiv] at hmain
  exact hmain

end Lightlike
