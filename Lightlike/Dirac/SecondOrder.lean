import Mathlib
import Lightlike.Dirac.Flat

/-!
# The second-order identity behind the Weitzenböck formula

For any array `a i j` of vectors in a Clifford module, the double sum `∑ᵢⱼ γᵢγⱼ aᵢⱼ` splits into
the "rough Laplacian" part `-∑ᵢ aᵢᵢ` and the antisymmetric part `½ ∑ᵢⱼ γᵢγⱼ (aᵢⱼ - aⱼᵢ)`. Applied to
`aᵢⱼ = ∇ᵢ∇ⱼ f` it expresses `D² = -∑ᵢ ∇ᵢ∇ᵢ + ½ ∑ᵢⱼ γᵢγⱼ [∇ᵢ, ∇ⱼ]`, where the commutator is the
curvature of the spinor connection. This is pure Clifford algebra: no derivative is involved.

## References

* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators* (1992), chapter
  "Clifford Modules and Dirac Operators" (source key `bgv-1992`); definitions only, no equation
  number is claimed.
-/

namespace Lightlike.Dirac

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- `γᵢγⱼ aᵢⱼ + γⱼγᵢ aᵢⱼ = -2 δᵢⱼ aᵢᵢ`. -/
lemma gam_pair_symm (ρ : CliffordRep n V) (i j : Fin n) (v : V) :
    gam ρ i (gam ρ j v) + gam ρ j (gam ρ i v) = if i = j then (-2 : ℝ) • v else 0 := by
  by_cases h : i = j
  · subst h
    simp [gam_sq, two_smul]
  · simp only [h, ↓reduceIte]
    exact gam_anticomm ρ h v

/-- Splitting of the Clifford double sum: `∑ᵢⱼ γᵢγⱼ aᵢⱼ = -∑ᵢ aᵢᵢ + ½ ∑ᵢⱼ γᵢγⱼ (aᵢⱼ - aⱼᵢ)`. -/
theorem clifford_double_sum (ρ : CliffordRep n V) (a : Fin n → Fin n → V) :
    ∑ i, ∑ j, gam ρ i (gam ρ j (a i j)) =
      -∑ i, a i i + (1 / 2 : ℝ) • ∑ i, ∑ j, gam ρ i (gam ρ j (a i j - a j i)) := by
  have hS2 : ∑ i, ∑ j, gam ρ i (gam ρ j (a j i)) = ∑ i, ∑ j, gam ρ j (gam ρ i (a i j)) :=
    Finset.sum_comm
  have hsum : ∑ i, ∑ j, gam ρ i (gam ρ j (a i j)) + ∑ i, ∑ j, gam ρ i (gam ρ j (a j i)) =
      (-2 : ℝ) • ∑ i, a i i := by
    rw [hS2, ← Finset.sum_add_distrib]
    simp only [← Finset.sum_add_distrib, gam_pair_symm]
    simp [Finset.smul_sum]
  have hsub : ∑ i, ∑ j, gam ρ i (gam ρ j (a i j - a j i)) =
      ∑ i, ∑ j, gam ρ i (gam ρ j (a i j)) - ∑ i, ∑ j, gam ρ i (gam ρ j (a j i)) := by
    simp only [map_sub, Finset.sum_sub_distrib]
  rw [hsub]
  set S1 := ∑ i, ∑ j, gam ρ i (gam ρ j (a i j))
  set S2 := ∑ i, ∑ j, gam ρ i (gam ρ j (a j i))
  set T := ∑ i, a i i
  have : S2 = (-2 : ℝ) • T - S1 := eq_sub_of_add_eq' hsum
  rw [this]
  module

end Lightlike.Dirac
