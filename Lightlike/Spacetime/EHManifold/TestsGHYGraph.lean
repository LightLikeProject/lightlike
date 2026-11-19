import Lightlike.Spacetime.EHManifold.GHYGraph

/-!
# Tests for the Gibbons–Hawking–York density with a general conormal

* `ghyDensityOf_single`: for the conormal `e_i` of a coordinate hyperplane (with `∂ν = 0`) the general
  density is the coordinate-face density `ghyDensity` of `GibbonsHawkingYork.lean`. This fixes the sign and
  the normalisation of `ghyDensityOf`.
* `graphConormal_zero`: the conormal of the graph of the zero function is `e_i`.

No catalogue entry.
-/

open Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- For the conormal of a coordinate hyperplane the general density is the coordinate-face density. -/
theorem ghyDensityOf_single (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (x : Fin n → ℝ)
    (hii : (g x)⁻¹ i i ≠ 0) :
    ghyDensityOf g (Pi.single i (1 : ℝ)) 0 x = ghyDensity g i x := by
  have hN : ∀ α, ∑ b, (g x)⁻¹ α b * (Pi.single i (1 : ℝ) : Fin n → ℝ) b = (g x)⁻¹ α i := by
    intro α
    simp [Pi.single_apply]
  have hS : ∑ a, (Pi.single i (1 : ℝ) : Fin n → ℝ) a * (g x)⁻¹ a i = (g x)⁻¹ i i := by
    simp [Pi.single_apply]
  have hΓ : ∀ α β, ∑ μ, christoffel g μ α β x * (Pi.single i (1 : ℝ) : Fin n → ℝ) μ =
      christoffel g i α β x := by
    intro α β
    simp [Pi.single_apply]
  have hsq : √|(g x)⁻¹ i i| ≠ 0 := (Real.sqrt_pos.2 (abs_pos.2 hii)).ne'
  have halg : ∀ c s d : ℝ, s ≠ 0 → -(2 * d * c) = 2 * d * s * (-(1 / s) * c) := by
    intro c s d hs
    rw [show 2 * d * s * (-(1 / s) * c) = -(2 * d * c) * (s * (1 / s)) by ring, mul_one_div_cancel hs,
      mul_one]
  unfold ghyDensityOf ghyDensity faceK conormalHup faceHup
  simp only [hN, hS, hΓ, Pi.zero_apply, zero_sub, mul_neg, Finset.sum_neg_distrib]
  exact halg _ _ _ hsq

/-- The conormal of the graph of the zero function is the `i`-th basis covector. -/
theorem graphConormal_zero (i : Fin (n + 1)) (y : Fin n → ℝ) :
    graphConormal (fun _ => (0 : ℝ)) i y = Pi.single i 1 := by
  ext j
  rcases Fin.eq_self_or_eq_succAbove i j with h | ⟨k, h⟩
  · rw [h]
    simp [graphConormal]
  · rw [h]
    simp [graphConormal, pd, Fin.succAbove_ne]

end Lightlike
