import Lightlike.Regge.Conv3.EdgePoly
import Lightlike.Regge.Geodesic.Tests

/-!
# Trust checks for the jet polynomial of the squared edge length

For the Euclidean metric every derivative of the metric and every Christoffel symbol vanishes, so
`edgePoly` is `|Δ|²` and it reproduces the squared distance exactly (error `0`). A polynomial with
the leading term dropped is a wrong model, and it is rejected by the same check.
-/

open Set Lightlike
open scoped Matrix

namespace Lightlike.Geodesic

variable {n : ℕ}

/-- **Known value.** For the Euclidean metric the jet polynomial is `|Δ|²`. -/
theorem edgePoly_euclid (v s Δ : Fin n → ℝ) : edgePoly euclid v s Δ = eNormSq Δ := by
  obtain ⟨h1, -, -⟩ := euclid_jets_eq_zero v s Δ
  obtain ⟨-, h2, h3⟩ := euclid_jets_eq_zero v s s
  obtain ⟨-, h4, h5⟩ := euclid_jets_eq_zero v Δ Δ
  simp [edgePoly, h1, h2, h4, h5, euclid, eNormSq]

/-- **Trust check (exact).** In the Euclidean case the error of `edge_sq_poly` is exactly `0`. -/
theorem edgePoly_euclid_exact (v w w' : Fin n → ℝ) :
    dist euclid univ (v + w) (v + w') ^ 2 =
      edgePoly euclid v (fun i => (w i + w' i) / 2) (w' - w) := by
  rw [dist_euclid isOpen_univ convex_univ (mem_univ _) (mem_univ _),
    show v + w' - (v + w) = w' - w by abel, Real.sq_sqrt (eNormSq_nonneg _), edgePoly_euclid]

/-- **Wrong-model control.** Dropping the leading term `g_v(Δ, Δ)` from the polynomial gives a
different value from the squared distance whenever the edge is non-degenerate. -/
theorem edgePoly_euclid_wrong {v w w' : Fin n → ℝ} (h : w ≠ w') :
    dist euclid univ (v + w) (v + w') ^ 2 ≠
      edgePoly euclid v (fun i => (w i + w' i) / 2) (w' - w) - (w' - w) ⬝ᵥ (euclid v *ᵥ (w' - w)) := by
  rw [edgePoly_euclid_exact]
  have hne : w' - w ≠ 0 := sub_ne_zero.2 h.symm
  have hpos : 0 < (w' - w) ⬝ᵥ (w' - w) := by
    rcases (dotProduct_self_star_nonneg (v := w' - w)).lt_or_eq with h1 | h1
    · simpa using h1
    · exact absurd (dotProduct_star_self_eq_zero.1 (by simpa using h1.symm)) hne
  simp only [euclid, Matrix.one_mulVec, edgePoly_euclid, eNormSq]
  intro hh
  linarith

end Lightlike.Geodesic
