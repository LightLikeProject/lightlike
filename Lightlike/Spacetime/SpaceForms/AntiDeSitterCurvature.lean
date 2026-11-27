import Lightlike.Spacetime.QuadricCurvature
import Lightlike.Spacetime.SpaceForms.AntiDeSitterKilling

/-!
# Anti-de Sitter space is maximally symmetric

The whole manifold `antiDeSitterSpace m = S¹ × ℝᵐ` with the metric induced from the quadric
`B(x, x) = -L²` of `ℂ × ℝᵐ` (signature `(2, m)`):

* `hasConstantCurvature_antiDeSitterSpace`: every locally smooth Levi-Civita connection has constant
  curvature `-1/L²`, `R(X, Y) Z = -(1/L²) (g(Y, Z) X - g(X, Z) Y)` at every point
  (`hasConstantCurvature_of_quadric` with `c = -L²`);
* `isMaximallySymmetric_antiDeSitterSpace`: with the `n (n + 1)/2` independent Killing fields of
  `exists_killing_antiDeSitterSpace`, `n = m + 1`, anti-de Sitter space is maximally symmetric with
  `K = -1/L²`.

**Which space (a difference of representation).** The space is the quadric itself, `S¹ × ℝᵐ`, whose
circle is timelike, so it has closed timelike curves.  In general relativity "anti-de Sitter space"
often means its universal cover `ℝ × ℝᵐ`, which is not constructed here.  Maximal symmetry and the
curvature `-1/L²` are proved on the quadric.

**References.** S. M. Carroll, *Spacetime and Geometry* (Addison-Wesley, 2004), section 8.1.
-/

noncomputable section

namespace Lightlike

variable {m : ℕ} {L : ℝ}

/-- **Anti-de Sitter space has constant curvature `-1/L²`** on the whole manifold `S¹ × ℝᵐ`. -/
theorem hasConstantCurvature_antiDeSitterSpace (hL : L ≠ 0) :
    HasConstantCurvature (antiDeSitterSpaceMetric m L hL) (-1 / L ^ 2) := by
  have h := hasConstantCurvature_of_quadric adsSpaceForm_symm (contMDiff_adsIncl (m := m) hL)
    (antiDeSitterSpaceMetric_apply hL) (neg_ne_zero.2 (pow_ne_zero 2 hL)) adsSpaceForm_adsIncl_self
    (dι_adsIncl_injective hL) (exists_dι_adsIncl_eq hL)
  rwa [show (-1 / L ^ 2 : ℝ) = 1 / -L ^ 2 by rw [div_neg, neg_div]]

/-- **Anti-de Sitter space is maximally symmetric**: constant curvature `-1/L²` and `n (n + 1)/2`
linearly independent smooth Killing fields, `n = m + 1` the dimension, on the whole manifold
`S¹ × ℝᵐ` (the quadric, not its universal cover). -/
theorem isMaximallySymmetric_antiDeSitterSpace (hL : L ≠ 0) :
    IsMaximallySymmetric (antiDeSitterSpaceMetric m L hL) (-1 / L ^ 2) :=
  ⟨hasConstantCurvature_antiDeSitterSpace hL, exists_killing_antiDeSitterSpace hL⟩

/-- Non-vacuity: four-dimensional anti-de Sitter space of radius `1` is maximally symmetric with
`K = -1`. -/
example : IsMaximallySymmetric (antiDeSitterSpaceMetric 3 1 one_ne_zero) (-1) := by
  have h := isMaximallySymmetric_antiDeSitterSpace (m := 3) (L := 1) one_ne_zero
  norm_num at h
  exact h

end Lightlike
