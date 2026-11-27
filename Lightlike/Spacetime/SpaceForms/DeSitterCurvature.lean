import Lightlike.Spacetime.QuadricCurvature
import Lightlike.Spacetime.SpaceForms.DeSitterKilling

/-!
# De Sitter space is maximally symmetric

The whole manifold `deSitterSpace m = ℝ × Sᵐ` with the metric induced from the hyperboloid `η(x, x) = L²` of the
Minkowski space `ℝ × ℝ^{m+1}`:

* `hasConstantCurvature_deSitterSpace`: every locally smooth Levi-Civita connection has constant curvature `1/L²`,
  `R(X, Y) Z = (1/L²) (g(Y, Z) X - g(X, Z) Y)` at every point (`hasConstantCurvature_of_quadric` with `c = L²`);
* `isMaximallySymmetric_deSitterSpace`: with the `n (n + 1)/2` independent Killing fields of
  `exists_killing_deSitterSpace`, `n = m + 1`, de Sitter space is maximally symmetric with `K = 1/L²`.

**References.** S. M. Carroll, *Spacetime and Geometry* (Addison-Wesley, 2004), section 8.1.
-/

noncomputable section

namespace Lightlike

variable {m : ℕ} {L : ℝ}

/-- **De Sitter space has constant curvature `1/L²`** on the whole manifold `ℝ × Sᵐ`. -/
theorem hasConstantCurvature_deSitterSpace (hL : L ≠ 0) :
    HasConstantCurvature (deSitterSpaceMetric m L hL) (1 / L ^ 2) :=
  hasConstantCurvature_of_quadric dSForm_symm (contMDiff_dSIncl L) (deSitterSpaceMetric_apply hL)
    (pow_ne_zero 2 hL) (dSForm_dSIncl_self L) (dι_dSIncl_injective hL) (exists_dι_dSIncl_eq hL)

/-- **De Sitter space is maximally symmetric**: constant curvature `1/L²` and `n (n + 1)/2` linearly independent smooth
Killing fields, `n = m + 1` the dimension, on the whole manifold `ℝ × Sᵐ`. -/
theorem isMaximallySymmetric_deSitterSpace (hL : L ≠ 0) :
    IsMaximallySymmetric (deSitterSpaceMetric m L hL) (1 / L ^ 2) :=
  ⟨hasConstantCurvature_deSitterSpace hL, exists_killing_deSitterSpace hL⟩

end Lightlike
