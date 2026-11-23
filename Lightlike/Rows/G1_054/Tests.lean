import Lightlike.Rows.G1_054.Failure
import Lightlike.Rows.G1_054.SubspaceUnique

/-!
# Tests for row G1-054

Sanity checks: the model-level KMS statement `kms_model` applies to the Gaussian vector, while the
wrong-rate flow fails.
-/

open scoped Real

namespace Lightlike.Rows.G1_054

/-- The Gaussian is an instance of `kms_model`: KMS relation at `β = 2π` on the boundary lines. -/
example : ∀ t : ℝ, laplace (matrixDensity gaussXi gaussXi) (-(2 * π * Complex.I * t) - 2 * π)
    = (starRingEnd ℂ) (laplace (matrixDensity gaussXi gaussXi) (-(2 * π * Complex.I * t))) :=
  (kms_model gaussXi_memLp gaussXi_memLp gaussXi_bwRel gaussXi_bwRel).2.2

/-- The same vector fails the relation at rate `2`. -/
example : ¬ ∀ t : ℝ, laplace (matrixDensity gaussXi gaussXi) (-(2 * π * Complex.I * t) - 2 * π * 2)
    = (starRingEnd ℂ) (laplace (matrixDensity gaussXi gaussXi) (-(2 * π * Complex.I * t))) := by
  have := gauss_not_kms_rate 2 (by norm_num) (by norm_num)
  simpa using this

#check @ModularPair.ext_of_subspace
#check @kms_model
#check @gauss_not_kms_rate

end Lightlike.Rows.G1_054
