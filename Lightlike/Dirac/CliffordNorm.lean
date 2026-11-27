import Mathlib
import Lightlike.Dirac.Flat

/-!
# A normed-algebra structure on `Cl(ℝⁿ, -‖·‖²)`

The Clifford algebra `Cl(ℝⁿ, -‖·‖²)` is finite-dimensional (it is linearly isomorphic to the
exterior algebra, `CliffordAlgebra.equivExterior`).  Through the injective algebra homomorphism
`Algebra.leftMulMatrix` into the matrices with the `ℓ∞` operator norm it carries a normed-ring and
normed-algebra structure (`clNormedRing`, `clNormedAlgebra`), so that functions with values in
the Clifford algebra (spin lifts of frame changes) can be differentiated.  They are not global
instances: the topology is the unique Hausdorff vector-space topology of a finite-dimensional real
space, but the norm depends on a choice of basis.  Files that differentiate Clifford-valued
functions activate them with `attribute [local instance]`.
-/

open CliffordAlgebra

namespace Lightlike.Dirac

variable {n : ℕ}

/-- The Clifford algebra `Cl(ℝⁿ, -‖·‖²)` is a finite real vector space. -/
instance cl_finite : Module.Finite ℝ (CliffordAlgebra (Qneg n)) := by
  have : Module.Finite ℝ (ExteriorAlgebra ℝ (E n)) :=
    Module.Finite.of_basis ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ExteriorAlgebra)
  exact Module.Finite.equiv (CliffordAlgebra.equivExterior (Qneg n)).symm

/-- A basis of the Clifford algebra (any one; only the induced topology matters). -/
noncomputable def clBasis (n : ℕ) :
    Module.Basis (Fin (Module.finrank ℝ (CliffordAlgebra (Qneg n)))) ℝ (CliffordAlgebra (Qneg n)) :=
  Module.finBasis ℝ _

/-- The normed-ring structure of the Clifford algebra, induced by the left regular representation
in the matrices with the `ℓ∞` operator norm. -/
@[instance_reducible]
noncomputable def clNormedRing (n : ℕ) : NormedRing (CliffordAlgebra (Qneg n)) :=
  letI := @Matrix.linftyOpNormedRing (Fin (Module.finrank ℝ (CliffordAlgebra (Qneg n)))) ℝ _ _ _
  NormedRing.induced (CliffordAlgebra (Qneg n)) _ (Algebra.leftMulMatrix (clBasis n))
    (Algebra.leftMulMatrix_injective (clBasis n))

/-- The normed-algebra structure of the Clifford algebra over `ℝ`. -/
@[instance_reducible]
noncomputable def clNormedAlgebra (n : ℕ) :
    @NormedAlgebra ℝ (CliffordAlgebra (Qneg n)) _ (clNormedRing n).toSeminormedRing :=
  letI := @Matrix.linftyOpNormedRing (Fin (Module.finrank ℝ (CliffordAlgebra (Qneg n)))) ℝ _ _ _
  letI := @Matrix.linftyOpNormedAlgebra ℝ (Fin (Module.finrank ℝ (CliffordAlgebra (Qneg n)))) ℝ
    _ _ _ _
  NormedAlgebra.induced ℝ (CliffordAlgebra (Qneg n)) _ (Algebra.leftMulMatrix (clBasis n))

end Lightlike.Dirac
