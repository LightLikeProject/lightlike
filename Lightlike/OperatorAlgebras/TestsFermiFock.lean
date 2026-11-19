import Lightlike.OperatorAlgebras.FermiFockGeneral

/-!
# Checks of the Fock representation of the CAR over a Hilbert space
-/

namespace Lightlike.OperatorAlgebras

open scoped InnerProductSpace

variable {ι : Type*} [LinearOrder ι]
variable {Γ : Type*} [NormedAddCommGroup Γ] [InnerProductSpace ℂ Γ] [CompleteSpace Γ] (B : HilbertBasis (Finset ι) ℂ Γ)

/-- The annihilation operators kill the vacuum. -/
theorem fermiAnn_vacuum (j : ι) : fermiAnn B j (B ∅) = 0 := by
  refine B.repr.injective (lp.ext (funext fun S => ?_))
  rw [repr_fermiAnn_apply, map_zero]
  split_ifs
  · rfl
  · rw [HilbertBasis.repr_self]
    simp [lp.single_apply, Pi.single_apply, Finset.insert_ne_empty]

/-- The creation operator of one mode on the vacuum gives the one-particle vector. -/
example (j : ι) : fermiCre B j (B ∅) = B {j} := by
  rw [fermiCre_basis, if_neg (Finset.notMem_empty j)]
  simp [fermiSign]

variable {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z] (b : HilbertBasis ι ℂ Z)

/-- Theorem 28: the field operators are a representation of the CAR over `Re(Z ⊕ Z̄) ≅ Z`. -/
example (w w' : Z) : fockField B b w * fockField B b w' + fockField B b w' * fockField B b w =
    ((2 * (⟪w, w'⟫_ℂ).re : ℝ) : ℂ) • (1 : Γ →L[ℂ] Γ) :=
  fockField_anticomm B b w w'

/-- Theorem 28: the Fock representation is irreducible. -/
example (W : Submodule ℂ Γ) (hWc : IsClosed (W : Set Γ)) (hW : ∀ w, ∀ x ∈ W, fockField B b w x ∈ W) :
    W = ⊥ ∨ W = ⊤ :=
  fockField_irreducible B b W hWc hW

/-- The model `ℓ²(Finset ι)` with its canonical Hilbert basis. -/
example (W : Submodule ℂ (FermiL2 ι)) (hWc : IsClosed (W : Set (FermiL2 ι)))
    (hW : ∀ w, ∀ x ∈ W, fockField (⟨LinearIsometryEquiv.refl ℂ (FermiL2 ι)⟩ : HilbertBasis (Finset ι) ℂ (FermiL2 ι)) b w x ∈ W) :
    W = ⊥ ∨ W = ⊤ :=
  fockField_irreducible _ b W hWc hW

end Lightlike.OperatorAlgebras
