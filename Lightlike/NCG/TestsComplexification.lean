import Lightlike.NCG.Complexification

/-!
# Tests for the complexification

* `selfComplexification`: a complex-linear triple over `⊕ Mₙᵢ(ℂ)` is its own complexification (`σ = π`, `φ = id`);
* `exists_unitary_self`: for it, `Complexification.exists_unitary` is the uniqueness theorem for complex summands.
-/

namespace Lightlike.NCG.TestsComplexification

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
variable {T : FiniteSpectralTriple (MatSum n) H}

/-- A complex-linear `π`, as a complex `*`-homomorphism. -/
noncomputable def piC (hℂ : IsComplexLinear T) : MatSum n →⋆ₐ[ℂ] (H →L[ℂ] H) where
  toFun := T.π
  map_one' := map_one T.π
  map_mul' := map_mul T.π
  map_zero' := map_zero T.π
  map_add' := map_add T.π
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, hℂ, map_one, Algebra.algebraMap_eq_smul_one]
  map_star' := map_star T.π

/-- **A complex-linear triple is its own complexification.** -/
noncomputable def selfComplexification (hℂ : IsComplexLinear T) : Complexification T n where
  σ := piC hℂ
  injective_σ := T.injective_π
  φ := StarAlgHom.id ℝ (MatSum n)
  pi_eq _ := rfl
  mem_span a := Submodule.subset_span ⟨a, rfl⟩

/-- **For a complex-linear triple the real-algebra uniqueness theorem is the complex one**: a unitary onto the model of
the multiplicity matrix, intertwining `π` and `J`. -/
theorem exists_unitary_self [∀ i, NeZero (n i)] (R : RealStructure T) (hℂ : IsComplexLinear T) :
    ∃ U : H ≃ₗᵢ[ℂ] HK n (fun i j => multiplicity ((selfComplexification hℂ).realStructure R) i j),
      (∀ a x, U (T.π a x) = piK a (U x)) ∧
        ∀ x, U (R.J x) = JK (multiplicity_symm ((selfComplexification hℂ).realStructure R)) (U x) :=
  (selfComplexification hℂ).exists_unitary R

end Lightlike.NCG.TestsComplexification
