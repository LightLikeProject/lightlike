import Lightlike.OperatorAlgebras.VonNeumannClassify
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Von Neumann's theorem with the deficiency indices as Hilbert dimensions

The deficiency spaces of a closed symmetric operator are closed (), hence Hilbert spaces with Hilbert bases.
Bonneau, Faraut and Valent, arXiv:quant-ph/0103153, Section 4, Theorem 1, cases (ii) and (iii), with  read as "the deficiency spaces have
Hilbert bases indexed by the same set":  has a self-adjoint extension iff this holds (). The invariance of the
Hilbert dimension (two Hilbert bases of one space have index sets of the same cardinality) is not needed for the statement and not proved here.
-/

open scoped InnerProductSpace LinearPMap

universe u

namespace Lightlike.OperatorAlgebras

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A : H →ₗ.[ℂ] H}

/-- **A deficiency space is an orthogonal complement**: `N_z = (ran (A - z̄))^⊥`; in particular it is closed. -/
lemma deficiencySpace_eq_orthogonal (hA : ClosedSymm A) (z : ℂ) :
    deficiencySpace A z = (LinearMap.range (shiftMap A ((starRingEnd ℂ) z)))ᗮ := by
  apply le_antisymm
  · intro p hp
    rw [Submodule.mem_orthogonal]
    rintro _ ⟨x, rfl⟩
    have h := inner_deficiency_shift hA (z := (starRingEnd ℂ) z) (by simpa using hp) x
    rw [← inner_conj_symm, h, map_zero]
  · have h := orthogonal_range_le_deficiency hA ((starRingEnd ℂ) z)
    simpa using h

instance [hA : Fact (ClosedSymm A)] (z : ℂ) : CompleteSpace (deficiencySpace A z) := by
  rw [deficiencySpace_eq_orthogonal hA.out z]
  exact (Submodule.isClosed_orthogonal _).completeSpace_coe

/-- **Von Neumann's theorem, case `n₊ = n₋`, existence** (with the deficiency indices as Hilbert dimensions): if `N_i` and `N_{-i}` have Hilbert
bases indexed by sets of the same cardinality, `A` has a self-adjoint extension. -/
theorem exists_selfAdjoint_ext_of_hilbertBasis (hA : ClosedSymm A) {ι κ : Type*}
    (bp : HilbertBasis ι ℂ (deficiencySpace A Complex.I)) (bm : HilbertBasis κ ℂ (deficiencySpace A (-Complex.I)))
    (e : ι ≃ κ) : ∃ B : H →ₗ.[ℂ] H, A ≤ B ∧ IsSelfAdjoint B := by
  have : Fact (ClosedSymm A) := ⟨hA⟩
  let bm' : HilbertBasis ι ℂ (deficiencySpace A (-Complex.I)) :=
    HilbertBasis.mk (v := bm ∘ e) (bm.orthonormal.comp e e.injective)
      (by rw [Set.range_comp, e.range_eq_univ, Set.image_univ, bm.dense_span])
  let U : deficiencySpace A Complex.I ≃ₗᵢ[ℂ] deficiencySpace A (-Complex.I) := bp.repr.trans bm'.repr.symm
  exact ⟨extU A U, le_extU hA, extU_isSelfAdjoint hA⟩

/-- **Von Neumann's theorem, cases `n₊ ≠ n₋` and the converse of existence** (Hilbert dimensions): if `A` has a self-adjoint extension, every
Hilbert basis of `N_i` gives a Hilbert basis of `N_{-i}` with the same index set. -/
theorem hilbertBasis_of_selfAdjoint_ext (hA : ClosedSymm A) {B : H →ₗ.[ℂ] H} (hAB : A ≤ B) (hB : IsSelfAdjoint B)
    {ι : Type*} (bp : HilbertBasis ι ℂ (deficiencySpace A Complex.I)) :
    Nonempty (HilbertBasis ι ℂ (deficiencySpace A (-Complex.I))) :=
  ⟨HilbertBasis.ofRepr ((unitaryOfExt hA hAB hB).symm.trans bp.repr)⟩

/-- **Von Neumann's theorem, cases (ii)/(iii), as an equivalence** (Hilbert dimensions): a closed symmetric densely defined `A` has a self-adjoint
extension iff its deficiency spaces `N_{±i}` have Hilbert bases indexed by the same type. -/
theorem exists_selfAdjoint_ext_iff (hA : ClosedSymm A) :
    (∃ B : H →ₗ.[ℂ] H, A ≤ B ∧ IsSelfAdjoint B) ↔
      ∃ (ι : Type u) (_ : HilbertBasis ι ℂ (deficiencySpace A Complex.I)),
        Nonempty (HilbertBasis ι ℂ (deficiencySpace A (-Complex.I))) := by
  have : Fact (ClosedSymm A) := ⟨hA⟩
  constructor
  · rintro ⟨B, hAB, hB⟩
    obtain ⟨w, bp, -⟩ := exists_hilbertBasis ℂ (deficiencySpace A Complex.I)
    exact ⟨w, bp, hilbertBasis_of_selfAdjoint_ext hA hAB hB bp⟩
  · rintro ⟨ι, bp, ⟨bm⟩⟩
    exact exists_selfAdjoint_ext_of_hilbertBasis hA bp bm (Equiv.refl ι)

end Lightlike.OperatorAlgebras
