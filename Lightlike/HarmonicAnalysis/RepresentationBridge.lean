import Lightlike.HarmonicAnalysis.SchurOrthogonality

/-!
# Unitary matrix representations and Mathlib's `Representation`

`UnitaryMatrixRep.toRepresentation` is the Mathlib `Representation ℂ G (ι → ℂ)` of a unitary matrix
representation, and `UnitaryMatrixRep.isIrreducible_iff_toRepresentation` shows that the irreducibility used in
the Peter–Weyl files (`UnitaryMatrixRep.IsIrreducible`: the index type is nonempty and the only invariant
subspaces are `⊥` and `⊤`) is Mathlib's `Representation.IsIrreducible` (the lattice of subrepresentations is
simple).

Alignment lemmas; no catalogue entry.
-/

namespace Lightlike.HarmonicAnalysis

noncomputable section

namespace UnitaryMatrixRep

variable {G : Type*} [Group G] [TopologicalSpace G] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The Mathlib `Representation` on `ι → ℂ` of a unitary matrix representation. -/
def toRepresentation (ρ : UnitaryMatrixRep G ι) : Representation ℂ G (ι → ℂ) where
  toFun g := Matrix.toLin' (ρ.mat g)
  map_one' := by rw [ρ.mat_one, Matrix.toLin'_one]; rfl
  map_mul' g h := by rw [ρ.mat_mul, Matrix.toLin'_mul]; rfl

lemma toRepresentation_apply (ρ : UnitaryMatrixRep G ι) (g : G) (v : ι → ℂ) :
    ρ.toRepresentation g v = (ρ.mat g).mulVec v := rfl

/-- Irreducibility of a unitary matrix representation is Mathlib's `Representation.IsIrreducible`. -/
theorem isIrreducible_iff_toRepresentation (ρ : UnitaryMatrixRep G ι) :
    ρ.IsIrreducible ↔ ρ.toRepresentation.IsIrreducible := by
  constructor
  · intro h
    haveI := h.1
    haveI : Nontrivial (Subrepresentation ρ.toRepresentation) :=
      ⟨⊥, ⊤, fun hbt => bot_ne_top (congrArg Subrepresentation.toSubmodule hbt)⟩
    refine { eq_bot_or_eq_top := fun W => ?_ }
    rcases h.2 W.toSubmodule (fun g v hv => W.apply_mem_toSubmodule g hv) with h1 | h1
    · exact Or.inl (Subrepresentation.toSubmodule_injective h1)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h1)
  · intro h
    refine ⟨?_, fun W hW => ?_⟩
    · by_contra hne
      rw [not_nonempty_iff] at hne
      have hbt : (⊥ : Subrepresentation ρ.toRepresentation) = ⊤ :=
        Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _)
      exact bot_ne_top hbt
    · rcases h.eq_bot_or_eq_top ⟨W, fun g v hv => hW g v hv⟩ with h1 | h1
      · exact Or.inl (congrArg Subrepresentation.toSubmodule h1)
      · exact Or.inr (congrArg Subrepresentation.toSubmodule h1)

end UnitaryMatrixRep

end

end Lightlike.HarmonicAnalysis
