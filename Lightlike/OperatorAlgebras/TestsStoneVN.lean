import Lightlike.OperatorAlgebras.StoneVN

/-!
# Checks of the Stone-von Neumann theorem
-/

namespace Lightlike.OperatorAlgebras

open MeasureTheory

attribute [local instance] InnerProductSpace.complexToReal

variable {h : Type*} [NormedAddCommGroup h] [InnerProductSpace ℂ h] [FiniteDimensional ℂ h]
  [MeasurableSpace h] [BorelSpace h]

/-- The Fock representation is irreducible, so its multiplicity space `ran P₀` is one-dimensional. -/
example : Module.finrank ℂ (vnRange (fockRepOf h).toCCRRep) = 1 := by
  haveI : Nontrivial (FockSpace h) :=
    ⟨⟨(fockRepOf h).Ω, 0, fun h0 => by simpa [h0] using (fockRepOf h).norm_Ω⟩⟩
  refine (isIrreducible_iff_finrank_vnRange _).mp ?_
  intro W hWc hW
  by_cases hb : W = ⊥
  · exact Or.inl hb
  · right
    obtain ⟨ψ, hψW, hψ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
    have hcyc := fockRep_cyclic (fockRepOf h) hψ0
    rw [eq_top_iff, ← hcyc]
    exact Submodule.topologicalClosure_minimal _
      (Submodule.span_le.mpr (by rintro _ ⟨f, rfl⟩; exact hW f ψ hψW)) hWc

/-- Every representation on the Fock space is a Hilbert sum of Fock representations. -/
example (R : CCRRep h (FockSpace h)) := stone_von_neumann R

end Lightlike.OperatorAlgebras
