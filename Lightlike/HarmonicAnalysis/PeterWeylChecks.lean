import Lightlike.HarmonicAnalysis.PeterWeylHilbert

/-!
# Checks for the Peter–Weyl theorem: abelian groups and the circle

For an abelian group every irreducible unitary matrix representation is one-dimensional (Schur's lemma), so the
Hilbert basis of `peterWeyl_hilbertBasis` consists of the characters; for the circle group these are
`z ↦ zⁿ`, `n ∈ ℤ`, and they are pairwise inequivalent and orthonormal in `L²(U(1))`.

Supporting lemmas; no catalogue entry.
-/

open MeasureTheory

namespace Lightlike.HarmonicAnalysis

noncomputable section

namespace UnitaryMatrixRep

variable {G : Type*} [Group G] [TopologicalSpace G] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- An irreducible unitary representation of an abelian group is one-dimensional. -/
theorem card_eq_one_of_commutative {ρ : UnitaryMatrixRep G ι} (hρ : ρ.IsIrreducible)
    (hcomm : ∀ g h : G, g * h = h * g) : Fintype.card ι = 1 := by
  obtain ⟨k⟩ := hρ.1
  have hscalar : ∀ h : G, ∃ c : ℂ, ρ.mat h = c • (1 : Matrix ι ι ℂ) := fun h =>
    schur_scalar hρ (ρ.mat h) fun g => by rw [← ρ.mat_mul, ← ρ.mat_mul, hcomm]
  let W : Submodule ℂ (ι → ℂ) := Submodule.span ℂ {Pi.single k 1}
  have hW : ∀ g, ∀ w ∈ W, (ρ.mat g).mulVec w ∈ W := by
    intro g w hw
    obtain ⟨c, hc⟩ := hscalar g
    rw [hc, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact W.smul_mem c hw
  have hne : W ≠ ⊥ := by
    intro h
    have : (Pi.single k (1 : ℂ) : ι → ℂ) ∈ W := Submodule.subset_span rfl
    rw [h] at this
    have h2 := congrFun (show (Pi.single k (1 : ℂ) : ι → ℂ) = 0 by simpa using this) k
    simp at h2
  have htop : W = ⊤ := (hρ.2 W hW).resolve_left hne
  refine Fintype.card_eq_one_iff.2 ⟨k, fun k' => ?_⟩
  by_contra hk
  have hmem : (Pi.single k' (1 : ℂ) : ι → ℂ) ∈ W := by rw [htop]; trivial
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
  have h3 := congrFun hc k'
  simp [Pi.single_apply, hk, Ne.symm hk] at h3

end UnitaryMatrixRep

end

end Lightlike.HarmonicAnalysis
