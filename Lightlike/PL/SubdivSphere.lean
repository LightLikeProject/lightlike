import Lightlike.PL.DerivedGeom
import Lightlike.PL.ImageSB
import Lightlike.PL.StellarHomeo

/-!
# Subdivisions of a simplex boundary are stellar spheres

`SubdivStellar E n` says that every geometric subdivision of a geometric complex of dimension at
most `n` in `E` is stellar equivalent to it. This is the statement that Newman's theorem reduces to
(`StellarEquiv.of_plHomeomorphic_of_subdivision`), restricted to low dimension. Given it for
dimension `m - 1`, every geometric subdivision of the boundary of an `m`-simplex is a stellar
sphere.

## Main results

* `SComplex.SubdivStellar`: the statement for subdivisions of dimension at most `n`.
* `SComplex.isGeom_boundary`: the boundary of an affinely independent simplex is geometric.
* `SComplex.isSB_of_subdivision_boundary`: a geometric subdivision of the boundary of a simplex that
  has the empty face is a stellar sphere.
-/

open Finset

namespace Lightlike.PL
namespace SComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]

/-- **Subdivisions of low dimension are stellar.** Every geometric subdivision `M` of a geometric
complex `N` whose simplices have at most `n + 1` vertices is stellar equivalent to `N`. Both
complexes contain the empty face: without it a complex with no faces at all would subdivide the
complex `{∅}` (both have empty underlying set) and they are not stellar equivalent. -/
def SubdivStellar (E : Type*) [AddCommGroup E] [Module ℝ E] [DecidableEq E] (n : ℕ) : Prop :=
  ∀ M N : SComplex E, IsSubdivision M N → ∅ ∈ M → ∅ ∈ N → (∀ s ∈ N, #s ≤ n + 1) →
    StellarEquiv M N

/-- The simplex on an affinely independent finite set is a geometric complex. -/
lemma isGeom_simplex {σ : Finset E} (hσ : AffineIndependent ℝ ((↑) : σ → E)) :
    IsGeom (simplex σ) where
  indep s hs := AffineIndependent.mono (t := (σ : Set E)) hσ (coe_subset.2 (mem_simplex.1 hs))
  inter s hs t ht := (hσ.convexHull_inter (mem_simplex.1 hs) (mem_simplex.1 ht)).symm.subset

/-- The boundary of the simplex on an affinely independent finite set is a geometric complex. -/
lemma isGeom_boundary {σ : Finset E} (hσ : AffineIndependent ℝ ((↑) : σ → E)) :
    IsGeom (boundary σ) :=
  (isGeom_simplex hσ).of_subcomplex fun s hs => mem_simplex.2 (mem_boundary.1 hs).subset

/-- Stellar equivalence inside an infinite vertex type follows from the unrestricted notion. -/
lemma StellarEquiv.in_of_infinite [Infinite E] {K L : SComplex E} (h : StellarEquiv K L) :
    StellarEquivIn K L :=
  StellarEquivIn.of_map Function.Embedding.inl h

/-- **A geometric subdivision of the boundary of a simplex is a stellar sphere**, given the
subdivision statement in the dimension of the boundary. -/
theorem isSB_of_subdivision_boundary [Infinite E] {m : ℕ} (hT : SubdivStellar E (m - 1))
    {σ : Finset E} (hσ : AffineIndependent ℝ ((↑) : σ → E)) (hcard : #σ = m + 1)
    {β : SComplex E} (hβ : IsSubdivision β (boundary σ)) (h0β : ∅ ∈ β) : IsSB false m β := by
  have hN : ∀ s ∈ boundary σ, #s ≤ m - 1 + 1 := fun s hs => by
    have := Finset.card_lt_card (mem_boundary.1 hs)
    omega
  have h0 : ∅ ∈ boundary σ := mem_boundary.2 (Finset.empty_ssubset.2 (Finset.card_pos.1 (by omega)))
  exact .inl ⟨σ, hcard, (hT β _ hβ h0β h0 hN).in_of_infinite⟩

end SComplex
end Lightlike.PL
