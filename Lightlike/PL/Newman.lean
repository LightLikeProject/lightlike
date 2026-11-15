import Lightlike.PL.SubdivCells
import Lightlike.PL.StellarHomeo
import Lightlike.PL.RadialCell

/-!
# Newman's theorem

PL homeomorphic simplicial complexes are stellar equivalent. The hard direction reduces to
geometric subdivisions (`StellarEquiv.of_plHomeomorphic_of_subdivision`), and every geometric
subdivision is stellar equivalent to the complex it subdivides (`subdivStellar`), by induction on
the dimension.

## Main results

* `SComplex.StellarEquiv.of_plHomeomorphic`: **Newman's theorem**, for complexes that either both
  have the empty face or both have none.
* `SComplex.derivedBoundary_isSphere_of_infinite`, `SComplex.cutSpheres_of_infinite`,
  `SComplex.isSB_of_polytope_boundary_of_infinite`: the sphere results that assumed stellar
  equivalence of lower-dimensional subdivisions, now without that assumption.
-/

open Finset

namespace Lightlike.PL
namespace SComplex

variable {V : Type*} [DecidableEq V]

/-- **Newman's theorem.** PL homeomorphic simplicial complexes are stellar equivalent (Lickorish,
Theorem 4.5), where the two complexes either both contain the empty face or both do not. -/
theorem StellarEquiv.of_plHomeomorphic {K L : SComplex V} (h0 : ∅ ∈ K ↔ ∅ ∈ L)
    (h : PLHomeomorphic K L) : StellarEquiv K L := by
  rcases isEmpty_or_nonempty V with hV | ⟨⟨v⟩⟩
  · have : K = L := ext_mem fun s => by
      rw [Finset.eq_empty_of_isEmpty s]
      exact h0
    rw [this]
  · haveI : Infinite (V →₀ ℝ) :=
      Infinite.of_injective (fun r : ℝ => Finsupp.single v r) (Finsupp.single_injective v)
    refine StellarEquiv.of_plHomeomorphic_of_subdivision (fun M N hsub h0M h0N => ?_) h0 h
    exact subdivStellar (N.faces.sup Finset.card) M N hsub h0M h0N fun s hs =>
      (Finset.le_sup (f := Finset.card) hs).trans (Nat.le_succ _)

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E] [Infinite E]

open Classical in
/-- **The derived boundary of a cell is a stellar sphere**, with no assumption on subdivisions
(`derivedBoundary_isSphere`, with its hypothesis discharged by `subdivStellar`). -/
theorem derivedBoundary_isSphere_of_infinite {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    {K : SComplex E} (hK : IsGeom K) (hKn : ∀ s ∈ K, #s ≤ n + 1) (H : ι → E →ᵃ[ℝ] ℝ)
    {C : CellIdx E ι} (hC : C ∈ cells K (fun i => ⇑(H i))) :
    ∃ d ≤ n, Module.finrank ℝ (cellA H C).direction = d ∧
      IsSB false d (orderComplex ((cells K (fun i => ⇑(H i))).filter (· < C))) :=
  derivedBoundary_isSphere (subdivStellar _) hK hKn H hC

/-- **The cut spheres exist**, with no assumption on subdivisions (`cutSpheres`). -/
theorem cutSpheres_of_infinite {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} {K : SComplex E}
    (hK : IsGeom K) (hKn : ∀ s ∈ K, #s ≤ n + 1) (H : ι → E →ᵃ[ℝ] ℝ) (h : E →ᵃ[ℝ] ℝ) :
    CutSpheres K H h :=
  cutSpheres (subdivStellar _) hK hKn H h

/-- **The boundary of a bounded polytope is a stellar sphere**, with no assumption on
subdivisions (`isSB_of_polytope_boundary`). -/
theorem isSB_of_polytope_boundary_of_infinite {κ : Type*} [Fintype κ] [Nonempty κ] {d : ℕ}
    (A : AffineSubspace ℝ E) [FiniteDimensional ℝ A.direction]
    (hd : Module.finrank ℝ A.direction = d) {v : E} (hvA : v ∈ A) (g : κ → E →ᵃ[ℝ] ℝ)
    (hneg : ∀ k, g k v < 0) (hbdd : ∀ y ∈ A, y ≠ v → ∃ k, g k v < g k y) {γ : SComplex E}
    (hγ : IsGeom γ) (h₀γ : ∅ ∈ γ) (hγn : ∀ s ∈ γ, #s ≤ d)
    (hspace : γ.space = {x | x ∈ A ∧ (∀ k, g k x ≤ 0) ∧ ∃ k, g k x = 0}) :
    IsSB false d γ :=
  isSB_of_polytope_boundary (subdivStellar _) A hd hvA g hneg hbdd hγ h₀γ hγn hspace

end SComplex
end Lightlike.PL
