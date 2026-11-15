import Lightlike.PL.PachnerMain
import Lightlike.PL.Newman

/-!
# Pachner's theorem, PL form

Two closed combinatorial manifolds are related by bistellar moves exactly when they are
piecewise-linearly homeomorphic. This is the stellar form of Pachner's theorem
(`SComplex.pachner`) combined with Newman's theorem
(`SComplex.StellarEquiv.of_plHomeomorphic`), which identifies PL homeomorphism with stellar
equivalence. Both complexes contain the empty face, as every complex with a vertex does; the
hypothesis excludes only the complex with no faces, for which the empty face decides stellar
equivalence and PL homeomorphism cannot.

## Main results

* `SComplex.isClosedCombManifold_iff_plHomeomorphic`: a complex is a closed combinatorial manifold
  (vertex links stellar equivalent to boundaries of simplices) exactly when its vertex links are PL
  homeomorphic to them, which is Lickorish's Definition 2.2.
* `SComplex.pachner_plHomeomorphic`: for a closed combinatorial manifold `K` and a complex `L`,
  both with the empty face, `PLHomeomorphic K L ↔ BistellarEquiv K L`.
-/

namespace Lightlike.PL
namespace SComplex

variable {V : Type*} [DecidableEq V]

/-- **Closed combinatorial manifolds, the PL reading.** A complex `K` is a closed combinatorial
`n`-manifold (every vertex link stellar equivalent to the boundary of an `n`-simplex) exactly when
the link of every vertex is PL homeomorphic to the boundary of an `n`-simplex, which is the
definition in Lickorish (Definition 2.2). The two directions are `PLHomeomorphic.of_stellarEquivIn`
and Newman's theorem `StellarEquiv.of_plHomeomorphic`. -/
theorem isClosedCombManifold_iff_plHomeomorphic {n : ℕ} {K : SComplex V} :
    IsClosedCombManifold n K ↔ ∀ v ∈ K.verts,
      ∃ A : Finset (V ⊕ ℕ), A.card = n + 1 ∧ PLHomeomorphic (K.link {v}) (boundary A) := by
  rw [isClosedCombManifold_iff]
  refine forall₂_congr fun v hv => exists_congr fun A => and_congr_right fun hA => ?_
  constructor
  · exact fun h => (PLHomeomorphic.lift _).trans (PLHomeomorphic.of_stellarEquivIn h)
  · intro h
    have h' : PLHomeomorphic (K.link {v}).lift (boundary A) := (PLHomeomorphic.lift _).symm.trans h
    have hv1 : ({v} : Finset V) ∈ K := mem_verts.1 hv
    have h0 : ∅ ∈ (K.link {v}).lift ↔ ∅ ∈ boundary A := by
      refine iff_of_true ?_ ?_
      · have hl : (∅ : Finset V) ∈ K.link {v} :=
          mem_link'.2 ⟨Finset.disjoint_empty_right _, by rw [Finset.union_empty]; exact hv1⟩
        exact mem_map.2 ⟨∅, hl, by simp⟩
      · rw [mem_boundary]
        refine ⟨Finset.empty_subset _, ?_⟩
        intro h
        have := Finset.card_eq_zero.2 (Finset.subset_empty.1 h)
        omega
    exact StellarEquivIn.of_map (Function.Embedding.inl : (V ⊕ ℕ) ↪ (V ⊕ ℕ) ⊕ ℕ)
      (StellarEquiv.of_plHomeomorphic h0 h')

/-- **Pachner's theorem, PL form: closed combinatorial manifolds are PL homeomorphic iff related
by bistellar moves.** -/
theorem pachner_plHomeomorphic {n : ℕ} {K L : SComplex V} (hK : IsClosedCombManifold n K)
    (h₀K : ∅ ∈ K) (h₀L : ∅ ∈ L) :
    PLHomeomorphic K L ↔ BistellarEquiv K L :=
  ⟨fun h => (pachner hK).1 (StellarEquiv.of_plHomeomorphic ⟨fun _ => h₀L, fun _ => h₀K⟩ h),
    fun h => PLHomeomorphic.of_stellarEquiv ((pachner hK).2 h)⟩

/-- **Non-vacuity.** The boundary of a triangle is a closed combinatorial 1-manifold, and the
theorem applies to it and its subdivision at a new vertex: they are related by bistellar moves. -/
example : BistellarEquiv (boundary ({0, 1, 2} : Finset ℕ))
    ((boundary ({0, 1, 2} : Finset ℕ)).starAt {0, 1} 3) := by
  have hK : IsClosedCombManifold 1 (boundary ({0, 1, 2} : Finset ℕ)) :=
    isClosedCombManifold_boundary (by decide)
  have hA : ({0, 1} : Finset ℕ) ∈ boundary ({0, 1, 2} : Finset ℕ) := by
    rw [mem_boundary]; decide
  have ha : (3 : ℕ) ∉ (boundary ({0, 1, 2} : Finset ℕ)).verts := by
    rw [verts_boundary (by decide)]; decide
  have h₀ : ∅ ∈ boundary ({0, 1, 2} : Finset ℕ) := empty_mem hA
  refine (pachner_plHomeomorphic hK h₀ ?_).1 (PLHomeomorphic.starAt hA ⟨0, by simp⟩ ha)
  exact (mem_starAt_of_notMem (by simp)).2 ⟨h₀, by simp⟩

end SComplex
end Lightlike.PL
