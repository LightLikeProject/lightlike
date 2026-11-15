import Lightlike.PL.Newman

/-!
# Checks of the subdivision theorem

* A complex with no faces at all subdivides the complex whose only face is `∅` (both have empty
  underlying set), and the two are not stellar equivalent: so the hypothesis `∅ ∈ M` of the
  theorem cannot be dropped.
* Newman's theorem on two different complexes: an edge and its subdivision at an inserted vertex,
  related by an explicit piecewise-linear homeomorphism.
* The hypotheses of the theorem are satisfiable: a point is a geometric complex that contains
  the empty face, and the theorem gives the equivalence for the subdivision of it by itself.
-/

open Finset

namespace Lightlike.PL
namespace SComplex

/-- The complex with no faces. -/
def voidComplex (W : Type*) : SComplex W := ⟨∅, by simp⟩

/-- The complex whose only face is the empty set. -/
def nullComplex (W : Type*) : SComplex W :=
  ⟨{∅}, fun s hs t ht => by
    rw [Finset.mem_singleton.1 hs] at ht
    simp [Finset.subset_empty.1 ht]⟩

lemma not_mem_voidComplex {W : Type*} (s : Finset W) : s ∉ voidComplex W := by
  intro h
  change s ∈ (∅ : Finset (Finset W)) at h
  simp at h

lemma mem_nullComplex {W : Type*} {s : Finset W} : s ∈ nullComplex W ↔ s = ∅ := by
  show s ∈ ({∅} : Finset (Finset W)) ↔ _
  simp

lemma isGeom_voidComplex : IsGeom (voidComplex ℝ) :=
  ⟨fun s hs => absurd hs (not_mem_voidComplex s), fun s hs => absurd hs (not_mem_voidComplex s)⟩

lemma isGeom_nullComplex : IsGeom (nullComplex ℝ) := by
  refine ⟨fun s hs => ?_, fun s hs t ht => ?_⟩
  · rw [mem_nullComplex.1 hs]; exact affineIndependent_of_subsingleton ℝ _
  · rw [mem_nullComplex.1 hs]; simp

/-- **The complex without faces subdivides the complex `{∅}`.** -/
lemma isSubdivision_void_null : IsSubdivision (voidComplex ℝ) (nullComplex ℝ) where
  geom' := isGeom_voidComplex
  geom := isGeom_nullComplex
  space_eq := by
    ext x
    simp only [mem_space]
    constructor
    · rintro ⟨s, hs, -⟩; exact absurd hs (not_mem_voidComplex s)
    · rintro ⟨s, hs, hx⟩
      rw [mem_nullComplex.1 hs] at hx
      simp at hx
  le s hs := absurd hs (not_mem_voidComplex s)

/-- **Wrong-model check.** They are not stellar equivalent, so dropping `∅ ∈ M` from the
subdivision theorem would make it false. -/
theorem not_stellarEquiv_void_null : ¬ StellarEquiv (voidComplex ℝ) (nullComplex ℝ) := by
  intro h
  have h₂ := StellarEquivIn.empty_mem_iff h
  simp only [lift, empty_mem_map_iff] at h₂
  exact not_mem_voidComplex _ (h₂.2 (mem_nullComplex.2 rfl))

/-- **Non-vacuity.** A point, with its empty face, is a geometric complex, and the theorem applies
to it. -/
example : StellarEquiv (simplex ({0} : Finset ℝ)) (simplex ({0} : Finset ℝ)) :=
  subdivStellar 0
    (simplex ({0} : Finset ℝ)) (simplex ({0} : Finset ℝ))
    (IsSubdivision.refl (isGeom_simplex (affineIndependent_of_subsingleton ℝ _)))
    (by simp) (by simp) (fun s hs => by
      have := Finset.card_le_card (mem_simplex.1 hs); simpa using this)

/-- **Newman's theorem on an example**: a complex is stellar equivalent to itself through its
PL homeomorphism with itself. -/
example (K : SComplex ℕ) : StellarEquiv K K :=
  StellarEquiv.of_plHomeomorphic Iff.rfl (PLHomeomorphic.refl K)

/-- The edge `{0, 1}` with all its faces, on the vertices `ℕ`. -/
def edge : SComplex ℕ := simplex {0, 1}

/-- The edge subdivided by a new vertex `2` in its interior. -/
def edgeSub : SComplex ℕ := edge.starAt {0, 1} 2

/-- The new vertex is a face of the subdivision, and not of the edge: the two complexes differ. -/
lemma edge_ne_edgeSub : edge ≠ edgeSub := by
  intro h
  have h2 : ({2} : Finset ℕ) ∈ edgeSub := by
    rw [edgeSub, mem_starAt]
    exact .inr ⟨∅, empty_mem (show ({0, 1} : Finset ℕ) ∈ edge by simp [edge]), by simp, by
      simpa [edge] using (show ({0, 1} : Finset ℕ) ∈ edge by simp [edge]), by simp⟩
  rw [← h] at h2
  have h3 := mem_simplex.1 h2 (Finset.mem_singleton_self 2)
  simp at h3

/-- **Newman's theorem on two different complexes**: the edge and its subdivision are PL
homeomorphic through the explicit map `starMap`, hence stellar equivalent. -/
theorem stellarEquiv_edge_edgeSub : StellarEquiv edge edgeSub := by
  have hA : ({0, 1} : Finset ℕ) ∈ edge := by simp [edge]
  have hne : ({0, 1} : Finset ℕ).Nonempty := ⟨0, by simp⟩
  have ha : (2 : ℕ) ∉ edge.verts := by
    rw [edge, verts_simplex]
    decide
  refine StellarEquiv.of_plHomeomorphic ?_ (PLHomeomorphic.starAt hA hne ha)
  have h0 : (∅ : Finset ℕ) ∈ edgeSub :=
    (mem_starAt_of_notMem (by simp)).2 ⟨empty_mem hA, by simp⟩
  exact ⟨fun _ => h0, fun _ => empty_mem hA⟩

end SComplex
end Lightlike.PL
