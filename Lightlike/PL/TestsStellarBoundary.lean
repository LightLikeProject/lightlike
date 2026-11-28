import Lightlike.PL.StellarBoundary

/-!
# Trust checks for stellar balls, spheres and the boundary

* The triangle is a stellar ball and not a stellar sphere; its boundary is a stellar sphere and not
  a stellar ball; `{∅}` (the `(−1)`-sphere) is a stellar sphere.
* The boundary of the tetrahedron (a closed combinatorial 2-manifold) has empty boundary.
* The triangle is a stellar 2-manifold whose boundary is not empty: the link of a vertex is an edge,
  a ball, so it is not a closed combinatorial 2-manifold.
-/

open Finset

namespace Lightlike.PL

open SComplex

lemma isStellarBall_triangle : (simplex ({0, 1, 2} : Finset (Fin 4))).IsStellarBall :=
  ⟨({0, 1, 2} : Finset (Fin 4)).map Function.Embedding.inl, by simp, by
    rw [lift_simplex]⟩

example : ¬ (simplex ({0, 1, 2} : Finset (Fin 4))).IsStellarSphere := fun h =>
  not_isStellarBall_and_isStellarSphere _ ⟨isStellarBall_triangle, h⟩

lemma isStellarSphere_circle : (boundary ({0, 1, 2} : Finset (Fin 4))).IsStellarSphere :=
  ⟨({0, 1, 2} : Finset (Fin 4)).map Function.Embedding.inl, by simp, by
    rw [lift_boundary]⟩

example : ¬ (boundary ({0, 1, 2} : Finset (Fin 4))).IsStellarBall := fun h =>
  not_isStellarBall_and_isStellarSphere _ ⟨h, isStellarSphere_circle⟩

/-- `{∅}` is the `(−1)`-sphere, the boundary of a single vertex. -/
example : (simplex (∅ : Finset (Fin 4))).IsStellarSphere :=
  ⟨{Sum.inr 0}, by simp, by
    rw [lift_simplex, map_empty, ← boundary_singleton (Sum.inr 0 : Fin 4 ⊕ ℕ)]⟩

/-- Non-vacuity: the boundary of the tetrahedron has empty boundary. -/
example : (boundary ({0, 1, 2, 3} : Finset (Fin 4))).stellarBoundary = ∅ := by
  have hc := isClosedCombManifold_boundary (n := 2) (A := ({0, 1, 2, 3} : Finset (Fin 4))) (by decide)
  exact (hc.isCombManifold.stellarBoundary_eq_empty_iff).2 hc

/-- The triangle is not closed: its boundary is not empty. -/
example : (simplex ({0, 1, 2} : Finset (Fin 4))).stellarBoundary ≠ ∅ := by
  intro h
  have hm := isCombManifold_simplex (n := 2) (A := ({0, 1, 2} : Finset (Fin 4))) (by decide)
  have hc := (hm.stellarBoundary_eq_empty_iff).1 h
  have hlk : (simplex ({0, 1, 2} : Finset (Fin 4))).link {0} = simplex {1, 2} := by
    apply SComplex.ext; decide +kernel
  have hs := hc.isStellarSphere_link (σ := {0}) (by decide) (by decide)
  rw [hlk] at hs
  refine not_isStellarBall_and_isStellarSphere _ ⟨⟨({1, 2} : Finset (Fin 4)).map Function.Embedding.inl, by simp, ?_⟩, hs⟩
  rw [lift_simplex]

end Lightlike.PL
