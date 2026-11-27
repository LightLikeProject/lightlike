import Lightlike.FourD.Tests

/-!
# Kühnel's 9-vertex triangulation of the complex projective plane

The 4-dimensional combinatorial manifold `CP²₉` with the vertices `0, …, 8` (the vertices `1, …, 9` of the list of Lutz, *The
Manifold Page*, "Kühnel's vertex-minimal triangulation of CP² with f-vector (9, 36, 84, 90, 36)", transcribed from
that list), its face numbers `(9, 36, 84, 90, 36)`, Euler characteristic `3` and the fact that it is closed. The list is checked
by the computation of the face numbers, of the Euler characteristic and of the two 4-simplices of every tetrahedron; that the
vertex links are 3-spheres (so that it is a manifold) is not checked here.
The orientation `cp2Orient` makes the complex an oriented pseudo-manifold (`cp2_orientation`).
-/

open Finset Lightlike.FourD Lightlike.FourD.Tests

namespace Lightlike.FourD.Tests

/-- The 36 four-simplices of the 9-vertex `CP²`. -/
def cp2Facets : Finset (Finset (Fin 9)) :=
  {
    {0, 1, 2, 3, 4},
    {0, 1, 2, 3, 6},
    {0, 1, 2, 4, 7},
    {0, 1, 2, 6, 7},
    {0, 1, 3, 4, 5},
    {0, 1, 3, 5, 6},
    {0, 1, 4, 5, 7},
    {0, 1, 5, 6, 8},
    {0, 1, 5, 7, 8},
    {0, 1, 6, 7, 8},
    {0, 2, 3, 4, 8},
    {0, 2, 3, 6, 7},
    {0, 2, 3, 7, 8},
    {0, 2, 4, 5, 7},
    {0, 2, 4, 5, 8},
    {0, 2, 5, 7, 8},
    {0, 3, 4, 5, 6},
    {0, 3, 4, 6, 8},
    {0, 3, 6, 7, 8},
    {0, 4, 5, 6, 8},
    {1, 2, 3, 4, 8},
    {1, 2, 3, 5, 6},
    {1, 2, 3, 5, 8},
    {1, 2, 4, 6, 7},
    {1, 2, 4, 6, 8},
    {1, 2, 5, 6, 8},
    {1, 3, 4, 5, 7},
    {1, 3, 4, 7, 8},
    {1, 3, 5, 7, 8},
    {1, 4, 6, 7, 8},
    {2, 3, 5, 6, 7},
    {2, 3, 5, 7, 8},
    {2, 4, 5, 6, 7},
    {2, 4, 5, 6, 8},
    {3, 4, 5, 6, 7},
    {3, 4, 6, 7, 8}}

/-- **Kühnel's 9-vertex triangulation of `CP²`.** -/
def cp2 : Complex4 (Fin 9) where
  simps := cp2Facets
  card_eq := by decide +kernel

/-- **The face numbers of the 9-vertex `CP²`** are `(9, 36, 84, 90, 36)`, its Euler characteristic is `3` and it is closed
(every tetrahedron lies in exactly two 4-simplices). -/
theorem cp2_checks : fvec cp2 = (9, 36, 84, 90, 36) ∧ cp2.euler4 = 3 ∧ cp2.IsClosed4 := by
  unfold Complex4.IsClosed4
  decide +kernel

/-- The 4-simplices of `cp2` of orientation `+1`. -/
def cp2Plus : Finset (Finset (Fin 9)) :=
  {
    {0, 1, 2, 3, 4},
    {0, 1, 2, 4, 7},
    {0, 1, 4, 5, 7},
    {0, 1, 5, 6, 8},
    {0, 1, 6, 7, 8},
    {0, 2, 3, 4, 8},
    {0, 2, 4, 5, 8},
    {0, 2, 5, 7, 8},
    {1, 2, 3, 5, 8},
    {1, 2, 4, 6, 7},
    {1, 2, 5, 6, 8},
    {1, 3, 4, 5, 7},
    {1, 3, 4, 7, 8},
    {1, 4, 6, 7, 8},
    {2, 3, 5, 6, 7},
    {2, 3, 5, 7, 8},
    {2, 4, 5, 6, 8},
    {3, 4, 5, 6, 7}}

/-- An orientation of the 9-vertex `CP²` (relative to the increasing order of the vertices). -/
def cp2Orient : Finset (Fin 9) → ℤ := fun s => if s ∈ cp2Plus then 1 else -1


/-- The coherence of `cp2Orient`, with the tetrahedron first (the tetrahedra are computed once). -/
lemma cp2_coherent_aux : ∀ t ∈ cp2.tets, ∀ s ∈ cp2.simps, t ⊆ s → ∀ s' ∈ cp2.simps, t ⊆ s' → s ≠ s' →
    cp2Orient s * relSign s t = -(cp2Orient s' * relSign s' t) := by
  decide +kernel

/-- **`cp2Orient` is an orientation of the 9-vertex `CP²`**: two 4-simplices sharing a tetrahedron induce opposite
orientations on it. -/
theorem cp2_orientation : cp2.IsOrientation cp2Orient :=
  ⟨by decide +kernel, fun s hs s' hs' hne t ht hts hts' => cp2_coherent_aux t ht s hs hts s' hs' hts' hne⟩

end Lightlike.FourD.Tests
