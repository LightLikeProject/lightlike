module

public import Lightlike.PonzanoRegge.SphereRecognition
public import Lightlike.Tests.SphereInvariants

/-!
# Tests for the recognition of triangulated 2-spheres

* `isSphere2_bdry_intrinsic`: **non-vacuity** of the converse. The boundary of the tetrahedron
  `0123`, given only by its intrinsic properties, is recognised as a combinatorial 2-sphere.
* `not_isSurfaceSphere_torus`, `not_isSurfaceSphere_wedge`: **wrong inputs** (the 7-vertex torus;
  two spheres glued at a vertex) fail the intrinsic conditions. Each is derived through the
  converse from the corresponding move-based test, so the two definitions are checked to reject
  the same complexes.
-/

@[expose] public section

namespace Lightlike.PR.Test.Sphere

/-- **Non-vacuity:** the boundary of a tetrahedron satisfies the intrinsic conditions, and the
converse `IsSurfaceSphere.isSphere2` recognises it. -/
theorem isSphere2_bdry_intrinsic : IsSphere2 (bdry (0 : Fin 4) 1 2 3) :=
  (isSurfaceSphere_bdry (a := (0 : Fin 4)) (b := 1) (c := 2) (d := 3) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)).isSphere2

/-- **Wrong input:** the torus is not an intrinsic triangulated 2-sphere. -/
theorem not_isSurfaceSphere_torus : ¬ IsSurfaceSphere torus := fun h =>
  not_isSphere2_torus h.isSphere2

/-- **Wrong input:** two spheres glued at a vertex are not an intrinsic triangulated 2-sphere. -/
theorem not_isSurfaceSphere_wedge : ¬ IsSurfaceSphere wedge := fun h =>
  not_isSphere2_wedge h.isSphere2

end Lightlike.PR.Test.Sphere
