import Lightlike.PL.Complex3
import Lightlike.PL.Links
import Lightlike.PL.Surface
import Lightlike.Tests.Manifold
import Mathlib.Tactic.FinCases

/-!
# Trust checks for PL topology, milestone PL1

Known examples and deliberately wrong inputs for the definitions of `PL/`:

* `isPLSphere_octahedron`: the octahedron (the join of three 0-spheres) is a PL 2-sphere; it is
  obtained from the boundary of a tetrahedron by two stellar subdivisions of edges, computed by
  kernel `decide`. `isClosedCombManifold_octahedron`: it is a closed combinatorial 2-manifold
  (every vertex link is a 4-cycle, a subdivided triangle).
* `isPLSphere_boundary` and `isClosedCombManifold_boundary` (in `Lightlike/PL/Manifold.lean`) give
  the boundary of every `(n+1)`-simplex as a PL `n`-sphere and a closed combinatorial `n`-manifold.
* `not_isCombManifold_wedge`: **wrong model** - two boundaries of tetrahedra glued at a vertex are
  rejected: the link of the common vertex is two disjoint triangles, which is disconnected, while
  PL 1-spheres and 1-balls are connected.
* `not_isPLSphere_two_spheres`: **wrong model** - two disjoint boundaries of tetrahedra do not form
  a PL 2-sphere (disconnected).
* `not_isPLSphere_one_tetrahedron`: **wrong dimension** - the boundary of a tetrahedron is not a PL
  1-sphere.
* `not_isBistellar_tetrahedron`: **wrong move** - a 2-2 flip in the boundary of a tetrahedron is
  not a bistellar move (the new edge already exists); `isBistellar_octahedron_flip`: in the
  octahedron the same kind of flip is one.

Links of simplices (`Lightlike/PL/Links.lean`): `link_octahedron_edge`,
`isPLSphere_link_octahedron_edge`, `link_triangle_edge`, `isPLBall_link_triangle_edge` (known values
agree with the general theorems) and `not_isPLSphere_wedge` (**wrong model**: the wedge is not a PL
2-sphere, because PL spheres are combinatorial manifolds).

Euler characteristic and intrinsic 2-spheres (`Lightlike/PL/Euler.lean`,
`Lightlike/PL/Surface.lean`): `euler_octahedron` (`χ = 2`, computed directly and by
`IsPLSphere.euler`), `euler_twoSpheres` (**wrong model**: `χ = 4`), `not_isPLBall_tetrahedron`,
`card_verts_link_octahedron_edge`, and `isSurfaceSphere_octahedron` (the octahedron is an intrinsic
triangulated 2-sphere).

Non-vacuity of the hypotheses of the main theorems:

* `stellarEquiv_weld_octahedron`, `weld_octahedron`: the conditions of `StellarEquiv.weld` and
  `starAt_weld` hold for the octahedron at the vertex `5`, and the weld is computed.
* `isBistellar_S3_14`, `isBistellar_S3_14_23`: the 1-4 and 2-3 moves of the tests of
  `PonzanoRegge/` are bistellar moves.
* `isClosedCombManifold_S3`, `stellarEquiv_S3_14`: the boundary of the 4-simplex of the tests of
  `PonzanoRegge/` (on `Fin 6`) satisfies the hypotheses of `isClosedCombManifold_ofComplex3`, and
  its 1-4 move is a stellar equivalence; `ofComplex3_S3` identifies it with the boundary of the
  simplex on `{0, …, 4}`.
-/

open Finset

namespace Lightlike.PL

open SComplex

set_option maxRecDepth 100000

/-! ## The octahedron -/

/-- The octahedron on the vertices `0, …, 5` with antipodal pairs `{0, 1}`, `{2, 3}`, `{4, 5}`:
the triangles with one vertex from each pair. -/
def octahedron : SComplex (Fin 6) :=
  closure {{0, 2, 4}, {0, 2, 5}, {0, 3, 4}, {0, 3, 5}, {1, 2, 4}, {1, 2, 5}, {1, 3, 4}, {1, 3, 5}}

/-- The octahedron arises from the boundary of the tetrahedron `0123` by subdividing the edge
`01` with the vertex `4` and then the edge `23` with the vertex `5`. -/
theorem octahedron_eq_starAt :
    ((boundary {0, 1, 2, 3}).starAt {0, 1} 4).starAt {2, 3} 5 = octahedron := by
  apply SComplex.ext
  decide +kernel

/-- **The octahedron is a PL 2-sphere.** -/
theorem isPLSphere_octahedron : IsPLSphere 2 octahedron := by
  refine IsPLSphere.of_stellarEquivIn (A := {0, 1, 2, 3}) (by decide +kernel) ?_
  rw [← octahedron_eq_starAt]
  have h₁ := StellarEquivIn.starAt (K := boundary ({0, 1, 2, 3} : Finset (Fin 6))) (A := {0, 1})
    (a := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h₂ := StellarEquivIn.starAt
    (K := (boundary ({0, 1, 2, 3} : Finset (Fin 6))).starAt {0, 1} 4)
    (A := {2, 3}) (a := 5) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact (h₁.trans h₂).symm

/-- The link of a vertex of the octahedron is a 4-cycle, obtained from the boundary of a triangle
`p p' q` by subdividing the edge `p p'` with `q'`. -/
lemma octahedron_link_of {v p p' q q' : Fin 6}
    (hlink : octahedron.link {v} = (boundary {p, p', q}).starAt {p, p'} q')
    (h₃ : #({p, p', q} : Finset (Fin 6)) = 1 + 2)
    (hmem : ({p, p'} : Finset (Fin 6)) ∈ boundary {p, p', q})
    (hne : ({p, p'} : Finset (Fin 6)).Nonempty) (hq' : q' ∉ (boundary {p, p', q}).verts) :
    IsPLSphere 1 (octahedron.link {v}) :=
  IsPLSphere.of_stellarEquivIn h₃ (hlink ▸ (StellarEquivIn.starAt hmem hne hq').symm)

/-- **The octahedron is a closed combinatorial 2-manifold**: each vertex link is a PL 1-sphere. -/
theorem isClosedCombManifold_octahedron : IsClosedCombManifold 2 octahedron := by
  refine isClosedCombManifold_succ_iff.2 fun v _ => ?_
  fin_cases v
  · exact octahedron_link_of (p := 2) (p' := 3) (q := 4) (q' := 5)
      (by apply SComplex.ext; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact octahedron_link_of (p := 2) (p' := 3) (q := 4) (q' := 5)
      (by apply SComplex.ext; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact octahedron_link_of (p := 0) (p' := 1) (q := 4) (q' := 5)
      (by apply SComplex.ext; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact octahedron_link_of (p := 0) (p' := 1) (q := 4) (q' := 5)
      (by apply SComplex.ext; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact octahedron_link_of (p := 0) (p' := 1) (q := 2) (q' := 3)
      (by apply SComplex.ext; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact octahedron_link_of (p := 0) (p' := 1) (q := 2) (q' := 3)
      (by apply SComplex.ext; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ## Wrong models -/

/-- Two boundaries of tetrahedra, `0123` and `0456`, glued at the vertex `0`. -/
def wedge : SComplex (Fin 7) :=
  closure {{1, 2, 3}, {0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {4, 5, 6}, {0, 4, 5}, {0, 4, 6}, {0, 5, 6}}

/-- The link of the wedge point is two disjoint triangles, which is not connected. -/
lemma not_isConnected_link_wedge : ¬ (wedge.link {0}).IsConnected := by
  rintro ⟨-, h⟩
  have hS : Separates {1, 2, 3} (wedge.link {0}) := by
    intro s hs
    rw [← mem_faces] at hs
    revert s
    decide +kernel
  rcases h _ hS with h' | h'
  · exact absurd h' (by decide +kernel)
  · exact absurd h' (by decide +kernel)

/-- **Two 2-spheres glued at a vertex are not a combinatorial 2-manifold.** -/
theorem not_isCombManifold_wedge : ¬ IsCombManifold 2 wedge := fun h =>
  not_isConnected_link_wedge (h.isConnected_link (n := 0) (by decide +kernel))

/-- Two disjoint boundaries of tetrahedra. -/
def twoSpheres : SComplex (Fin 8) :=
  closure {{0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}, {4, 5, 6}, {4, 5, 7}, {4, 6, 7}, {5, 6, 7}}

/-- **Two disjoint 2-spheres do not form a PL 2-sphere.** -/
theorem not_isPLSphere_two_spheres : ¬ IsPLSphere 2 twoSpheres := by
  intro h
  obtain ⟨-, hc⟩ := (h.isConnected : twoSpheres.IsConnected)
  have hS : Separates {0, 1, 2, 3} twoSpheres := by
    intro s hs
    rw [← mem_faces] at hs
    revert s
    decide +kernel
  rcases hc _ hS with h' | h'
  · exact absurd h' (by decide +kernel)
  · exact absurd h' (by decide +kernel)

/-- **The boundary of a tetrahedron is not a PL 1-sphere** (its dimension is 2). -/
theorem not_isPLSphere_one_tetrahedron : ¬ IsPLSphere 1 (boundary ({0, 1, 2, 3} : Finset (Fin 4))) :=
  fun h => absurd (h.dim_unique (isPLSphere_boundary (n := 2) (by decide +kernel))) (by decide)

/-- **A 2-2 flip in the boundary of a tetrahedron is not a bistellar move**: the link of the edge
`01` is `∂{2, 3}`, but the edge `23` is already present. -/
theorem not_isBistellar_tetrahedron :
    ¬ (boundary ({0, 1, 2, 3} : Finset (Fin 4))).IsBistellar {0, 1} {2, 3} := fun h =>
  h.notMem (by decide +kernel)

/-- The link condition holds in that example, so it is exactly `B ∉ K` that rules the flip out. -/
lemma link_tetrahedron_edge :
    (boundary ({0, 1, 2, 3} : Finset (Fin 4))).link {0, 1} = boundary {2, 3} := by
  apply SComplex.ext
  decide +kernel

/-- **The 2-2 flip in the octahedron is a bistellar move**: the link of the edge `02` is
`∂{4, 5}`, and the edge `45` is not present (contrast `not_isBistellar_tetrahedron`). -/
theorem isBistellar_octahedron_flip : octahedron.IsBistellar {0, 2} {4, 5} where
  nonempty_left := by decide +kernel
  nonempty_right := by decide +kernel
  disjoint := by decide +kernel
  link_eq := by apply SComplex.ext; decide +kernel
  notMem := by decide +kernel

/-! ## Links of simplices -/

/-- **Known value**: the link of the edge `02` of the octahedron is the 0-sphere `{4, 5}`. -/
theorem link_octahedron_edge : octahedron.link {0, 2} = boundary {4, 5} := by
  apply SComplex.ext; decide +kernel

/-- `IsClosedCombManifold.isPLSphere_link` on the octahedron: the link of an edge is a PL
0-sphere, in agreement with `link_octahedron_edge`. -/
theorem isPLSphere_link_octahedron_edge : IsPLSphere 0 (octahedron.link {0, 2}) :=
  isClosedCombManifold_octahedron.isPLSphere_link (σ := {0, 2}) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- **Known value**: in the triangle `012` (a 2-ball) the link of the edge `01` is the single
vertex `2`, a 0-ball. -/
theorem link_triangle_edge :
    (simplex ({0, 1, 2} : Finset (Fin 3))).link {0, 1} = simplex {2} := by
  apply SComplex.ext; decide +kernel

/-- `IsCombManifold.isPLSphere_or_isPLBall_link` on the triangle, in agreement with
`link_triangle_edge`. -/
theorem isPLBall_link_triangle_edge :
    IsPLSphere 0 ((simplex ({0, 1, 2} : Finset (Fin 3))).link {0, 1}) ∨
      IsPLBall 0 ((simplex ({0, 1, 2} : Finset (Fin 3))).link {0, 1}) :=
  (isCombManifold_simplex (n := 2) (A := ({0, 1, 2} : Finset (Fin 3))) (by decide +kernel)
    ).isPLSphere_or_isPLBall_link (σ := {0, 1}) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- **Wrong model**: two 2-spheres glued at a vertex are not a PL 2-sphere, since PL spheres are
combinatorial manifolds (`IsPLSphere.isClosedCombManifold`) and the wedge is not. -/
theorem not_isPLSphere_wedge : ¬ IsPLSphere 2 wedge := fun h =>
  not_isCombManifold_wedge h.isClosedCombManifold.isCombManifold

/-! ## Euler characteristic and intrinsic 2-spheres -/

/-- **Known value**: the octahedron has `6 − 12 + 8 = 2` as Euler characteristic, computed
directly; `IsPLSphere.euler` gives `1 + (−1)² = 2`. -/
theorem euler_octahedron : octahedron.euler = 2 := by decide +kernel

/-- `IsPLSphere.euler` on the octahedron, in agreement with `euler_octahedron`. -/
theorem euler_octahedron' : octahedron.euler = 1 + (-1 : ℤ) ^ 2 := isPLSphere_octahedron.euler

/-- **Wrong model**: two disjoint 2-spheres have Euler characteristic `4`, not `2`. -/
theorem euler_twoSpheres : twoSpheres.euler = 4 := by decide +kernel

/-- **Different Euler characteristics rule out stellar equivalence**: the boundary of a
tetrahedron (`χ = 2`) and two disjoint 2-spheres (`χ = 4`) are not stellar equivalent. -/
theorem not_stellarEquiv_tetrahedron_twoSpheres :
    ¬ StellarEquiv (boundary ({0, 1, 2, 3} : Finset (Fin 8))) twoSpheres :=
  not_stellarEquiv_of_euler_ne (by
    rw [euler_boundary ⟨0, by simp⟩, euler_twoSpheres]
    norm_num)

/-- **A PL sphere is not a PL ball**: the boundary of a tetrahedron is not a PL ball of any
dimension. -/
theorem not_isPLBall_tetrahedron (m : ℕ) :
    ¬ IsPLBall m (boundary ({0, 1, 2, 3} : Finset (Fin 4))) :=
  (isPLSphere_boundary (n := 2) (by decide)).not_isPLBall

/-- **Known value**: the link of an edge of the octahedron has two vertices, as
`IsPLSphere.card_verts_zero` predicts for a PL 0-sphere. -/
theorem card_verts_link_octahedron_edge : #(octahedron.link {0, 2}).verts = 2 :=
  isPLSphere_link_octahedron_edge.card_verts_zero

/-- The triangles of the octahedron. -/
def octahedronTris : Finset (Finset (Fin 6)) :=
  {{0, 2, 4}, {0, 2, 5}, {0, 3, 4}, {0, 3, 5}, {1, 2, 4}, {1, 2, 5}, {1, 3, 4}, {1, 3, 5}}

/-- **The octahedron is an intrinsic triangulated 2-sphere** of `PonzanoRegge/`, by
`isSurfaceSphere_of_isPLSphere`. -/
theorem isSurfaceSphere_octahedron : Lightlike.PR.IsSurfaceSphere octahedronTris :=
  isSurfaceSphere_of_isPLSphere (show ∀ τ ∈ octahedronTris, #τ = 3 by decide +kernel)
    isPLSphere_octahedron

/-- **The octahedron is a combinatorial 2-sphere of `PonzanoRegge/`** (reached from the boundary
of a tetrahedron by 2-dimensional bistellar moves), by `isSphere2_iff`. -/
theorem isSphere2_octahedron : Lightlike.PR.IsSphere2 octahedronTris :=
  isSphere2_iff.2 ⟨show ∀ τ ∈ octahedronTris, #τ = 3 by decide +kernel, isPLSphere_octahedron⟩

/-! ## Non-vacuity of the main hypotheses -/

/-- The link of the vertex `5` of the octahedron is `∂{2, 3} * ∂{0, 1}`. -/
lemma link_octahedron_five :
    octahedron.link {5} = (boundary {2, 3}).join (boundary {0, 1}) := by
  apply SComplex.ext; decide +kernel

/-- The hypotheses of `StellarEquiv.weld` hold for the octahedron at `5` along `{2, 3}`. -/
theorem stellarEquiv_weld_octahedron : StellarEquiv octahedron (octahedron.weld 5 {2, 3}) :=
  StellarEquiv.weld (L := boundary {0, 1}) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) link_octahedron_five

/-- The weld of the octahedron at `5` along `{2, 3}` is the first subdivision of
`octahedron_eq_starAt`, as `weld_starAt` predicts. -/
theorem weld_octahedron :
    octahedron.weld 5 {2, 3} = (boundary {0, 1, 2, 3}).starAt {0, 1} 4 := by
  apply SComplex.ext; decide +kernel

/-- The 1-4 move of the tests of `PonzanoRegge/` is a bistellar move. -/
theorem isBistellar_S3_14 : (ofComplex3 Lightlike.PR.Test.Manifold.S3).IsBistellar {0, 1, 2, 3} {5} :=
  isBistellar_move14 Lightlike.PR.Test.Manifold.hmove14_S3

/-- The 2-3 move of the tests of `PonzanoRegge/` is a bistellar move. -/
theorem isBistellar_S3_14_23 :
    (ofComplex3 (Lightlike.PR.move14 Lightlike.PR.Test.Manifold.S3 Lightlike.PR.Test.Manifold.hmove14_S3)).IsBistellar
      {0, 1, 2} {4, 5} :=
  isBistellar_move23 Lightlike.PR.Test.Manifold.hmove23_S3_14

/-- The boundary of the 4-simplex of the tests of `PonzanoRegge/` generates the boundary of the
simplex on `{0, …, 4}`. -/
theorem ofComplex3_S3 : ofComplex3 Lightlike.PR.Test.Manifold.S3 = boundary {0, 1, 2, 3, 4} := by
  apply SComplex.ext; decide +kernel

/-- The hypotheses of `isClosedCombManifold_ofComplex3` hold for the boundary of the 4-simplex of
the tests of `PonzanoRegge/` (vertex type `Fin 6`). -/
theorem isClosedCombManifold_S3 : IsClosedCombManifold 3 (ofComplex3 Lightlike.PR.Test.Manifold.S3) :=
  isClosedCombManifold_ofComplex3 Lightlike.PR.Test.Manifold.isCombManifold_S3

/-- `StellarEquiv.bistellar` applied to the 1-4 move of the tests of `PonzanoRegge/`: inside
`Fin 6` the move uses the last spare vertex, and the stellar equivalence needs one more. -/
theorem stellarEquiv_S3_14 :
    StellarEquiv (ofComplex3 Lightlike.PR.Test.Manifold.S3)
      (ofComplex3 (Lightlike.PR.move14 Lightlike.PR.Test.Manifold.S3 Lightlike.PR.Test.Manifold.hmove14_S3)) := by
  rw [ofComplex3_move14]
  exact StellarEquiv.bistellar _

end Lightlike.PL
