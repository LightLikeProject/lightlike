import Lightlike.PL.Bistellar
import Lightlike.PL.Invariants

/-!
# PL spheres, PL balls and combinatorial manifolds

The spheres, balls and manifolds of this library are Lickorish's **stellar** ones (*Simplicial
moves on complexes and manifolds*, 1999, Definition 3.1). A **PL `n`-sphere** (`IsPLSphere`) is a
complex stellar equivalent to the boundary of an `(n+1)`-simplex, and a **PL `n`-ball**
(`IsPLBall`) one stellar equivalent to an `n`-simplex. A **combinatorial `n`-manifold**
(`IsCombManifold`) is a complex in which the link of every vertex is a PL `(n−1)`-sphere or
`(n−1)`-ball in this sense; it is **closed** (`IsClosedCombManifold`) when every vertex link is a
sphere.

These are not Lickorish's *combinatorial* spheres, balls and manifolds (Definition 2.2), which ask
for a piecewise-linear homeomorphism to the boundary of a simplex or to a simplex instead of a
stellar equivalence. The two readings agree by Newman's theorem (Lickorish §4), which is milestone
P3 and not yet formalized. Until then, "PL sphere", "PL ball" and "combinatorial manifold" in this
library always mean the stellar notions.

The void complex (no faces, not even `∅`) has no vertices, so it satisfies
`IsClosedCombManifold n` and `IsCombManifold n` for every `n`. Results that need a nonempty complex
assume it (for example `pachner3` and `pachner4` in `Lightlike/PL/PachnerMoves.lean`); the PL
spheres and balls are never void.

Each notion comes in two versions. The versions ending in `In` (`IsPLSphereIn`, …) use stellar
equivalence inside the vertex type (`StellarEquivIn`); they are the right notion on an infinite
vertex type and are used to develop the theory there. The main versions (`IsPLSphere`, …) apply
the `In` version to the lift of the complex to `V ⊕ ℕ`, so that they do not depend on how many
vertices `V` has to spare.

To include `n = 0` without subtraction, the vertex-link condition for an `n`-manifold is phrased
with the boundary of a simplex on `n + 1` vertices (a PL `(n−1)`-sphere; for `n = 0` this is
`{∅}`) and a simplex on `n` vertices (a PL `(n−1)`-ball). For `n + 1` the conditions read
`IsPLSphere n` and `IsPLBall n` (`isClosedCombManifold_succ_iff`, `isCombManifold_succ_iff`).

## Main results

* `isPLSphere_boundary`, `isPLBall_simplex`: the standard models.
* `isClosedCombManifold_boundary`: the boundary of an `(n+1)`-simplex is a closed combinatorial
  `n`-manifold; `isCombManifold_simplex`: the `n`-simplex is a combinatorial `n`-manifold.
* `IsPLSphere.maxCard`, `IsPLBall.maxCard`, `IsPLSphere.dim_unique`: a PL `n`-sphere or `n`-ball
  has dimension `n`, so `n` is determined.
* `IsPLSphere.isConnected` (`n ≥ 1`), `IsPLBall.isConnected`: they are connected.
* `IsPLSphere.of_stellarEquiv`, `IsClosedCombManifold.isCombManifold`: basic closure properties.
-/

open Finset

namespace Lightlike.PL

namespace SComplex

variable {V : Type*} [DecidableEq V]

/-! ## Inside the vertex type -/

/-- `K` is a PL `n`-sphere inside `V`: stellar equivalent inside `V` to the boundary of an
`(n+1)`-simplex on vertices of `V`. -/
def IsPLSphereIn (n : ℕ) (K : SComplex V) : Prop :=
  ∃ A : Finset V, #A = n + 2 ∧ StellarEquivIn K (boundary A)

/-- `K` is a PL `n`-ball inside `V`: stellar equivalent inside `V` to an `n`-simplex. -/
def IsPLBallIn (n : ℕ) (K : SComplex V) : Prop :=
  ∃ A : Finset V, #A = n + 1 ∧ StellarEquivIn K (simplex A)

/-- `K` is a closed combinatorial `n`-manifold inside `V`: every vertex link is stellar equivalent
inside `V` to the boundary of a simplex on `n + 1` vertices. -/
def IsClosedCombManifoldIn (n : ℕ) (K : SComplex V) : Prop :=
  ∀ v ∈ K.verts, ∃ A : Finset V, #A = n + 1 ∧ StellarEquivIn (K.link {v}) (boundary A)

/-- `K` is a combinatorial `n`-manifold inside `V`: every vertex link is stellar equivalent inside
`V` to the boundary of a simplex on `n + 1` vertices or to a simplex on `n` vertices. -/
def IsCombManifoldIn (n : ℕ) (K : SComplex V) : Prop :=
  ∀ v ∈ K.verts, (∃ A : Finset V, #A = n + 1 ∧ StellarEquivIn (K.link {v}) (boundary A)) ∨
    ∃ A : Finset V, #A = n ∧ StellarEquivIn (K.link {v}) (simplex A)

lemma IsPLSphereIn.of_stellarEquivIn {n : ℕ} {K L : SComplex V} (hK : IsPLSphereIn n K)
    (h : StellarEquivIn K L) : IsPLSphereIn n L := by
  obtain ⟨A, hA, hKA⟩ := hK
  exact ⟨A, hA, h.symm.trans hKA⟩

lemma IsPLBallIn.of_stellarEquivIn {n : ℕ} {K L : SComplex V} (hK : IsPLBallIn n K)
    (h : StellarEquivIn K L) : IsPLBallIn n L := by
  obtain ⟨A, hA, hKA⟩ := hK
  exact ⟨A, hA, h.symm.trans hKA⟩

lemma isClosedCombManifoldIn_boundary {n : ℕ} {A : Finset V} (hA : #A = n + 2) :
    IsClosedCombManifoldIn n (boundary A) := by
  intro v hv
  refine ⟨A.erase v, ?_, by rw [link_boundary_vertex hv]⟩
  rw [verts_boundary (by omega)] at hv
  rw [card_erase_of_mem hv, hA]; rfl

lemma isCombManifoldIn_simplex {n : ℕ} {A : Finset V} (hA : #A = n + 1) :
    IsCombManifoldIn n (simplex A) := by
  intro v hv
  rw [verts_simplex] at hv
  refine .inr ⟨A.erase v, by rw [card_erase_of_mem hv, hA]; rfl, ?_⟩
  rw [link_simplex (singleton_subset_iff.2 hv), sdiff_singleton_eq_erase]

lemma IsPLSphereIn.maxCard {n : ℕ} {K : SComplex V} (h : IsPLSphereIn n K) :
    K.maxCard = n + 1 := by
  obtain ⟨A, hA, hKA⟩ := h
  rw [hKA.maxCard_eq, maxCard_boundary (card_pos.1 (by omega)), hA]
  rfl

lemma IsPLBallIn.maxCard {n : ℕ} {K : SComplex V} (h : IsPLBallIn n K) : K.maxCard = n + 1 := by
  obtain ⟨A, hA, hKA⟩ := h
  rw [hKA.maxCard_eq, maxCard_simplex, hA]

lemma IsPLSphereIn.isConnected {n : ℕ} {K : SComplex V} (h : IsPLSphereIn (n + 1) K) :
    K.IsConnected := by
  obtain ⟨A, hA, hKA⟩ := h
  exact hKA.isConnected_iff.2 (isConnected_boundary (by omega))

lemma IsPLBallIn.isConnected {n : ℕ} {K : SComplex V} (h : IsPLBallIn n K) : K.IsConnected := by
  obtain ⟨A, hA, hKA⟩ := h
  exact hKA.isConnected_iff.2 (isConnected_simplex (card_pos.1 (by omega)))

/-! ## The main notions -/

/-- `K` is a **PL `n`-sphere**: it is stellar equivalent to the boundary of an `(n+1)`-simplex
(with an unlimited supply of new vertices: `IsPLSphereIn` for the lift of `K` to `V ⊕ ℕ`). -/
def IsPLSphere (n : ℕ) (K : SComplex V) : Prop := IsPLSphereIn n K.lift

/-- `K` is a **PL `n`-ball**: it is stellar equivalent to an `n`-simplex. -/
def IsPLBall (n : ℕ) (K : SComplex V) : Prop := IsPLBallIn n K.lift

/-- `K` is a **closed combinatorial `n`-manifold**: the link of every vertex is a PL
`(n−1)`-sphere, i.e. stellar equivalent to the boundary of a simplex on `n + 1` vertices. -/
def IsClosedCombManifold (n : ℕ) (K : SComplex V) : Prop := IsClosedCombManifoldIn n K.lift

/-- `K` is a **combinatorial `n`-manifold** (possibly with boundary): the link of every vertex is a
PL `(n−1)`-sphere or a PL `(n−1)`-ball. -/
def IsCombManifold (n : ℕ) (K : SComplex V) : Prop := IsCombManifoldIn n K.lift

/-- The vertex-link condition, read on the links of `K` themselves. -/
lemma isClosedCombManifold_iff {n : ℕ} {K : SComplex V} :
    IsClosedCombManifold n K ↔ ∀ v ∈ K.verts,
      ∃ A : Finset (V ⊕ ℕ), #A = n + 1 ∧ StellarEquivIn (K.link {v}).lift (boundary A) := by
  simp only [IsClosedCombManifold, IsClosedCombManifoldIn, verts_lift, Finset.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  refine forall₂_congr fun v _ => ?_
  rw [← map_singleton, link_lift]

/-- The vertex-link condition, read on the links of `K` themselves. -/
lemma isCombManifold_iff {n : ℕ} {K : SComplex V} :
    IsCombManifold n K ↔ ∀ v ∈ K.verts,
      (∃ A : Finset (V ⊕ ℕ), #A = n + 1 ∧ StellarEquivIn (K.link {v}).lift (boundary A)) ∨
      ∃ A : Finset (V ⊕ ℕ), #A = n ∧ StellarEquivIn (K.link {v}).lift (simplex A) := by
  simp only [IsCombManifold, IsCombManifoldIn, verts_lift, Finset.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  refine forall₂_congr fun v _ => ?_
  rw [← map_singleton, link_lift]

lemma isClosedCombManifold_succ_iff {n : ℕ} {K : SComplex V} :
    IsClosedCombManifold (n + 1) K ↔ ∀ v ∈ K.verts, IsPLSphere n (K.link {v}) :=
  isClosedCombManifold_iff

lemma isCombManifold_succ_iff {n : ℕ} {K : SComplex V} :
    IsCombManifold (n + 1) K ↔ ∀ v ∈ K.verts, IsPLSphere n (K.link {v}) ∨ IsPLBall n (K.link {v}) :=
  isCombManifold_iff

/-- A closed combinatorial manifold is a combinatorial manifold. -/
lemma IsClosedCombManifold.isCombManifold {n : ℕ} {K : SComplex V}
    (h : IsClosedCombManifold n K) : IsCombManifold n K := fun v hv => .inl (h v hv)

/-- Being a PL sphere is invariant under stellar equivalence. -/
lemma IsPLSphere.of_stellarEquiv {n : ℕ} {K L : SComplex V} (hK : IsPLSphere n K)
    (h : StellarEquiv K L) : IsPLSphere n L :=
  IsPLSphereIn.of_stellarEquivIn hK h

/-- Being a PL ball is invariant under stellar equivalence. -/
lemma IsPLBall.of_stellarEquiv {n : ℕ} {K L : SComplex V} (hK : IsPLBall n K)
    (h : StellarEquiv K L) : IsPLBall n L :=
  IsPLBallIn.of_stellarEquivIn hK h

/-- A complex stellar equivalent to a PL sphere inside `V` is a PL sphere. -/
lemma IsPLSphere.of_stellarEquivIn {n : ℕ} {K : SComplex V} {A : Finset V} (hA : #A = n + 2)
    (h : StellarEquivIn K (boundary A)) : IsPLSphere n K :=
  ⟨A.map Function.Embedding.inl, by rw [card_map, hA], by
    rw [← lift_boundary]; exact StellarEquiv.of_in h⟩

/-- **The boundary of an `(n+1)`-simplex is a PL `n`-sphere.** -/
theorem isPLSphere_boundary {n : ℕ} {A : Finset V} (hA : #A = n + 2) :
    IsPLSphere n (boundary A) :=
  IsPLSphere.of_stellarEquivIn hA (.refl _)

/-- The `n`-simplex is a PL `n`-ball. -/
theorem isPLBall_simplex {n : ℕ} {A : Finset V} (hA : #A = n + 1) : IsPLBall n (simplex A) :=
  ⟨A.map Function.Embedding.inl, by rw [card_map, hA], by rw [lift_simplex]⟩

/-- **The boundary of an `(n+1)`-simplex is a closed combinatorial `n`-manifold**: the link of a
vertex `v` is the boundary of the simplex on the other `n + 1` vertices. -/
theorem isClosedCombManifold_boundary {n : ℕ} {A : Finset V} (hA : #A = n + 2) :
    IsClosedCombManifold n (boundary A) := by
  rw [IsClosedCombManifold, lift_boundary]
  exact isClosedCombManifoldIn_boundary (by rw [card_map, hA])

/-- **The `n`-simplex is a combinatorial `n`-manifold**: the link of a vertex is the simplex on the
other `n` vertices. -/
theorem isCombManifold_simplex {n : ℕ} {A : Finset V} (hA : #A = n + 1) :
    IsCombManifold n (simplex A) := by
  rw [IsCombManifold, lift_simplex]
  exact isCombManifoldIn_simplex (by rw [card_map, hA])

/-- A PL `n`-sphere has dimension `n`: its largest faces have `n + 1` vertices. -/
theorem IsPLSphere.maxCard {n : ℕ} {K : SComplex V} (h : IsPLSphere n K) : K.maxCard = n + 1 := by
  rw [← IsPLSphereIn.maxCard h, lift, maxCard_map]

/-- A PL `n`-ball has dimension `n`. -/
theorem IsPLBall.maxCard {n : ℕ} {K : SComplex V} (h : IsPLBall n K) : K.maxCard = n + 1 := by
  rw [← IsPLBallIn.maxCard h, lift, maxCard_map]

/-- **The dimension of a PL sphere is determined**: a complex is a PL sphere of at most one
dimension. -/
theorem IsPLSphere.dim_unique {n m : ℕ} {K : SComplex V} (hn : IsPLSphere n K)
    (hm : IsPLSphere m K) : n = m := by
  have := hn.maxCard.symm.trans hm.maxCard
  omega

/-- **A PL sphere of dimension at least one is connected.** -/
theorem IsPLSphere.isConnected {n : ℕ} {K : SComplex V} (h : IsPLSphere (n + 1) K) :
    K.IsConnected :=
  (isConnected_map_iff K _).1 (IsPLSphereIn.isConnected h)

/-- **A PL ball is connected.** -/
theorem IsPLBall.isConnected {n : ℕ} {K : SComplex V} (h : IsPLBall n K) : K.IsConnected :=
  (isConnected_map_iff K _).1 (IsPLBallIn.isConnected h)

/-- In a combinatorial manifold of dimension at least two, every vertex link is connected. -/
theorem IsCombManifold.isConnected_link {n : ℕ} {K : SComplex V} (h : IsCombManifold (n + 2) K)
    {v : V} (hv : v ∈ K.verts) : (K.link {v}).IsConnected := by
  rcases isCombManifold_succ_iff.1 h v hv with h' | h'
  · exact h'.isConnected
  · exact h'.isConnected

end SComplex

end Lightlike.PL
