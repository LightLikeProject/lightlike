import Lightlike.PL.PachnerMoves
import Lightlike.PL.Tests
import Lightlike.PL.Tests4

/-!
# Trust checks for Pachner's theorem (milestone PL2)

* `bistellarEquiv_octahedron`: by `pachner`, the octahedron is bistellar equivalent to the boundary
  of a tetrahedron (it is stellar equivalent to it). `bistellarChain_octahedron`: **known value** -
  an explicit chain of four bistellar moves (two 1-3 moves and two 2-2 flips), computed by kernel
  `decide`, relates them, in agreement with the theorem.
* `not_bistellarEquiv_twoSpheres`, `not_bistellarEquiv_dim`: **wrong inputs** - the boundary of a
  tetrahedron is not bistellar equivalent to two disjoint 2-spheres, nor to the boundary of a
  4-simplex (bistellar equivalence implies stellar equivalence, which preserves connectedness and
  dimension).
* `bistellarChain_rename`: **known value** - renaming a vertex of a triangle is a chain of two
  bistellar moves, as `IsClosedCombManifold.bistellarEquiv_map` predicts for every closed
  combinatorial manifold; `bistellarEquiv_map_octahedron` applies that theorem.
* `move3_S3`, `move4_K3`: the corollaries `pachner3`, `pachner4` applied to the tests of
  `PonzanoRegge/` and `FourD/`: the boundary of the 4-simplex and its images under the moves of
  those tests are related by chains of moves on `Complex3`, `Complex4`. There the stellar
  equivalence comes from the moves themselves.
* `move3_cell16`, `move4_cross5`: **the hard direction on triangulations built independently.**
  The boundary of the 16-cell (`cell16`, 16 tetrahedra) and of the 5-dimensional cross-polytope
  (`cross5`, 32 4-simplices) are defined directly, by choosing one vertex from each antipodal pair.
  Their stellar equivalence with the boundary of a simplex is proven by explicit starrings
  (`ofComplex3_cell16`, `ofComplex4_cross5`, kernel `decide`): starring a facet of `∂Δⁿ⁺¹`
  gives the suspension of the boundary of that facet, and starring two opposite edges of a
  tetrahedron gives the octahedron. `pachner3` and `pachner4` then produce chains of 2-3, 3-2, 1-4,
  4-1 moves on `Complex3` and of the five 4D moves on `Complex4`.
-/

open Finset

namespace Lightlike.PL

open SComplex

set_option maxRecDepth 100000

/-! ## Bistellar equivalence on `V` -/

namespace SComplex

variable {V : Type*} [DecidableEq V]

@[refl] lemma BistellarEquiv.refl (K : SComplex V) : BistellarEquiv K K := BistellarEquivIn.refl _

@[trans] lemma BistellarEquiv.trans {K L M : SComplex V} (h₁ : BistellarEquiv K L)
    (h₂ : BistellarEquiv L M) : BistellarEquiv K M := BistellarEquivIn.trans h₁ h₂

/-- A bistellar move inside `V` is a bistellar equivalence. -/
lemma BistellarEquiv.bistellar {K : SComplex V} {A B : Finset V} (h : IsBistellar K A B) :
    BistellarEquiv K (K.bistellar A B h) := by
  change BistellarEquivIn (K.map _) ((K.bistellar A B h).map _)
  rw [map_bistellar h]
  exact BistellarEquivIn.bistellar _

end SComplex

/-! ## The octahedron -/

/-- **Pachner's theorem on a known example**: the octahedron is bistellar equivalent to the
boundary of a tetrahedron. -/
theorem bistellarEquiv_octahedron :
    BistellarEquiv (boundary ({0, 1, 2, 3} : Finset (Fin 6))) octahedron := by
  have hst : StellarEquiv (boundary ({0, 1, 2, 3} : Finset (Fin 6))) octahedron := by
    rw [← octahedron_eq_starAt]
    have h₁ := StellarEquivIn.starAt (K := boundary ({0, 1, 2, 3} : Finset (Fin 6))) (A := {0, 1})
      (a := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h₂ := StellarEquivIn.starAt
      (K := (boundary ({0, 1, 2, 3} : Finset (Fin 6))).starAt {0, 1} 4)
      (A := {2, 3}) (a := 5) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    exact StellarEquiv.of_in (h₁.trans h₂)
  exact (pachner (isClosedCombManifold_boundary (n := 2) (by decide +kernel))).1 hst

/-- The first move: a 1-3 move on the triangle `012` with the new vertex `4`. -/
lemma oct₁ : (boundary ({0, 1, 2, 3} : Finset (Fin 6))).IsBistellar {0, 1, 2} {4} where
  nonempty_left := by decide +kernel
  nonempty_right := by decide +kernel
  disjoint := by decide +kernel
  link_eq := by apply SComplex.ext; decide +kernel
  notMem := by decide +kernel

/-- The second move: the 2-2 flip of the edge `01` to `34`. -/
lemma oct₂ : ((boundary ({0, 1, 2, 3} : Finset (Fin 6))).bistellar {0, 1, 2} {4} oct₁).IsBistellar
    {0, 1} {3, 4} where
  nonempty_left := by decide +kernel
  nonempty_right := by decide +kernel
  disjoint := by decide +kernel
  link_eq := by apply SComplex.ext; decide +kernel
  notMem := by decide +kernel

/-- After two moves: the boundary of the tetrahedron with the edge `01` subdivided by `4`. -/
def octK₂ : SComplex (Fin 6) :=
  closure {{1, 2, 4}, {0, 2, 4}, {0, 2, 3}, {1, 2, 3}, {0, 3, 4}, {1, 3, 4}}

lemma octK₂_eq : (((boundary ({0, 1, 2, 3} : Finset (Fin 6))).bistellar {0, 1, 2} {4} oct₁).bistellar
    {0, 1} {3, 4} oct₂) = octK₂ := by
  apply SComplex.ext; decide +kernel

/-- The third move: a 1-3 move on the triangle `023` with the new vertex `5`. -/
lemma oct₃ : octK₂.IsBistellar {0, 2, 3} {5} where
  nonempty_left := by decide +kernel
  nonempty_right := by decide +kernel
  disjoint := by decide +kernel
  link_eq := by apply SComplex.ext; decide +kernel
  notMem := by decide +kernel

/-- The fourth move: the 2-2 flip of the edge `23` to `15`. -/
lemma oct₄ : (octK₂.bistellar {0, 2, 3} {5} oct₃).IsBistellar {2, 3} {1, 5} where
  nonempty_left := by decide +kernel
  nonempty_right := by decide +kernel
  disjoint := by decide +kernel
  link_eq := by apply SComplex.ext; decide +kernel
  notMem := by decide +kernel

/-- **Known value**: an explicit chain of four bistellar moves, computed by kernel `decide`, from the
boundary of a tetrahedron to the octahedron (two 1-3 moves and two 2-2 flips), in agreement with
`bistellarEquiv_octahedron`. -/
theorem bistellarChain_octahedron :
    BistellarEquiv (boundary ({0, 1, 2, 3} : Finset (Fin 6))) octahedron := by
  have e₄ : (octK₂.bistellar {0, 2, 3} {5} oct₃).bistellar {2, 3} {1, 5} oct₄ = octahedron := by
    apply SComplex.ext; decide +kernel
  have c₁ := BistellarEquiv.bistellar oct₁
  have c₂ := BistellarEquiv.bistellar oct₂
  rw [octK₂_eq] at c₂
  have c₃ := BistellarEquiv.bistellar oct₃
  have c₄ := BistellarEquiv.bistellar oct₄
  rw [e₄] at c₄
  exact c₁.trans (c₂.trans (c₃.trans c₄))

/-! ## Renamings -/

/-- The first move of the renaming: a 1-2 move on the edge `01` of the triangle with the new
vertex `3`. -/
lemma ren₁ : (boundary ({0, 1, 2} : Finset (Fin 4))).IsBistellar {0, 1} {3} where
  nonempty_left := by decide +kernel
  nonempty_right := by decide +kernel
  disjoint := by decide +kernel
  link_eq := by apply SComplex.ext; decide +kernel
  notMem := by decide +kernel

/-- The second move of the renaming: the 2-1 move removing the vertex `0`, whose link is now
`{2, 3}`. -/
lemma ren₂ : ((boundary ({0, 1, 2} : Finset (Fin 4))).bistellar {0, 1} {3} ren₁).IsBistellar
    {0} {2, 3} where
  nonempty_left := by decide +kernel
  nonempty_right := by decide +kernel
  disjoint := by decide +kernel
  link_eq := by apply SComplex.ext; decide +kernel
  notMem := by decide +kernel

/-- **Known value**: renaming the vertex `0` of a triangle to `3` is a chain of two bistellar
moves, computed by kernel `decide` (even inside `Fin 4`), as `bistellarEquiv_map` predicts. -/
theorem bistellarChain_rename :
    BistellarEquivIn (boundary ({0, 1, 2} : Finset (Fin 4)))
      ((boundary ({0, 1, 2} : Finset (Fin 4))).map (Equiv.swap 0 3).toEmbedding) := by
  have e : ((boundary ({0, 1, 2} : Finset (Fin 4))).bistellar {0, 1} {3} ren₁).bistellar
      {0} {2, 3} ren₂ = (boundary ({0, 1, 2} : Finset (Fin 4))).map (Equiv.swap 0 3).toEmbedding := by
    apply SComplex.ext; decide +kernel
  rw [← e]
  exact (BistellarEquivIn.bistellar ren₁).trans (BistellarEquivIn.bistellar ren₂)

/-- `bistellarEquiv_map` on the octahedron: the renaming that swaps `0` with `2` and `4` with `5`
is a bistellar equivalence. -/
theorem bistellarEquiv_map_octahedron : BistellarEquiv octahedron
    (octahedron.map (Equiv.swap (0 : Fin 6) 2 * Equiv.swap 4 5).toEmbedding) :=
  isClosedCombManifold_octahedron.bistellarEquiv_map _

/-- **Isomorphisms are bistellar** (`bistellarEquiv_of_iso`) for a map that is injective on the
vertices but not a permutation of them: translating the boundary of the tetrahedron `0123` in
`Fin 8` by `4` gives the boundary of `4567`. -/
theorem bistellarEquiv_iso_tetra :
    BistellarEquiv (boundary ({0, 1, 2, 3} : Finset (Fin 8))) (boundary {4, 5, 6, 7}) :=
  IsClosedCombManifold.bistellarEquiv_of_iso (f := fun x => x + 4)
    (isClosedCombManifold_boundary (n := 2) (by decide)) (by
      rw [verts_boundary (by decide)]
      intro x hx y hy h
      simpa using h) (by decide +kernel)

/-! ## Wrong inputs -/

/-- **Wrong input**: the boundary of a tetrahedron is not bistellar equivalent to two disjoint
2-spheres (they are not even stellar equivalent: one is connected, the other is not). -/
theorem not_bistellarEquiv_twoSpheres :
    ¬ BistellarEquiv (boundary ({0, 1, 2, 3} : Finset (Fin 8))) twoSpheres := by
  intro h
  have hc := (BistellarEquiv.stellarEquiv h).isConnected_iff.1
    (isConnected_boundary (by decide +kernel))
  have := not_isPLSphere_two_spheres
  obtain ⟨-, hconn⟩ := hc
  have hS : Separates {0, 1, 2, 3} twoSpheres := by
    intro s hs
    rw [← mem_faces] at hs
    revert s
    decide +kernel
  rcases hconn _ hS with h' | h'
  · exact absurd h' (by decide +kernel)
  · exact absurd h' (by decide +kernel)

/-- **Wrong input**: the boundary of a tetrahedron is not bistellar equivalent to the boundary of a
4-simplex (different dimensions). -/
theorem not_bistellarEquiv_dim :
    ¬ BistellarEquiv (boundary ({0, 1, 2, 3} : Finset (Fin 5))) (boundary {0, 1, 2, 3, 4}) := by
  intro h
  have := (BistellarEquiv.stellarEquiv h).maxCard_eq
  rw [maxCard_boundary (by decide), maxCard_boundary (by decide)] at this
  exact absurd this (by decide)

/-! ## The corollaries on the tests of `PonzanoRegge/` and `FourD/` -/

/-- `pachner3` on the tests of `PonzanoRegge/`: the boundary of the 4-simplex and its image under
the 1-4 and 2-3 moves are related by a chain of moves on `Complex3`. -/
theorem move3_S3 : Relation.EqvGen Move3Step
    (mapComplex3 Lightlike.PR.Test.Manifold.S3 (Function.Embedding.inl : Fin 6 ↪ Fin 6 ⊕ ℕ))
    (mapComplex3 (Lightlike.PR.move23 (Lightlike.PR.move14 Lightlike.PR.Test.Manifold.S3
      Lightlike.PR.Test.Manifold.hmove14_S3) Lightlike.PR.Test.Manifold.hmove23_S3_14)
      (Function.Embedding.inl : Fin 6 ↪ Fin 6 ⊕ ℕ)) := by
  refine (pachner3 Lightlike.PR.Test.Manifold.isCombManifold_S3 (by decide +kernel)).1 ?_
  have h₁ := StellarEquiv.bistellar (isBistellar_move14 Lightlike.PR.Test.Manifold.hmove14_S3)
  rw [← ofComplex3_move14 Lightlike.PR.Test.Manifold.hmove14_S3] at h₁
  have h₂ := StellarEquiv.bistellar (isBistellar_move23 Lightlike.PR.Test.Manifold.hmove23_S3_14)
  rw [← ofComplex3_move23 Lightlike.PR.Test.Manifold.hmove23_S3_14] at h₂
  exact h₁.trans h₂

/-- `pachner4` on the tests of `FourD/`: the boundary of the 5-simplex and its image under the 1-5,
2-4 and 3-3 moves are related by a chain of moves on `Complex4`. -/
theorem move4_K3 : Relation.EqvGen Move4Step
    (mapComplex4 Lightlike.FourD.Tests.K0 (Function.Embedding.inl : Fin 8 ↪ Fin 8 ⊕ ℕ))
    (mapComplex4 Lightlike.FourD.Tests.K3 (Function.Embedding.inl : Fin 8 ↪ Fin 8 ⊕ ℕ)) := by
  refine (pachner4 isCombManifold4_K0 (by decide +kernel)).1 ?_
  have h₁ := StellarEquiv.bistellar (isBistellar_move4 Lightlike.FourD.Tests.isMove15)
  rw [← ofComplex4_move Lightlike.FourD.Tests.isMove15] at h₁
  have h₂ := StellarEquiv.bistellar (isBistellar_move4 Lightlike.FourD.Tests.isMove24)
  rw [← ofComplex4_move Lightlike.FourD.Tests.isMove24] at h₂
  have h₃ := StellarEquiv.bistellar (isBistellar_move4 Lightlike.FourD.Tests.isMove33)
  rw [← ofComplex4_move Lightlike.FourD.Tests.isMove33] at h₃
  exact h₁.trans (h₂.trans h₃)

/-! ## The hard direction on independently built triangulations -/

/-- No two vertices of `s` form an antipodal pair `{2i, 2i + 1}`. -/
def CrossFree {m : ℕ} (s : Finset (Fin m)) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x.val / 2 = y.val / 2 → x = y

/-- `CrossFree` is decidable. -/
instance {m : ℕ} (s : Finset (Fin m)) : Decidable (CrossFree s) := by
  unfold CrossFree; infer_instance

/-- The facets of the boundary of the cross-polytope on `Fin m` (antipodal pairs `{2i, 2i + 1}`):
the `k`-element vertex sets with no antipodal pair. -/
def crossFacets (m k : ℕ) : Finset (Finset (Fin m)) :=
  (univ : Finset (Fin m)).powerset.filter fun s => #s = k ∧ CrossFree s

/-- **The boundary of the 16-cell** (the 4-dimensional cross-polytope) as a `Complex3`: its 16
tetrahedra take one vertex from each of the antipodal pairs `{0,1}, {2,3}, {4,5}, {6,7}`. -/
def cell16 : Lightlike.PR.Complex3 (Fin 8) where
  tets := crossFacets 8 4
  card_eq _ ht := (mem_filter.mp ht).2.1

/-- The boundary of the 4-simplex `{0, 1, 2, 3, 4}` in `Fin 8` as a `Complex3`. -/
def simplex4 : Lightlike.PR.Complex3 (Fin 8) where
  tets := ({0, 1, 2, 3, 4} : Finset (Fin 8)).powersetCard 4
  card_eq _ ht := (mem_powersetCard.mp ht).2

/-- The boundary of the 16-cell has 16 tetrahedra. -/
theorem card_cell16 : #cell16.tets = 16 := by decide +kernel

/-- `simplex4` generates the boundary of the 4-simplex. -/
theorem ofComplex3_simplex4 : ofComplex3 simplex4 = boundary ({0, 1, 2, 3, 4} : Finset (Fin 8)) := by
  apply SComplex.ext; decide +kernel

/-- **Known value**: starring the facet `0123` of `∂Δ⁴` (new vertex `5`), then the edges `01` and `23`
(new vertices `6`, `7`), gives the boundary of the 16-cell. -/
theorem ofComplex3_cell16 : ofComplex3 cell16 =
    (((boundary ({0, 1, 2, 3, 4} : Finset (Fin 8))).starAt {0, 1, 2, 3} 5).starAt {0, 1} 6).starAt
      {2, 3} 7 := by
  apply SComplex.ext; decide +kernel

/-- **The boundary of the 4-simplex and the boundary of the 16-cell are stellar equivalent**, by
three starrings. -/
theorem stellarEquiv_cell16 : StellarEquiv (ofComplex3 simplex4) (ofComplex3 cell16) := by
  rw [ofComplex3_simplex4, ofComplex3_cell16]
  have h₁ := StellarEquivIn.starAt (K := boundary ({0, 1, 2, 3, 4} : Finset (Fin 8)))
    (A := {0, 1, 2, 3}) (a := 5) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h₂ := StellarEquivIn.starAt
    (K := (boundary ({0, 1, 2, 3, 4} : Finset (Fin 8))).starAt {0, 1, 2, 3} 5)
    (A := {0, 1}) (a := 6) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h₃ := StellarEquivIn.starAt
    (K := ((boundary ({0, 1, 2, 3, 4} : Finset (Fin 8))).starAt {0, 1, 2, 3} 5).starAt {0, 1} 6)
    (A := {2, 3}) (a := 7) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact StellarEquiv.of_in (h₁.trans (h₂.trans h₃))

/-- The boundary of the 4-simplex is a closed combinatorial 3-manifold of `PonzanoRegge/`. -/
theorem isCombManifold_simplex4 : Lightlike.PR.IsCombManifold simplex4 := by
  rw [isCombManifold_iff_ofComplex3, ofComplex3_simplex4]
  exact isClosedCombManifold_boundary (by decide)

/-- **The hard direction of `pachner3` on independently built triangulations of `S³`**: the boundary
of the 4-simplex and the boundary of the 16-cell are related by a chain of 2-3, 3-2, 1-4 and 4-1
moves. -/
theorem move3_cell16 : Relation.EqvGen Move3Step
    (mapComplex3 simplex4 (Function.Embedding.inl : Fin 8 ↪ Fin 8 ⊕ ℕ))
    (mapComplex3 cell16 (Function.Embedding.inl : Fin 8 ↪ Fin 8 ⊕ ℕ)) :=
  (pachner3 isCombManifold_simplex4 (by decide +kernel)).1 stellarEquiv_cell16

/-- **Non-vacuity**: the boundary of the 16-cell is a closed combinatorial 3-manifold of
`PonzanoRegge/`, by stellar equivalence with the boundary of the 4-simplex. -/
theorem isCombManifold_cell16 : Lightlike.PR.IsCombManifold cell16 := by
  rw [isCombManifold_iff_ofComplex3]
  exact (StellarEquiv.isClosedCombManifold_iff stellarEquiv_cell16).1
    (isCombManifold_iff_ofComplex3.1 isCombManifold_simplex4)

/-- **The boundary of the 5-dimensional cross-polytope** as a `Complex4`: its 32 4-simplices take
one vertex from each of the antipodal pairs `{0,1}, {2,3}, {4,5}, {6,7}, {8,9}`. -/
def cross5 : Lightlike.FourD.Complex4 (Fin 10) where
  simps := crossFacets 10 5
  card_eq _ hs := (mem_filter.mp hs).2.1

/-- The boundary of the 5-dimensional cross-polytope has 32 4-simplices. -/
theorem card_cross5 : #cross5.simps = 32 := by decide +kernel

set_option maxHeartbeats 800000 in
/-- **Known value**: starring the facet `01234` of `∂Δ⁵` on `{0, 1, 2, 3, 4, 8}` (new vertex `9`),
then the facet `0123` of `∂(01234)` (new vertex `5`), then the edges `01` and `23` (new vertices
`6`, `7`), gives the boundary of the 5-dimensional cross-polytope. -/
theorem ofComplex4_cross5 : ofComplex4 cross5 =
    ((((boundary ({0, 1, 2, 3, 4, 8} : Finset (Fin 10))).starAt {0, 1, 2, 3, 4} 9).starAt
      {0, 1, 2, 3} 5).starAt {0, 1} 6).starAt {2, 3} 7 := by
  apply SComplex.ext; decide +kernel

set_option maxHeartbeats 600000 in
/-- **The boundary of the 5-simplex and the boundary of the 5-dimensional cross-polytope are
stellar equivalent**, by four starrings. -/
theorem stellarEquiv_cross5 :
    StellarEquiv (ofComplex4 (Lightlike.FourD.Complex4.sphere ({0, 1, 2, 3, 4, 8} : Finset (Fin 10))))
      (ofComplex4 cross5) := by
  rw [ofComplex4_sphere (by decide), ofComplex4_cross5]
  have h₁ := StellarEquivIn.starAt (K := boundary ({0, 1, 2, 3, 4, 8} : Finset (Fin 10)))
    (A := {0, 1, 2, 3, 4}) (a := 9) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h₂ := StellarEquivIn.starAt
    (K := (boundary ({0, 1, 2, 3, 4, 8} : Finset (Fin 10))).starAt {0, 1, 2, 3, 4} 9)
    (A := {0, 1, 2, 3}) (a := 5) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h₃ := StellarEquivIn.starAt
    (K := ((boundary ({0, 1, 2, 3, 4, 8} : Finset (Fin 10))).starAt {0, 1, 2, 3, 4} 9).starAt
      {0, 1, 2, 3} 5)
    (A := {0, 1}) (a := 6) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have h₄ := StellarEquivIn.starAt
    (K := (((boundary ({0, 1, 2, 3, 4, 8} : Finset (Fin 10))).starAt {0, 1, 2, 3, 4} 9).starAt
      {0, 1, 2, 3} 5).starAt {0, 1} 6)
    (A := {2, 3}) (a := 7) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact StellarEquiv.of_in (h₁.trans (h₂.trans (h₃.trans h₄)))

/-- **The hard direction of `pachner4` on independently built triangulations of `S⁴`**: the
boundary of the 5-simplex and the boundary of the 5-dimensional cross-polytope are related by a
chain of the five 4D moves of `FourD/`. -/
theorem move4_cross5 : Relation.EqvGen Move4Step
    (mapComplex4 (Lightlike.FourD.Complex4.sphere ({0, 1, 2, 3, 4, 8} : Finset (Fin 10)))
      (Function.Embedding.inl : Fin 10 ↪ Fin 10 ⊕ ℕ))
    (mapComplex4 cross5 (Function.Embedding.inl : Fin 10 ↪ Fin 10 ⊕ ℕ)) :=
  (pachner4 (isCombManifold4_sphere (by decide)) (by decide +kernel)).1 stellarEquiv_cross5

/-- **Non-vacuity**: the boundary of the 5-dimensional cross-polytope is a closed combinatorial
4-manifold, by stellar equivalence with the boundary of the 5-simplex. -/
theorem isCombManifold4_cross5 : IsCombManifold4 cross5 :=
  (StellarEquiv.isClosedCombManifold_iff stellarEquiv_cross5).1 (isCombManifold4_sphere (by decide))

end Lightlike.PL
