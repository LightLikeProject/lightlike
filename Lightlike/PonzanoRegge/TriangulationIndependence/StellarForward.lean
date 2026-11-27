import Lightlike.PonzanoRegge.TriangulationIndependence.Main
import Lightlike.PL.Stellar
import Lightlike.PL.Complex3
import Lightlike.PL.StarClosure

/-!
# Stellar subdivisions of a combinatorial 3-manifold as forward Pachner moves

A stellar subdivision of the simplicial complex `ofComplex3 K` at a face `A` with a new vertex `a`
(`SComplex.starAt`, `Lightlike/PL/Stellar.lean`) is realised by 2-3 and 1-4 moves on `K`, with no
inverse move:

* a tetrahedron: one 1-4 move (`ofComplex3_move14_eq_starAt`; `Lightlike.PL.ofComplex3_move14`
  is the same move as a bistellar move);
* a triangle in two tetrahedra: a 1-4 move and one 2-3 move (`ForwardMoves.exists_starAt_triangle`),
  through the star of a complex given by generators (`Lightlike.PL.SComplex.starAt_closure`).

An edge is different: forward moves only add edges (`ForwardMoves.edges_subset`) and the
subdivision at an edge deletes it, so no edge subdivision is a forward descendant
(`not_forwardMoves_starAt_edge`). An edge subdivision is reached only as a common forward
descendant (`CommonForward`).
-/

open Finset Lightlike.PR

namespace Lightlike.PR

open Lightlike.PL Lightlike.PL.SComplex

variable {V : Type*} [DecidableEq V]

/-- A proper subset of `{A, B, C, D}` lies in one of its four triangles. -/
lemma subset_triangle_of_not_superset {A B C D : V} {s : Finset V}
    (hs : s ⊆ {A, B, C, D}) (h : ¬ ({A, B, C, D} : Finset V) ⊆ s) :
    s ⊆ {B, C, D} ∨ s ⊆ {A, C, D} ∨ s ⊆ {A, B, D} ∨ s ⊆ {A, B, C} := by
  by_contra hcon
  rw [not_or, not_or, not_or] at hcon
  obtain ⟨h1, h2, h3, h4⟩ := hcon
  apply h
  intro x hx
  simp only [mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · by_contra hxs
    exact h1 (fun y hy => by
      have := hs hy
      simp only [mem_insert, mem_singleton] at this ⊢
      rcases this with rfl | h | h | h
      · exact absurd hy hxs
      all_goals simp [h])
  · by_contra hxs
    exact h2 (fun y hy => by
      have := hs hy
      simp only [mem_insert, mem_singleton] at this ⊢
      rcases this with h | rfl | h | h
      · simp [h]
      · exact absurd hy hxs
      all_goals simp [h])
  · by_contra hxs
    exact h3 (fun y hy => by
      have := hs hy
      simp only [mem_insert, mem_singleton] at this ⊢
      rcases this with h | h | rfl | h
      · simp [h]
      · simp [h]
      · exact absurd hy hxs
      · simp [h])
  · by_contra hxs
    exact h4 (fun y hy => by
      have := hs hy
      simp only [mem_insert, mem_singleton] at this ⊢
      rcases this with h | h | h | rfl
      · simp [h]
      · simp [h]
      · simp [h]
      · exact absurd hy hxs)

/-- A face of a triangle lies in the tetrahedron obtained by adding a vertex. -/
lemma sub3 {V : Type*} [DecidableEq V] (X Y Z E : V) : ({X, Y, Z} : Finset V) ⊆ {X, Y, Z, E} := by
  intro x hx; simp only [mem_insert, mem_singleton] at hx ⊢; tauto

/-- A tetrahedron lies in the cone on its triangle. -/
lemma sub4 {V : Type*} [DecidableEq V] (X Y Z E : V) :
    ({X, Y, Z, E} : Finset V) ⊆ insert E ({X, Y, Z} : Finset V) := by
  intro x hx; simp only [mem_insert, mem_singleton] at hx ⊢; tauto

/-- The cone on a triangle lies in the tetrahedron. -/
lemma insert_sub {V : Type*} [DecidableEq V] (X Y Z E : V) :
    insert E ({X, Y, Z} : Finset V) ⊆ {X, Y, Z, E} := by
  intro x hx; simp only [mem_insert, mem_singleton] at hx ⊢
  rcases hx with h | h | h | h <;> simp [h]

/-- A tetrahedron of `K` is maximal: a tetrahedron containing it equals it. -/
lemma tet_eq_of_subset {K : Complex3 V} {T t : Finset V} (hT : T ∈ K.tets) (ht : t ∈ K.tets)
    (h : T ⊆ t) : t = T :=
  (eq_of_subset_of_card_le h (by rw [K.card_eq T hT, K.card_eq t ht])).symm

/-- A face of the cone `E * tri` on a triangle (or smaller face) `tri` of the tetrahedron `T` is
either a face of `K` not containing `T`, or a cone on such a face, as in `mem_starAt`. -/
lemma cone_case {K : Complex3 V} {T tri s : Finset V} {E : V} (hT : T ∈ K.tets) (htri : tri ⊆ T)
    (hnot : ¬ T ⊆ tri) (hs : s ⊆ insert E tri) :
    ((∃ t ∈ K.tets, s ⊆ t) ∧ ¬ T ⊆ s) ∨
      ∃ t : Finset V, (∃ u ∈ K.tets, t ⊆ u) ∧ ¬ T ⊆ t ∧ (∃ u ∈ K.tets, T ∪ t ⊆ u) ∧
        insert E t = s := by
  by_cases hEs : E ∈ s
  · right
    have hsub : s.erase E ⊆ tri := fun x hx => by
      have := hs (mem_of_mem_erase hx)
      rcases mem_insert.1 this with h | h
      · exact absurd h (mem_erase.1 hx).1
      · exact h
    refine ⟨s.erase E, ⟨T, hT, hsub.trans htri⟩, fun h => hnot (h.trans hsub), ⟨T, hT, ?_⟩,
      insert_erase hEs⟩
    exact union_subset subset_rfl (hsub.trans htri)
  · left
    have hsub : s ⊆ tri := fun x hx => by
      rcases mem_insert.1 (hs hx) with h | h
      · exact absurd (h ▸ hx) hEs
      · exact h
    exact ⟨⟨T, hT, hsub.trans htri⟩, fun h => hnot (h.trans hsub)⟩

/-- **A stellar subdivision at a tetrahedron is one 1-4 move**: the complex of `move14 K h` is the
stellar subdivision of `ofComplex3 K` at the tetrahedron `ABCD` with new vertex `E`. -/
theorem ofComplex3_move14_eq_starAt {K : Complex3 V} {A B C D E : V} (h : IsMove14 K A B C D E) :
    ofComplex3 (move14 K h) = (ofComplex3 K).starAt {A, B, C, D} E := by
  refine ext_mem fun s => ?_
  rw [mem_starAt]
  simp only [ofComplex3, mem_closure, move14, mem_union, mem_insert, mem_singleton, mem_erase]
  have hT := h.mem
  have mem4 : ∀ x ∈ ({A, B, C, D} : Finset V), x = A ∨ x = B ∨ x = C ∨ x = D := fun x hx => by
    simpa using hx
  have nA : ¬ ({A, B, C, D} : Finset V) ⊆ {A, B, C} := fun hh => by
    have := hh (show D ∈ ({A, B, C, D} : Finset V) by simp)
    simp only [mem_insert, mem_singleton] at this
    rcases this with e | e | e
    exacts [h.hAD e.symm, h.hBD e.symm, h.hCD e.symm]
  have nB : ¬ ({A, B, C, D} : Finset V) ⊆ {A, B, D} := fun hh => by
    have := hh (show C ∈ ({A, B, C, D} : Finset V) by simp)
    simp only [mem_insert, mem_singleton] at this
    rcases this with e | e | e
    exacts [h.hAC e.symm, h.hBC e.symm, h.hCD e]
  have nC : ¬ ({A, B, C, D} : Finset V) ⊆ {A, C, D} := fun hh => by
    have := hh (show B ∈ ({A, B, C, D} : Finset V) by simp)
    simp only [mem_insert, mem_singleton] at this
    rcases this with e | e | e
    exacts [h.hAB e.symm, h.hBC e, h.hBD e]
  have nD : ¬ ({A, B, C, D} : Finset V) ⊆ {B, C, D} := fun hh => by
    have := hh (show A ∈ ({A, B, C, D} : Finset V) by simp)
    simp only [mem_insert, mem_singleton] at this
    rcases this with e | e | e
    exacts [h.hAB e, h.hAC e, h.hAD e]
  have tA : ({A, B, C} : Finset V) ⊆ {A, B, C, D} := by intro x hx; simp at hx ⊢; tauto
  have tB : ({A, B, D} : Finset V) ⊆ {A, B, C, D} := by intro x hx; simp at hx ⊢; tauto
  have tC : ({A, C, D} : Finset V) ⊆ {A, B, C, D} := by intro x hx; simp at hx ⊢; tauto
  have tD : ({B, C, D} : Finset V) ⊆ {A, B, C, D} := by intro x hx; simp at hx ⊢; tauto
  constructor
  · rintro ⟨t, (ht | ht | ht | ht) | ⟨hne, hmem⟩, hst⟩
    · exact cone_case hT tA nA (hst.trans (by rw [ht]; exact sub4 _ _ _ _))
    · exact cone_case hT tB nB (hst.trans (by rw [ht]; exact sub4 _ _ _ _))
    · exact cone_case hT tC nC (hst.trans (by rw [ht]; exact sub4 _ _ _ _))
    · exact cone_case hT tD nD (hst.trans (by rw [ht]; exact sub4 _ _ _ _))
    · left
      exact ⟨⟨t, hmem, hst⟩, fun hh => hne (tet_eq_of_subset hT hmem (hh.trans hst))⟩
  · rintro (⟨⟨t, ht, hst⟩, hn⟩ | ⟨t, ⟨u, hu, htu⟩, hn, ⟨w, hw, hAw⟩, rfl⟩)
    · by_cases htA : t = {A, B, C, D}
      · subst htA
        rcases subset_triangle_of_not_superset hst hn with h1 | h1 | h1 | h1
        · exact ⟨{B, C, D, E}, by simp, h1.trans (sub3 _ _ _ _)⟩
        · exact ⟨{A, C, D, E}, by simp, h1.trans (sub3 _ _ _ _)⟩
        · exact ⟨{A, B, D, E}, by simp, h1.trans (sub3 _ _ _ _)⟩
        · exact ⟨{A, B, C, E}, by simp, h1.trans (sub3 _ _ _ _)⟩
      · exact ⟨t, Or.inr ⟨htA, ht⟩, hst⟩
    · have hwT : w = {A, B, C, D} := tet_eq_of_subset hT hw (subset_union_left.trans hAw)
      subst hwT
      have htT : t ⊆ {A, B, C, D} := subset_union_right.trans hAw
      rcases subset_triangle_of_not_superset htT hn with h1 | h1 | h1 | h1
      · exact ⟨{B, C, D, E}, by simp, (insert_subset_insert E h1).trans (insert_sub _ _ _ _)⟩
      · exact ⟨{A, C, D, E}, by simp, (insert_subset_insert E h1).trans (insert_sub _ _ _ _)⟩
      · exact ⟨{A, B, D, E}, by simp, (insert_subset_insert E h1).trans (insert_sub _ _ _ _)⟩
      · exact ⟨{A, B, C, E}, by simp, (insert_subset_insert E h1).trans (insert_sub _ _ _ _)⟩

/-! ## No edge star is reached by forward moves

Forward moves only add edges (`edges_move23`, `edges_move14`), while the stellar subdivision at an
edge `AB` deletes `AB`. So the star of an edge is never a forward descendant; it is reached only up
to a common forward descendant. -/

/-- **Forward moves keep every edge.** -/
theorem ForwardStep.edges_subset {K K' : Complex3 V} (h : ForwardStep K K') : K.edges ⊆ K'.edges := by
  cases h with
  | m23 h => rw [edges_move23]; exact subset_insert _ _
  | m14 h => rw [edges_move14]; exact subset_union_left

/-- Along a chain of forward moves the edge set only grows. -/
theorem ForwardMoves.edges_subset {K K' : Complex3 V} (h : ForwardMoves K K') :
    K.edges ⊆ K'.edges := by
  induction h with
  | refl => exact subset_rfl
  | tail _ hs ih => exact ih.trans hs.edges_subset

/-- The stellar subdivision at an edge `AB`, with an apex `a` other than `A` and `B`, has no edge
`AB`. -/
theorem pair_notMem_starAt {K : SComplex V} {A B a : V} (haA : a ≠ A) (haB : a ≠ B) :
    ({A, B} : Finset V) ∉ K.starAt {A, B} a := by
  rw [mem_starAt]
  rintro (⟨-, h⟩ | ⟨t, -, -, -, ht⟩)
  · exact h subset_rfl
  · have : a ∈ ({A, B} : Finset V) := ht ▸ mem_insert_self a t
    simp only [mem_insert, mem_singleton] at this
    rcases this with e | e
    exacts [haA e, haB e]

/-- **The star of an edge is not a forward descendant.** If `AB` is an edge of `K` and
`ofComplex3 K'` is the stellar subdivision of `ofComplex3 K` at `AB` (apex `a ∉ {A, B}`), then
there is no chain of 2-3 and 1-4 moves from `K` to `K'`. -/
theorem not_forwardMoves_starAt_edge {K K' : Complex3 V} {A B a : V} (hAB : {A, B} ∈ K.edges)
    (haA : a ≠ A) (haB : a ≠ B)
    (hK' : ofComplex3 K' = (ofComplex3 K).starAt {A, B} a) : ¬ ForwardMoves K K' := by
  intro hf
  obtain ⟨t, ht, hst, -⟩ := Complex3.mem_edges.1 (hf.edges_subset hAB)
  apply pair_notMem_starAt (K := ofComplex3 K) haA haB
  rw [← hK']
  change _ ∈ closure K'.tets
  exact mem_closure.2 ⟨t, ht, hst⟩


/-! ## The star of a triangle -/

/-- **The star of a triangle is two forward moves**: if the triangle `ABC` lies in exactly the two
tetrahedra `ABCD` and `ABCF` and `a` is a fresh vertex, a 1-4 move at `ABCD` with `a` and a 2-3
move on `ABC` with apexes `a` and `F` give the stellar subdivision of `ofComplex3 K` at `ABC`. -/
theorem ForwardMoves.exists_starAt_triangle {K : Complex3 V} {A B C D F a : V}
    (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D) (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D)
    (hAF : A ≠ F) (hBF : B ≠ F) (hCF : C ≠ F) (hDF : D ≠ F)
    (hD : ({A, B, C, D} : Finset V) ∈ K.tets) (hF : ({A, B, C, F} : Finset V) ∈ K.tets)
    (hface : ∀ t ∈ K.tets, ({A, B, C} : Finset V) ⊆ t → t = {A, B, C, D} ∨ t = {A, B, C, F})
    (ha : ∀ t ∈ K.tets, a ∉ t) :
    ∃ K' : Complex3 V, ForwardMoves K K' ∧
      ofComplex3 K' = (ofComplex3 K).starAt {A, B, C} a := by
  have haD := ha _ hD
  have haF := ha _ hF
  simp only [mem_insert, mem_singleton, not_or] at haD haF
  obtain ⟨haA, haB, haC, haD'⟩ := haD
  obtain ⟨-, -, -, haF'⟩ := haF
  have h14 : IsMove14 K A B C D a :=
    ⟨hAB, hAC, hAD, Ne.symm haA, hBC, hBD, Ne.symm haB, hCD, Ne.symm haC, Ne.symm haD', hD,
      fun t ht hat => ha t ht hat⟩
  have hne : ({A, B, C, F} : Finset V) ≠ {A, B, C, D} := fun h => by
    have : F ∈ ({A, B, C, D} : Finset V) := h ▸ by simp
    simp only [mem_insert, mem_singleton] at this
    rcases this with h | h | h | h
    exacts [hAF h.symm, hBF h.symm, hCF h.symm, hDF h.symm]
  have h23 : IsMove23 (move14 K h14) A B C a F := by
    refine ⟨hAB, hAC, Ne.symm haA, hAF, hBC, Ne.symm haB, hBF, Ne.symm haC, hCF, haF',
      ?_, ?_, ?_, ?_⟩
    · simp [move14]
    · simp only [move14, mem_union, mem_erase]
      exact .inr ⟨hne, hF⟩
    · intro t ht hsub
      simp only [move14, mem_union, mem_insert, mem_singleton, mem_erase] at ht
      rcases ht with (rfl | rfl | rfl | rfl) | ⟨htD, ht⟩
      · exact .inl rfl
      · exfalso
        have := hsub (by simp : C ∈ ({A, B, C} : Finset V))
        simp only [mem_insert, mem_singleton] at this
        rcases this with h | h | h | h
        exacts [hAC h.symm, hBC h.symm, hCD h, haC h.symm]
      · exfalso
        have := hsub (by simp : B ∈ ({A, B, C} : Finset V))
        simp only [mem_insert, mem_singleton] at this
        rcases this with h | h | h | h
        exacts [hAB h.symm, hBC h, hBD h, haB h.symm]
      · exfalso
        have := hsub (by simp : A ∈ ({A, B, C} : Finset V))
        simp only [mem_insert, mem_singleton] at this
        rcases this with h | h | h | h
        exacts [hAB h, hAC h, hAD h, haA h.symm]
      · rcases hface t ht hsub with h | h
        · exact absurd h htD
        · exact .inr h
    · intro t ht hsub
      have haT : a ∈ t := hsub (by simp)
      have hFT : F ∈ t := hsub (by simp)
      simp only [move14, mem_union, mem_insert, mem_singleton, mem_erase] at ht
      rcases ht with (rfl | rfl | rfl | rfl) | ⟨-, ht⟩
      all_goals first | exact ha _ ht haT | (simp only [mem_insert, mem_singleton] at hFT; grind)
  refine ⟨move23 (move14 K h14) h23, (Relation.ReflTransGen.single (.m14 h14)).tail (.m23 h23), ?_⟩
  rw [ofComplex3, ofComplex3, starAt_closure]
  congr 1
  ext t
  simp only [move23, move14, mem_union, mem_insert, mem_singleton, mem_erase, mem_filter,
    mem_biUnion, mem_image]
  constructor
  · rintro ((rfl | rfl | rfl) | ⟨h1, h2, (rfl | rfl | rfl | rfl) | ⟨h3, ht⟩⟩)
    · exact .inr ⟨{A, B, C, F}, ⟨hF, by intro x; simp; tauto⟩, C, by simp, by ext y; simp; grind⟩
    · exact .inr ⟨{A, B, C, F}, ⟨hF, by intro x; simp; tauto⟩, A, by simp, by ext y; simp; grind⟩
    · exact .inr ⟨{A, B, C, F}, ⟨hF, by intro x; simp; tauto⟩, B, by simp, by ext y; simp; grind⟩
    · exact absurd rfl h2
    · exact .inr ⟨{A, B, C, D}, ⟨hD, by intro x; simp; tauto⟩, C, by simp, by ext y; simp; grind⟩
    · exact .inr ⟨{A, B, C, D}, ⟨hD, by intro x; simp; tauto⟩, B, by simp, by ext y; simp; grind⟩
    · exact .inr ⟨{A, B, C, D}, ⟨hD, by intro x; simp; tauto⟩, A, by simp, by ext y; simp; grind⟩
    · refine .inl ⟨ht, fun hsub => ?_⟩
      rcases hface t ht hsub with h | h
      · exact h3 h
      · exact h1 h
  · rintro (⟨ht, hsub⟩ | ⟨u, ⟨hu, hsub⟩, x, hx, rfl⟩)
    · have hT : ∀ T : Finset V, ({A, B, C} : Finset V) ⊆ T → t ≠ T := fun T hT h =>
        hsub (h ▸ hT)
      refine .inr ⟨hT _ (by intro y; simp; tauto), hT _ (by intro y; simp; tauto),
        .inr ⟨hT _ (by intro y; simp; tauto), ht⟩⟩
    · have ne_of : ∀ (S T : Finset V) (y : V), y ∈ T → y ∉ S → S ≠ T :=
        fun S T y hT hS h => hS (h ▸ hT)
      have nC : ∀ S : Finset V, C ∉ S → S ≠ {A, B, C, F} ∧ S ≠ {A, B, C, a} := fun S hS =>
        ⟨ne_of _ _ C (by simp) hS, ne_of _ _ C (by simp) hS⟩
      have nB : ∀ S : Finset V, B ∉ S → S ≠ {A, B, C, F} ∧ S ≠ {A, B, C, a} := fun S hS =>
        ⟨ne_of _ _ B (by simp) hS, ne_of _ _ B (by simp) hS⟩
      have nA : ∀ S : Finset V, A ∉ S → S ≠ {A, B, C, F} ∧ S ≠ {A, B, C, a} := fun S hS =>
        ⟨ne_of _ _ A (by simp) hS, ne_of _ _ A (by simp) hS⟩
      rcases hface u hu hsub with rfl | rfl <;> obtain hx | hx | hx := hx <;> rw [hx]
      · have e : insert a (({A, B, C, D} : Finset V).erase A) = {B, C, D, a} := by
          ext y; simp; grind
        rw [e]
        exact .inr ⟨(nA _ (by simp; grind)).1, (nA _ (by simp; grind)).2, .inl (.inr (.inr (.inr rfl)))⟩
      · have e : insert a (({A, B, C, D} : Finset V).erase B) = {A, C, D, a} := by
          ext y; simp; grind
        rw [e]
        exact .inr ⟨(nB _ (by simp; grind)).1, (nB _ (by simp; grind)).2, .inl (.inr (.inr (.inl rfl)))⟩
      · have e : insert a (({A, B, C, D} : Finset V).erase C) = {A, B, D, a} := by
          ext y; simp; grind
        rw [e]
        exact .inr ⟨(nC _ (by simp; grind)).1, (nC _ (by simp; grind)).2, .inl (.inr (.inl rfl))⟩
      · have e : insert a (({A, B, C, F} : Finset V).erase A) = {B, C, a, F} := by
          ext y; simp; grind
        rw [e]
        exact .inl (.inr (.inl rfl))
      · have e : insert a (({A, B, C, F} : Finset V).erase B) = {C, A, a, F} := by
          ext y; simp; grind
        rw [e]
        exact .inl (.inr (.inr rfl))
      · have e : insert a (({A, B, C, F} : Finset V).erase C) = {A, B, a, F} := by
          ext y; simp; grind
        rw [e]
        exact .inl (.inl rfl)

end Lightlike.PR
