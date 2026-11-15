import Lightlike.PL.Ball

/-!
# Attaching a cone along a boundary ball

For a complex `M`, a subcomplex `K` and a new vertex `v`, write `v ⋆ K ∪ M` for the complex obtained
by attaching the cone on `K` to `M` along `K`. The predicate `ConeAttach v K M` says that this is
stellar equivalent to `M`. This file collects the moves that transport the statement along stellar
subdivisions of `K`, the first ingredient of Lickorish's Lemma 3.7.

## Main results

* `ConeAttach.of_starAt`: a subdivision of `K` and `M` at a common face reduces the statement to
  the subdivided pair.
* `ConeAttach.of_starAt_outside`: a subdivision of `M` at a face outside `K` leaves the statement
  unchanged.
-/

open Finset

namespace Lightlike.PL
namespace SComplex

variable {V : Type*} [DecidableEq V]

/-- `ConeAttach v K M`: attaching the cone `v ⋆ K` to `M` along `K` does not change the stellar
equivalence class of `M`. -/
def ConeAttach (v : V) (K M : SComplex V) : Prop :=
  StellarEquivIn ((cone v K).union M) M

/-- Subdividing the face `A` of `K ⊆ M` (away from the apex) in both complexes: the statement for
the subdivided pair implies the statement for the original pair. -/
theorem ConeAttach.of_starAt {v a : V} {K M : SComplex V} {A : Finset V} (hAK : A ∈ K)
    (hAM : A ∈ M) (hne : A.Nonempty) (hvK : v ∉ K.verts) (hvM : v ∉ M.verts)
    (haM : a ∉ M.verts) (haK : a ∉ K.verts) (hav : a ≠ v)
    (h : ConeAttach v (K.starAt A a) (M.starAt A a)) : ConeAttach v K M := by
  have hvA : v ∉ A := fun hv => hvK (subset_verts hAK hv)
  have haX : a ∉ ((cone v K).union M).verts := by
    rw [verts_union]
    intro h'
    rcases mem_union.1 h' with h' | h'
    · rcases mem_insert.1 (verts_cone_subset K v h') with h'' | h''
      · exact hav h''
      · exact haK h''
    · exact haM h'
  have hAX : A ∈ (cone v K).union M := mem_union_iff.2 (.inr hAM)
  have e : ((cone v K).union M).starAt A a =
      (cone v (K.starAt A a)).union (M.starAt A a) := by
    rw [starAt_union, cone_starAt hvK hvA]
  have s1 := StellarEquivIn.starAt hAX hne haX
  rw [e] at s1
  exact s1.trans (h.trans (StellarEquivIn.starAt hAM hne haM).symm)

/-- Subdividing `M` at a face `A` that is not in `K` (and avoids the apex) does not affect the cone
`v ⋆ K`: the statement for the subdivided `M` implies the statement for `M`. -/
theorem ConeAttach.of_starAt_outside {v a : V} {K M : SComplex V} {A : Finset V} (hAM : A ∈ M)
    (hAK : A ∉ K) (hne : A.Nonempty) (hvM : v ∉ M.verts) (haM : a ∉ M.verts) (haK : a ∉ K.verts)
    (hav : a ≠ v) (h : ConeAttach v K (M.starAt A a)) : ConeAttach v K M := by
  have hvA : v ∉ A := fun hv => hvM (subset_verts hAM hv)
  have hAC : A ∉ cone v K := by
    intro hA
    obtain ⟨t, ht, h' | h'⟩ := mem_cone.1 hA
    · exact hAK (h' ▸ ht)
    · exact hvA (h' ▸ mem_insert_self v t)
  have haX : a ∉ ((cone v K).union M).verts := by
    rw [verts_union]
    intro h'
    rcases mem_union.1 h' with h' | h'
    · rcases mem_insert.1 (verts_cone_subset K v h') with h'' | h''
      · exact hav h''
      · exact haK h''
    · exact haM h'
  have hAX : A ∈ (cone v K).union M := mem_union_iff.2 (.inr hAM)
  have e : ((cone v K).union M).starAt A a = (cone v K).union (M.starAt A a) := by
    rw [starAt_union, starAt_of_notMem hAC]
  have s1 := StellarEquivIn.starAt hAX hne haX
  rw [e] at s1
  exact s1.trans (h.trans (StellarEquivIn.starAt hAM hne haM).symm)

/-! ## Starring a ball inside a larger complex -/

/-- A tame move is a stellar equivalence. -/
lemma TStep.stellarEquivIn {E X Y : SComplex V} {S : Finset V} (h : TStep E S X Y) :
    StellarEquivIn X Y := by
  rcases h with ⟨B, b, hs, rfl⟩ | ⟨B, b, hs, -, rfl⟩
  · exact StellarEquivIn.starAt hs.1 hs.2.1 hs.2.2.2.1
  · exact (StellarEquivIn.starAt hs.1 hs.2.1 hs.2.2.2.1).symm

/-- A chain of tame moves is a stellar equivalence. -/
lemma TChain.stellarEquivIn {E X Y : SComplex V} {S : Finset V} (h : TChain E S X Y) :
    StellarEquivIn X Y := by
  induction h with
  | refl => exact StellarEquivIn.refl _
  | tail _ h ih => exact ih.trans h.stellarEquivIn

/-- **Starring a ball inside a complex.** If `P` is a PL ball and `R` meets `P` only inside the
boundary of `P`, then replacing `P` by the cone `y ⋆ ∂P` from a new vertex `y` is a stellar
equivalence of `P ∪ R`. -/
theorem stellarEquivIn_star_ball [Infinite V] {P R : SComplex V} {m : ℕ} (hP : IsSB true m P)
    (hB : IsBallIn P) (hv : ∀ x ∈ R.verts, x ∈ P.verts → x ∈ P.bd.verts)
    (hf : ∀ s ∈ P, s ∈ R → s ∈ P.bd) {y : V} (hyP : y ∉ P.verts) (hyR : y ∉ R.verts) :
    StellarEquivIn (P.union R) ((cone y P.bd).union R) := by
  have hst := starrable_ball m P hP hB R.verts (fun x hxS hxP => hv x hxS hxP) y
    (fun h => hyR h) hyP (fun h => hyP (mem_verts.2 (bd_subset (mem_verts.1 h))))
  have hg := hst.glue (R := R) (E' := P.bd) (S' := ∅) subset_rfl hv hf
    subset_union_left (fun s hs => .inl hs) (empty_subset _)
  exact hg.stellarEquivIn

/-! ## Cones on balls -/

/-- The cone on `∂B` is a stellar subdivision of the simplex `Δ_B`. -/
lemma stellarEquivIn_cone_boundary {B : Finset V} (hB : B.Nonempty) {v : V} (hv : v ∉ B) :
    StellarEquivIn (cone v (boundary B)) (simplex B) := by
  have e : (simplex ((∅ : Finset V) ∪ B)).starAt B v = cone v (boundary B) := by
    rw [starAt_simplex_eq_join (Finset.disjoint_empty_left B)]
    rfl
  rw [empty_union] at e
  rw [← e]
  refine (StellarEquivIn.starAt (mem_simplex.2 subset_rfl) hB ?_).symm
  rwa [verts_simplex]

/-- **A cone on a ball or sphere model is a ball model**: if `L` is a PL `(m-1)`-sphere or ball
and `v` is not a vertex of `L`, then `v ⋆ L` is a PL `m`-ball. -/
theorem isSB_cone [Infinite V] {m : ℕ} {L : SComplex V} (h : IsSB true m L) {v : V}
    (hv : v ∉ L.verts) : IsSB true (m + 1) (cone v L) := by
  rcases h with ⟨A, hA, hLA⟩ | ⟨-, A, hA, hLA⟩
  · obtain ⟨B, hB, hBd⟩ := exists_card_disjoint ({v} ∪ L.verts) (m + 1)
    rw [disjoint_union_right] at hBd
    have hLB : StellarEquivIn L (boundary B) :=
      hLA.trans (StellarEquivIn.boundary_of_card (hA.trans hB.symm))
    have hBne : B.Nonempty := card_pos.1 (by omega)
    have hvB : v ∉ B := fun h => disjoint_left.1 hBd.1 h (mem_singleton_self v)
    have hvB' : (boundary B).verts ⊆ B := fun z hz => (mem_boundary.1 (mem_verts.1 hz)).subset
      (mem_singleton_self z)
    have h1 : StellarEquivIn (cone v L) (cone v (boundary B)) := by
      unfold cone
      rw [join_comm, join_comm (simplex {v})]
      refine StellarEquivIn.join_right hLB (mem_simplex.2 (empty_subset _)) ?_ ?_
      · rw [verts_simplex, disjoint_singleton_right]; exact hv
      · rw [verts_simplex, disjoint_singleton_right]; exact fun h => hvB (hvB' h)
    exact .inr ⟨rfl, B, hB, h1.trans (stellarEquivIn_cone_boundary hBne hvB)⟩
  · obtain ⟨C, hC, hCd⟩ := exists_card_disjoint ({v} ∪ L.verts) m
    rw [disjoint_union_right] at hCd
    have hLC : StellarEquivIn L (simplex C) :=
      hLA.trans (StellarEquivIn.simplex_of_card (hA.trans hC.symm))
    have hvC : v ∉ C := fun h => disjoint_left.1 hCd.1 h (mem_singleton_self v)
    have h1 : StellarEquivIn (cone v L) (cone v (simplex C)) := by
      unfold cone
      rw [join_comm, join_comm (simplex {v})]
      refine StellarEquivIn.join_right hLC (mem_simplex.2 (empty_subset _)) ?_ ?_
      · rw [verts_simplex, disjoint_singleton_right]; exact hv
      · rw [verts_simplex]; exact hCd.1
    refine .inr ⟨rfl, insert v C, ?_, ?_⟩
    · rw [card_insert_of_notMem hvC, hC]
    · rw [simplex_insert_eq_cone]; exact h1

/-- **The star of a boundary vertex is a ball**: if `{b}` lies in the boundary of a combinatorial
`n`-manifold `M`, then the star of `b` is a PL ball (a cone on the ball `lk(b, M)`). -/
theorem IsMfdIn.isBall_star [Infinite V] {n : ℕ} {M : SComplex V} (hM : IsMfdIn true n M) {b : V}
    (hb : {b} ∈ M.bd) : ∃ m, IsSB true m (M.star {b}) ∧ IsBallIn (M.star {b}) := by
  have hbM : {b} ∈ M := bd_subset hb
  have hL : IsBallIn (M.link {b}) := (hM.mem_bd_iff hbM (singleton_nonempty b)).1 hb
  obtain ⟨m, -, hSB⟩ := (isMfdIn_main true n).1 M hM {b} hbM (singleton_nonempty b)
  have hbL : b ∉ (M.link {b}).verts := fun h =>
    disjoint_left.1 (disjoint_verts_link M {b}) (mem_singleton_self b) h
  have e : M.star {b} = cone b (M.link {b}) := star_eq_join M {b}
  rw [e]
  have hS := isSB_cone hSB hbL
  refine ⟨m + 1, hS, (hS.isBallIn_iff).2 ?_⟩
  unfold cone
  rw [signedCount_join (by rw [verts_simplex, disjoint_singleton_left]; exact hbL),
    signedCount_simplex (singleton_nonempty b), zero_mul]

/-! ## Links and boundary of a cone -/

/-- The link of a face `u` of `L` (not through the apex) in the cone `w ⋆ L` is the cone on the
link of `u` in `L`. -/
lemma link_cone_of_mem {w : V} {L : SComplex V} {u : Finset V} (hw : w ∉ L.verts) (hu : u ∈ L) :
    (cone w L).link u = cone w (L.link u) := by
  have := link_join (P := simplex {w}) (Q := L) (t := ∅) (u := u)
    (by rw [verts_simplex, disjoint_singleton_left]; exact hw) (mem_simplex.2 (empty_subset _)) hu
  rw [empty_union, link_empty] at this
  exact this

/-- The link of a face `insert w ρ` through the apex of the cone `w ⋆ L` is the link of `ρ` in
`L`. -/
lemma link_cone_insert {w : V} {L : SComplex V} {ρ : Finset V} (hw : w ∉ L.verts) (hρ : ρ ∈ L) :
    (cone w L).link (insert w ρ) = L.link ρ := by
  have := link_join (P := simplex {w}) (Q := L) (t := {w}) (u := ρ)
    (by rw [verts_simplex, disjoint_singleton_left]; exact hw)
    (mem_simplex.2 subset_rfl) hρ
  rw [← insert_eq, link_simplex (subset_refl _), sdiff_self, Finset.bot_eq_empty, simplex_empty_join] at this
  exact this

/-- A cone on a ball or sphere model is a ball. -/
lemma isBallIn_cone [Infinite V] {m : ℕ} {L : SComplex V} (hL : IsSB true m L) {w : V}
    (hw : w ∉ L.verts) : IsBallIn (cone w L) := by
  refine ((isSB_cone hL hw).isBallIn_iff).2 ?_
  unfold cone
  rw [signedCount_join (by rw [verts_simplex, disjoint_singleton_left]; exact hw),
    signedCount_simplex (singleton_nonempty w), zero_mul]

/-- **The boundary of a cone on a ball**: for a PL ball `L` (given as `IsSB`-model) and a vertex
`w ∉ L`, the boundary of `w ⋆ L` consists of `L` together with the cone on `∂L`. -/
theorem bd_cone [Infinite V] {m : ℕ} {L : SComplex V} (hL : IsSB true m L) (hLb : IsBallIn L)
    (h0 : ∅ ∈ L) {w : V} (hw : w ∉ L.verts) : (cone w L).bd = L.union (cone w L.bd) := by
  have hSB := isSB_cone hL hw
  have hP : IsMfdIn true m (cone w L) := (isMfdIn_main true m).2 _ hSB
  have hL0 : ∅ ∈ L.bd := mem_bd.2 ⟨h0, .inl rfl⟩
  refine ext_mem fun σ => ?_
  rw [mem_union_iff, mem_cone]
  constructor
  · intro hσ
    have hσP := bd_subset hσ
    obtain ⟨t, ht, hσt⟩ := mem_cone.1 hσP
    rcases hσt with rfl | rfl
    · exact .inl ht
    · refine .inr ⟨t, ?_, .inr rfl⟩
      rcases t.eq_empty_or_nonempty with rfl | htne
      · exact hL0
      · have hlink := (hP.mem_bd_iff hσP (insert_nonempty w t)).1 hσ
        rw [link_cone_insert hw ht] at hlink
        have hLm : IsMfdIn true (m - 1) L := by
          rcases m with _ | k
          · exact absurd (hL.verts_eq_empty ▸ subset_verts ht (htne.choose_spec)) (notMem_empty _)
          · exact (isMfdIn_main true k).2 _ hL
        obtain ⟨m', -, hm'⟩ := (isMfdIn_main true (m - 1)).1 L hLm t ht htne
        exact ((hLm.mem_bd_iff ht htne).2 hlink)
  · have hLsub : ∀ σ ∈ L, σ ∈ (cone w L).bd := by
      intro σ hσ
      rcases σ.eq_empty_or_nonempty with rfl | hne
      · exact mem_bd.2 ⟨mem_cone.2 ⟨∅, h0, .inl rfl⟩, .inl rfl⟩
      · have hσP : σ ∈ cone w L := mem_cone.2 ⟨σ, hσ, .inl rfl⟩
        rcases m with _ | k
        · exact absurd (hL.verts_eq_empty ▸ subset_verts hσ (hne.choose_spec)) (notMem_empty _)
        have hLm : IsMfdIn true k L := (isMfdIn_main true k).2 _ hL
        obtain ⟨m', -, hm'⟩ := (isMfdIn_main true k).1 L hLm σ hσ hne
        refine (hP.mem_bd_iff hσP hne).2 ?_
        rw [link_cone_of_mem hw hσ]
        exact isBallIn_cone hm' (fun h => hw (verts_link_subset L σ h))
    rintro (hσ | ⟨t, htb, hσt⟩)
    · exact hLsub σ hσ
    · have htL := bd_subset htb
      rcases hσt with rfl | rfl
      · exact hLsub σ htL
      · have hσP : insert w t ∈ cone w L := mem_cone.2 ⟨t, htL, .inr rfl⟩
        refine (hP.mem_bd_iff hσP (insert_nonempty w t)).2 ?_
        rw [link_cone_insert hw htL]
        rcases t.eq_empty_or_nonempty with rfl | hne
        · rwa [link_empty]
        · rcases m with _ | k
          · exact absurd (hL.verts_eq_empty ▸ subset_verts htL (hne.choose_spec)) (notMem_empty _)
          have hLm : IsMfdIn true k L := (isMfdIn_main true k).2 _ hL
          exact (hLm.mem_bd_iff htL hne).1 htb

/-! ## The wing lemma -/

/-- Faces of a double cone. -/
lemma mem_cone_cone {a b : V} {J : SComplex V} {s : Finset V} :
    s ∈ cone a (cone b J) ↔ ∃ j ∈ J, s = j ∨ s = insert b j ∨ s = insert a j ∨
      s = insert a (insert b j) := by
  rw [mem_cone]
  constructor
  · rintro ⟨t, ht, h | h⟩
    · obtain ⟨j, hj, h' | h'⟩ := mem_cone.1 ht
      · exact ⟨j, hj, .inl (h.trans h')⟩
      · exact ⟨j, hj, .inr (.inl (h.trans h'))⟩
    · obtain ⟨j, hj, h' | h'⟩ := mem_cone.1 ht
      · exact ⟨j, hj, .inr (.inr (.inl (h.trans (by rw [h']))))⟩
      · exact ⟨j, hj, .inr (.inr (.inr (h.trans (by rw [h']))))⟩
  · rintro ⟨j, hj, h | h | h | h⟩
    · exact ⟨j, mem_cone.2 ⟨j, hj, .inl rfl⟩, .inl h⟩
    · exact ⟨insert b j, mem_cone.2 ⟨j, hj, .inr rfl⟩, .inl h⟩
    · exact ⟨j, mem_cone.2 ⟨j, hj, .inl rfl⟩, .inr h⟩
    · exact ⟨insert b j, mem_cone.2 ⟨j, hj, .inr rfl⟩, .inr h⟩

/-- **The wing lemma.** Let `J ⊆ M0` with `y ⋆ J ⊆ M0`, and let `v, w` be two vertices outside
`M0` and `J`, distinct from `y` and from each other. Attaching a second cone `v ⋆ w ⋆ J` to
`M0 ∪ w ⋆ y ⋆ J` along `w ⋆ J` does not change the stellar equivalence class: the result is the
subdivision of `M0 ∪ v ⋆ y ⋆ J` at the edge `{y, v}` with new vertex `w`, and `M0 ∪ v ⋆ y ⋆ J`
is isomorphic to `M0 ∪ w ⋆ y ⋆ J` by exchanging `v` and `w`. -/
theorem wing [Infinite V] {M0 J : SComplex V} {y v w : V} (hJe : ∅ ∈ J) (hJ0 : ∀ j ∈ J, j ∈ M0)
    (hyJ : ∀ j ∈ J, insert y j ∈ M0) (hvM : v ∉ M0.verts) (hwM : w ∉ M0.verts)
    (hvJ : v ∉ J.verts) (hwJ : w ∉ J.verts) (hyJ' : y ∉ J.verts) (hyv : y ≠ v) (hyw : y ≠ w)
    (hvw : v ≠ w) :
    StellarEquivIn ((M0.union (cone w (cone y J))).union (cone v (cone w J)))
      (M0.union (cone w (cone y J))) := by
  have hv0 : ∀ s ∈ M0, v ∉ s := fun s hs h => hvM (mem_verts_of_mem hs h)
  have hw0 : ∀ s ∈ M0, w ∉ s := fun s hs h => hwM (mem_verts_of_mem hs h)
  have hjv : ∀ j ∈ J, v ∉ j := fun s hs h => hvJ (mem_verts_of_mem hs h)
  have hjw : ∀ j ∈ J, w ∉ j := fun s hs h => hwJ (mem_verts_of_mem hs h)
  have hjy : ∀ j ∈ J, y ∉ j := fun s hs h => hyJ' (mem_verts_of_mem hs h)
  set B : Finset V := insert y {v} with hB
  have hyB : y ∈ B := mem_insert_self _ _
  have hvB : v ∈ B := mem_insert_of_mem (mem_singleton_self v)
  set Z : SComplex V := M0.union (cone v (cone y J)) with hZ
  have hZmem : ∀ s, s ∈ Z ↔ s ∈ M0 ∨ ∃ j ∈ J, s = j ∨ s = insert y j ∨ s = insert v j ∨
      s = insert v (insert y j) := fun s => by
    rw [hZ, mem_union_iff, mem_cone_cone]
  have hwZ : w ∉ Z.verts := by
    intro h
    obtain ⟨t, ht, hwt⟩ : ∃ t ∈ Z, w ∈ t := ⟨{w}, mem_verts.1 h, mem_singleton_self w⟩
    rcases (hZmem t).1 ht with h' | ⟨j, hj, e | e | e | e⟩
    · exact hw0 t h' hwt
    · exact hjw j hj (e ▸ hwt)
    · rw [e] at hwt
      rcases mem_insert.1 hwt with h' | h'
      · exact hyw h'.symm
      · exact hjw j hj h'
    · rw [e] at hwt
      rcases mem_insert.1 hwt with h' | h'
      · exact hvw h'.symm
      · exact hjw j hj h'
    · rw [e] at hwt
      rcases mem_insert.1 hwt with h' | h'
      · exact hvw h'.symm
      · rcases mem_insert.1 h' with h'' | h''
        · exact hyw h''.symm
        · exact hjw j hj h''
  have hBZ : B ∈ Z := by
    rw [hZmem]
    exact .inr ⟨∅, hJe, .inr (.inr (.inr (by ext x; simp [hB, or_comm])))⟩
  have hnB : ∀ s : Finset V, (v ∉ s ∨ y ∉ s) → ¬ B ⊆ s := fun s h hs => by
    rcases h with h | h
    · exact h (hs hvB)
    · exact h (hs hyB)
  have hBu : ∀ j : Finset V, B ∪ j = insert v (insert y j) := fun j => by
    ext x; simp [hB]; tauto
  have hZyj : ∀ j ∈ J, insert y j ∈ Z := fun j hj => (hZmem _).2 (.inr ⟨j, hj, .inr (.inl rfl)⟩)
  have hZj : ∀ j ∈ J, j ∈ Z := fun j hj => (hZmem _).2 (.inr ⟨j, hj, .inl rfl⟩)
  have hZvj : ∀ j ∈ J, insert v j ∈ Z := fun j hj =>
    (hZmem _).2 (.inr ⟨j, hj, .inr (.inr (.inl rfl))⟩)
  have hZvyj : ∀ j ∈ J, insert v (insert y j) ∈ Z := fun j hj =>
    (hZmem _).2 (.inr ⟨j, hj, .inr (.inr (.inr rfl))⟩)
  have hX : (M0.union (cone w (cone y J))).union (cone v (cone w J)) = Z.starAt B w := by
    refine ext_mem fun s => ?_
    rw [mem_starAt, mem_union_iff, mem_union_iff, mem_cone_cone, mem_cone_cone]
    constructor
    · rintro ((h | ⟨j, hj, e | e | e | e⟩) | ⟨j, hj, e | e | e | e⟩)
      · exact .inl ⟨(hZmem s).2 (.inl h), hnB s (.inl (hv0 s h))⟩
      · subst e; exact .inl ⟨hZj s hj, hnB _ (.inl (hjv _ hj))⟩
      · subst e
        exact .inl ⟨hZyj j hj, hnB _ (.inl (fun h => by
          rcases mem_insert.1 h with h | h
          · exact hyv h.symm
          · exact hjv j hj h))⟩
      · subst e
        refine .inr ⟨j, hZj j hj, hnB _ (.inl (hjv j hj)), ?_, rfl⟩
        rw [hBu]; exact hZvyj j hj
      · subst e
        refine .inr ⟨insert y j, hZyj j hj, hnB _ (.inl (fun h => by
          rcases mem_insert.1 h with h | h
          · exact hyv h.symm
          · exact hjv j hj h)), ?_, rfl⟩
        rw [hBu, insert_eq_of_mem (mem_insert_self y j)]; exact hZvyj j hj
      · subst e; exact .inl ⟨hZj s hj, hnB _ (.inl (hjv _ hj))⟩
      · subst e
        refine .inr ⟨j, hZj j hj, hnB _ (.inl (hjv j hj)), ?_, rfl⟩
        rw [hBu]; exact hZvyj j hj
      · subst e
        exact .inl ⟨hZvj j hj, hnB _ (.inr (fun h => by
          rcases mem_insert.1 h with h | h
          · exact hyv h
          · exact hjy j hj h))⟩
      · subst e
        refine .inr ⟨insert v j, hZvj j hj, hnB _ (.inr (fun h => by
          rcases mem_insert.1 h with h | h
          · exact hyv h
          · exact hjy j hj h)), ?_, ?_⟩
        · rw [hBu]
          have : insert v (insert y (insert v j)) = insert v (insert y j) := by
            ext x; simp; tauto
          rw [this]; exact hZvyj j hj
        · ext x; simp; tauto
    · rintro (⟨hsZ, hBs⟩ | ⟨t, htZ, hBt, hBtZ, rfl⟩)
      · rcases (hZmem s).1 hsZ with h | ⟨j, hj, e | e | e | e⟩
        · exact .inl (.inl h)
        · exact .inl (.inl (e ▸ hJ0 j hj))
        · exact .inl (.inl (e ▸ hyJ j hj))
        · exact .inr ⟨j, hj, .inr (.inr (.inl e))⟩
        · exact absurd (by rw [e, ← hBu j]; exact subset_union_left) hBs
      · rcases (hZmem _).1 hBtZ with h | ⟨j, hj, e | e | e | e⟩
        · exact absurd (mem_union_left _ hvB) (hv0 _ h)
        · exact absurd (e ▸ mem_union_left _ hvB) (hjv j hj)
        · rcases mem_insert.1 (e ▸ mem_union_left t hvB) with h' | h'
          · exact absurd h'.symm hyv
          · exact absurd h' (hjv j hj)
        · rcases mem_insert.1 (e ▸ mem_union_left t hyB) with h' | h'
          · exact absurd h' hyv
          · exact absurd h' (hjy j hj)
        · have hsub : t ⊆ insert v (insert y j) := e ▸ subset_union_right
          by_cases hvt : v ∈ t
          · have hyt : y ∉ t := fun h => hBt (insert_subset h (singleton_subset_iff.2 hvt))
            have ht' : t.erase v ∈ J := down_mem hj (by
              intro x hx
              obtain ⟨hxv, hxt⟩ := mem_erase.1 hx
              rcases mem_insert.1 (hsub hxt) with h | h
              · exact absurd h hxv
              · rcases mem_insert.1 h with h | h
                · exact absurd (h ▸ hxt) hyt
                · exact h)
            refine .inr ⟨t.erase v, ht', .inr (.inr (.inr ?_))⟩
            ext x
            simp only [mem_insert, mem_erase]
            by_cases hx : x = v <;> simp [hx, hvt]
          · have htc : t ∈ cone y J := down_mem (mem_cone.2 ⟨j, hj, .inr rfl⟩) (by
              intro x hx
              rcases mem_insert.1 (hsub hx) with h | h
              · exact absurd (h ▸ hx) hvt
              · exact h)
            obtain ⟨j', hj', e' | e'⟩ := mem_cone.1 htc
            · exact .inl (.inr ⟨j', hj', .inr (.inr (.inl (by rw [e'])))⟩)
            · exact .inl (.inr ⟨j', hj', .inr (.inr (.inr (by rw [e'])))⟩)
  have h1 : StellarEquivIn Z (Z.starAt B w) := StellarEquivIn.starAt hBZ ⟨y, hyB⟩ hwZ
  have hsw : ∀ x, x ≠ v → x ≠ w → (Equiv.swap v w) x = x := fun x h1 h2 =>
    Equiv.swap_apply_of_ne_of_ne h1 h2
  have hM0 : M0.map (Equiv.swap v w).toEmbedding = M0 := by
    rw [map_congr (g := Function.Embedding.refl V), map_refl]
    intro x hx
    exact hsw x (fun h => hvM (h ▸ hx)) (fun h => hwM (h ▸ hx))
  have hJm : J.map (Equiv.swap v w).toEmbedding = J := by
    rw [map_congr (g := Function.Embedding.refl V), map_refl]
    intro x hx
    exact hsw x (fun h => hvJ (h ▸ hx)) (fun h => hwJ (h ▸ hx))
  have h2 : Z.map (Equiv.swap v w).toEmbedding = M0.union (cone w (cone y J)) := by
    rw [hZ, map_union, map_cone, map_cone, hM0, hJm]
    show _ = _
    have e1 : (Equiv.swap v w).toEmbedding v = w := by simp
    have e2 : (Equiv.swap v w).toEmbedding y = y := by
      simp [Equiv.swap_apply_of_ne_of_ne hyv hyw]
    rw [e1, e2]
  rw [hX]
  exact h1.symm.trans (h2 ▸ StellarEquivIn.map_swap Z v w)

/-! ## The base case of the collar lemma -/

/-- If a cone `w ⋆ J` lies in the boundary of a manifold `M`, with `w` an interior vertex of the
cone, and the interior faces of the cone have all their boundary neighbours inside it, then the
link of `w` in `M` has boundary exactly `J`. -/
lemma link_bd_eq_of_cone [Infinite V] {n n' : ℕ} {M J : SComplex V} {w : V} (hM : IsMfdIn true n M)
    (hL : IsMfdIn true n' (M.link {w})) (hJe : ∅ ∈ J) (hw : w ∉ J.verts)
    (hK : ∀ s ∈ cone w J, s ∈ M.bd) (hint : {w} ∉ (cone w J).bd)
    (hF : ∀ A ∈ cone w J, A ∉ (cone w J).bd → ∀ s ∈ M.bd, A ⊆ s → s ∈ cone w J) :
    (M.link {w}).bd = J := by
  have hw1 : {w} ∈ cone w J := mem_cone.2 ⟨∅, hJe, .inr (by simp)⟩
  have hwb : {w} ∈ M.bd := hK _ hw1
  rw [← hM.link_bd_eq hL hwb (singleton_nonempty w)]
  refine ext_mem fun s => ?_
  rw [mem_link']
  constructor
  · rintro ⟨hd, hs⟩
    have h := hF {w} hw1 hint _ hs subset_union_left
    obtain ⟨t, ht, e | e⟩ := mem_cone.1 h
    · exact absurd (mem_verts_of_mem ht (e ▸ (by simp : w ∈ ({w} ∪ s : Finset V)))) hw
    · have hwt : w ∉ t := fun h => hw (mem_verts_of_mem ht h)
      have hws : w ∉ s := fun h => disjoint_singleton_left.1 hd h
      have : s = t := by
        ext x
        have := congrArg (x ∈ ·) e
        simp only [mem_insert, mem_union, mem_singleton] at this
        by_cases hx : x = w
        · subst hx; simp [hws, hwt]
        · simpa [hx] using this
      exact this ▸ ht
  · intro hs
    have hws : w ∉ s := fun h => hw (mem_verts_of_mem hs h)
    exact ⟨disjoint_singleton_left.2 hws,
      hK _ (mem_cone.2 ⟨s, hs, .inr (Finset.insert_eq w s)⟩)⟩

/-- The cone on a cone does not depend on the order of the apexes. -/
lemma cone_cone_comm (a b : V) (J : SComplex V) : cone a (cone b J) = cone b (cone a J) :=
  ext_mem fun s => by
    rw [mem_cone_cone, mem_cone_cone]
    constructor <;> rintro ⟨j, hj, h | h | h | h⟩
    · exact ⟨j, hj, .inl h⟩
    · exact ⟨j, hj, .inr (.inr (.inl h))⟩
    · exact ⟨j, hj, .inr (.inl h)⟩
    · exact ⟨j, hj, .inr (.inr (.inr (h.trans (Finset.insert_comm _ _ _))))⟩
    · exact ⟨j, hj, .inl h⟩
    · exact ⟨j, hj, .inr (.inr (.inl h))⟩
    · exact ⟨j, hj, .inr (.inl h)⟩
    · exact ⟨j, hj, .inr (.inr (.inr (h.trans (Finset.insert_comm _ _ _))))⟩

set_option maxHeartbeats 1600000 in
/-- **The base case of the collar lemma.** Let `M` be a combinatorial manifold and `w ⋆ J` a cone
inside `∂M` in which `w` is an interior vertex and which contains every boundary neighbour of its
interior faces. Attaching a new cone `v ⋆ (w ⋆ J)` along `w ⋆ J` does not change the stellar
equivalence class of `M`. -/
theorem collar_base [Infinite V] {n : ℕ} {M J : SComplex V} {w v : V} (hM : IsMfdIn true (n + 1) M)
    (hJe : ∅ ∈ J) (hw : w ∉ J.verts)
    (hK : ∀ s ∈ cone w J, s ∈ M.bd) (hint : {w} ∉ (cone w J).bd)
    (hF : ∀ A ∈ cone w J, A ∉ (cone w J).bd → ∀ s ∈ M.bd, A ⊆ s → s ∈ cone w J)
    (hvM : v ∉ M.verts) :
    StellarEquivIn ((cone v (cone w J)).union M) M := by
  have hw1 : {w} ∈ cone w J := mem_cone.2 ⟨∅, hJe, .inr (by simp)⟩
  have hwb : {w} ∈ M.bd := hK _ hw1
  have hwM : {w} ∈ M := bd_subset hwb
  obtain ⟨m, hLSB, hLb⟩ : ∃ m, IsSB true (m + 1) (M.link {w}) ∧ IsBallIn (M.link {w}) := by
    obtain ⟨m, hm, h⟩ := (isMfdIn_main true (n + 1)).1 M hM {w} hwM (singleton_nonempty w)
    have hm' : m = n + 1 := by simpa using hm
    exact ⟨n, hm' ▸ h, (hM.mem_bd_iff hwM (singleton_nonempty w)).1 hwb⟩
  have hLM : IsMfdIn true m (M.link {w}) := (isMfdIn_main true m).2 _ hLSB
  have hLJ : (M.link {w}).bd = J := link_bd_eq_of_cone hM hLM hJe hw hK hint hF
  have hwL : w ∉ (M.link {w}).verts := fun h =>
    disjoint_left.1 (disjoint_verts_link M {w}) (mem_singleton_self w) h
  have h0 : ∅ ∈ M.link {w} := bd_subset (hLJ ▸ hJe)
  have hPe : M.star {w} = cone w (M.link {w}) := star_eq_join M {w}
  have hPb : (M.star {w}).bd = (M.link {w}).union (cone w J) := by
    rw [hPe, bd_cone hLSB hLb h0 hwL, hLJ]
  have hPSB : IsSB true (m + 2) (M.star {w}) := hPe ▸ isSB_cone hLSB hwL
  have hPB : IsBallIn (M.star {w}) := hPe ▸ isBallIn_cone hLSB hwL
  have hPM : ∀ s ∈ M.star {w}, s ∈ M := fun s hs => down_mem (mem_star.1 hs) subset_union_right
  have hJM : ∀ j ∈ J, j ∈ M.link {w} := fun j hj => bd_subset (hLJ ▸ hj)
  have hKM : ∀ s ∈ cone w J, s ∈ M := fun s hs => bd_subset (hK s hs)
  obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset (M.verts ∪ J.verts ∪ {v, w})
  simp only [mem_union, mem_insert, mem_singleton, not_or] at hy
  obtain ⟨⟨hyM, hyJ⟩, hyv, hyw⟩ := hy
  have hvw : v ≠ w := fun h => hvM (h ▸ mem_verts.2 hwM)
  have hmem : ∀ s, s ∈ M ↔ s ∈ M.del {w} ∨ s ∈ M.star {w} := fun s => by
    have := mem_union_iff (K := M.del {w}) (L := M.star {w}) (s := s)
    rwa [← del_union_star] at this
  have hf0 : ∀ s ∈ M.star {w}, s ∈ M.del {w} → s ∈ (M.star {w}).bd := by
    intro s hs hR
    rw [hPb]
    rw [hPe] at hs
    obtain ⟨t, ht, e | e⟩ := mem_cone.1 hs
    · exact mem_union_iff.2 (.inl (e ▸ ht))
    · exact absurd (singleton_subset_iff.2 (e ▸ mem_insert_self w t)) (mem_del.1 hR).2
  have hfK : ∀ s ∈ M.star {w}, s ∈ cone v (cone w J) → s ∈ (M.star {w}).bd := by
    intro s hs hR
    rw [hPb]
    obtain ⟨t, ht, e | e⟩ := mem_cone.1 hR
    · exact mem_union_iff.2 (.inr (e ▸ ht))
    · exact absurd (mem_verts_of_mem (hPM s hs) (e ▸ mem_insert_self v t)) hvM
  have hfR : ∀ s ∈ M.star {w}, s ∈ (M.del {w}).union (cone v (cone w J)) →
      s ∈ (M.star {w}).bd := fun s hs h =>
    (mem_union_iff.1 h).elim (hf0 s hs) (hfK s hs)
  have hvOf : ∀ R : SComplex V, (∀ s ∈ M.star {w}, s ∈ R → s ∈ (M.star {w}).bd) →
      ∀ x ∈ R.verts, x ∈ (M.star {w}).verts → x ∈ (M.star {w}).bd.verts :=
    fun R hf x hx hxP => mem_verts.2 (hf _ (mem_verts.1 hxP) (mem_verts.1 hx))
  have hyP : y ∉ (M.star {w}).verts := fun h => hyM (mem_verts.2 (hPM _ (mem_verts.1 h)))
  have hyJ' : y ∉ (cone w J).verts := notMem_verts_cone hyw hyJ
  have hyR0 : y ∉ (M.del {w}).verts := fun h =>
    hyM (mem_verts.2 (mem_del.1 (mem_verts.1 h)).1)
  have hyR : y ∉ ((M.del {w}).union (cone v (cone w J))).verts := fun h =>
    (mem_union_iff.1 (mem_verts.1 h)).elim (fun h' => hyR0 (mem_verts.2 h'))
      (fun h' => notMem_verts_cone hyv hyJ' (mem_verts.2 h'))
  have E1 := stellarEquivIn_star_ball hPSB hPB (hvOf _ hf0) hf0 hyP hyR0
  have E2 := stellarEquivIn_star_ball hPSB hPB (hvOf _ hfR) hfR hyP hyR
  -- the complex M0 and the wing move
  have hLM' : ∀ s ∈ M.link {w}, s ∈ M := fun s hs => (mem_link.1 hs).1
  have hvL : v ∉ (M.link {w}).verts := fun h => hvM (mem_verts.2 (hLM' _ (mem_verts.1 h)))
  have hvJ : v ∉ J.verts := fun h => hvL (mem_verts.2 (hJM _ (mem_verts.1 h)))
  have hvM0 : v ∉ ((M.del {w}).union (cone y (M.link {w}))).verts := by
    intro h
    rcases mem_union_iff.1 (mem_verts.1 h) with h' | h'
    · exact hvM (mem_verts.2 (mem_del.1 h').1)
    · exact notMem_verts_cone (Ne.symm hyv) hvL (mem_verts.2 h')
  have hwM0 : w ∉ ((M.del {w}).union (cone y (M.link {w}))).verts := by
    intro h
    rcases mem_union_iff.1 (mem_verts.1 h) with h' | h'
    · exact (mem_del.1 h').2 subset_rfl
    · exact notMem_verts_cone (Ne.symm hyw) hwL (mem_verts.2 h')
  have W := wing (M0 := (M.del {w}).union (cone y (M.link {w}))) (J := J) (y := y) (v := v)
    (w := w) hJe
    (fun j hj => mem_union_iff.2 (.inr (mem_cone.2 ⟨j, hJM j hj, .inl rfl⟩)))
    (fun j hj => mem_union_iff.2 (.inr (mem_cone.2 ⟨j, hJM j hj, .inr rfl⟩)))
    hvM0 hwM0 hvJ hw hyJ hyv hyw hvw
  have EQ1 : (cone y (M.star {w}).bd).union (M.del {w}) =
      ((M.del {w}).union (cone y (M.link {w}))).union (cone w (cone y J)) := by
    rw [hPb, cone_union, cone_cone_comm y w J]
    refine ext_mem fun s => ?_
    simp only [mem_union_iff, or_assoc, or_comm, or_left_comm]
  have EQ2 : (cone y (M.star {w}).bd).union ((M.del {w}).union (cone v (cone w J))) =
      (((M.del {w}).union (cone y (M.link {w}))).union (cone w (cone y J))).union
        (cone v (cone w J)) := by
    rw [hPb, cone_union, cone_cone_comm y w J]
    exact ext_mem fun s => by simp only [mem_union_iff, or_assoc, or_comm, or_left_comm]
  have EQ3 : (cone v (cone w J)).union M =
      (M.star {w}).union ((M.del {w}).union (cone v (cone w J))) :=
    ext_mem fun s => by simp only [mem_union_iff, hmem s, or_assoc, or_comm, or_left_comm]
  have EQ4 : M = (M.star {w}).union (M.del {w}) :=
    ext_mem fun s => by simp only [mem_union_iff, hmem s, or_assoc, or_comm, or_left_comm]
  rw [← EQ4] at E1
  rw [EQ3]
  refine E2.trans ?_
  rw [EQ2, ← EQ1]
  rw [← EQ1] at W
  exact W.trans E1.symm

/-! ## The collar lemma: hypotheses and the forward step -/

/-- The hypotheses of the collar lemma: `M` is a combinatorial `(n+1)`-manifold, `K` is an
`n`-ball inside `∂M` that is *full* (every boundary face containing an interior face of `K` lies in
`K`), and `v` is a new vertex. -/
structure CollarHyp (n : ℕ) (v : V) (M K : SComplex V) : Prop where
  /-- `M` is a combinatorial manifold with boundary. -/
  mfd : IsMfdIn true (n + 1) M
  /-- `K` is a ball. -/
  sb : IsSB true (n + 1) K
  /-- `K` is a ball. -/
  ball : IsBallIn K
  /-- `K` is nonempty. -/
  empty : ∅ ∈ K
  /-- `K` lies in the boundary of `M`. -/
  sub : ∀ s ∈ K, s ∈ M.bd
  /-- The apex is new. -/
  fresh : v ∉ M.verts
  /-- Fullness. -/
  full : ∀ A ∈ K, A ∉ K.bd → ∀ s ∈ M.bd, A ⊆ s → s ∈ K

/-- **The forward step**: a stellar move at an interior face of `K` preserves the hypotheses. -/
theorem CollarHyp.starAt [Infinite V] {n : ℕ} {v : V} {M K : SComplex V} (h : CollarHyp n v M K)
    {B : Finset V} {b : V} (hBK : B ∈ K) (hBb : B ∉ K.bd) (hne : B.Nonempty) (hb : b ∉ M.verts)
    (hbv : b ≠ v) : CollarHyp n v (M.starAt B b) (K.starAt B b) := by
  have hBM : B ∈ M := bd_subset (h.sub B hBK)
  have hbK : b ∉ K.verts := fun hh => hb (mem_verts.2 (bd_subset (h.sub _ (mem_verts.1 hh))))
  have hKm : IsMfdIn true n K := (isMfdIn_main true n).2 _ h.sb
  have hbd1 : (K.starAt B b).bd = K.bd := hKm.bd_starAt_of_notMem hBK hne hbK hBb
  have hbd2 : (M.starAt B b).bd = M.bd.starAt B b := h.mfd.bd_starAt_of_mem hBM hne hb
  have hBMb : B ∈ M.bd := h.sub B hBK
  have eq : StellarEquivIn K (K.starAt B b) := StellarEquivIn.starAt hBK hne hbK
  refine ⟨(isMfdIn_starAt_iff (isMfdIn_main true (n + 1)).1 hBM hne hb).2 h.mfd,
    h.sb.of_stellarEquivIn eq, h.ball.of_stellarEquivIn eq,
    mem_starAt.2 (.inl ⟨h.empty, fun hh => (Finset.not_nonempty_empty (hne.mono hh))⟩), ?_, ?_, ?_⟩
  · intro s hs
    rw [hbd2, mem_starAt]
    rcases mem_starAt.1 hs with ⟨h1, h2⟩ | ⟨u, hu, hBu, hBu', e⟩
    · exact .inl ⟨h.sub s h1, h2⟩
    · exact .inr ⟨u, h.sub u hu, hBu, h.sub _ hBu', e⟩
  · intro hv
    rcases (mem_verts_starAt hBM hne hb).1 hv with e | ⟨hx, -⟩
    · exact hbv e.symm
    · exact h.fresh hx
  · intro A' hA' hA'b s hs hAs
    rw [hbd1] at hA'b
    rw [hbd2, mem_starAt] at hs
    have hfull := h.full B hBK hBb
    have hbA : ∀ u ∈ K, b ∉ u := fun u hu hh => hbK (mem_verts_of_mem hu hh)
    have hbM : ∀ u ∈ M, b ∉ u := fun u hu hh => hb (mem_verts_of_mem hu hh)
    rcases hs with ⟨hs1, hs2⟩ | ⟨t, ht, hBt, hBt', rfl⟩
    · rcases mem_starAt.1 hA' with ⟨h1, -⟩ | ⟨u, hu, -, -, rfl⟩
      · exact mem_starAt.2 (.inl ⟨h.full A' h1 hA'b s hs1 hAs, hs2⟩)
      · exact absurd (hAs (mem_insert_self b u)) (hbM s (bd_subset hs1))
    · have hBtK : B ∪ t ∈ K := hfull _ hBt' subset_union_left
      have htK : t ∈ K := down_mem hBtK subset_union_right
      exact mem_starAt.2 (.inr ⟨t, htK, hBt, hBtK, rfl⟩)

/-- The statement proved by induction along a tame chain: for every `M` satisfying the collar
hypotheses with `K = X`, `∂X = E`, whose vertices outside `X` avoid the finite set `T`, and with
`v ∉ T`, attaching `v ⋆ X` does not change `M` up to stellar equivalence. -/
def CollarOK (S : Finset V) (E X : SComplex V) (T : Finset V) : Prop :=
  ∀ (n : ℕ) (v : V) (M : SComplex V), CollarHyp n v M X → X.bd = E → v ∉ T → v ∈ S →
    (∀ x ∈ M.verts, x ∉ X.verts → x ∉ T) → StellarEquivIn ((cone v X).union M) M

/-- The forward step of the induction. -/
theorem collar_fwd [Infinite V] {E X : SComplex V} {S : Finset V} {B : Finset V} {b : V}
    {T : Finset V} (hsub : IsSub E S X B b) (hok : CollarOK S E (X.starAt B b) T) :
    CollarOK S E X (insert b T) := by
  intro n v M h hE hv hvS hT
  obtain ⟨hBX, hne, hBE, hbX, -, -, -⟩ := hsub
  have hbT : b ∈ insert b T := mem_insert_self b T
  have hbM : b ∉ M.verts := fun hh => hT b hh hbX hbT
  have hbv : b ≠ v := fun e => hv (e ▸ hbT)
  have hBb : B ∉ X.bd := hE ▸ hBE
  have h1 := h.starAt hBX hBb hne hbM hbv
  have hKm : IsMfdIn true n X := (isMfdIn_main true n).2 _ h.sb
  have hbd1 : (X.starAt B b).bd = E := (hKm.bd_starAt_of_notMem hBX hne hbX hBb).trans hE
  have hvX : v ∉ X.verts := fun hh => h.fresh (mem_verts.2 (bd_subset (h.sub _ (mem_verts.1 hh))))
  have hBM : B ∈ M := bd_subset (h.sub B hBX)
  have hfm : ((cone v X).union M).starAt B b = (cone v (X.starAt B b)).union (M.starAt B b) := by
    rw [starAt_union, cone_starAt hvX (fun hh => hvX (mem_verts_of_mem hBX hh))]
  have W := hok n v (M.starAt B b) h1 hbd1 (fun hh => hv (mem_insert_of_mem hh)) hvS
    (by
      intro x hx hxX hxT
      rcases (mem_verts_starAt hBM hne hbM).1 hx with e | ⟨hxM, hBx⟩
      · exact hxX ((mem_verts_starAt hBX hne hbX).2 (.inl e))
      · exact hT x hxM (fun hh => hxX ((mem_verts_starAt hBX hne hbX).2 (.inr ⟨hh, hBx⟩)))
          (mem_insert_of_mem hxT))
  have e1 : StellarEquivIn ((cone v X).union M) ((cone v (X.starAt B b)).union (M.starAt B b)) := by
    rw [← hfm]
    exact StellarEquivIn.starAt (mem_union_iff.2 (.inr hBM)) hne
      (fun hh => by
        rcases mem_union_iff.1 (mem_verts.1 hh) with h' | h'
        · exact absurd (verts_cone_subset X v (mem_verts.2 h')) (by
            simp only [mem_insert, not_or]; exact ⟨hbv, hbX⟩)
        · exact hbM (mem_verts.2 h'))
  have e2 : StellarEquivIn (M.starAt B b) M := (StellarEquivIn.starAt hBM hne hbM).symm
  exact e1.trans (W.trans e2)


/-- The base of the induction: the cone `w ⋆ E` on its own boundary. -/
theorem collar_base_ok [Infinite V] {S : Finset V} {E : SComplex V} {w : V} (hw : w ∉ E.verts) :
    CollarOK S E (cone w E) ∅ := by
  intro n v M h hE _ _ _
  have hJe : ∅ ∈ E := hE ▸ mem_bd.2 ⟨h.empty, .inl rfl⟩
  refine collar_base h.mfd hJe hw h.sub ?_ ?_ h.fresh
  · rw [hE]; exact fun hh => hw (mem_verts.2 hh)
  · intro A hA hAb
    exact h.full A hA hAb

/-- The weld step of the induction, as a statement: the inverse of a tame subdivision. -/
def CollarWeldStep (E : SComplex V) (S : Finset V) : Prop :=
  ∀ (X' : SComplex V) (B : Finset V) (b : V) (T' : Finset V), IsSub E S X' B b → ¬ B ⊆ E.verts →
    CollarOK S E X' T' → CollarOK S E (X'.starAt B b) T'

/-- The induction along a tame chain. -/
theorem collar_chain [Infinite V] {E : SComplex V} {S : Finset V} {X Y : SComplex V}
    (hch : TChain E S X Y) (hY : CollarOK S E Y ∅) (hweld : CollarWeldStep E S) :
    ∃ T : Finset V, (∀ b ∈ T, b ∉ S) ∧ CollarOK S E X T := by
  induction hch using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨∅, by simp, hY⟩
  | head hstep _ ih =>
    obtain ⟨T, hT, hok⟩ := ih
    rcases hstep with ⟨B, b, hsub, rfl⟩ | ⟨B, b, hsub, hBE, rfl⟩
    · exact ⟨insert b T, fun x hx => by
        rcases mem_insert.1 hx with rfl | hx
        · exact hsub.2.2.2.2.1
        · exact hT x hx, collar_fwd hsub hok⟩
    · exact ⟨T, hT, hweld _ B b T hsub hBE hok⟩

/-- The collar lemma, given the weld step: attaching a cone `v ⋆ K` along
a full ball `K` in the boundary of a combinatorial manifold `M` does not change `M` up to stellar
equivalence. -/
theorem collar_lemma_of_weld [Infinite V] (hweld : ∀ (E : SComplex V) (S : Finset V), CollarWeldStep E S)
    {n : ℕ} {v : V} {M K : SComplex V} (h : CollarHyp n v M K) :
    StellarEquivIn ((cone v K).union M) M := by
  classical
  have hKM : ∀ x ∈ K.verts, x ∈ M.verts := fun x hx =>
    mem_verts.2 (bd_subset (h.sub _ (mem_verts.1 hx)))
  have hEK : K.bd.verts ⊆ K.verts := fun x hx => mem_verts.2 (bd_subset (mem_verts.1 hx))
  set S : Finset V := (insert v M.verts).filter (fun x => x ∉ K.verts ∨ x ∈ K.bd.verts) with hS
  obtain ⟨w, hw⟩ := Infinite.exists_notMem_finset (S ∪ K.verts)
  rw [mem_union, not_or] at hw
  have hst := starrable_ball (n + 1) K h.sb h.ball S
    (fun x hx hxK => by
      rcases (Finset.mem_filter.1 hx).2 with h' | h'
      · exact absurd hxK h'
      · exact h') w hw.1 hw.2 (fun hh => hw.2 (hEK hh))
  obtain ⟨T, hT, hok⟩ := collar_chain hst (collar_base_ok (fun hh => hw.2 (hEK hh)))
    (hweld K.bd S)
  have hvS : v ∈ S := Finset.mem_filter.2 ⟨mem_insert_self v _, .inl (fun hh => h.fresh (hKM v hh))⟩
  refine hok n v M h rfl (fun hh => hT v hh hvS) hvS ?_
  intro x hx hxK hxT
  exact hT x hxT (Finset.mem_filter.2 ⟨mem_insert_of_mem hx, .inl hxK⟩)

/-! ## The boundary along a tame chain -/

/-- One tame move on `X`, run inside `X ∪ R`, keeps the complex a manifold and keeps its boundary,
provided no face of `X` that lies in the boundary lies outside `E`. -/
theorem tstep_bd_union [Infinite V] {n : ℕ} {E R X X1 : SComplex V} {S : Finset V}
    (h : TStep E S X X1) (hRS : R.verts ⊆ S) (hm : IsMfdIn true n (X.union R))
    (hv : ∀ x ∈ R.verts, x ∈ X.verts → x ∈ E.verts)
    (hf : ∀ s ∈ X, s ∈ R → s ∈ E) (hbd : ∀ s ∈ X, s ∈ (X.union R).bd → s ∈ E) :
    IsMfdIn true n (X1.union R) ∧ (X1.union R).bd = (X.union R).bd ∧
      ∀ s ∈ X1, s ∈ (X.union R).bd → s ∈ E := by
  have hB' : ∀ L : SComplex V, IsMfdIn true n L → ∀ τ ∈ L, τ.Nonempty →
      ∃ m, m + #τ = n + 1 ∧ IsSB true m (L.link τ) := fun L hL τ hτ hne =>
    (isMfdIn_main true n).1 L hL τ hτ hne
  obtain ⟨hv1, hf1⟩ := h.glue_inv hRS hv hf
  rcases h with ⟨B, b, hsub, rfl⟩ | ⟨B, b, hsub, hBE, rfl⟩
  · obtain ⟨hBX, hne, hBE, hbX, hbS, hbE, -⟩ := hsub
    have hBR : B ∉ R := fun h' => hBE (hf B hBX h')
    have hfm : (X.starAt B b).union R = (X.union R).starAt B b := by
      rw [starAt_union, starAt_of_notMem hBR]
    have hBu : B ∈ X.union R := mem_union_iff.2 (.inl hBX)
    have hbu : b ∉ (X.union R).verts := by
      rw [verts_union, Finset.mem_union, not_or]; exact ⟨hbX, fun h' => hbS (hRS h')⟩
    have hBnb : B ∉ (X.union R).bd := fun h' => hBE (hbd B hBX h')
    refine ⟨?_, ?_, ?_⟩
    · rw [hfm]; exact (isMfdIn_starAt_iff hB' hBu hne hbu).2 hm
    · rw [hfm]; exact hm.bd_starAt_of_notMem hBu hne hbu hBnb
    · intro s hs hs'
      rcases mem_starAt.1 hs with ⟨h1, -⟩ | ⟨t, -, -, -, rfl⟩
      · exact hbd s h1 hs'
      · exact absurd (mem_verts_of_mem (bd_subset hs') (mem_insert_self b t)) hbu
  · obtain ⟨hBX1, hne, hBE', hbX1, hbS, hbE, -⟩ := hsub
    have hBR : B ∉ R := fun h' => hBE (fun x hx => subset_verts (hf1 B hBX1 h') hx)
    have hfm : (X1.starAt B b).union R = (X1.union R).starAt B b := by
      rw [starAt_union, starAt_of_notMem hBR]
    have hBu : B ∈ X1.union R := mem_union_iff.2 (.inl hBX1)
    have hbu : b ∉ (X1.union R).verts := by
      rw [verts_union, Finset.mem_union, not_or]; exact ⟨hbX1, fun h' => hbS (hRS h')⟩
    rw [hfm] at hm hbd ⊢
    have hm1 : IsMfdIn true n (X1.union R) := (isMfdIn_starAt_iff hB' hBu hne hbu).1 hm
    have hbX : {b} ∈ X1.starAt B b := mem_verts.1 (apex_mem_verts hBX1 hne)
    have hBnb : B ∉ (X1.union R).bd := fun h' =>
      hbE (mem_verts.2 (hbd {b} hbX ((hm1.apex_mem_bd_starAt_iff hBu hne hbu).2 h')))
    have hb1 : ((X1.union R).starAt B b).bd = (X1.union R).bd :=
      hm1.bd_starAt_of_notMem hBu hne hbu hBnb
    refine ⟨hm1, hb1.symm, ?_⟩
    intro s hs hs'
    rw [hb1] at hs'
    have hbs : b ∉ s := fun h' => hbX1 (mem_verts_of_mem hs h')
    have hBs : ¬ B ⊆ s := fun hBs => hBnb (down_mem hs' hBs)
    exact hbd s ((mem_starAt_of_notMem hbs).2 ⟨hs, hBs⟩) (by rw [hb1]; exact hs')

/-- **The boundary is unchanged along a tame chain run inside `X ∪ R`**: the result is again a
manifold with the same boundary. -/
theorem tchain_bd_union [Infinite V] {n : ℕ} {E R X Y : SComplex V} {S : Finset V}
    (hch : TChain E S X Y) (hRS : R.verts ⊆ S) (hm : IsMfdIn true n (X.union R))
    (hv : ∀ x ∈ R.verts, x ∈ X.verts → x ∈ E.verts)
    (hf : ∀ s ∈ X, s ∈ R → s ∈ E) (hbd : ∀ s ∈ X, s ∈ (X.union R).bd → s ∈ E) :
    IsMfdIn true n (Y.union R) ∧ (Y.union R).bd = (X.union R).bd := by
  revert hm hv hf hbd
  induction hch using Relation.ReflTransGen.head_induction_on with
  | refl => intro hm _ _ _; exact ⟨hm, rfl⟩
  | @head X X1 hstep _ ih =>
    intro hm hv hf hbd
    obtain ⟨hm1, hb1, hbd1⟩ := tstep_bd_union hstep hRS hm hv hf hbd
    obtain ⟨hv1, hf1⟩ := hstep.glue_inv hRS hv hf
    obtain ⟨h2, h3⟩ := ih hm1 hv1 hf1 (fun s hs hs' => hbd1 s hs (hb1 ▸ hs'))
    exact ⟨h2, h3.trans hb1⟩

/-- **Replacing a ball by a cone on its boundary keeps the boundary**: if `P` is a PL ball inside
the manifold `P ∪ R`, meeting `R` only in `∂P` and meeting `∂(P ∪ R)` only in `∂P`, then replacing
`P` by the cone `y ⋆ ∂P` gives a manifold with the same boundary. -/
theorem starBall_bd [Infinite V] {n m : ℕ} {P R : SComplex V} (hP : IsSB true m P)
    (hB : IsBallIn P) (hm : IsMfdIn true n (P.union R))
    (hv : ∀ x ∈ R.verts, x ∈ P.verts → x ∈ P.bd.verts)
    (hf : ∀ s ∈ P, s ∈ R → s ∈ P.bd) (hbd : ∀ s ∈ P, s ∈ (P.union R).bd → s ∈ P.bd)
    {y : V} (hyP : y ∉ P.verts) (hyR : y ∉ R.verts) :
    IsMfdIn true n ((cone y P.bd).union R) ∧ ((cone y P.bd).union R).bd = (P.union R).bd := by
  have hst := starrable_ball m P hP hB R.verts (fun x hxS hxP => hv x hxS hxP) y
    (fun h => hyR h) hyP (fun h => hyP (mem_verts.2 (bd_subset (mem_verts.1 h))))
  exact tchain_bd_union hst subset_rfl hm hv hf hbd

/-- **The converse of the forward step**: if the subdivided pair satisfies the collar hypotheses,
so does the pair before subdividing at the face `B`. -/
theorem CollarHyp.of_starAt [Infinite V] {n : ℕ} {v : V} {M K : SComplex V} {B : Finset V} {b : V}
    (h : CollarHyp n v (M.starAt B b) (K.starAt B b)) (hBK : B ∈ K) (hBb : B ∉ K.bd)
    (hne : B.Nonempty) (hBM : B ∈ M) (hbM : b ∉ M.verts) (hbK : b ∉ K.verts) (hv : v ∉ M.verts) :
    CollarHyp n v M K := by
  have eq : StellarEquivIn K (K.starAt B b) := StellarEquivIn.starAt hBK hne hbK
  have hsb : IsSB true (n + 1) K := h.sb.of_stellarEquivIn eq.symm
  have hKm : IsMfdIn true n K := (isMfdIn_main true n).2 _ hsb
  have hMm : IsMfdIn true (n + 1) M :=
    (isMfdIn_starAt_iff (isMfdIn_main true (n + 1)).1 hBM hne hbM).1 h.mfd
  have hbd1 : (K.starAt B b).bd = K.bd := hKm.bd_starAt_of_notMem hBK hne hbK hBb
  have hbd2 : (M.starAt B b).bd = M.bd.starAt B b := hMm.bd_starAt_of_mem hBM hne hbM
  have hbbd : ∀ t ∈ M.bd, b ∉ t := fun t ht hh => hbM (mem_verts_of_mem (bd_subset ht) hh)
  -- an inserted face of the boundary of `M`, seen in `∂M` itself
  have hins : ∀ u, b ∉ u → insert b u ∈ M.bd.starAt B b → ¬ B ⊆ u → B ∪ u ∈ M.bd := by
    intro u hbu hu hBu
    rcases mem_starAt.1 hu with ⟨h1, -⟩ | ⟨t, ht, hBt, hBt', e⟩
    · exact absurd (mem_insert_self b u) (hbbd _ h1)
    · rw [← insert_cancel (hbbd t ht) hbu e]; exact hBt'
  have hsplit : ∀ s ∈ K, B ⊆ s → insert b (s \ B) ∈ K.starAt B b := by
    intro s hs hBs
    have hbu : b ∉ s \ B := fun hh => hbK (mem_verts_of_mem hs (mem_sdiff.1 hh).1)
    refine (insert_mem_starAt hbK hbu).2 ⟨down_mem hs sdiff_subset, fun hh => ?_, ?_⟩
    · obtain ⟨x, hx⟩ := hne
      exact (mem_sdiff.1 (hh hx)).2 hx
    · rwa [union_sdiff_of_subset hBs]
  refine ⟨hMm, hsb, h.ball.of_stellarEquivIn eq.symm, down_mem hBK (empty_subset _), ?_, hv, ?_⟩
  · intro s hs
    by_cases hBs : B ⊆ s
    · have h1 := h.sub _ (hsplit s hs hBs)
      rw [hbd2] at h1
      have hbu : b ∉ s \ B := fun hh => hbK (mem_verts_of_mem hs (mem_sdiff.1 hh).1)
      rw [← union_sdiff_of_subset hBs]
      exact hins _ hbu h1 (fun hh => by
        obtain ⟨x, hx⟩ := hne
        exact (mem_sdiff.1 (hh hx)).2 hx)
    · have h1 := h.sub s ((mem_starAt_of_notMem fun hh => hbK (mem_verts_of_mem hs hh)).2 ⟨hs, hBs⟩)
      rw [hbd2] at h1
      rcases mem_starAt.1 h1 with ⟨h2, -⟩ | ⟨t, -, -, -, e⟩
      · exact h2
      · exact absurd (e ▸ mem_insert_self b t) (fun hh => hbK (mem_verts_of_mem hs hh))
  · intro A hA hAb s hs hAs
    have hb1 : {b} ∈ K.starAt B b := mem_verts.1 (apex_mem_verts hBK hne)
    have hb2 : {b} ∉ (K.starAt B b).bd := by
      rw [hbd1]; exact fun hh => hbK (mem_verts.2 (bd_subset hh))
    have hsM : ∀ t, B ⊆ t → t ∈ M.bd → t ∈ K := by
      intro t hBt ht
      have hbu : b ∉ t \ B := fun hh => hbbd t ht (mem_sdiff.1 hh).1
      have h3 : insert b (t \ B) ∈ (M.starAt B b).bd := by
        rw [hbd2, mem_starAt]
        refine .inr ⟨t \ B, down_mem ht sdiff_subset, fun hh => ?_, ?_, rfl⟩
        · obtain ⟨x, hx⟩ := hne
          exact (mem_sdiff.1 (hh hx)).2 hx
        · rwa [union_sdiff_of_subset hBt]
      have h4 := h.full {b} hb1 hb2 _ h3 (singleton_subset_iff.2 (mem_insert_self b _))
      have h5 := ((insert_mem_starAt hbK hbu).1 h4).2.2
      rwa [union_sdiff_of_subset hBt] at h5
    by_cases hBs : B ⊆ s
    · exact hsM s hBs hs
    · have hBA : ¬ B ⊆ A := fun hh => hBs (hh.trans hAs)
      have hA' : A ∈ K.starAt B b := (mem_starAt_of_notMem fun hh =>
        hbK (mem_verts_of_mem hA hh)).2 ⟨hA, hBA⟩
      have hs' : s ∈ (M.starAt B b).bd := by
        rw [hbd2, mem_starAt]; exact .inl ⟨hs, hBs⟩
      have h6 := h.full A hA' (by rw [hbd1]; exact hAb) s hs' hAs
      exact ((mem_starAt_of_notMem (hbbd s hs)).1 h6).1

/-! ## The weld step -/

/-- Union of complexes is commutative. -/
lemma union_comm' (K L : SComplex V) : K.union L = L.union K :=
  ext_mem fun s => by simp only [mem_union_iff, or_comm]

/-- Union of complexes is associative. -/
lemma union_assoc' (K L M : SComplex V) : (K.union L).union M = K.union (L.union M) :=
  ext_mem fun s => by simp only [mem_union_iff, or_assoc]

/-- **The outside forward step**: subdividing `M` at a face `B` that is not a face of `K` keeps
the collar hypotheses. -/
theorem CollarHyp.starAt_outside [Infinite V] {n : ℕ} {v : V} {M K : SComplex V}
    (h : CollarHyp n v M K) {B : Finset V} {c : V} (hBM : B ∈ M) (hBK : B ∉ K)
    (hne : B.Nonempty) (hc : c ∉ M.verts) (hcv : c ≠ v) :
    CollarHyp n v (M.starAt B c) K := by
  have hbd : (M.starAt B c).bd = M.bd.starAt B c := h.mfd.bd_starAt_of_mem hBM hne hc
  have hcA : ∀ A ∈ K, c ∉ A := fun A hA hh => hc (mem_verts_of_mem (bd_subset (h.sub A hA)) hh)
  refine ⟨(isMfdIn_starAt_iff (isMfdIn_main true (n + 1)).1 hBM hne hc).2 h.mfd, h.sb, h.ball,
    h.empty, ?_, ?_, ?_⟩
  · intro s hs
    rw [hbd, mem_starAt]
    exact .inl ⟨h.sub s hs, fun hBs => hBK (down_mem hs hBs)⟩
  · intro hv
    rcases (mem_verts_starAt hBM hne hc).1 hv with e | ⟨hx, -⟩
    · exact hcv e.symm
    · exact h.fresh hx
  · intro A hA hAb s hs hAs
    rw [hbd, mem_starAt] at hs
    rcases hs with ⟨hs1, -⟩ | ⟨t, ht, hBt, hBt', rfl⟩
    · exact h.full A hA hAb s hs1 hAs
    · have hAt : A ⊆ t := fun x hx => by
        rcases mem_insert.1 (hAs hx) with rfl | h'
        · exact absurd hx (hcA A hA)
        · exact h'
      exact absurd (down_mem (h.full A hA hAb (B ∪ t) hBt' (hAt.trans subset_union_right))
        subset_union_left) hBK

/-- Faces of `R` avoiding `b` do not change the link of `{b}` in a union. -/
lemma link_union_of_notMem {K R : SComplex V} {b : V} (hR : ∀ s ∈ R, b ∉ s) :
    (K.union R).link {b} = K.link {b} := ext_mem fun s => by
  rw [mem_link', mem_link', mem_union_iff]
  constructor
  · rintro ⟨hd, h | h⟩
    · exact ⟨hd, h⟩
    · exact absurd (mem_union.2 (.inl (mem_singleton_self b))) (hR _ h)
  · rintro ⟨hd, h⟩
    exact ⟨hd, .inl h⟩

/-- The link of a boundary vertex of an `(n+1)`-manifold is an `n`-ball. -/
theorem link_vertex_ball [Infinite V] {n : ℕ} {M : SComplex V} (hM : IsMfdIn true (n + 1) M)
    {b : V} (hb : {b} ∈ M.bd) : IsSB true (n + 1) (M.link {b}) ∧ IsBallIn (M.link {b}) := by
  have hbM : {b} ∈ M := bd_subset hb
  obtain ⟨m, hm, hSB⟩ := (isMfdIn_main true (n + 1)).1 M hM {b} hbM (singleton_nonempty b)
  have hmn : m = n + 1 := by simpa using hm
  subst hmn
  exact ⟨hSB, (hM.mem_bd_iff hbM (singleton_nonempty b)).1 hb⟩

/-- Facts about the star of a boundary vertex `b` of a manifold `M`: it is a ball meeting the rest
of `M` and the boundary of `M` only in its own boundary. -/
theorem star_facts [Infinite V] {n : ℕ} {M : SComplex V} (hM : IsMfdIn true (n + 1) M) {b : V}
    (hb : {b} ∈ M.bd) :
    IsSB true (n + 2) (M.star {b}) ∧ IsBallIn (M.star {b}) ∧
    (∀ s ∈ M.star {b}, s ∈ M.del {b} → s ∈ (M.star {b}).bd) ∧
    (∀ s ∈ M.star {b}, s ∈ M.bd → s ∈ (M.star {b}).bd) ∧
    (M.star {b}).bd.link {b} = (M.link {b}).bd := by
  have hbM : {b} ∈ M := bd_subset hb
  obtain ⟨hNsb, hNball⟩ := link_vertex_ball hM hb
  have hbN : b ∉ (M.link {b}).verts := fun h =>
    disjoint_left.1 (disjoint_verts_link M {b}) (mem_singleton_self b) h
  have h0 : ∅ ∈ M.link {b} := mem_link'.2 ⟨disjoint_empty_right _, by simpa using hbM⟩
  have hPe : M.star {b} = cone b (M.link {b}) := star_eq_join M {b}
  have hPbd : (M.star {b}).bd = (M.link {b}).union (cone b (M.link {b}).bd) := by
    rw [hPe]; exact bd_cone hNsb hNball h0 hbN
  have hNbd : (M.link {b}).bd = M.bd.link {b} :=
    (hM.link_bd_eq ((isMfdIn_main true n).2 _ hNsb) hb (singleton_nonempty b)).symm
  have hbNb : b ∉ (M.link {b}).bd.verts := fun h => hbN (mem_verts.2 (bd_subset (mem_verts.1 h)))
  refine ⟨hPe ▸ isSB_cone hNsb hbN, hPe ▸ isBallIn_cone hNsb hbN, ?_, ?_, ?_⟩
  · intro s hs hs'
    rw [mem_del] at hs'
    rw [hPbd]
    refine mem_union_iff.2 (.inl (mem_link'.2 ⟨?_, mem_star.1 hs⟩))
    exact disjoint_singleton_left.2 fun h => hs'.2 (singleton_subset_iff.2 h)
  · intro s hs hsb
    rw [hPbd]
    rw [hPe] at hs
    obtain ⟨t, ht, rfl | rfl⟩ := mem_cone.1 hs
    · exact mem_union_iff.2 (.inl ht)
    · refine mem_union_iff.2 (.inr (mem_cone.2 ⟨t, ?_, .inr rfl⟩))
      rw [hNbd]
      have hbt : b ∉ t := fun h => hbN (mem_verts_of_mem ht h)
      exact mem_link'.2 ⟨disjoint_singleton_left.2 hbt, by rwa [← insert_eq]⟩
  · rw [hPbd, union_comm', link_union_of_notMem fun s hs h => hbN (mem_verts_of_mem hs h)]
    exact link_cone_apex hbNb

/-- **Re-coning the star of a boundary vertex**: replacing the star of `b` by a cone from a new
vertex `y` on its boundary is a stellar equivalence which keeps the manifold and its boundary, and
the link of `b` becomes the cone from `y` on the link of `b` in `∂M`. -/
theorem collar_replace [Infinite V] {n : ℕ} {M : SComplex V} (hM : IsMfdIn true (n + 1) M) {b y : V}
    (hb : {b} ∈ M.bd) (hy : y ∉ M.verts) :
    IsMfdIn true (n + 1) ((cone y (M.star {b}).bd).union (M.del {b})) ∧
    ((cone y (M.star {b}).bd).union (M.del {b})).bd = M.bd ∧
    StellarEquivIn M ((cone y (M.star {b}).bd).union (M.del {b})) ∧
    ((cone y (M.star {b}).bd).union (M.del {b})).link {b} = cone y (M.bd.link {b}) ∧
    (∀ s ∈ (cone y (M.star {b}).bd).union (M.del {b}), y ∈ s ∨ s ∈ M) := by
  obtain ⟨hPsb, hPball, hi, hii, hlk⟩ := star_facts hM hb
  have hMe : (M.star {b}).union (M.del {b}) = M :=
    (union_comm' _ _).trans (del_union_star M {b}).symm
  have hPM : ∀ s ∈ M.star {b}, s ∈ M := fun s hs =>
    down_mem (mem_star.1 hs) subset_union_right
  have hyP : y ∉ (M.star {b}).verts := fun h => hy (mem_verts.2 (hPM _ (mem_verts.1 h)))
  have hyR : y ∉ (M.del {b}).verts := fun h => hy (mem_verts.2 ((mem_del.1 (mem_verts.1 h)).1))
  have hv : ∀ x ∈ (M.del {b}).verts, x ∈ (M.star {b}).verts → x ∈ (M.star {b}).bd.verts :=
    fun x hx hxP => mem_verts.2 (hi _ (mem_verts.1 hxP) (mem_verts.1 hx))
  have hbd' : ∀ s ∈ M.star {b}, s ∈ ((M.star {b}).union (M.del {b})).bd → s ∈ (M.star {b}).bd :=
    fun s hs hs' => hii s hs (by rwa [hMe] at hs')
  have hm' : IsMfdIn true (n + 1) ((M.star {b}).union (M.del {b})) := by rw [hMe]; exact hM
  obtain ⟨h1, h2⟩ := starBall_bd hPsb hPball hm' hv hi hbd' hyP hyR
  refine ⟨h1, by rw [h2, hMe], ?_, ?_, ?_⟩
  · have := stellarEquivIn_star_ball hPsb hPball hv hi hyP hyR
    rwa [hMe] at this
  · have hbP : {b} ∈ (M.star {b}).bd := hii {b} (mem_star.2 (by simpa using bd_subset hb)) hb
    have hyb : y ∉ (M.star {b}).bd.verts := fun h => hyP (mem_verts.2 (bd_subset (mem_verts.1 h)))
    rw [link_union_of_notMem fun s hs h => (mem_del.1 hs).2 (singleton_subset_iff.2 h),
      link_cone_of_mem hyb hbP, hlk]
    rw [(hM.link_bd_eq ((isMfdIn_main true n).2 _ (link_vertex_ball hM hb).1) hb
      (singleton_nonempty b)).symm]
  · intro s hs
    rcases mem_union_iff.1 hs with h | h
    · obtain ⟨t, ht, rfl | rfl⟩ := mem_cone.1 h
      · exact .inr (hPM _ (bd_subset ht))
      · exact .inl (mem_insert_self y t)
    · exact .inr (mem_del.1 h).1

/-- A cone on a join is the join with the cone. -/
lemma cone_join_right (y : V) (A L : SComplex V) : cone y (A.join L) = A.join (cone y L) := by
  unfold cone
  rw [← join_assoc, join_comm (simplex {y}) A, join_assoc]

/-- Union is left-commutative. -/
lemma union_left_comm' (A K L : SComplex V) : A.union (K.union L) = K.union (A.union L) :=
  ext_mem fun s => by simp only [mem_union_iff, or_left_comm]

/-- **The weld step, once the face `B` is outside `M`.** -/
theorem collar_weld_core [Infinite V] {E : SComplex V} {S : Finset V} {X0 : SComplex V}
    {B : Finset V} {b : V} {T' : Finset V} (hsub : IsSub E S X0 B b) (hBE : ¬ B ⊆ E.verts)
    (hok : CollarOK S E X0 T') {n : ℕ} {v : V} {M : SComplex V}
    (h : CollarHyp n v M (X0.starAt B b)) (hE : (X0.starAt B b).bd = E) (hv : v ∉ T')
    (hvS : v ∈ S) (hT : ∀ x ∈ M.verts, x ∉ (X0.starAt B b).verts → x ∉ T') (hBM : B ∉ M) :
    StellarEquivIn ((cone v (X0.starAt B b)).union M) M := by
  classical
  obtain ⟨hBX0, hne, hBE', hbX0, hbS, hbE, hS⟩ := hsub
  have hbB : b ∉ B := notMem_of_notMem_verts hbX0 hBX0
  have hXm : IsMfdIn true n (X0.starAt B b) := (isMfdIn_main true n).2 _ h.sb
  have eq0 : StellarEquivIn X0 (X0.starAt B b) := StellarEquivIn.starAt hBX0 hne hbX0
  have hsb0 : IsSB true (n + 1) X0 := h.sb.of_stellarEquivIn eq0.symm
  have hX0m : IsMfdIn true n X0 := (isMfdIn_main true n).2 _ hsb0
  have hb1 : {b} ∈ X0.starAt B b := mem_verts.1 (apex_mem_verts hBX0 hne)
  have hbMb : {b} ∈ M.bd := h.sub _ hb1
  have hbnd : {b} ∉ (X0.starAt B b).bd := by rw [hE]; exact fun hh => hbE (mem_verts.2 hh)
  have hBX0b : B ∉ X0.bd := fun hh => hbnd ((hX0m.apex_mem_bd_starAt_iff hBX0 hne hbX0).2 hh)
  have hE0 : X0.bd = E := (hX0m.bd_starAt_of_notMem hBX0 hne hbX0 hBX0b).symm.trans hE
  have hXM : ∀ x ∈ (X0.starAt B b).verts, x ∈ M.verts := fun x hx =>
    mem_verts.2 (bd_subset (h.sub _ (mem_verts.1 hx)))
  have hbM : b ∈ M.verts := hXM b (mem_verts.2 hb1)
  have hbv : b ≠ v := fun e => h.fresh (e ▸ hbM)
  -- the new vertex
  obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset (M.verts ∪ B ∪ T' ∪ {v})
  simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hy
  obtain ⟨⟨⟨hyM, hyB⟩, hyT⟩, hyv⟩ := hy
  obtain ⟨hM1m, hM1bd, hM1eq, hM1lk, hM1face⟩ := collar_replace h.mfd hbMb hyM
  obtain ⟨hPsb, hPball, hi, hii, -⟩ := star_facts h.mfd hbMb
  set M1 := (cone y (M.star {b}).bd).union (M.del {b}) with hM1
  have hlkX : M.bd.link {b} = (X0.starAt B b).link {b} := by
    refine ext_mem fun s => ?_
    rw [mem_link', mem_link']
    constructor
    · rintro ⟨hd, hs⟩
      exact ⟨hd, h.full {b} hb1 hbnd _ hs subset_union_left⟩
    · rintro ⟨hd, hs⟩
      exact ⟨hd, h.sub _ hs⟩
  have hlk1 : M1.link {b} = (boundary B).join (cone y (X0.link B)) := by
    rw [hM1lk, hlkX, link_starAt_apex hbX0, cone_join_right]
  have hBM1 : B ∉ M1 := fun hB1 => (hM1face B hB1).elim hyB hBM
  have hdis : Disjoint B (cone y (X0.link B)).verts := by
    refine disjoint_left.2 fun x hxB hx => ?_
    rcases mem_insert.1 (verts_cone_subset _ y hx) with rfl | hx'
    · exact hyB hxB
    · exact disjoint_left.1 (disjoint_verts_link X0 B) hxB hx'
  have hM2eq : (M1.weld b B).starAt B b = M1 := starAt_weld hbB hne hBM1 hdis hlk1
  have hbM1 : b ∈ M1.verts := mem_verts.2 (bd_subset (hM1bd ▸ hbMb))
  have hbM2 : b ∉ (M1.weld b B).verts := notMem_verts_weld M1 b B
  have hBM2 : B ∈ M1.weld b B := by
    by_contra hh
    rw [starAt_of_notMem hh] at hM2eq
    rw [hM2eq] at hbM2
    exact hbM2 hbM1
  have hM2verts : ∀ x ∈ (M1.weld b B).verts, x ∈ M1.verts ∨ x ∈ B := by
    intro x hx
    rcases mem_weld.1 (mem_verts.1 hx) with ⟨hs, -⟩ | ⟨u, hu, -, -, -, -, he⟩
    · exact .inl (mem_verts.2 hs)
    · have : x ∈ B ∪ u := he ▸ mem_singleton_self x
      rcases mem_union.1 this with h' | h'
      · exact .inr h'
      · exact .inl (mem_verts_of_mem hu h')
  have hvB : v ∉ B := by
    intro hvB
    have hvX0 : v ∈ X0.verts := subset_verts hBX0 hvB
    by_cases hBv : B ⊆ {v}
    · exact hS v hvS (Finset.Subset.antisymm hBv (singleton_subset_iff.2 hvB))
    · exact h.fresh (hXM v ((mem_verts_starAt hBX0 hne hbX0).2 (.inr ⟨hvX0, hBv⟩)))
  have hvM1 : v ∉ M1.verts := fun hv' => by
    rcases hM1face {v} (mem_verts.1 hv') with h' | h'
    · exact hyv (mem_singleton.1 h')
    · exact h.fresh (mem_verts.2 h')
  have hvM2 : v ∉ (M1.weld b B).verts := fun hv' =>
    (hM2verts v hv').elim hvM1 hvB
  have hh1 : CollarHyp n v ((M1.weld b B).starAt B b) (X0.starAt B b) := by
    rw [hM2eq]
    exact ⟨hM1m, h.sb, h.ball, h.empty, fun s hs => by rw [hM1bd]; exact h.sub s hs, hvM1,
      fun A hA hAb s hs hAs => h.full A hA hAb s (by rwa [hM1bd] at hs) hAs⟩
  have hh2 : CollarHyp n v (M1.weld b B) X0 :=
    hh1.of_starAt hBX0 hBX0b hne hBM2 hbM2 hbX0 hvM2
  have hT2 : ∀ x ∈ (M1.weld b B).verts, x ∉ X0.verts → x ∉ T' := by
    intro x hx hxX0
    rcases hM2verts x hx with h' | h'
    · rcases hM1face {x} (mem_verts.1 h') with h'' | h''
      · rw [← mem_singleton.1 h'']; exact hyT
      · refine hT x (mem_verts.2 h'') fun hxX => ?_
        rcases (mem_verts_starAt hBX0 hne hbX0).1 hxX with rfl | ⟨hx0, -⟩
        · exact hbM2 hx
        · exact hxX0 hx0
    · exact absurd (subset_verts hBX0 h') hxX0
  have hW := hok n v (M1.weld b B) hh2 hE0 hv hvS hT2
  have e4 : StellarEquivIn (M1.weld b B) M1 := by
    have := StellarEquivIn.starAt hBM2 hne hbM2
    rwa [hM2eq] at this
  have hvX0 : v ∉ X0.verts := fun hh => hvM2 (mem_verts.2 (bd_subset (hh2.sub _ (mem_verts.1 hh))))
  have e2 : StellarEquivIn ((cone v X0).union (M1.weld b B))
      ((cone v (X0.starAt B b)).union M1) := by
    have hfm : ((cone v X0).union (M1.weld b B)).starAt B b =
        (cone v (X0.starAt B b)).union M1 := by
      rw [starAt_union, cone_starAt hvX0 hvB, hM2eq]
    rw [← hfm]
    refine StellarEquivIn.starAt (mem_union_iff.2 (.inr hBM2)) hne ?_
    rw [verts_union, Finset.mem_union, not_or]
    refine ⟨fun hh => ?_, hbM2⟩
    rcases mem_insert.1 (verts_cone_subset X0 v hh) with e | e
    · exact hbv e
    · exact hbX0 e
  have e1 : StellarEquivIn ((cone v (X0.starAt B b)).union M)
      ((cone v (X0.starAt B b)).union M1) := by
    have hMe : (M.star {b}).union (M.del {b}) = M :=
      (union_comm' _ _).trans (del_union_star M {b}).symm
    have hPM : ∀ s ∈ M.star {b}, s ∈ M := fun s hs =>
      down_mem (mem_star.1 hs) subset_union_right
    have hf' : ∀ s ∈ M.star {b}, s ∈ (cone v (X0.starAt B b)).union (M.del {b}) →
        s ∈ (M.star {b}).bd := by
      intro s hsP hsR
      rcases mem_union_iff.1 hsR with hc | hd
      · obtain ⟨t, ht, e | e⟩ := mem_cone.1 hc
        · rw [e] at hsP ⊢; exact hii t hsP (h.sub t ht)
        · rw [e] at hsP; exact absurd (mem_verts_of_mem (hPM _ hsP) (mem_insert_self v t)) h.fresh
      · exact hi s hsP hd
    have hv' : ∀ x ∈ ((cone v (X0.starAt B b)).union (M.del {b})).verts, x ∈ (M.star {b}).verts →
        x ∈ (M.star {b}).bd.verts := fun x hx hxP =>
      mem_verts.2 (hf' _ (mem_verts.1 hxP) (mem_verts.1 hx))
    have hyP : y ∉ (M.star {b}).verts := fun hh => hyM (mem_verts.2 (hPM _ (mem_verts.1 hh)))
    have hyR : y ∉ ((cone v (X0.starAt B b)).union (M.del {b})).verts := by
      rw [verts_union, Finset.mem_union, not_or]
      refine ⟨fun hh => ?_, fun hh => hyM (mem_verts.2 ((mem_del.1 (mem_verts.1 hh)).1))⟩
      rcases mem_insert.1 (verts_cone_subset _ v hh) with e | e
      · exact hyv e
      · exact hyM (hXM y e)
    have := stellarEquivIn_star_ball hPsb hPball hv' hf' hyP hyR
    have l1 : (cone v (X0.starAt B b)).union M =
        (M.star {b}).union ((cone v (X0.starAt B b)).union (M.del {b})) := by
      conv_lhs => rw [← hMe]
      exact union_left_comm' _ _ _
    have l2 : (cone v (X0.starAt B b)).union M1 =
        (cone y (M.star {b}).bd).union ((cone v (X0.starAt B b)).union (M.del {b})) :=
      union_left_comm' _ _ _
    rw [l1, l2]; exact this
  exact e1.trans (e2.symm.trans (hW.trans (e4.trans hM1eq.symm)))

/-- **The weld step.** -/
theorem collar_weld [Infinite V] (E : SComplex V) (S : Finset V) : CollarWeldStep E S := by
  classical
  intro X0 B b T' hsub hBE hok n v M h hE hv hvS hT
  have hsub' := hsub
  obtain ⟨hBX0, hne, -, hbX0, -, -, -⟩ := hsub'
  have hbB : b ∉ B := notMem_of_notMem_verts hbX0 hBX0
  by_cases hBM : B ∈ M
  · have hXM : ∀ x ∈ (X0.starAt B b).verts, x ∈ M.verts := fun x hx =>
      mem_verts.2 (bd_subset (h.sub _ (mem_verts.1 hx)))
    have hBX : B ∉ X0.starAt B b := fun hh => by
      rcases mem_starAt.1 hh with ⟨-, hn⟩ | ⟨t, -, -, -, he⟩
      · exact hn subset_rfl
      · exact hbB (he ▸ mem_insert_self b t)
    obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset (M.verts ∪ {v} ∪ T')
    simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hc
    obtain ⟨⟨hcM, hcv⟩, hcT⟩ := hc
    have hBc : c ∉ B := fun hh => hcM (mem_verts_of_mem hBM hh)
    have h' := h.starAt_outside hBM hBX hne hcM hcv
    have hBM' : B ∉ M.starAt B c := fun hh => by
      rcases mem_starAt.1 hh with ⟨-, hn⟩ | ⟨t, -, -, -, he⟩
      · exact hn subset_rfl
      · exact hBc (he ▸ mem_insert_self c t)
    have hT' : ∀ x ∈ (M.starAt B c).verts, x ∉ (X0.starAt B b).verts → x ∉ T' := by
      intro x hx hxX
      rcases (mem_verts_starAt hBM hne hcM).1 hx with rfl | ⟨hxM, -⟩
      · exact hcT
      · exact hT x hxM hxX
    have hcore := collar_weld_core hsub hBE hok h' hE hv hvS hT' hBM'
    have hvB : v ∉ B := fun hh => h.fresh (mem_verts_of_mem hBM hh)
    have hBcone : B ∉ cone v (X0.starAt B b) := fun hh => by
      rcases mem_cone.1 hh with ⟨t, ht, e | e⟩
      · exact hBX (e ▸ ht)
      · exact hvB (e ▸ mem_insert_self v t)
    have hfm : ((cone v (X0.starAt B b)).union M).starAt B c =
        (cone v (X0.starAt B b)).union (M.starAt B c) := by
      rw [starAt_union, starAt_of_notMem hBcone]
    have e1 : StellarEquivIn ((cone v (X0.starAt B b)).union M)
        ((cone v (X0.starAt B b)).union (M.starAt B c)) := by
      rw [← hfm]
      refine StellarEquivIn.starAt (mem_union_iff.2 (.inr hBM)) hne ?_
      rw [verts_union, Finset.mem_union, not_or]
      refine ⟨fun hh => ?_, hcM⟩
      rcases mem_insert.1 (verts_cone_subset _ v hh) with e | e
      · exact hcv e
      · exact hcM (hXM c e)
    exact e1.trans (hcore.trans (StellarEquivIn.starAt hBM hne hcM).symm)
  · exact collar_weld_core hsub hBE hok h hE hv hvS hT hBM

/-- **The collar lemma** (Lickorish, Lemma 3.7): attaching a cone `v ⋆ K` along a full ball `K` in
the boundary of a combinatorial manifold `M` does not change `M` up to stellar equivalence. -/
theorem collar_lemma [Infinite V] {n : ℕ} {v : V} {M K : SComplex V} (h : CollarHyp n v M K) :
    StellarEquivIn ((cone v K).union M) M :=
  collar_lemma_of_weld collar_weld h

end SComplex
end Lightlike.PL
