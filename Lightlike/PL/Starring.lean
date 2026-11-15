import Lightlike.PL.Exchange

/-!
# Starring a complex relative to a subcomplex

Lickorish (*Simplicial moves on complexes and manifolds*, 1999, §3) proves Newman's theorem by
starring: a complex `X` that contains `E` is moved, by stellar moves that leave `E` alone, to the
cone `w ⋆ E` on `E` from a new vertex `w`. This file sets up those moves and proves Lickorish's
Lemma 3.4.

* `IsSub E S X B b`: subdividing `X` at the face `B` with apex `b` is admissible: `B` is not a face
  of `E`, the apex is new to `X`, to `E` and to the protected vertex set `S`, and `B` is not a
  single protected vertex.
* `TStep E S`, `TChain E S`: one tame move (an admissible subdivision, or the inverse of one whose
  set `B` has a vertex outside `E`) and finite chains of them. Chains keep the protected vertices
  of a complex (`TChain.mem_verts_iff`) and commute with renaming vertices (`TChain.map`).
* `Starrable E X`: for every protected set `S` that meets `X` only in vertices of `E` and every
  new vertex `w`, there is a tame chain from `X` to `w ⋆ E`.

## Main results

* `starAt_triple`, `starAt_comm`: stellar subdivisions at `A` and at `B` commute when `A ∪ B` is
  not a face, and agree after one further subdivision in general.
* `Starrable.map_perm`: starrability is invariant under permutations of the vertices.
* `Starrable.starAt`: Lickorish's Lemma 3.4 for one move: if `X` is starrable relative to `E`,
  then a subdivision of `X` is starrable relative to the induced subdivision of `E`.
* `TChain.glue`: a tame chain can be run with a further complex `R`, on protected vertices only,
  glued on.
* `Starrable.toCone`: Lickorish's Lemma 3.5: a starrable complex is moved to a cone over `E` with
  any new apex by tame moves.
-/

open Finset

namespace Lightlike.PL
namespace SComplex
variable {V : Type*} [DecidableEq V]

/-- The vertices of a subdivision are the old vertices and the apex. -/
lemma verts_starAt_subset (K : SComplex V) (A : Finset V) (a : V) :
    (K.starAt A a).verts ⊆ insert a K.verts := by
  intro x hx
  rcases mem_starAt.1 (mem_verts.1 hx) with ⟨h, -⟩ | ⟨t, ht, -, -, he⟩
  · exact mem_insert_of_mem (mem_verts.2 h)
  · have h := he ▸ mem_insert_self a t
    rw [← mem_singleton.1 h]
    exact mem_insert_self a _

/-- Membership in a stellar subdivision, read off by erasing the apex `a` and putting `A` back
when `a` was present. -/
lemma mem_starAt_iff_erase {K : SComplex V} {A : Finset V} {a : V} (ha : a ∉ K.verts)
    {s : Finset V} :
    s ∈ K.starAt A a ↔ s.erase a ∪ (if a ∈ s then A else ∅) ∈ K ∧ ¬ A ⊆ s.erase a := by
  by_cases has : a ∈ s
  · obtain ⟨t, hat, rfl⟩ : ∃ t, a ∉ t ∧ s = insert a t :=
      ⟨s.erase a, notMem_erase a s, (insert_erase has).symm⟩
    simp only [erase_insert hat, mem_insert_self, ↓reduceIte]
    rw [insert_mem_starAt ha hat, union_comm]
    exact ⟨fun h => ⟨h.2.2, h.2.1⟩, fun h => ⟨down_mem h.1 subset_union_left, h.2, h.1⟩⟩
  · simp only [has, ↓reduceIte, union_empty, erase_eq_of_notMem has]
    exact mem_starAt_of_notMem has

omit [DecidableEq V] in
/-- If some point of `Z'` outside `W'` lies in `Z` but not in `W`, then `Z ⊄ W`. -/
lemma not_subset_mono {Z W Z' W' : Finset V} (h : ¬ Z' ⊆ W')
    (hk : ∀ x ∈ Z', x ∉ W' → x ∈ Z ∧ x ∉ W) : ¬ Z ⊆ W := fun hZ =>
  h fun x hx => by_contra fun hW => (hk x hx hW).2 (hZ (hk x hx hW).1)

/-- A closed description of the faces of `((K.starAt A a).starAt B b).starAt (insert a (B \ A)) d`,
used to compare the two orders in `starAt_triple`. -/
def TripleMem (K : SComplex V) (A : Finset V) (a : V) (B : Finset V) (b d : V)
    (s : Finset V) : Prop :=
  ((s.erase a).erase b).erase d ∪ (if a ∈ s then A else ∅) ∪ (if b ∈ s then B else ∅) ∪
      (if d ∈ s then A ∪ B else ∅) ∈ K ∧
    ¬ A ⊆ ((s.erase a).erase b).erase d ∪ (if b ∈ s then B else ∅) ∧
    ¬ B ⊆ ((s.erase a).erase b).erase d ∪ (if a ∈ s then A else ∅) ∧
    (d ∈ s → ¬ A ∩ B ⊆ ((s.erase a).erase b).erase d)

/-- `TripleMem` is symmetric in the two subdivisions. -/
lemma tripleMem_comm {K : SComplex V} {A B : Finset V} {a b d : V} {s : Finset V} :
    TripleMem K A a B b d s ↔ TripleMem K B b A a d s := by
  unfold TripleMem
  rw [erase_right_comm (s := s) (a := a), union_right_comm (((s.erase b).erase a).erase d),
    union_comm A B, inter_comm A B]
  tauto

set_option maxHeartbeats 1000000 in
/-- The faces of `((K.starAt A a).starAt B b).starAt (insert a (B \ A)) d` are described by
`TripleMem`. -/
lemma mem_triple_iff {K : SComplex V} {A B : Finset V} {a b d : V} (ha : a ∉ K.verts)
    (hb : b ∉ K.verts) (hd : d ∉ K.verts) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (haA : a ∉ A) (haB : a ∉ B) (_hbA : b ∉ A) (hbB : b ∉ B) (hdA : d ∉ A) (hdB : d ∉ B)
    {s : Finset V} :
    s ∈ ((K.starAt A a).starAt B b).starAt (insert a (B \ A)) d ↔ TripleMem K A a B b d s := by
  have hb1 : b ∉ (K.starAt A a).verts := fun h => by
    rcases mem_insert.1 (verts_starAt_subset _ _ _ h) with h | h
    · exact hab h.symm
    · exact hb h
  have hd2 : d ∉ ((K.starAt A a).starAt B b).verts := fun h => by
    rcases mem_insert.1 (verts_starAt_subset _ _ _ h) with h | h
    · exact hbd h.symm
    rcases mem_insert.1 (verts_starAt_subset _ _ _ h) with h | h
    · exact had h.symm
    · exact hd h
  rw [mem_starAt_iff_erase hd2, mem_starAt_iff_erase hb1, mem_starAt_iff_erase ha]
  have e1 : b ∈ s.erase d ∪ (if d ∈ s then insert a (B \ A) else ∅) ↔ b ∈ s := by
    by_cases h : d ∈ s <;> simp [h, hbd, hab.symm, hbB]
  have e2 : a ∈ (s.erase d ∪ (if d ∈ s then insert a (B \ A) else ∅)).erase b ∪
      (if b ∈ s then B else ∅) ↔ a ∈ s ∨ d ∈ s := by
    by_cases h : d ∈ s <;> by_cases h' : b ∈ s <;> simp [h, h', had, hab, haB]
  simp only [e1]
  simp only [e2]
  unfold TripleMem
  by_cases h1 : a ∈ s <;> by_cases h2 : b ∈ s <;> by_cases h3 : d ∈ s <;>
    simp only [h1, h2, h3, ↓reduceIte, or_true, or_false, true_implies, and_assoc] <;>
    refine and_congr ?_ ?_
  all_goals first
    | (apply Iff.of_eq; congr 1; ext x; simp only [mem_union, mem_erase, mem_insert, mem_sdiff, ne_eq, notMem_empty]; grind)
    | (constructor <;> rintro ⟨h₁, h₂, h₃⟩ <;> refine ⟨?_, ?_, ?_⟩ <;>
      first
      | exact False.elim
      | (refine fun h => absurd (h (mem_insert_self a _)) ?_; simp [h1]; done)
      | (refine not_subset_mono h₁ ?_; intro x hx hW
         simp only [mem_union, mem_erase, mem_insert, mem_sdiff, mem_inter, ne_eq, notMem_empty] at hx hW ⊢
         grind)
      | (refine not_subset_mono h₂ ?_; intro x hx hW
         simp only [mem_union, mem_erase, mem_insert, mem_sdiff, mem_inter, ne_eq, notMem_empty] at hx hW ⊢
         grind)
      | (refine not_subset_mono h₃ ?_; intro x hx hW
         simp only [mem_union, mem_erase, mem_insert, mem_sdiff, mem_inter, ne_eq] at hx hW ⊢
         grind))


/-- Subdividing at `A`, then at `B`, then at the edge `insert a (B \ A)` from the first apex gives
the same complex as the symmetric order with the same third apex `d`. No condition on `A ∪ B` is
needed. -/
theorem starAt_triple {K : SComplex V} {A B : Finset V} {a b d : V} (ha : a ∉ K.verts)
    (hb : b ∉ K.verts) (hd : d ∉ K.verts) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (haA : a ∉ A) (haB : a ∉ B) (hbA : b ∉ A) (hbB : b ∉ B) (hdA : d ∉ A) (hdB : d ∉ B) :
    ((K.starAt A a).starAt B b).starAt (insert a (B \ A)) d =
      ((K.starAt B b).starAt A a).starAt (insert b (A \ B)) d :=
  ext_mem fun s => by
    rw [mem_triple_iff ha hb hd hab had hbd haA haB hbA hbB hdA hdB,
      mem_triple_iff hb ha hd hab.symm hbd had hbB hbA haB haA hdB hdA, tripleMem_comm]


/-! ## Unions -/

/-- The union of two complexes: the faces of either. -/
def union (K L : SComplex V) : SComplex V where
  faces := K.faces ∪ L.faces
  down s hs t ht := by
    rcases Finset.mem_union.1 hs with h | h
    · exact Finset.mem_union.2 (.inl (K.down s h t ht))
    · exact Finset.mem_union.2 (.inr (L.down s h t ht))

/-- The faces of a union. -/
lemma mem_union_iff {K L : SComplex V} {s : Finset V} : s ∈ K.union L ↔ s ∈ K ∨ s ∈ L :=
  Finset.mem_union

/-- The vertices of a union. -/
lemma verts_union (K L : SComplex V) : (K.union L).verts = K.verts ∪ L.verts := by
  ext x; simp only [mem_verts, mem_union_iff, Finset.mem_union]

/-- Subdivision distributes over unions. -/
lemma starAt_union (K L : SComplex V) (A : Finset V) (a : V) :
    (K.union L).starAt A a = (K.starAt A a).union (L.starAt A a) := ext_mem fun s => by
  simp only [mem_union_iff, mem_starAt]
  constructor
  · rintro (⟨h | h, hA⟩ | ⟨t, -, h₁, h | h, rfl⟩)
    · exact .inl (.inl ⟨h, hA⟩)
    · exact .inr (.inl ⟨h, hA⟩)
    · exact .inl (.inr ⟨t, down_mem h subset_union_right, h₁, h, rfl⟩)
    · exact .inr (.inr ⟨t, down_mem h subset_union_right, h₁, h, rfl⟩)
  · rintro ((⟨h, hA⟩ | ⟨t, ht, h₁, h₂, rfl⟩) | (⟨h, hA⟩ | ⟨t, ht, h₁, h₂, rfl⟩))
    · exact .inl ⟨.inl h, hA⟩
    · exact .inr ⟨t, .inl ht, h₁, .inl h₂, rfl⟩
    · exact .inl ⟨.inr h, hA⟩
    · exact .inr ⟨t, .inr ht, h₁, .inr h₂, rfl⟩

/-! ## Small facts about subdivisions -/

/-- A set without the apex that is not a face stays a non-face. -/
lemma notMem_starAt_of_notMem {K : SComplex V} {A B : Finset V} {a : V} (hB : B ∉ K)
    (haB : a ∉ B) : B ∉ K.starAt A a := fun h => hB ((mem_starAt_of_notMem haB).1 h).1

/-- If `A ∪ B` is not a face then `a ∪ (B \ A)` is not a face after subdividing at `A` with
apex `a`. -/
lemma insert_sdiff_notMem_starAt {K : SComplex V} {A B : Finset V} {a : V} (ha : a ∉ K.verts)
    (haB : a ∉ B) (hAB : A ∪ B ∉ K) : insert a (B \ A) ∉ K.starAt A a := fun h =>
  hAB (by
    rw [← union_sdiff_self_eq_union]
    exact ((insert_mem_starAt ha fun h' => haB (mem_sdiff.1 h').1).1 h).2.2)

/-- A vertex other than the apex is a vertex of the subdivision only if it was one before. -/
lemma notMem_verts_starAt {K : SComplex V} {A : Finset V} {a x : V} (hx : x ≠ a)
    (hxK : x ∉ K.verts) : x ∉ (K.starAt A a).verts := fun h =>
  (mem_insert.1 (verts_starAt_subset K A a h)).elim hx hxK

/-- Subdividing at a set that is not a single vertex keeps every vertex. -/
lemma verts_subset_verts_starAt {K : SComplex V} {A : Finset V} {a : V}
    (hA : ∀ x, ¬ A ⊆ {x}) : K.verts ⊆ (K.starAt A a).verts := fun x hx =>
  mem_verts.2 (mem_starAt.2 (.inl ⟨mem_verts.1 hx, hA x⟩))

/-- Subdivision of a cone away from its apex is the cone on the subdivision. -/
lemma cone_starAt {E : SComplex V} {A : Finset V} {a w : V} (hw : w ∉ E.verts) (hwA : w ∉ A) :
    (cone w E).starAt A a = cone w (E.starAt A a) := by
  rw [cone, cone, join_comm, ← join_starAt, join_comm]
  · rw [verts_simplex]; exact disjoint_singleton_right.2 hw
  · rw [verts_simplex]; exact disjoint_singleton_right.2 hwA

/-- Renaming vertices commutes with taking cones. -/
lemma map_cone {W : Type*} [DecidableEq W] (E : SComplex V) (w : V) (f : V ↪ W) :
    (cone w E).map f = cone (f w) (E.map f) := ext_mem fun s => by
  rw [mem_map, mem_cone]
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨u, hu, h⟩ := mem_cone.1 ht
    refine ⟨u.map f, map_mem_map.2 hu, ?_⟩
    rcases h with rfl | rfl
    · exact .inl rfl
    · exact .inr (Finset.map_insert f w _)
  · rintro ⟨t, ht, rfl | rfl⟩
    · obtain ⟨u, hu, rfl⟩ := mem_map.1 ht
      exact ⟨u, mem_cone.2 ⟨u, hu, .inl rfl⟩, rfl⟩
    · obtain ⟨u, hu, rfl⟩ := mem_map.1 ht
      exact ⟨insert w u, mem_cone.2 ⟨u, hu, .inr rfl⟩, Finset.map_insert f w u⟩

/-- Subdivisions at sets whose union is not a face commute. -/
theorem starAt_comm [Infinite V] {K : SComplex V} {A B : Finset V} {a b : V} (hAB : A ∪ B ∉ K)
    (ha : a ∉ K.verts) (hb : b ∉ K.verts) (hab : a ≠ b) (haA : a ∉ A) (haB : a ∉ B)
    (hbA : b ∉ A) (hbB : b ∉ B) :
    (K.starAt A a).starAt B b = (K.starAt B b).starAt A a := by
  obtain ⟨d, hd⟩ := Infinite.exists_notMem_finset (K.verts ∪ A ∪ B ∪ {a, b})
  simp only [Finset.mem_union, mem_insert, mem_singleton, not_or] at hd
  obtain ⟨⟨⟨hdK, hdA⟩, hdB⟩, had, hbd⟩ := hd
  have h1 : insert a (B \ A) ∉ (K.starAt A a).starAt B b :=
    notMem_starAt_of_notMem (insert_sdiff_notMem_starAt ha haB hAB) (by simp [hab.symm, hbB])
  have h2 : insert b (A \ B) ∉ (K.starAt B b).starAt A a :=
    notMem_starAt_of_notMem (insert_sdiff_notMem_starAt hb hbA (by rwa [union_comm]))
      (by simp [hab, haA])
  have := starAt_triple ha hb hdK hab (Ne.symm had) (Ne.symm hbd) haA haB hbA hbB hdA hdB
  rwa [starAt_of_notMem h1, starAt_of_notMem h2] at this

/-! ## Tame stellar moves

Stellar moves relative to a protected complex `E` and a protected set of vertices `S`: no face of
`E` is subdivided, no vertex of `E` or `S` is used as an apex, no vertex of `S` is removed, and a
weld only removes a cone whose base `B` has a vertex outside `E`. -/

/-- `starAt B b` is an admissible subdivision of `X` relative to `E` and `S`: `B` is a nonempty
face of `X` outside `E`, the apex `b` is new to `X`, `S` and `E`, and `B` is not a single vertex
of `S`. -/
def IsSub (E : SComplex V) (S : Finset V) (X : SComplex V) (B : Finset V) (b : V) : Prop :=
  B ∈ X ∧ B.Nonempty ∧ B ∉ E ∧ b ∉ X.verts ∧ b ∉ S ∧ b ∉ E.verts ∧ ∀ x ∈ S, B ≠ {x}

/-- One tame move: an admissible subdivision, or the inverse of an admissible subdivision whose
face `B` has a vertex outside `E`. -/
def TStep (E : SComplex V) (S : Finset V) (X Y : SComplex V) : Prop :=
  (∃ B b, IsSub E S X B b ∧ Y = X.starAt B b) ∨
    (∃ B b, IsSub E S Y B b ∧ ¬ B ⊆ E.verts ∧ X = Y.starAt B b)

/-- Finite chains of tame moves. -/
abbrev TChain (E : SComplex V) (S : Finset V) : SComplex V → SComplex V → Prop :=
  Relation.ReflTransGen (TStep E S)

variable {E X Y : SComplex V} {S S' B : Finset V} {b : V}

/-- An admissible subdivision stays admissible for fewer protected vertices. -/
lemma IsSub.mono (h : IsSub E S X B b) (hS : S' ⊆ S) : IsSub E S' X B b :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun h' => h.2.2.2.2.1 (hS h'), h.2.2.2.2.2.1,
    fun x hx => h.2.2.2.2.2.2 x (hS hx)⟩

/-- A tame move stays tame for fewer protected vertices. -/
lemma TStep.mono (h : TStep E S X Y) (hS : S' ⊆ S) : TStep E S' X Y := by
  rcases h with ⟨B, b, h, rfl⟩ | ⟨B, b, h, hB, rfl⟩
  · exact .inl ⟨B, b, h.mono hS, rfl⟩
  · exact .inr ⟨B, b, h.mono hS, hB, rfl⟩

/-- Fewer protected vertices allow more moves. -/
lemma TChain.mono (h : TChain E S X Y) (hS : S' ⊆ S) : TChain E S' X Y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h ih => exact ih.tail (h.mono hS)

/-- Subdividing at a set that may or may not be a face is a chain of at most one move. -/
lemma TChain.fwd (hne : B.Nonempty) (hBE : B ∉ E) (hb : b ∉ X.verts) (hbS : b ∉ S)
    (hbE : b ∉ E.verts) (hS : ∀ x ∈ S, B ≠ {x}) : TChain E S X (X.starAt B b) := by
  by_cases hB : B ∈ X
  · exact Relation.ReflTransGen.single (.inl ⟨B, b, ⟨hB, hne, hBE, hb, hbS, hbE, hS⟩, rfl⟩)
  · rw [starAt_of_notMem hB]

/-- Undoing a subdivision at a set with a vertex outside `E` is a chain of at most one move. -/
lemma TChain.weld (hBE : ¬ B ⊆ E.verts) (hne : B.Nonempty) (hb : b ∉ X.verts) (hbS : b ∉ S)
    (hbE : b ∉ E.verts) (hS : ∀ x ∈ S, B ≠ {x}) : TChain E S (X.starAt B b) X := by
  by_cases hB : B ∈ X
  · exact Relation.ReflTransGen.single
      (.inr ⟨B, b, ⟨hB, hne, fun h => hBE (subset_verts h), hb, hbS, hbE, hS⟩, hBE, rfl⟩)
  · rw [starAt_of_notMem hB]

/-- An admissible subdivision keeps and creates no protected vertex. -/
lemma IsSub.mem_verts_starAt_iff (h : IsSub E S X B b) {x : V} (hx : x ∈ S) :
    x ∈ (X.starAt B b).verts ↔ x ∈ X.verts := by
  rw [mem_verts_starAt h.1 h.2.1 h.2.2.2.1]
  constructor
  · rintro (rfl | ⟨h', -⟩)
    · exact absurd hx h.2.2.2.2.1
    · exact h'
  · exact fun h' => .inr ⟨h', fun h'' => h.2.2.2.2.2.2 x hx (h.2.1.subset_singleton_iff.1 h'')⟩

/-- Tame moves keep the protected vertices of a complex. -/
lemma TStep.mem_verts_iff (h : TStep E S X Y) {x : V} (hx : x ∈ S) :
    x ∈ X.verts ↔ x ∈ Y.verts := by
  rcases h with ⟨B, b, h, rfl⟩ | ⟨B, b, h, -, rfl⟩
  · exact (h.mem_verts_starAt_iff hx).symm
  · exact h.mem_verts_starAt_iff hx

/-- Chains of tame moves keep the protected vertices of a complex. -/
lemma TChain.mem_verts_iff (h : TChain E S X Y) {x : V} (hx : x ∈ S) :
    x ∈ X.verts ↔ x ∈ Y.verts := by
  induction h with
  | refl => exact Iff.rfl
  | tail _ h ih => exact ih.trans (h.mem_verts_iff hx)

/-! ## Renaming vertices -/

section Map

variable {W : Type*} [DecidableEq W]

/-- Renaming vertices maps admissible subdivisions to admissible subdivisions. -/
lemma IsSub.map (h : IsSub E S X B b) (f : V ↪ W) :
    IsSub (E.map f) (S.map f) (X.map f) (B.map f) (f b) := by
  obtain ⟨hB, hne, hBE, hbX, hbS, hbE, hS⟩ := h
  refine ⟨map_mem_map.2 hB, hne.map, fun h => hBE (map_mem_map.1 h), ?_, ?_, ?_, ?_⟩
  · rw [verts_map, mem_map' f]; exact hbX
  · rw [mem_map' f]; exact hbS
  · rw [verts_map, mem_map' f]; exact hbE
  · intro x hx h
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hx
    rw [← Finset.map_singleton, Finset.map_inj] at h
    exact hS y hy h

/-- Renaming vertices maps tame moves to tame moves. -/
lemma TStep.map (h : TStep E S X Y) (f : V ↪ W) :
    TStep (E.map f) (S.map f) (X.map f) (Y.map f) := by
  rcases h with ⟨B, b, h, rfl⟩ | ⟨B, b, h, hB, rfl⟩
  · exact .inl ⟨B.map f, f b, h.map f, map_starAt X B b f⟩
  · refine .inr ⟨B.map f, f b, h.map f, ?_, map_starAt Y B b f⟩
    rw [verts_map, Finset.map_subset_map]; exact hB

/-- Renaming vertices maps chains of tame moves to chains of tame moves. -/
lemma TChain.map (h : TChain E S X Y) (f : V ↪ W) :
    TChain (E.map f) (S.map f) (X.map f) (Y.map f) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h ih => exact ih.tail (h.map f)

end Map

/-! ## Starrable complexes -/

/-- `X` is starrable relative to `E`: for every protected set `S` that meets `X` only in vertices
of `E`, and every vertex `w` new to `S`, `X` and `E`, a chain of tame moves turns `X` into the cone
`w ⋆ E`. For a ball `X` with boundary `E` this is the notion of Lickorish's Section 3. -/
def Starrable (E X : SComplex V) : Prop :=
  ∀ S : Finset V, (∀ x ∈ S, x ∈ X.verts → x ∈ E.verts) → ∀ w, w ∉ S → w ∉ X.verts →
    w ∉ E.verts → TChain E S X (cone w E)

/-- Starrability is invariant under permutations of the vertices. -/
theorem Starrable.map_perm (h : Starrable E X) (σ : Equiv.Perm V) :
    Starrable (E.map σ.toEmbedding) (X.map σ.toEmbedding) := by
  intro S hS w hwS hwX hwE
  have eS : (S.map σ.symm.toEmbedding).map σ.toEmbedding = S := by ext x; simp
  have ew : σ.toEmbedding (σ.symm w) = w := by simp
  have key := h (S.map σ.symm.toEmbedding) (fun x hx hxX => ?_) (σ.symm w) ?_ ?_ ?_
  · have := key.map σ.toEmbedding
    rwa [map_cone, eS, ew] at this
  · have h1 : σ x ∈ S := by
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hx
      simpa using hy
    have h2 := hS (σ x) h1 (by rw [verts_map]; exact Finset.mem_map_of_mem _ hxX)
    rw [verts_map] at h2
    simpa using h2
  · exact fun h' => hwS ((Finset.mem_map' σ.symm.toEmbedding).1 h')
  · intro h'
    exact hwX (by rw [verts_map, ← ew]; exact Finset.mem_map_of_mem _ h')
  · intro h'
    exact hwE (by rw [verts_map, ← ew]; exact Finset.mem_map_of_mem _ h')

/-! ## Subdivisions of starrable complexes -/

/-- Every vertex of a face is a vertex of the complex. -/
lemma mem_verts_of_mem {K : SComplex V} {s : Finset V} {x : V} (hs : s ∈ K) (hx : x ∈ s) :
    x ∈ K.verts := subset_verts hs hx

/-- The inductive core of Lickorish's Lemma 3.4: a chain of tame moves from `K` to `w ⋆ E` that
also protects the apex `a` gives a chain from the subdivision of `K` at `A` to `w ⋆ E'`, where
`E'` is the subdivision of `E` at `A`. -/
theorem TChain.starAt_core [Infinite V] {A : Finset V} {a w : V}
    (hAE : A ⊆ E.verts) (haE : a ∉ E.verts) (hwE : w ∉ E.verts) (haS : A ∉ E → a ∉ S)
    {K : SComplex V} (hK : TChain E (insert a S) K (cone w E)) (hA : A ∈ K) (ha : a ∉ K.verts) :
    TChain (E.starAt A a) S (K.starAt A a) (cone w (E.starAt A a)) := by
  revert hA ha
  induction hK using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro _ _
    rw [cone_starAt hwE (fun h => hwE (hAE h))]
  | @head K K1 hstep hrest ih =>
    intro hA ha
    have haA : a ∉ A := fun h => ha (mem_verts_of_mem hA h)
    rcases hstep with ⟨B, b, ⟨hB, hBne, hBE, hbK, hbS, hbE, hBS⟩, rfl⟩ |
      ⟨B, b, ⟨hB, hBne, hBE, hbK, hbS, hbE, hBS⟩, hBEv, rfl⟩
    · -- a forward move `K1 = K.starAt B b`
      simp only [mem_insert, not_or] at hbS
      obtain ⟨hba, hbS⟩ := hbS
      have haB : a ∉ B := fun h => ha (mem_verts_of_mem hB h)
      have hbA : b ∉ A := fun h => hbK (mem_verts_of_mem hA h)
      have hbB : b ∉ B := fun h => hbK (mem_verts_of_mem hB h)
      have hbE' : b ∉ (E.starAt A a).verts := notMem_verts_starAt hba hbE
      have hBE' : B ∉ E.starAt A a := notMem_starAt_of_notMem hBE haB
      have hBS' : ∀ x ∈ S, B ≠ {x} := fun x hx => hBS x (mem_insert_of_mem hx)
      have ih' : ¬ B ⊆ A → TChain (E.starAt A a) S ((K.starAt B b).starAt A a)
          (cone w (E.starAt A a)) := fun h =>
        ih ((mem_starAt_of_notMem hbA).2 ⟨hA, h⟩) (notMem_verts_starAt (Ne.symm hba) ha)
      have step1 : TChain (E.starAt A a) S (K.starAt A a) ((K.starAt A a).starAt B b) :=
        TChain.fwd hBne hBE' (notMem_verts_starAt hba hbK) hbS hbE' hBS'
      by_cases hAB : A ∪ B ∈ K
      · obtain ⟨d, hd⟩ := Infinite.exists_notMem_finset (K.verts ∪ E.verts ∪ S ∪ A ∪ B ∪ {a, b})
        simp only [Finset.mem_union, mem_insert, mem_singleton, not_or] at hd
        obtain ⟨⟨⟨⟨⟨hdK, hdE⟩, hdS⟩, hdA⟩, hdB⟩, hda, hdb⟩ := hd
        have hdE' : d ∉ (E.starAt A a).verts := notMem_verts_starAt hda hdE
        have triple := starAt_triple ha hbK hdK (Ne.symm hba) (Ne.symm hda) (Ne.symm hdb) haA haB
          hbA hbB hdA hdB
        have hDS : ∀ x ∈ S, insert b (A \ B) ≠ {x} := fun x hx h => by
          have h1 : b ∈ insert b (A \ B) := mem_insert_self b _
          rw [h, mem_singleton] at h1
          exact hbS (h1 ▸ hx)
        by_cases hBA : B ⊆ A
        · -- the subdivided face lies in `A`, so `A ∉ E` and `E' = E`
          have hAE' : A ∉ E := fun h => hBE (down_mem h hBA)
          have haS' : a ∉ S := haS hAE'
          have hAK1 : A ∉ K.starAt B b := fun h => ((mem_starAt_of_notMem hbA).1 h).2 hBA
          rw [starAt_of_notMem hAE'] at step1 hdE' ⊢
          have step2 : TChain E S ((K.starAt A a).starAt B b)
              (((K.starAt A a).starAt B b).starAt (insert a (B \ A)) d) :=
            TChain.fwd (insert_nonempty _ _) (fun h => haE (mem_verts_of_mem h (mem_insert_self a _)))
              (notMem_verts_starAt hdb (notMem_verts_starAt hda hdK)) hdS hdE
              (fun x hx h => by
                have h1 : a ∈ insert a (B \ A) := mem_insert_self a _
                rw [h, mem_singleton] at h1
                exact haS' (h1 ▸ hx))
          rw [triple, starAt_of_notMem hAK1] at step2
          have step3 : TChain E S ((K.starAt B b).starAt (insert b (A \ B)) d) (K.starAt B b) :=
            TChain.weld (fun h => hbE (h (mem_insert_self b _))) (insert_nonempty _ _)
              (notMem_verts_starAt hdb hdK) hdS hdE hDS
          exact step1.trans (step2.trans (step3.trans (TChain.mono hrest (subset_insert a S))))
        · obtain ⟨y, hyB, hyA⟩ := not_subset.1 hBA
          have step2 : TChain (E.starAt A a) S ((K.starAt A a).starAt B b)
              (((K.starAt A a).starAt B b).starAt (insert a (B \ A)) d) :=
            TChain.fwd (insert_nonempty _ _)
              (insert_sdiff_notMem_starAt haE haB (fun h => hBE (down_mem h subset_union_right)))
              (notMem_verts_starAt hdb (notMem_verts_starAt hda hdK)) hdS hdE'
              (fun x _ h => by
                have h1 : a ∈ insert a (B \ A) := mem_insert_self a _
                have h2 : y ∈ insert a (B \ A) := mem_insert_of_mem (mem_sdiff.2 ⟨hyB, hyA⟩)
                rw [h, mem_singleton] at h1 h2
                exact haB (h1.trans h2.symm ▸ hyB))
          rw [triple] at step2
          have step3 : TChain (E.starAt A a) S
              (((K.starAt B b).starAt A a).starAt (insert b (A \ B)) d)
              ((K.starAt B b).starAt A a) :=
            TChain.weld (fun h => hbE' (h (mem_insert_self b _))) (insert_nonempty _ _)
              (notMem_verts_starAt hda (notMem_verts_starAt hdb hdK)) hdS hdE' hDS
          exact step1.trans (step2.trans (step3.trans (ih' hBA)))
      · have hBA : ¬ B ⊆ A := fun h => hAB (by rwa [union_eq_left.2 h])
        rw [starAt_comm hAB ha hbK (Ne.symm hba) haA haB hbA hbB] at step1
        exact step1.trans (ih' hBA)
    · -- a weld `K = K1.starAt B b`
      simp only [mem_insert, not_or] at hbS
      obtain ⟨hba, hbS⟩ := hbS
      have hbA : b ∉ A := fun h => hbE (hAE h)
      have hBA : ¬ B ⊆ A := fun h => hBEv (h.trans hAE)
      have hAK1 : A ∈ K1 := ((mem_starAt_of_notMem hbA).1 hA).1
      have haK1 : a ∉ K1.verts := fun h => ha (by
        rw [mem_verts_starAt hB hBne hbK]
        exact .inr ⟨h, fun h' => hBS a (mem_insert_self a S) (hBne.subset_singleton_iff.1 h')⟩)
      have haB : a ∉ B := fun h => haK1 (mem_verts_of_mem hB h)
      have hbB : b ∉ B := fun h => hbK (mem_verts_of_mem hB h)
      have hbE' : b ∉ (E.starAt A a).verts := notMem_verts_starAt hba hbE
      obtain ⟨y, hyB, hyE⟩ := not_subset.1 hBEv
      have hyE' : y ∉ (E.starAt A a).verts :=
        notMem_verts_starAt (fun h => haB (h ▸ hyB)) hyE
      have hBS' : ∀ x ∈ S, B ≠ {x} := fun x hx => hBS x (mem_insert_of_mem hx)
      have stepB : TChain (E.starAt A a) S ((K1.starAt A a).starAt B b) (K1.starAt A a) :=
        TChain.weld (fun h => hyE' (h hyB)) hBne (notMem_verts_starAt hba hbK) hbS hbE' hBS'
      have ih' := ih hAK1 haK1
      by_cases hAB : A ∪ B ∈ K1
      · obtain ⟨d, hd⟩ := Infinite.exists_notMem_finset (K1.verts ∪ E.verts ∪ S ∪ A ∪ B ∪ {a, b})
        simp only [Finset.mem_union, mem_insert, mem_singleton, not_or] at hd
        obtain ⟨⟨⟨⟨⟨hdK, hdE⟩, hdS⟩, hdA⟩, hdB⟩, hda, hdb⟩ := hd
        have hdE' : d ∉ (E.starAt A a).verts := notMem_verts_starAt hda hdE
        have step1 : TChain (E.starAt A a) S ((K1.starAt B b).starAt A a)
            (((K1.starAt B b).starAt A a).starAt (insert b (A \ B)) d) :=
          TChain.fwd (insert_nonempty _ _)
            (fun h => hbE' (mem_verts_of_mem h (mem_insert_self b _)))
            (notMem_verts_starAt hda (notMem_verts_starAt hdb hdK)) hdS hdE'
            (fun x hx h => by
              have h1 : b ∈ insert b (A \ B) := mem_insert_self b _
              rw [h, mem_singleton] at h1
              exact hbS (h1 ▸ hx))
        rw [← starAt_triple haK1 hbK hdK (Ne.symm hba) (Ne.symm hda) (Ne.symm hdb) haA haB hbA hbB
          hdA hdB] at step1
        have hyC : y ∈ insert a (B \ A) := mem_insert_of_mem (mem_sdiff.2 ⟨hyB, fun h => hyE (hAE h)⟩)
        have step2 : TChain (E.starAt A a) S
            (((K1.starAt A a).starAt B b).starAt (insert a (B \ A)) d)
            ((K1.starAt A a).starAt B b) :=
          TChain.weld (fun h => hyE' (h hyC)) (insert_nonempty _ _)
            (notMem_verts_starAt hdb (notMem_verts_starAt hda hdK)) hdS hdE'
            (fun x _ h => by
              have h1 : a ∈ insert a (B \ A) := mem_insert_self a _
              have h2 := hyC
              rw [h, mem_singleton] at h1 h2
              exact haB (h1.trans h2.symm ▸ hyB))
        exact step1.trans (step2.trans (stepB.trans ih'))
      · rw [← starAt_comm hAB haK1 hbK (Ne.symm hba) haA haB hbA hbB]
        exact stepB.trans ih'

/-- Lickorish's Lemma 3.4 for one move: a subdivision of a starrable complex is starrable relative
to the induced subdivision of `E`. -/
theorem Starrable.starAt [Infinite V] {K : SComplex V} (h : Starrable E K) {A : Finset V} {a : V}
    (hA : A ∈ K) (hne : A.Nonempty) (ha : a ∉ K.verts) (haE : a ∉ E.verts) :
    Starrable (E.starAt A a) (K.starAt A a) := by
  by_cases hsing : ∃ x, A = {x}
  · obtain ⟨x, rfl⟩ := hsing
    rw [starAt_singleton ha, starAt_singleton haE]
    exact h.map_perm _
  have hA1 : ∀ x, ¬ A ⊆ {x} := fun x h' => hsing ⟨x, hne.subset_singleton_iff.1 h'⟩
  intro S hS w hwS hwL hwE'
  have haL : a ∈ (K.starAt A a).verts := (mem_verts_starAt hA hne ha).2 (.inl rfl)
  have hKL : K.verts ⊆ (K.starAt A a).verts := verts_subset_verts_starAt hA1
  have hEE : E.verts ⊆ (E.starAt A a).verts := verts_subset_verts_starAt hA1
  have hS' : ∀ x ∈ S, x ∈ K.verts → x ∈ E.verts := fun x hx hxK =>
    (mem_insert.1 (verts_starAt_subset E A a (hS x hx (hKL hxK)))).resolve_left
      (fun h' => ha (h' ▸ hxK))
  by_cases hAE : A ⊆ E.verts
  · refine TChain.starAt_core hAE haE (fun h' => hwE' (hEE h')) (fun hAE' haS => ?_)
      (h _ ?_ w ?_ (fun h' => hwL (hKL h')) (fun h' => hwE' (hEE h'))) hA ha
    · have := hS a haS haL
      rw [starAt_of_notMem hAE'] at this
      exact haE this
    · intro x hx hxK
      rcases mem_insert.1 hx with rfl | hx
      · exact absurd hxK ha
      · exact hS' x hx hxK
    · simp only [mem_insert, not_or]
      exact ⟨fun h' => hwL (h' ▸ haL), hwS⟩
  · have hAE' : A ∉ E := fun h' => hAE (subset_verts h')
    rw [starAt_of_notMem hAE'] at hS hwE' ⊢
    have haS : a ∉ S := fun haS => haE (hS a haS haL)
    exact Relation.ReflTransGen.head
      (.inr ⟨A, a, ⟨hA, hne, hAE', ha, haS, haE, fun x _ h' => hA1 x (le_of_eq h')⟩, hAE, rfl⟩)
      (h S hS' w hwS (fun h' => hwL (hKL h')) hwE')


/-! ## Cones -/

/-- Away from the apex, membership in a cone is membership in the base after erasing the apex. -/
lemma mem_cone_iff_erase {K : SComplex V} {v : V} (hv : v ∉ K.verts) {s : Finset V} :
    s ∈ cone v K ↔ s.erase v ∈ K := by
  rw [mem_cone]
  constructor
  · rintro ⟨t, ht, rfl | rfl⟩
    · rwa [erase_eq_of_notMem fun h => hv (mem_verts_of_mem ht h)]
    · rwa [erase_insert fun h => hv (mem_verts_of_mem ht h)]
  · intro h
    by_cases hs : v ∈ s
    · exact ⟨_, h, .inr (insert_erase hs).symm⟩
    · exact ⟨_, h, .inl (erase_eq_of_notMem hs).symm⟩

/-- A set without the apex lies in the cone exactly when it lies in the base. -/
lemma mem_cone_of_notMem {K : SComplex V} {v : V} {t : Finset V} (hv : v ∉ K.verts)
    (ht : v ∉ t) : t ∈ cone v K ↔ t ∈ K := by
  rw [mem_cone_iff_erase hv, erase_eq_of_notMem ht]

/-- A set through the apex lies in the cone exactly when the rest lies in the base. -/
lemma insert_mem_cone {K : SComplex V} {v : V} {t : Finset V} (hv : v ∉ K.verts) (ht : v ∉ t) :
    insert v t ∈ cone v K ↔ t ∈ K := by
  rw [mem_cone_iff_erase hv, erase_insert ht]

/-- The vertices of a cone are the apex and the vertices of the base. -/
lemma verts_cone_subset (K : SComplex V) (v : V) : (cone v K).verts ⊆ insert v K.verts := by
  intro x hx
  obtain ⟨t, ht, h | h⟩ := mem_cone.1 (mem_verts.1 hx)
  · exact mem_insert_of_mem (mem_verts.2 (h ▸ ht))
  · have hx' : x ∈ insert v t := by rw [← h]; exact mem_singleton_self x
    rcases mem_insert.1 hx' with rfl | h'
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_verts_of_mem ht h')

/-- The base of a cone is part of it. -/
lemma verts_subset_verts_cone (K : SComplex V) (v : V) : K.verts ⊆ (cone v K).verts :=
  fun _ hx => mem_verts.2 (mem_cone.2 ⟨_, mem_verts.1 hx, .inl rfl⟩)

/-- The apex is a vertex of the cone on a nonempty complex. -/
lemma mem_verts_cone_apex {K : SComplex V} {v : V} (hK : ∅ ∈ K) : v ∈ (cone v K).verts :=
  mem_verts.2 (mem_cone.2 ⟨∅, hK, .inr (by simp)⟩)

/-- A point other than the apex and outside the base is not a vertex of the cone. -/
lemma notMem_verts_cone {K : SComplex V} {v x : V} (hxv : x ≠ v) (hx : x ∉ K.verts) :
    x ∉ (cone v K).verts := fun h =>
  (mem_insert.1 (verts_cone_subset K v h)).elim hxv hx

/-- Union is commutative. -/
lemma union_comm (K L : SComplex V) : K.union L = L.union K :=
  ext_mem fun s => by rw [mem_union_iff, mem_union_iff, or_comm]

/-- The cone on a union is the union of the cones. -/
lemma cone_union (K L : SComplex V) (v : V) :
    cone v (K.union L) = (cone v K).union (cone v L) := ext_mem fun s => by
  simp only [mem_cone, mem_union_iff]
  constructor
  · rintro ⟨t, ht | ht, h⟩
    · exact .inl ⟨t, ht, h⟩
    · exact .inr ⟨t, ht, h⟩
  · rintro (⟨t, ht, h⟩ | ⟨t, ht, h⟩)
    · exact ⟨t, .inl ht, h⟩
    · exact ⟨t, .inr ht, h⟩

/-- Cones from two new apexes commute. -/
lemma cone_comm {K : SComplex V} {v w : V} (hvw : v ≠ w) (hv : v ∉ K.verts) (hw : w ∉ K.verts) :
    cone v (cone w K) = cone w (cone v K) := ext_mem fun s => by
  rw [mem_cone_iff_erase (notMem_verts_cone hvw hv), mem_cone_iff_erase hw,
    mem_cone_iff_erase (notMem_verts_cone hvw.symm hw), mem_cone_iff_erase hv, erase_right_comm]

/-- Renaming vertices commutes with unions. -/
lemma map_union {W : Type*} [DecidableEq W] (K L : SComplex V) (f : V ↪ W) :
    (K.union L).map f = (K.map f).union (L.map f) := ext_mem fun s => by
  simp only [mem_map, mem_union_iff]
  constructor
  · rintro ⟨t, ht | ht, rfl⟩
    · exact .inl ⟨t, ht, rfl⟩
    · exact .inr ⟨t, ht, rfl⟩
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ⟨t, .inl ht, rfl⟩
    · exact ⟨t, .inr ht, rfl⟩

/-- A renaming that fixes every vertex fixes the complex. -/
lemma map_eq_self {K : SComplex V} {f : V ↪ V} (h : ∀ x ∈ K.verts, f x = x) : K.map f = K := by
  rw [map_congr (g := Function.Embedding.refl V) h, map_refl]

/-- The vertices of a star are vertices of the complex. -/
lemma verts_star_subset (K : SComplex V) (σ : Finset V) : (K.star σ).verts ⊆ K.verts :=
  fun _ hx => mem_verts.2 (down_mem (mem_star.1 (mem_verts.1 hx)) subset_union_right)

/-- The star of the apex of a cone is the whole cone. -/
lemma star_cone_apex {E : SComplex V} {u : V} (hu : u ∉ E.verts) :
    (cone u E).star {u} = cone u E := ext_mem fun s => by
  rw [mem_star, mem_cone_iff_erase hu, mem_cone_iff_erase hu, singleton_union,
    erase_insert_eq_erase]

/-- Subdividing a cone at its apex renames the apex. -/
lemma cone_starAt_apex {E : SComplex V} {u w : V} (hu : u ∉ E.verts)
    (hw : w ∉ (cone u E).verts) : (cone u E).starAt {u} w = cone w E := by
  rw [starAt_singleton hw, map_cone,
    map_swap_eq_self hu fun h => hw (verts_subset_verts_cone E u h)]
  congr 1
  exact Equiv.swap_apply_left u w

/-- A subdivision of a cone at a face through the apex: the cone on the subdivided base, together
with the cone from the new apex on the star of the face. -/
theorem cone_starAt_insert {K : SComplex V} {A : Finset V} {v b : V} (hv : v ∉ K.verts)
    (hb : b ∉ K.verts) (hbv : b ≠ v) (hvA : v ∉ A) :
    (cone v K).starAt (insert v A) b = (cone v (K.starAt A b)).union (cone b (K.star A)) := by
  have hb' : b ∉ (cone v K).verts := notMem_verts_cone hbv hb
  have hv' : v ∉ (K.starAt A b).verts := notMem_verts_starAt hbv.symm hv
  have hbs : b ∉ (K.star A).verts := fun h => hb (verts_star_subset K A h)
  have hvKs : ∀ u, v ∈ u → u ∉ K := fun u hu h => hv (mem_verts_of_mem h hu)
  refine ext_mem fun s => ?_
  obtain ⟨t, hvt, hbt, h | h | h | h⟩ : ∃ t, v ∉ t ∧ b ∉ t ∧
      (s = t ∨ s = insert v t ∨ s = insert b t ∨ s = insert v (insert b t)) := by
    refine ⟨(s.erase v).erase b, fun h => notMem_erase v s (mem_of_mem_erase h),
      notMem_erase b _, ?_⟩
    by_cases h1 : v ∈ s <;> by_cases h2 : b ∈ s
    · refine .inr (.inr (.inr ?_))
      rw [insert_erase (mem_erase.2 ⟨hbv, h2⟩), insert_erase h1]
    · refine .inr (.inl ?_)
      rw [erase_eq_of_notMem fun h => h2 (mem_of_mem_erase h), insert_erase h1]
    · refine .inr (.inr (.inl ?_))
      rw [erase_eq_of_notMem h1, insert_erase h2]
    · refine .inl ?_
      rw [erase_eq_of_notMem h1, erase_eq_of_notMem h2]
  all_goals subst s
  · rw [mem_union_iff, mem_starAt_of_notMem hbt, mem_cone_of_notMem hv hvt,
      mem_cone_of_notMem hv' hvt, mem_starAt_of_notMem hbt, mem_cone_of_notMem hbs hbt, mem_star]
    have : ¬ insert v A ⊆ t := fun h => hvt (h (mem_insert_self v A))
    constructor
    · rintro ⟨h, -⟩
      by_cases hA : A ⊆ t
      · exact .inr (by rwa [union_eq_right.2 hA])
      · exact .inl ⟨h, hA⟩
    · rintro (⟨h, -⟩ | h)
      · exact ⟨h, this⟩
      · exact ⟨down_mem h subset_union_right, this⟩
  · have hbvt : b ∉ insert v t := by simp [hbv, hbt]
    rw [mem_union_iff, mem_starAt_of_notMem hbvt, insert_mem_cone hv hvt,
      insert_mem_cone hv' hvt, mem_starAt_of_notMem hbt, mem_cone_of_notMem hbs hbvt, mem_star,
      insert_subset_insert_iff hvA]
    refine ⟨fun h => .inl h, fun h => h.elim id fun h => ?_⟩
    exact absurd h (hvKs _ (mem_union_right _ (mem_insert_self v t)))
  · have hvbt : v ∉ insert b t := by simp [hbv.symm, hvt]
    have hvAt : v ∉ A ∪ t := by simp [hvA, hvt]
    rw [mem_union_iff, insert_mem_starAt hb' hbt, mem_cone_of_notMem hv hvt,
      mem_cone_of_notMem hv' hvbt, insert_mem_starAt hb hbt, insert_mem_cone hbs hbt, mem_star,
      insert_union, insert_mem_cone hv hvAt]
    have : ¬ insert v A ⊆ t := fun h => hvt (h (mem_insert_self v A))
    constructor
    · rintro ⟨-, -, h⟩
      exact .inr h
    · rintro (⟨-, -, h⟩ | h)
      · exact ⟨down_mem h subset_union_right, this, h⟩
      · exact ⟨down_mem h subset_union_right, this, h⟩
  · have hbvt : b ∉ insert v t := by simp [hbv, hbt]
    have hvbt : v ∉ insert b t := by simp [hbv.symm, hvt]
    have hvAt : v ∉ A ∪ t := by simp [hvA, hvt]
    have e : insert v A ∪ insert v t = insert v (A ∪ t) := by
      ext x; simp only [mem_union, mem_insert]; tauto
    rw [mem_union_iff, insert_mem_cone hv' hvbt, insert_mem_starAt hb hbt, insert_comm v b t,
      insert_mem_starAt hb' hbvt, insert_mem_cone hbs hbvt, mem_star, insert_mem_cone hv hvt,
      insert_subset_insert_iff hvA, e, insert_mem_cone hv hvAt]
    refine ⟨fun h => .inl h, fun h => h.elim id fun h => ?_⟩
    exact absurd h (hvKs _ (mem_union_right _ (mem_insert_self v t)))

/-! ## Gluing a fixed complex along a chain -/

section Glue

variable {E' R Z : SComplex V}

/-- An admissible subdivision of `Z` stays admissible for `Z ∪ R` and a coarser `E'`, as long as
`R` only meets `Z` inside `E`. -/
lemma IsSub.glue (h : IsSub E S Z B b) (hRS : R.verts ⊆ S) (hf : ∀ s ∈ Z, s ∈ R → s ∈ E)
    (hE'v : E'.verts ⊆ E.verts ∪ R.verts) (hE'f : ∀ s ∈ E', s ∈ E ∨ s ∈ R) (hS' : S' ⊆ S) :
    IsSub E' S' (Z.union R) B b ∧ B ∉ R := by
  obtain ⟨hB, hne, hBE, hbZ, hbS, hbE, hS⟩ := h
  have hBR : B ∉ R := fun h' => hBE (hf B hB h')
  have hbR : b ∉ R.verts := fun h' => hbS (hRS h')
  refine ⟨⟨mem_union_iff.2 (.inl hB), hne, fun h' => (hE'f B h').elim hBE hBR, ?_,
    fun h' => hbS (hS' h'), fun h' => ?_, fun x hx => hS x (hS' hx)⟩, hBR⟩
  · rw [verts_union, Finset.mem_union, not_or]; exact ⟨hbZ, hbR⟩
  · exact (Finset.mem_union.1 (hE'v h')).elim hbE hbR

/-- A tame move keeps the condition that `R` meets the complex only inside `E`. -/
lemma TStep.glue_inv (h : TStep E S X Y) (hRS : R.verts ⊆ S)
    (hv : ∀ x ∈ R.verts, x ∈ X.verts → x ∈ E.verts) (hf : ∀ s ∈ X, s ∈ R → s ∈ E) :
    (∀ x ∈ R.verts, x ∈ Y.verts → x ∈ E.verts) ∧ ∀ s ∈ Y, s ∈ R → s ∈ E := by
  have hv' : ∀ x ∈ R.verts, x ∈ Y.verts → x ∈ E.verts := fun x hx hxY =>
    hv x hx ((h.mem_verts_iff (hRS hx)).2 hxY)
  refine ⟨hv', fun s hs hsR => ?_⟩
  have hbs : ∀ c, c ∉ S → c ∉ s := fun c hc hcs =>
    hc (hRS (mem_verts_of_mem hsR hcs))
  rcases h with ⟨B, c, hsub, rfl⟩ | ⟨B, c, hsub, hBE, rfl⟩
  · exact hf s ((mem_starAt_of_notMem (hbs c hsub.2.2.2.2.1)).1 hs).1 hsR
  · refine hf s ((mem_starAt_of_notMem fun hcs => hsub.2.2.2.1 (mem_verts_of_mem hs hcs)).2
      ⟨hs, fun hBs => ?_⟩) hsR
    obtain ⟨y, hyB, hyE⟩ := Finset.not_subset.1 hBE
    exact hyE (hv' y (mem_verts_of_mem hsR (hBs hyB)) (mem_verts_of_mem hsub.1 hyB))

/-- A tame move relative to `E` glued to `R` is a tame move relative to `E'`. -/
lemma TStep.glue (h : TStep E S X Y) (hRS : R.verts ⊆ S) (hfX : ∀ s ∈ X, s ∈ R → s ∈ E)
    (hvY : ∀ x ∈ R.verts, x ∈ Y.verts → x ∈ E.verts) (hfY : ∀ s ∈ Y, s ∈ R → s ∈ E)
    (hE'v : E'.verts ⊆ E.verts ∪ R.verts) (hE'f : ∀ s ∈ E', s ∈ E ∨ s ∈ R) (hS' : S' ⊆ S) :
    TStep E' S' (X.union R) (Y.union R) := by
  rcases h with ⟨B, c, hsub, rfl⟩ | ⟨B, c, hsub, hBE, rfl⟩
  · obtain ⟨hsub', hBR⟩ := hsub.glue hRS hfX hE'v hE'f hS'
    exact .inl ⟨B, c, hsub', by rw [starAt_union, starAt_of_notMem hBR]⟩
  · obtain ⟨hsub', hBR⟩ := hsub.glue hRS hfY hE'v hE'f hS'
    refine .inr ⟨B, c, hsub', fun hB => ?_, by rw [starAt_union, starAt_of_notMem hBR]⟩
    obtain ⟨y, hyB, hyE⟩ := Finset.not_subset.1 hBE
    rcases Finset.mem_union.1 (hE'v (hB hyB)) with h' | h'
    · exact hyE h'
    · exact hyE (hvY y h' (mem_verts_of_mem hsub.1 hyB))

/-- Gluing: a chain of tame moves relative to `E` stays a chain of tame moves relative to `E'`
after adding a complex `R` whose vertices are protected and which meets the start only inside
`E`, provided `E'` lies in `E ∪ R`. -/
theorem TChain.glue (h : TChain E S X Y) (hRS : R.verts ⊆ S)
    (hv : ∀ x ∈ R.verts, x ∈ X.verts → x ∈ E.verts) (hf : ∀ s ∈ X, s ∈ R → s ∈ E)
    (hE'v : E'.verts ⊆ E.verts ∪ R.verts) (hE'f : ∀ s ∈ E', s ∈ E ∨ s ∈ R) (hS' : S' ⊆ S) :
    TChain E' S' (X.union R) (Y.union R) := by
  revert hv hf
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro _ _; exact Relation.ReflTransGen.refl
  | @head X X1 hstep _ ih =>
    intro hv hf
    obtain ⟨hv1, hf1⟩ := hstep.glue_inv hRS hv hf
    exact Relation.ReflTransGen.head (hstep.glue hRS hf hv1 hf1 hE'v hE'f hS') (ih hv1 hf1)

end Glue

/-! ## Lickorish's Lemma 3.5: cones on starrable complexes -/

/-- Subdividing an edge of `w ⋆ E`-type: the double cone `v ⋆ u ⋆ E` is starrable relative to
`u ⋆ E ∪ v ⋆ E` by one subdivision of the edge `{v, u}`. -/
lemma starrable_cone_cone {E : SComplex V} {u v : V} (huv : u ≠ v) (huE : u ∉ E.verts)
    (hvE : v ∉ E.verts) : Starrable ((cone u E).union (cone v E)) (cone v (cone u E)) := by
  intro S _ w hwS hwX hwE
  by_cases hE : ∅ ∈ E
  · have hvu' : v ∉ (cone u E).verts := notMem_verts_cone huv.symm hvE
    have huv' : u ∉ (cone v E).verts := notMem_verts_cone huv huE
    have hwu' : w ∉ (cone u E).verts := fun h' => hwX (verts_subset_verts_cone _ v h')
    have hwE0 : w ∉ E.verts := fun h' => hwu' (verts_subset_verts_cone E u h')
    have hu1 : {u} ∈ cone u E := mem_verts.1 (mem_verts_cone_apex hE)
    have hwv : w ≠ v := fun e => hwX (e ▸ mem_verts_cone_apex (mem_cone.2 ⟨∅, hE, .inl rfl⟩))
    have key : (cone v (cone u E)).starAt (insert v {u}) w =
        cone w ((cone u E).union (cone v E)) := by
      rw [cone_starAt_insert hvu' hwu' hwv (by simpa using huv.symm), star_cone_apex huE,
        cone_starAt_apex huE hwu', cone_comm hwv.symm hvE hwE0, cone_union]
      exact union_comm _ _
    rw [← key]
    refine Relation.ReflTransGen.single (.inl ⟨insert v {u}, w, ⟨mem_cone.2 ⟨{u}, hu1, .inr rfl⟩,
      insert_nonempty _ _, fun h' => ?_, hwX, hwS, hwE, fun x _ e => ?_⟩, rfl⟩)
    · rcases mem_union_iff.1 h' with h'' | h''
      · exact hvu' (mem_verts_of_mem h'' (mem_insert_self v _))
      · exact huv' (mem_verts_of_mem h'' (by simp))
    · have h1 : u ∈ ({x} : Finset V) := by rw [← e]; simp
      have h2 : v ∈ ({x} : Finset V) := by rw [← e]; simp
      exact huv ((mem_singleton.1 h1).trans (mem_singleton.1 h2).symm)
  · have hE0 : ∀ s, s ∉ E := fun s hs => hE (down_mem hs (empty_subset s))
    have : cone v (cone u E) = cone w ((cone u E).union (cone v E)) :=
      ext_mem fun s => by simp [mem_cone, mem_union_iff, hE0]
    rw [this]

/-- A set through a new point is not a single point. -/
lemma insert_ne_singleton {A : Finset V} {w x : V} (hne : A.Nonempty) (hwA : w ∉ A) :
    insert w A ≠ {x} := fun e => by
  obtain ⟨y, hy⟩ := hne
  have h1 : y ∈ ({x} : Finset V) := by rw [← e]; exact mem_insert_of_mem hy
  have h2 : w ∈ ({x} : Finset V) := by rw [← e]; exact mem_insert_self w A
  exact hwA ((mem_singleton.1 h2).trans (mem_singleton.1 h1).symm ▸ hy)

/-- The forward case of Lemma 3.5: if the cone on a subdivision of `K` is starrable, so is the
cone on `K`. -/
lemma starrable_cone_fwd [Infinite V] {E K : SComplex V} {A : Finset V} {a v : V} (hA : A ∈ K)
    (hne : A.Nonempty) (hAE : A ∉ E) (ha : a ∉ K.verts) (hav : a ≠ v) (haE : a ∉ E.verts)
    (hvK : v ∉ K.verts) (hvE : v ∉ E.verts)
    (ih : Starrable ((K.starAt A a).union (cone v E)) (cone v (K.starAt A a))) :
    Starrable (K.union (cone v E)) (cone v K) := by
  intro S hS w hwS hwX hwE'
  obtain ⟨b, hb⟩ := Infinite.exists_notMem_finset (K.verts ∪ E.verts ∪ S ∪ {a, v, w})
  simp only [Finset.mem_union, mem_insert, mem_singleton, not_or] at hb
  obtain ⟨⟨⟨hbK, hbE⟩, hbS⟩, hba, hbv, hbw⟩ := hb
  have hvA : v ∉ A := fun h => hvK (mem_verts_of_mem hA h)
  have haA : a ∉ A := fun h => ha (mem_verts_of_mem hA h)
  have hbA : b ∉ A := fun h => hbK (mem_verts_of_mem hA h)
  have hwK : w ∉ K.verts := fun h => hwX (verts_subset_verts_cone K v h)
  have hwA : w ∉ A := fun h => hwK (mem_verts_of_mem hA h)
  have hwv : w ≠ v := fun e => hwX (e ▸ mem_verts_cone_apex (down_mem hA (empty_subset A)))
  have hcE : ∀ x, x ∉ (cone v E).verts → x ∉ E.verts := fun x hx h =>
    hx (verts_subset_verts_cone E v h)
  have hwvE : w ∉ (cone v E).verts := fun h => hwE' (by rw [verts_union]; exact mem_union_right _ h)
  have hbE' : b ∉ (K.union (cone v E)).verts := by
    rw [verts_union, Finset.mem_union, not_or]; exact ⟨hbK, notMem_verts_cone hbv hbE⟩
  have hAc : A ∉ cone v E := fun h => hAE ((mem_cone_of_notMem hvE hvA).1 h)
  -- the induction hypothesis with the apex renamed to `b`
  have ih' : Starrable ((K.starAt A b).union (cone v E)) (cone v (K.starAt A b)) := by
    have hAm : A.map (Equiv.swap a b).toEmbedding = A := by
      ext x
      rw [Finset.mem_map_equiv, Equiv.symm_swap]
      by_cases hxa : x = a
      · subst hxa; rw [Equiv.swap_apply_left]; exact iff_of_false hbA haA
      by_cases hxb : x = b
      · subst hxb; rw [Equiv.swap_apply_right]; exact iff_of_false haA hbA
      · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]
    have := ih.map_perm (Equiv.swap a b)
    rw [map_union, map_cone, map_cone, map_starAt, map_swap_eq_self ha hbK,
      map_swap_eq_self haE hbE, hAm,
      show (Equiv.swap a b).toEmbedding a = b from Equiv.swap_apply_left a b,
      show (Equiv.swap a b).toEmbedding v = v from
        Equiv.swap_apply_of_ne_of_ne hav.symm (Ne.symm hbv)] at this
    exact this
  -- step 1: subdivide `v ⋆ K` at `v ⋆ A`
  have dec1 := cone_starAt_insert (A := A) hvK hbK hbv hvA
  have c1 : TChain (K.union (cone v E)) S (cone v K)
      ((cone v (K.starAt A b)).union (cone b (K.star A))) := by
    rw [← dec1]
    refine Relation.ReflTransGen.single (.inl ⟨insert v A, b, ⟨mem_cone.2 ⟨A, hA, .inr rfl⟩,
      insert_nonempty _ _, fun h => ?_, notMem_verts_cone hbv hbK, hbS, hbE',
      fun x _ => insert_ne_singleton hne hvA⟩, rfl⟩)
    rcases mem_union_iff.1 h with h' | h'
    · exact hvK (mem_verts_of_mem h' (mem_insert_self v A))
    · exact hAE ((insert_mem_cone hvE hvA).1 h')
  -- step 2: the renamed chain, glued to `b ⋆ st(A, K)`
  have hRv : (cone b (K.star A)).verts ⊆ insert b K.verts := fun x hx =>
    (mem_insert.1 (verts_cone_subset _ b hx)).elim (fun h => mem_insert.2 (.inl h))
      (fun h => mem_insert_of_mem (verts_star_subset K A h))
  have hvR : v ∉ (cone b (K.star A)).verts := fun h =>
    (mem_insert.1 (hRv h)).elim (fun e => hbv e.symm) hvK
  have hK1v : (K.starAt A b).verts ⊆ ((K.starAt A b).union (cone v E)).verts := by
    rw [verts_union]; exact subset_union_left
  have c2 := ih' (S ∪ (cone b (K.star A)).verts) (fun x hx hxX => by
      rcases mem_insert.1 (verts_cone_subset _ v hxX) with rfl | h
      · rcases Finset.mem_union.1 hx with h | h
        · have := hS x h (mem_verts_cone_apex (down_mem hA (empty_subset A)))
          rw [verts_union, Finset.mem_union] at this ⊢
          exact .inr (this.resolve_left hvK)
        · exact absurd h hvR
      · exact hK1v h) w
    (by
      rw [Finset.mem_union, not_or]
      exact ⟨hwS, fun h => (mem_insert.1 (hRv h)).elim (fun e => hbw e.symm) hwK⟩)
    (notMem_verts_cone hwv (notMem_verts_starAt (Ne.symm hbw) hwK))
    (by
      rw [verts_union, Finset.mem_union, not_or]
      exact ⟨notMem_verts_starAt (Ne.symm hbw) hwK, hwvE⟩)
  have c2' := c2.glue (R := cone b (K.star A)) (E' := K.union (cone v E)) (S' := S)
    subset_union_right
    (fun x hx hxX => by
      rcases mem_insert.1 (verts_cone_subset _ v hxX) with rfl | h
      · exact absurd hx hvR
      · exact hK1v h)
    (fun s hs hsR => by
      have hvs : v ∉ s := fun h => hvR (mem_verts_of_mem hsR h)
      exact mem_union_iff.2 (.inl ((mem_cone_of_notMem
        (notMem_verts_starAt (Ne.symm hbv) hvK) hvs).1 hs)))
    (fun x hx => by
      rw [verts_union, Finset.mem_union] at hx
      rw [Finset.mem_union, verts_union, Finset.mem_union]
      rcases hx with hx | hx
      · by_cases hAx : A ⊆ {x}
        · refine .inr (verts_subset_verts_cone _ b (mem_verts.2 (mem_star.2 ?_)))
          rw [union_eq_right.2 hAx]; exact mem_verts.1 hx
        · exact .inl (.inl ((mem_verts_starAt hA hne hbK).2 (.inr ⟨hx, hAx⟩)))
      · exact .inl (.inr hx))
    (fun s hs => by
      rcases mem_union_iff.1 hs with hs | hs
      · by_cases hAs : A ⊆ s
        · refine .inr (mem_cone.2 ⟨s, mem_star.2 ?_, .inl rfl⟩)
          rwa [union_eq_right.2 hAs]
        · exact .inl (mem_union_iff.2 (.inl ((mem_starAt_of_notMem
            fun h => hbK (mem_verts_of_mem hs h)).2 ⟨hs, hAs⟩)))
      · exact .inl (mem_union_iff.2 (.inr hs)))
    subset_union_left
  -- step 3: weld `w ⋆ E'` at `w ⋆ A`
  have dec3 := cone_starAt_insert (A := A) hwE' hbE' hbw hwA
  have hstar : (K.union (cone v E)).star A = K.star A := ext_mem fun s => by
    rw [mem_star, mem_star, mem_union_iff]
    refine or_iff_left fun h => ?_
    rw [mem_cone_iff_erase hvE] at h
    exact hAE (down_mem h fun x hx => mem_erase.2 ⟨fun e => hvA (e ▸ hx), mem_union_left _ hx⟩)
  rw [starAt_union, starAt_of_notMem hAc, hstar] at dec3
  refine c1.trans (c2'.tail (.inr ⟨insert w A, b, ⟨mem_cone.2 ⟨A, mem_union_iff.2 (.inl hA),
    .inr rfl⟩, insert_nonempty _ _, fun h => hwE' (mem_verts_of_mem h (mem_insert_self w A)),
    notMem_verts_cone hbw hbE', hbS, hbE', fun x _ => insert_ne_singleton hne hwA⟩,
    fun h => hwE' (h (mem_insert_self w A)), dec3.symm⟩))

/-- Lickorish's Lemma 3.5: if `K` is starrable relative to `E`, then the cone `v ⋆ K` is starrable
relative to `K ∪ v ⋆ E`, the boundary of the cone when `E` is the boundary of `K`. -/
theorem Starrable.toCone [Infinite V] {E K : SComplex V} {v : V} (h : Starrable E K)
    (hvK : v ∉ K.verts) (hvE : v ∉ E.verts) :
    Starrable (K.union (cone v E)) (cone v K) := by
  obtain ⟨u, hu⟩ := Infinite.exists_notMem_finset (K.verts ∪ E.verts ∪ {v})
  simp only [Finset.mem_union, mem_singleton, not_or] at hu
  obtain ⟨⟨huK, huE⟩, huv⟩ := hu
  have hch := h {v} (fun x hx hxK => by
    obtain rfl := mem_singleton.1 hx; exact absurd hxK hvK) u
    (fun h' => huv (mem_singleton.1 h')) huK huE
  clear h huK
  revert hvK
  induction hch using Relation.ReflTransGen.head_induction_on with
  | refl => intro _; exact starrable_cone_cone huv huE hvE
  | @head K K1 hstep _ ih =>
    intro hvK
    have hvK1 : v ∉ K1.verts := fun h' =>
      hvK ((hstep.mem_verts_iff (mem_singleton_self v)).2 h')
    have ih := ih hvK1
    rcases hstep with ⟨A, a, hsub, rfl⟩ | ⟨B, b, hsub, hBE, rfl⟩
    · obtain ⟨hA, hne, hAE, ha, haS, haE, -⟩ := hsub
      exact starrable_cone_fwd hA hne hAE ha (fun e => haS (e ▸ mem_singleton_self v)) haE hvK
        hvE ih
    · obtain ⟨hB, hne, -, hb, hbS, hbE, -⟩ := hsub
      have hbv : b ≠ v := fun e => hbS (e ▸ mem_singleton_self v)
      have hvB : v ∉ B := fun h' => hvK1 (mem_verts_of_mem hB h')
      have hBc : B ∉ cone v E := fun h' =>
        hBE (subset_verts ((mem_cone_of_notMem hvE hvB).1 h'))
      have := ih.starAt (A := B) (a := b) (mem_cone.2 ⟨B, hB, .inl rfl⟩) hne
        (notMem_verts_cone hbv hb)
        (by rw [verts_union, Finset.mem_union, not_or]; exact ⟨hb, notMem_verts_cone hbv hbE⟩)
      rwa [starAt_union, starAt_of_notMem hBc, cone_starAt hvK1 hvB] at this

end SComplex
end Lightlike.PL
