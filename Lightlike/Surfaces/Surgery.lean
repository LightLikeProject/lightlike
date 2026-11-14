import Lightlike.Surfaces.Arc
import Lightlike.Surfaces.Sum

/-!
# Checked surgery on closed surfaces

Several steps of the classification cut a small region out of a closed surface and glue in a
different one with the same boundary: removing a tube, capping a band, forming a connected sum. The
region `X` and its replacement `Y` are concrete complexes on natural-number labels, placed in the
surface `K` by an embedding `f` of the labels. This file proves once and for all that the result
`surg K f X Y = (K \ f(X)) ∪ f(Y)` is again a closed connected surface, provided a finite,
decidable list of conditions on `X` and `Y` holds (`SurgOK`, checked by `decide +kernel`) and the
placement satisfies a few conditions in `K` (`SurgCtx`).

The template conditions are local:

* every pair of labels of `Y` lies in as many triangles of `X` as of `Y`, or in two of `X` and none
  of `Y` (an edge that disappears), or in none of `X` and two of `Y` (a new edge, which must be
  safe: a new label, or a pair known to span no triangle of `K`);
* at a label of `X`, the link in `Y` together with the old link vertices that keep their edge is
  connected (reachability by a finite closure, `reachAll`); at a new label, the link in `Y` is
  connected.

Links in the result are then connected by a projection argument (`connEdges_of_proj`), and the
Euler characteristic changes by `χ(Y) − χ(X)` (`euler2_surg`).
-/

open Finset

namespace Lightlike.Surfaces

open Lightlike.PR

/-! ## Reachability by a finite closure -/

/-- One closure step: add the edges of `E` that meet `R`. -/
def reachStep (E : Finset (Finset ℕ)) (R : Finset ℕ) : Finset ℕ :=
  R ∪ (E.filter (fun e => ∃ x ∈ e, x ∈ R)).biUnion id

/-- The labels reached from `a` in `n` closure steps along the edges of `E`. -/
def reach (E : Finset (Finset ℕ)) (a : ℕ) : ℕ → Finset ℕ
  | 0 => {a}
  | n + 1 => reachStep E (reach E a n)

/-- The labels reached from `a` along the edges of `E` (as many steps as `E` has vertices). -/
def reachAll (E : Finset (Finset ℕ)) (a : ℕ) : Finset ℕ := reach E a #(verts2 E)

/-- **Soundness of reachability:** every label reached from `a` is joined to `a` by a path of
edges of `E`. -/
lemma reach_sound {E : Finset (Finset ℕ)} (hE : ∀ e ∈ E, #e = 2) {a : ℕ} :
    ∀ n, ∀ x ∈ reach E a n, Relation.ReflTransGen (fun p q => ({p, q} : Finset ℕ) ∈ E) a x
  | 0, x, hx => by
    rw [reach, mem_singleton] at hx
    exact hx ▸ .refl
  | n + 1, x, hx => by
    rw [reach, reachStep, mem_union, mem_biUnion] at hx
    rcases hx with hx | ⟨e, he, hxe⟩
    · exact reach_sound hE n x hx
    · rw [mem_filter] at he
      obtain ⟨he, y, hye, hy⟩ := he
      simp only [id] at hxe
      by_cases hxy : x = y
      · exact hxy ▸ reach_sound hE n y hy
      · have hsub : ({y, x} : Finset ℕ) ⊆ e := by
          intro z hz
          rw [mem_insert, mem_singleton] at hz
          rcases hz with rfl | rfl <;> assumption
        have heq : ({y, x} : Finset ℕ) = e :=
          eq_of_subset_of_card_le hsub (by rw [hE e he, card_pair (Ne.symm hxy)])
        exact (reach_sound hE n y hy).tail (heq ▸ he)

/-- Soundness of `reachAll`. -/
lemma reachAll_sound {E : Finset (Finset ℕ)} (hE : ∀ e ∈ E, #e = 2) {a x : ℕ}
    (hx : x ∈ reachAll E a) :
    Relation.ReflTransGen (fun p q => ({p, q} : Finset ℕ) ∈ E) a x :=
  reach_sound hE _ x hx

/-! ## Connectivity by projection -/

variable {V : Type*} [DecidableEq V]

/-- Adjacency through a pair in an edge set is symmetric. -/
lemma adj_symm {N : Finset (Finset V)} :
    ∀ a b, ({a, b} : Finset V) ∈ N → ({b, a} : Finset V) ∈ N := fun a b h => by
  rwa [pair_comm]

/-- **Connectivity by projection.** Let `S` be a connected edge set and `N` another one. Call the
vertices satisfying `k` *kept*. If every edge of `S` between kept vertices is joined in `N`, every
edge of `S` from a kept vertex to a removed one has its kept end joined in `N` to an anchor `a` of
`S`, and every vertex of `N` is a kept vertex of `S` or joined in `N` to `a`, then `N` is
connected. (Project each vertex of `S` to itself if kept, to `a` otherwise.) -/
lemma connEdges_of_proj {S N : Finset (Finset V)} (k : V → Prop) {a : V}
    (hS : IsConnEdges S) (ha : a ∈ verts2 S)
    (h1 : ∀ x y, ({x, y} : Finset V) ∈ S → k x → k y →
      Relation.ReflTransGen (fun p q => ({p, q} : Finset V) ∈ N) x y)
    (h2 : ∀ x y, ({x, y} : Finset V) ∈ S → k x → ¬ k y →
      Relation.ReflTransGen (fun p q => ({p, q} : Finset V) ∈ N) x a)
    (h3 : ∀ w ∈ verts2 N, (w ∈ verts2 S ∧ k w) ∨
      Relation.ReflTransGen (fun p q => ({p, q} : Finset V) ∈ N) w a) :
    IsConnEdges N := by
  classical
  set R := fun p q => ({p, q} : Finset V) ∈ N
  let g : V → V := fun x => if k x then x else a
  have hga : g a = a := by simp only [g]; split_ifs <;> rfl
  have step : ∀ x y, ({x, y} : Finset V) ∈ S → Relation.ReflTransGen R (g x) (g y) := by
    intro x y hxy
    by_cases hx : k x <;> by_cases hy : k y <;> simp only [g, hx, hy, ↓reduceIte]
    · exact h1 x y hxy hx hy
    · exact h2 x y hxy hx hy
    · exact rtg_symm adj_symm (h2 y x (adj_symm _ _ hxy) hy hx)
    · exact .refl
  have proj : ∀ w ∈ verts2 S, k w → Relation.ReflTransGen R w a := by
    intro w hw hk
    have path : ∀ x y, Relation.ReflTransGen (fun p q => ({p, q} : Finset V) ∈ S) x y →
        Relation.ReflTransGen R (g x) (g y) := by
      intro x y hxy
      induction hxy with
      | refl => exact .refl
      | tail _ hbc ih => exact ih.trans (step _ _ hbc)
    have := path w a (hS w hw a ha)
    rwa [hga, show g w = w by simp only [g, hk, ↓reduceIte]] at this
  have toA : ∀ w ∈ verts2 N, Relation.ReflTransGen R w a := by
    intro w hw
    rcases h3 w hw with ⟨hwS, hk⟩ | h
    · exact proj w hwS hk
    · exact h
  intro u hu w hw
  exact (toA u hu).trans (rtg_symm adj_symm (toA w hw))

/-! ## Counting triangles at an edge -/

/-- The number of triangles of `X` containing `e`. -/
def cnt {W : Type*} [DecidableEq W] (X : Finset (Finset W)) (e : Finset W) : ℕ :=
  #(X.filter (e ⊆ ·))

/-- A pair is an edge exactly when some triangle contains it. -/
lemma mem_edges2_iff_cnt {M : Finset (Finset V)} {e : Finset V} (he : #e = 2) :
    e ∈ edges2 M ↔ 0 < cnt M e := by
  rw [mem_edges2, cnt, card_pos]
  constructor
  · rintro ⟨τ, hτ, hs, -⟩
    exact ⟨τ, mem_filter.mpr ⟨hτ, hs⟩⟩
  · rintro ⟨τ, hτ⟩
    rw [mem_filter] at hτ
    exact ⟨τ, hτ.1, hτ.2, he⟩

/-- Edges have two vertices. -/
lemma card_of_mem_edges2 {M : Finset (Finset V)} {e : Finset V} (he : e ∈ edges2 M) : #e = 2 := by
  obtain ⟨_, _, _, h⟩ := mem_edges2.mp he
  exact h

section lift

variable {f : ℕ ↪ V}

/-- Relabelling preserves the number of triangles at an edge. -/
lemma cnt_liftK (Z : Finset (Finset ℕ)) (e : Finset ℕ) : cnt (liftK f Z) (e.map f) = cnt Z e := by
  rw [cnt, cnt, liftK, filter_image]
  simp only [map_subset_map]
  exact card_image_of_injective _ (map_injective f)

/-- Every vertex of a relabelled complex is the image of a label. -/
lemma exists_label {Z : Finset (Finset ℕ)} {s : Finset V} (hs : s ∈ liftK f Z) {x : V}
    (hx : x ∈ s) : ∃ m ∈ verts2 Z, f m = x := by
  obtain ⟨t, ht, rfl⟩ := mem_liftK.mp hs
  obtain ⟨m, hm, rfl⟩ := mem_map.mp hx
  exact ⟨m, mem_verts2.mpr ⟨t, ht, hm⟩, rfl⟩

/-- A vertex of a relabelled triangle at `f n`, other than `f n`, is the image of a label in
the link of `n`. -/
lemma exists_link_label {Z : Finset (Finset ℕ)} {s : Finset V} (hs : s ∈ liftK f Z) {n : ℕ}
    (hn : f n ∈ s) {x : V} (hx : x ∈ s) (hxn : x ≠ f n) :
    ∃ m, f m = x ∧ m ≠ n ∧ m ∈ verts2 (lk2 Z n) := by
  obtain ⟨t, ht, rfl⟩ := mem_liftK.mp hs
  obtain ⟨m, hm, rfl⟩ := mem_map.mp hx
  rw [mem_map' f] at hn
  have hmn : m ≠ n := fun h => hxn (h ▸ rfl)
  refine ⟨m, rfl, hmn, mem_verts2.mpr ⟨t.erase n, mem_lk2.mpr ⟨notMem_erase n t, ?_⟩,
    mem_erase.mpr ⟨hmn, hm⟩⟩⟩
  rwa [insert_erase hn]

/-- Relabelling carries link edges to link edges. -/
lemma lift_lk2_edge {Z : Finset (Finset ℕ)} {M : Finset (Finset V)} (hZ : liftK f Z ⊆ M) {n p q : ℕ}
    (h : ({p, q} : Finset ℕ) ∈ lk2 Z n) : ({f p, f q} : Finset V) ∈ lk2 M (f n) := by
  rw [mem_lk2] at h ⊢
  obtain ⟨hn, hZn⟩ := h
  refine ⟨?_, hZ ?_⟩
  · rw [← map_pair (f := f)]
    exact fun h' => hn ((mem_map' f).mp h')
  · have : (insert n {p, q} : Finset ℕ).map f = insert (f n) {f p, f q} := by simp
    rw [← this]
    exact map_mem_liftK.mpr hZn

/-- Reachability in the link of `n` in `Z` lifts to the link of `f n` in any complex containing
the image of `Z`. -/
lemma lift_reach {Z : Finset (Finset ℕ)} {M : Finset (Finset V)} (hZ : liftK f Z ⊆ M)
    (hZ3 : ∀ t ∈ Z, #t = 3) {n a x : ℕ} (hx : x ∈ reachAll (lk2 Z n) a) :
    Relation.ReflTransGen (fun p q => ({p, q} : Finset V) ∈ lk2 M (f n)) (f a) (f x) := by
  have hE : ∀ e ∈ lk2 Z n, #e = 2 := by
    intro e he
    rw [mem_lk2] at he
    have h3 := hZ3 _ he.2
    rw [card_insert_of_notMem he.1] at h3
    omega
  exact (reachAll_sound hE hx).lift f (fun p q h => lift_lk2_edge hZ h)

/-- Relabelling carries the link of `n` into the link of `f n`. -/
lemma lift_lk2 {Z : Finset (Finset ℕ)} {M : Finset (Finset V)} (hZ : liftK f Z ⊆ M) {n : ℕ}
    {e : Finset ℕ} (h : e ∈ lk2 Z n) : e.map f ∈ lk2 M (f n) := by
  rw [mem_lk2] at h ⊢
  refine ⟨fun h' => h.1 ((mem_map' f).mp h'), hZ ?_⟩
  rw [← map_insert]
  exact map_mem_liftK.mpr h.2

end lift

/-! ## The template conditions and the placement -/

/-- The **template conditions** for replacing the region `X` by `Y`. Labels of `X` are boundary
labels and must all occur in `Y`; labels of `Y` only are new. `S` lists pairs of boundary labels
that span no triangle of the surrounding surface.

* `X` and `Y` are nonempty and the triangles of `Y` have three labels;
* each pair of labels of `Y` lies in as many triangles of `X` as of `Y`, or in two of `X` and none
  of `Y`, or in none of `X` and two of `Y` and is safe;
* at each label `n` of `Y` there is an anchor `a` that every vertex of the link of `n` in `Y`
  reaches inside that link; at a boundary label the anchor is in the link of `n` in `X`, and so is
  reached by every vertex `m` of that link with `nm` in fewer or more than two triangles of `X`. -/
def SurgOK (X Y : Finset (Finset ℕ)) (S : List (ℕ × ℕ)) : Prop :=
  X.Nonempty ∧ Y.Nonempty ∧ (∀ t ∈ Y, #t = 3) ∧ verts2 X ⊆ verts2 Y ∧
  (∀ p ∈ verts2 Y, ∀ q ∈ verts2 Y, p ≠ q →
    cnt X {p, q} = cnt Y {p, q} ∨ (cnt X {p, q} = 2 ∧ cnt Y {p, q} = 0) ∨
      (cnt X {p, q} = 0 ∧ cnt Y {p, q} = 2 ∧ Safe (verts2 X) S p q)) ∧
  (∀ n ∈ verts2 Y, ∃ a ∈ verts2 Y,
    (∀ m ∈ verts2 (lk2 Y n), m ∈ reachAll (lk2 Y n) a) ∧
    (n ∈ verts2 X → a ∈ verts2 (lk2 X n) ∧
      ∀ m ∈ verts2 (lk2 X n), cnt X {n, m} ≠ 2 → m ∈ reachAll (lk2 Y n) a))

instance (X Y : Finset (Finset ℕ)) (S : List (ℕ × ℕ)) : Decidable (SurgOK X Y S) := by
  unfold SurgOK; infer_instance

/-- The **placement conditions** for the surgery in `K` through the labelling `f`: the region lies
in `K`, new labels go to vertices outside `K`, the pairs of `S` span no triangle of `K`, and no
triangle of the replacement is already in `K`. -/
structure SurgCtx (K : Finset (Finset V)) (f : ℕ ↪ V) (X Y : Finset (Finset ℕ))
    (S : List (ℕ × ℕ)) : Prop where
  sub : liftK f X ⊆ K
  fresh : ∀ n ∈ verts2 Y, n ∉ verts2 X → f n ∉ verts2 K
  safe : ∀ p ∈ S, ∀ t ∈ K, ¬ ({f p.1, f p.2} : Finset V) ⊆ t
  new : ∀ t ∈ Y, t.map f ∉ K

/-- The result of the surgery: remove the image of `X` from `K` and add the image of `Y`. -/
def surg (K : Finset (Finset V)) (f : ℕ ↪ V) (X Y : Finset (Finset ℕ)) : Finset (Finset V) :=
  K \ liftK f X ∪ liftK f Y

section surgery

variable {K : Finset (Finset V)} {f : ℕ ↪ V} {X Y : Finset (Finset ℕ)} {S : List (ℕ × ℕ)}

/-- Membership in the result of a surgery. -/
lemma mem_surg {s : Finset V} :
    s ∈ surg K f X Y ↔ (s ∈ K ∧ s ∉ liftK f X) ∨ s ∈ liftK f Y := by
  rw [surg, mem_union, mem_sdiff]

/-- The replacement is disjoint from the surface. -/
lemma SurgCtx.disj_Y (hC : SurgCtx K f X Y S) : Disjoint K (liftK f Y) := by
  rw [disjoint_left]
  intro s hs hsY
  obtain ⟨t, ht, rfl⟩ := mem_liftK.mp hsY
  exact hC.new t ht hs

/-- The result is disjoint from the removed region. -/
lemma SurgCtx.disj_X (hC : SurgCtx K f X Y S) : Disjoint (surg K f X Y) (liftK f X) := by
  rw [disjoint_left]
  intro s hs hsX
  rcases mem_surg.mp hs with h | h
  · exact h.2 hsX
  · exact disjoint_left.mp hC.disj_Y (hC.sub hsX) h

/-- Result plus region equals surface plus replacement. -/
lemma SurgCtx.union_eq (hC : SurgCtx K f X Y S) :
    surg K f X Y ∪ liftK f X = K ∪ liftK f Y := by
  ext s
  rw [mem_union, mem_surg, mem_union]
  constructor
  · rintro ((⟨h, -⟩ | h) | h)
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inl (hC.sub h)
  · rintro (h | h)
    · by_cases hX : s ∈ liftK f X
      · exact Or.inr hX
      · exact Or.inl (Or.inl ⟨h, hX⟩)
    · exact Or.inl (Or.inr h)

/-- Triangle counts add over a disjoint union. -/
lemma cnt_union {A B : Finset (Finset V)} (h : Disjoint A B) (e : Finset V) :
    cnt (A ∪ B) e = cnt A e + cnt B e := by
  rw [cnt, cnt, cnt, filter_union, card_union_of_disjoint (disjoint_filter_filter h)]

/-- Triangle counts grow with the complex. -/
lemma cnt_mono {A B : Finset (Finset V)} (h : A ⊆ B) (e : Finset V) : cnt A e ≤ cnt B e :=
  card_le_card (filter_subset_filter _ h)

/-- Triangle counts at an edge: result plus region equals surface plus replacement. -/
lemma SurgCtx.cnt_eq (hC : SurgCtx K f X Y S) (e : Finset V) :
    cnt (surg K f X Y) e + cnt (liftK f X) e = cnt K e + cnt (liftK f Y) e := by
  rw [← cnt_union hC.disj_X, ← cnt_union hC.disj_Y, hC.union_eq]

/-- Triangle numbers: result plus region equals surface plus replacement. -/
lemma SurgCtx.card_eq (hC : SurgCtx K f X Y S) :
    #(surg K f X Y) + #(liftK f X) = #K + #(liftK f Y) := by
  rw [← card_union_of_disjoint hC.disj_X, ← card_union_of_disjoint hC.disj_Y, hC.union_eq]

/-- An edge with an end outside the image of `Y` lies in no relabelled triangle of `Z`. -/
lemma cnt_zero_of_notMem {Z : Finset (Finset ℕ)} (hZ : verts2 Z ⊆ verts2 Y) {x y : V}
    (h : (¬ ∃ p ∈ verts2 Y, f p = x) ∨ ¬ ∃ q ∈ verts2 Y, f q = y) :
    cnt (liftK f Z) {x, y} = 0 := by
  rw [cnt, card_eq_zero, filter_eq_empty_iff]
  intro s hs hsub
  rcases h with h | h
  · obtain ⟨m, hm, hmx⟩ := exists_label hs (hsub (mem_insert_self x {y}))
    exact h ⟨m, hZ hm, hmx⟩
  · obtain ⟨m, hm, hmx⟩ := exists_label hs (hsub (mem_insert_of_mem (mem_singleton_self y)))
    exact h ⟨m, hZ hm, hmx⟩

/-- The four ways an edge can meet the region and its replacement. -/
lemma SurgCtx.cnt_class (hC : SurgCtx K f X Y S) (hok : SurgOK X Y S) {e : Finset V}
    (he : #e = 2) :
    (cnt (liftK f X) e = 0 ∧ cnt (liftK f Y) e = 0) ∨ cnt (liftK f X) e = cnt (liftK f Y) e ∨
      (cnt (liftK f X) e = 2 ∧ cnt (liftK f Y) e = 0) ∨
      (cnt (liftK f X) e = 0 ∧ cnt (liftK f Y) e = 2 ∧ cnt K e = 0) := by
  obtain ⟨-, -, -, hXY, hpairs, -⟩ := hok
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp he
  by_cases hx : ∃ p ∈ verts2 Y, f p = x
  · by_cases hy : ∃ q ∈ verts2 Y, f q = y
    · obtain ⟨p, hp, rfl⟩ := hx
      obtain ⟨q, hq, rfl⟩ := hy
      have hpq : p ≠ q := fun h => hxy (by rw [h])
      rw [← map_pair (f := f) p q, cnt_liftK, cnt_liftK]
      rcases hpairs p hp q hq hpq with h | h | ⟨h0, h2, hs⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · refine Or.inr (Or.inr (Or.inr ⟨h0, h2, ?_⟩))
        rw [cnt, card_eq_zero, filter_eq_empty_iff]
        intro t ht hsub
        rw [map_pair] at hsub
        rcases hs with h | h | h | h
        · exact hC.fresh p hp h (mem_verts2.mpr ⟨t, ht, hsub (mem_insert_self _ _)⟩)
        · exact hC.fresh q hq h
            (mem_verts2.mpr ⟨t, ht, hsub (mem_insert_of_mem (mem_singleton_self _))⟩)
        · exact hC.safe _ h t ht hsub
        · exact hC.safe _ h t ht (by rw [pair_comm]; exact hsub)
    · exact Or.inl ⟨cnt_zero_of_notMem hXY (Or.inr hy), cnt_zero_of_notMem subset_rfl (Or.inr hy)⟩
  · exact Or.inl ⟨cnt_zero_of_notMem hXY (Or.inl hx), cnt_zero_of_notMem subset_rfl (Or.inl hx)⟩

/-- The result of a checked surgery on a closed complex is closed. -/
theorem SurgCtx.isClosed2 (hC : SurgCtx K f X Y S) (hok : SurgOK X Y S) (hK : IsClosed2 K) :
    IsClosed2 (surg K f X Y) := by
  intro e he
  have h2 := card_of_mem_edges2 he
  have h0 := (mem_edges2_iff_cnt h2).mp he
  have hc := hC.cnt_eq e
  have hle : cnt (liftK f X) e ≤ cnt K e := cnt_mono hC.sub e
  have hle' : cnt (liftK f Y) e ≤ cnt (surg K f X Y) e := cnt_mono subset_union_right e
  have hKe : 0 < cnt K e → cnt K e = 2 := fun h => hK e ((mem_edges2_iff_cnt h2).mpr h)
  have := hC.cnt_class hok h2
  show cnt _ e = 2
  omega

/-- The result of a surgery has triangles only. -/
lemma isTri2_surg (hK : IsTri2 K) (hY3 : ∀ t ∈ Y, #t = 3) : IsTri2 (surg K f X Y) := by
  intro τ hτ
  rcases mem_surg.mp hτ with h | h
  · exact hK τ h.1
  · obtain ⟨t, ht, rfl⟩ := mem_liftK.mp h
    rw [card_map]
    exact hY3 t ht

/-- Links in the result of a checked surgery on a surface are connected. -/
theorem SurgCtx.isLinkConn (hC : SurgCtx K f X Y S) (hok : SurgOK X Y S) (hK : IsSurface K) :
    IsLinkConn (surg K f X Y) := by
  obtain ⟨-, -, hY3, hXY, -, hlinks⟩ := hok
  have hYL : liftK f Y ⊆ surg K f X Y := subset_union_right
  have hmemL : ∀ s ∈ K, s ∉ liftK f X → s ∈ surg K f X Y := fun s hs hsX =>
    mem_surg.mpr (Or.inl ⟨hs, hsX⟩)
  intro v hv
  by_cases hvY : ∃ n ∈ verts2 Y, f n = v
  · obtain ⟨n, hnY, rfl⟩ := hvY
    obtain ⟨a, -, hreachY, hX⟩ := hlinks n hnY
    have good : ∀ m ∈ reachAll (lk2 Y n) a, Relation.ReflTransGen
        (fun p q => ({p, q} : Finset V) ∈ lk2 (surg K f X Y) (f n)) (f m) (f a) :=
      fun m hm => rtg_symm adj_symm (lift_reach hYL hY3 hm)
    by_cases hnX : n ∈ verts2 X
    · obtain ⟨ha, hreachX⟩ := hX hnX
      have hnK : f n ∈ verts2 K := by
        obtain ⟨t, ht, hnt⟩ := mem_verts2.mp hnX
        exact mem_verts2.mpr ⟨_, hC.sub (map_mem_liftK.mpr ht), mem_map_of_mem f hnt⟩
      have key : ∀ m, m ≠ n → cnt X {n, m} = 2 → ∀ s ∈ K, ({f n, f m} : Finset V) ⊆ s →
          s ∈ liftK f X := by
        intro m hmn hc s hs hsub
        have he2 : #({f n, f m} : Finset V) = 2 := card_pair (fun h => hmn (f.injective h).symm)
        have hX2 : cnt (liftK f X) {f n, f m} = 2 := by rw [← map_pair, cnt_liftK]; exact hc
        have hK2 : cnt K {f n, f m} = 2 := hK.closed _ ((mem_edges2_iff_cnt he2).mpr
          (by have := cnt_mono hC.sub ({f n, f m} : Finset V); omega))
        have heq : (liftK f X).filter (({f n, f m} : Finset V) ⊆ ·) =
            K.filter (({f n, f m} : Finset V) ⊆ ·) :=
          eq_of_subset_of_card_le (filter_subset_filter _ hC.sub) (hK2.trans hX2.symm).le
        have : s ∈ K.filter (({f n, f m} : Finset V) ⊆ ·) := mem_filter.mpr ⟨hs, hsub⟩
        rw [← heq] at this
        exact (mem_filter.mp this).1
      refine connEdges_of_proj (fun x => ¬ ∃ m, f m = x ∧ m ≠ n ∧ cnt X {n, m} = 2)
        (a := f a) (hK.link _ hnK) ?_ ?_ ?_ ?_
      · obtain ⟨e, he, hae⟩ := mem_verts2.mp ha
        exact mem_verts2.mpr ⟨_, lift_lk2 hC.sub he, mem_map_of_mem f hae⟩
      · intro x y hxy hx hy
        rw [mem_lk2] at hxy
        by_cases hs : insert (f n) {x, y} ∈ liftK f X
        · obtain ⟨mx, rfl, hmx, hmxX⟩ := exists_link_label (x := x) hs (mem_insert_self _ _)
            (by simp) (fun h => hxy.1 (by simp [h]))
          obtain ⟨my, rfl, hmy, hmyX⟩ := exists_link_label (x := y) hs (mem_insert_self _ _)
            (by simp) (fun h => hxy.1 (by simp [h]))
          exact (good mx (hreachX mx hmxX (fun hc => hx ⟨mx, rfl, hmx, hc⟩))).trans
            (rtg_symm adj_symm (good my (hreachX my hmyX (fun hc => hy ⟨my, rfl, hmy, hc⟩))))
        · exact .single (mem_lk2.mpr ⟨hxy.1, hmemL _ hxy.2 hs⟩)
      · intro x y hxy hx hy
        rw [mem_lk2] at hxy
        obtain ⟨m, rfl, hmn, hc⟩ := not_not.mp hy
        have hs := key m hmn hc _ hxy.2 (by
          intro z hz
          simp only [mem_insert, mem_singleton] at hz ⊢
          tauto)
        obtain ⟨mx, rfl, hmx, hmxX⟩ := exists_link_label (x := x) hs (mem_insert_self _ _)
          (by simp) (fun h => hxy.1 (by simp [h]))
        exact good mx (hreachX mx hmxX (fun hc => hx ⟨mx, rfl, hmx, hc⟩))
      · intro w hw
        obtain ⟨e, he, hwe⟩ := mem_verts2.mp hw
        rw [mem_lk2] at he
        rcases mem_surg.mp he.2 with ⟨hK', hX'⟩ | hY'
        · refine Or.inl ⟨mem_verts2.mpr ⟨e, mem_lk2.mpr ⟨he.1, hK'⟩, hwe⟩, ?_⟩
          rintro ⟨m, rfl, hmn, hc⟩
          exact hX' (key m hmn hc _ hK' (insert_subset_insert _ (singleton_subset_iff.mpr hwe)))
        · obtain ⟨m, rfl, -, hmY⟩ := exists_link_label (x := w) hY' (mem_insert_self _ _)
            (mem_insert_of_mem hwe) (fun h => he.1 (h ▸ hwe))
          exact Or.inr (good m (hreachY m hmY))
    · have hfresh := hC.fresh n hnY hnX
      have toA : ∀ w ∈ verts2 (lk2 (surg K f X Y) (f n)), Relation.ReflTransGen
          (fun p q => ({p, q} : Finset V) ∈ lk2 (surg K f X Y) (f n)) w (f a) := by
        intro w hw
        obtain ⟨e, he, hwe⟩ := mem_verts2.mp hw
        rw [mem_lk2] at he
        rcases mem_surg.mp he.2 with ⟨hK', -⟩ | hY'
        · exact absurd (mem_verts2.mpr ⟨_, hK', mem_insert_self _ _⟩) hfresh
        · obtain ⟨m, rfl, -, hmY⟩ := exists_link_label (x := w) hY' (mem_insert_self _ _)
            (mem_insert_of_mem hwe) (fun h => he.1 (h ▸ hwe))
          exact good m (hreachY m hmY)
      intro u hu w hw
      exact (toA u hu).trans (rtg_symm adj_symm (toA w hw))
  · have hvK : v ∈ verts2 K := by
      obtain ⟨s, hs, hvs⟩ := mem_verts2.mp hv
      rcases mem_surg.mp hs with ⟨hK', -⟩ | hY'
      · exact mem_verts2.mpr ⟨s, hK', hvs⟩
      · exact absurd (exists_label hY' hvs) hvY
    have heq : lk2 (surg K f X Y) v = lk2 K v := by
      ext e
      rw [mem_lk2, mem_lk2]
      refine and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
      · rcases mem_surg.mp h with ⟨hK', -⟩ | hY'
        · exact hK'
        · exact absurd (exists_label hY' (mem_insert_self _ _)) hvY
      · refine hmemL _ h fun hX' => hvY ?_
        obtain ⟨m, hm, hmv⟩ := exists_label hX' (mem_insert_self v e)
        exact ⟨m, hXY hm, hmv⟩
    rw [heq]
    exact hK.link v hvK

/-- Paths along the edges of an edge set can be reversed. -/
lemma rtg_pair_symm {M : Finset (Finset V)} {a b : V}
    (h : Relation.ReflTransGen (fun x y => ({x, y} : Finset V) ∈ M) a b) :
    Relation.ReflTransGen (fun x y => ({x, y} : Finset V) ∈ M) b a :=
  rtg_symm adj_symm h

/-- The result of a checked surgery on a surface is connected, provided the labels of `Y` are
joined to each other in it. -/
theorem SurgCtx.isConnected2 (hC : SurgCtx K f X Y S) (hok : SurgOK X Y S) (hK : IsSurface K)
    (hconn : ∀ m₁ ∈ verts2 Y, ∀ m₂ ∈ verts2 Y,
      Relation.ReflTransGen (fun x y => ({x, y} : Finset V) ∈ edges2 (surg K f X Y)) (f m₁) (f m₂)) :
    IsConnected2 (surg K f X Y) := by
  obtain ⟨hXne, -, -, hXY, -, -⟩ := hok
  obtain ⟨t₀, ht₀⟩ := hXne
  have ht₀K := hC.sub (map_mem_liftK.mpr ht₀)
  obtain ⟨y₀, hy₀⟩ : t₀.Nonempty := by
    have := hK.card _ ht₀K
    rw [card_map] at this
    exact card_pos.mp (by omega)
  have hy₀Y : y₀ ∈ verts2 Y := hXY (mem_verts2.mpr ⟨t₀, ht₀, hy₀⟩)
  have hy₀K : f y₀ ∈ verts2 K := mem_verts2.mpr ⟨_, ht₀K, mem_map_of_mem f hy₀⟩
  have toBase : ∀ u ∈ verts2 (surg K f X Y), Relation.ReflTransGen
      (fun x y => ({x, y} : Finset V) ∈ edges2 (surg K f X Y)) u (f y₀) := by
    intro u hu
    by_cases huY : ∃ m ∈ verts2 Y, f m = u
    · obtain ⟨m, hm, rfl⟩ := huY
      exact hconn m hm y₀ hy₀Y
    · have huK : u ∈ verts2 K := by
        obtain ⟨s, hs, hus⟩ := mem_verts2.mp hu
        rcases mem_surg.mp hs with ⟨hK', -⟩ | hY'
        · exact mem_verts2.mpr ⟨s, hK', hus⟩
        · exact absurd (exists_label hY' hus) huY
      have walk : ∀ w, Relation.ReflTransGen (fun x y => ({x, y} : Finset V) ∈ edges2 K) u w →
          Relation.ReflTransGen (fun x y => ({x, y} : Finset V) ∈ edges2 (surg K f X Y)) w u ∨
          Relation.ReflTransGen (fun x y => ({x, y} : Finset V) ∈ edges2 (surg K f X Y))
            u (f y₀) := by
        intro w hw
        induction hw with
        | refl => exact Or.inl .refl
        | @tail b c _ hbc ih =>
          rcases ih with ih | ih
          · by_cases hL : ({b, c} : Finset V) ∈ edges2 (surg K f X Y)
            · exact Or.inl (.head (adj_symm _ _ hL) ih)
            · right
              obtain ⟨τ, hτ, hsub, hcard⟩ := mem_edges2.mp hbc
              have hτX : τ ∈ liftK f X := by
                by_contra hτX
                exact hL (mem_edges2.mpr ⟨τ, mem_surg.mpr (Or.inl ⟨hτ, hτX⟩), hsub, hcard⟩)
              obtain ⟨m, hm, rfl⟩ := exists_label hτX (hsub (mem_insert_self _ _))
              exact (rtg_pair_symm ih).trans (hconn m (hXY hm) y₀ hy₀Y)
          · exact Or.inr ih
      rcases walk _ (hK.connected u huK _ hy₀K) with h | h
      · exact rtg_pair_symm h
      · exact h
  intro u hu w hw
  exact (toBase u hu).trans (rtg_pair_symm (toBase w hw))

/-- **Checked surgery.** Replacing a region `X` of a surface `K` by `Y`, under the template
conditions `SurgOK` and the placement conditions `SurgCtx`, gives a surface, provided the labels
of `Y` are joined to each other in the result. -/
theorem IsSurface.surgery (hK : IsSurface K) (hC : SurgCtx K f X Y S) (hok : SurgOK X Y S)
    (hconn : ∀ m₁ ∈ verts2 Y, ∀ m₂ ∈ verts2 Y,
      Relation.ReflTransGen (fun x y => ({x, y} : Finset V) ∈ edges2 (surg K f X Y)) (f m₁) (f m₂)) :
    IsSurface (surg K f X Y) where
  nonempty := by
    obtain ⟨t, ht⟩ := hok.2.1
    exact ⟨_, mem_surg.mpr (Or.inr (map_mem_liftK.mpr ht))⟩
  card := isTri2_surg hK.card hok.2.2.1
  closed := hC.isClosed2 hok hK.closed
  link := hC.isLinkConn hok hK
  connected := hC.isConnected2 hok hK hconn

/-- The connectivity hypothesis of `IsSurface.surgery` holds when `Y` itself is connected (every
label of `Y` is reached from one label along the edges of `Y`). -/
lemma hconn_of_reach {M : Finset (Finset V)} (hYM : liftK f Y ⊆ M) {a : ℕ}
    (h : ∀ m ∈ verts2 Y, m ∈ reachAll (edges2 Y) a) :
    ∀ m₁ ∈ verts2 Y, ∀ m₂ ∈ verts2 Y,
      Relation.ReflTransGen (fun x y => ({x, y} : Finset V) ∈ edges2 M) (f m₁) (f m₂) := by
  have lift : ∀ m ∈ verts2 Y,
      Relation.ReflTransGen (fun x y => ({x, y} : Finset V) ∈ edges2 M) (f a) (f m) := by
    intro m hm
    refine (reachAll_sound (fun e he => card_of_mem_edges2 he) (h m hm)).lift f ?_
    intro p q hpq
    obtain ⟨τ, hτ, hsub, hcard⟩ := mem_edges2.mp hpq
    refine mem_edges2.mpr ⟨τ.map f, hYM (map_mem_liftK.mpr hτ), ?_, ?_⟩
    · rw [← map_pair]
      exact map_subset_map.mpr hsub
    · rw [← map_pair, card_map]
      exact hcard
  intro m₁ h₁ m₂ h₂
  exact (rtg_pair_symm (lift m₁ h₁)).trans (lift m₂ h₂)

/-! ## The Euler characteristic -/

/-- Vertices grow with the complex. -/
lemma verts2_mono {A B : Finset (Finset V)} (h : A ⊆ B) : verts2 A ⊆ verts2 B := by
  intro x hx
  obtain ⟨τ, hτ, hxτ⟩ := mem_verts2.mp hx
  exact mem_verts2.mpr ⟨τ, h hτ, hxτ⟩

/-- Edges of a union. -/
lemma edges2_union (A B : Finset (Finset V)) : edges2 (A ∪ B) = edges2 A ∪ edges2 B := by
  simp only [edges2, union_biUnion]

/-- Relabelling does not change the Euler characteristic. -/
lemma euler2_liftK (Z : Finset (Finset ℕ)) : euler2 (liftK f Z) = euler2 Z := by
  rw [euler2, euler2, verts2_liftK f, card_map, edges2_liftK f,
    card_image_of_injective _ (map_injective f), liftK, card_image_of_injective _ (map_injective f)]

/-- **The Euler characteristic under checked surgery:** `χ(result) = χ(K) − χ(X) + χ(Y)`. -/
theorem SurgCtx.euler2_surg (hC : SurgCtx K f X Y S) (hok : SurgOK X Y S) (hK : IsClosed2 K) :
    euler2 (surg K f X Y) + euler2 X = euler2 K + euler2 Y := by
  have hXY := hok.2.2.2.1
  rw [← euler2_liftK (f := f) X, ← euler2_liftK (f := f) Y]
  have hYL : liftK f Y ⊆ surg K f X Y := subset_union_right
  have hV : #(verts2 (surg K f X Y)) + #(verts2 (liftK f X)) =
      #(verts2 K) + #(verts2 (liftK f Y)) := by
    have hU : verts2 (surg K f X Y) ∪ verts2 (liftK f X) = verts2 K ∪ verts2 (liftK f Y) := by
      rw [← verts2_union, ← verts2_union, hC.union_eq]
    rw [← card_union_add_card_inter, hU, ← card_union_add_card_inter (verts2 K)]
    congr 2
    ext w
    rw [mem_inter, mem_inter]
    constructor
    · rintro ⟨-, hw⟩
      refine ⟨verts2_mono hC.sub hw, ?_⟩
      rw [verts2_liftK f] at hw ⊢
      obtain ⟨m, hm, rfl⟩ := mem_map.mp hw
      exact mem_map_of_mem f (hXY hm)
    · rintro ⟨hwK, hw⟩
      refine ⟨verts2_mono hYL hw, ?_⟩
      rw [verts2_liftK f] at hw ⊢
      obtain ⟨m, hm, rfl⟩ := mem_map.mp hw
      by_cases hmX : m ∈ verts2 X
      · exact mem_map_of_mem f hmX
      · exact absurd hwK (hC.fresh m hm hmX)
  have hE : #(edges2 (surg K f X Y)) + #(edges2 (liftK f X)) =
      #(edges2 K) + #(edges2 (liftK f Y)) := by
    have hU : edges2 (surg K f X Y) ∪ edges2 (liftK f X) = edges2 K ∪ edges2 (liftK f Y) := by
      rw [← edges2_union, ← edges2_union, hC.union_eq]
    rw [← card_union_add_card_inter, hU, ← card_union_add_card_inter (edges2 K)]
    congr 2
    ext e
    rw [mem_inter, mem_inter]
    by_cases h2 : #e = 2
    · rw [mem_edges2_iff_cnt h2, mem_edges2_iff_cnt h2, mem_edges2_iff_cnt h2,
        mem_edges2_iff_cnt h2]
      have hc := hC.cnt_eq e
      have hle : cnt (liftK f X) e ≤ cnt K e := cnt_mono hC.sub e
      have hle' : cnt (liftK f Y) e ≤ cnt (surg K f X Y) e := cnt_mono hYL e
      have hKe : 0 < cnt K e → cnt K e = 2 := fun h => hK e ((mem_edges2_iff_cnt h2).mpr h)
      have := hC.cnt_class hok h2
      omega
    · exact ⟨fun h => absurd (card_of_mem_edges2 h.1) h2,
        fun h => absurd (card_of_mem_edges2 h.1) h2⟩
  have hT := hC.card_eq
  simp only [euler2]
  omega

end surgery

end Lightlike.Surfaces
