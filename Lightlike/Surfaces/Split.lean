import Lightlike.Surfaces.Arc

/-!
# Splitting a vertex along an arc of its link

Let `l = p, x₁, …, q` be an arc of distinct vertices in the link of a vertex `u` of a closed
surface (consecutive entries `a, b` with `{u, a, b}` a triangle). **Splitting `u` along `l`**
with a new vertex `u'` moves the fan of triangles `{u, a, b}` along `l` to `u'` and fills the gap
with the two triangles `{u, u', p}` and `{u, u', q}`.

* `splitV`: the split complex;
* `IsSurface.split_steps`: it is reached from the surface by 2D moves: a subdivision of the
  first triangle of the fan by `u'`, then one flip for each further triangle.
-/

open Finset

namespace Lightlike.Surfaces

open Lightlike.PR

variable {V : Type*} [DecidableEq V]

/-- The triangles `{u, xᵢ, xᵢ₊₁}` of the fan around `u` along a list `x₀, x₁, …`. -/
def fanT (u : V) : List V → Finset (Finset V)
  | x :: y :: l => insert {u, x, y} (fanT u (y :: l))
  | _ => ∅

/-- **Splitting the vertex `u` along the list `l`** (an arc `p, …, q` of its link) with the new
vertex `u'`: the fan of `l` around `u` is replaced by the fan around `u'`, and the triangles
`{u, u', p}` and `{u, u', q}` are added. -/
def splitV (L : Finset (Finset V)) (u u' p q : V) (l : List V) : Finset (Finset V) :=
  insert {u, u', p} (insert {u, u', q} ((L \ fanT u l) ∪ fanT u' l))

/-- A triangle of the fan around `w` along `l` contains `w`, and its other vertices lie on `l`. -/
lemma mem_fanT {w : V} : ∀ {l : List V} {τ : Finset V}, τ ∈ fanT w l →
    w ∈ τ ∧ ∀ c ∈ τ, c = w ∨ c ∈ l
  | x :: y :: l, τ, h => by
    rw [fanT, mem_insert] at h
    rcases h with rfl | h
    · refine ⟨by simp, fun c hc => ?_⟩
      simp only [mem_insert, mem_singleton] at hc
      rcases hc with rfl | rfl | rfl <;> simp
    · obtain ⟨h1, h2⟩ := mem_fanT h
      exact ⟨h1, fun c hc => (h2 c hc).imp_right (List.mem_cons_of_mem _)⟩
  | [], τ, h => by simp [fanT] at h
  | [_], τ, h => by simp [fanT] at h

/-- The fan along a chain of triangles of `L` around `w` is part of `L`. -/
lemma fanT_subset {L : Finset (Finset V)} {w : V} : ∀ {l : List V},
    l.IsChain (fun a b => ({w, a, b} : Finset V) ∈ L) → fanT w l ⊆ L
  | x :: y :: l, h => by
    rw [List.isChain_cons_cons] at h
    rw [fanT]
    exact insert_subset h.1 (fanT_subset h.2)
  | [], _ => by simp [fanT]
  | [_], _ => by simp [fanT]

/-- The vertices of a chain of triangles around `w` (of length at least two) are vertices of `L`. -/
lemma mem_verts2_of_chain {L : Finset (Finset V)} {w : V} :
    ∀ {x y : V} {l : List V}, (x :: y :: l).IsChain (fun a b => ({w, a, b} : Finset V) ∈ L) →
      ∀ a ∈ x :: y :: l, a ∈ verts2 L
  | x, y, [], h, a, ha => by
    rw [List.isChain_cons_cons] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    exact mem_verts2.mpr ⟨_, h.1, by rcases ha with rfl | rfl <;> simp⟩
  | x, y, z :: l, h, a, ha => by
    rw [List.isChain_cons_cons] at h
    rcases List.mem_cons.mp ha with rfl | ha
    · exact mem_verts2.mpr ⟨_, h.1, by simp⟩
    · exact mem_verts2_of_chain h.2 a ha

/-- **Splitting a vertex by moves.** Let `x, y, …, q` be a list of distinct vertices different
from `u`, any two consecutive entries `a, b` forming a triangle `{u, a, b}` of the closed surface
`L`, and `u'` a new vertex. Then the split complex `splitV L u u' x q (x :: y :: l)` is reached
from `L` by 2D moves. By induction on the list from its front: the last triangle is subdivided
by `u'`, and each earlier triangle `{u, x, y}` is brought to `u'` by flipping `uy` into `u'x`. -/
theorem IsSurface.split_steps {L : Finset (Finset V)} (hS : IsSurface L) {u u' : V}
    (hu' : u' ∉ verts2 L) : ∀ (l : List V) (x y q : V), (x :: y :: l).Nodup →
      u ∉ x :: y :: l → (x :: y :: l).IsChain (fun a b => ({u, a, b} : Finset V) ∈ L) →
      (y :: l).getLast? = some q →
      Relation.ReflTransGen Move2 L (splitV L u u' x q (x :: y :: l)) := by
  intro l
  induction l with
  | nil =>
    intro x y q hnd hu hch hq
    simp only [List.getLast?_singleton, Option.some.injEq] at hq
    subst hq
    rw [List.isChain_cons_cons] at hch
    have hτ := hch.1
    obtain ⟨hux, huy, hxy⟩ := tri_ne (hS.card _ hτ)
    have hmv := Move2.sub13 (x := u') hux huy hxy hτ hu'
    have hu'L : ∀ τ ∈ L, u' ∉ τ := fun τ hτ h => hu' (mem_verts2.mpr ⟨τ, hτ, h⟩)
    have heq : insert {u, x, u'} (insert {x, y, u'} (insert {u, y, u'} (L.erase {u, x, y}))) =
        splitV L u u' x y [x, y] := by
      ext τ
      simp only [splitV, fanT, mem_insert, mem_union, mem_sdiff, mem_erase, notMem_empty,
        or_false]
      have e1 : ({u, x, u'} : Finset V) = {u, u', x} := by rw [pair_comm]
      have e2 : ({x, y, u'} : Finset V) = {u', x, y} := by
        ext w; simp only [mem_insert, mem_singleton]; tauto
      have e3 : ({u, y, u'} : Finset V) = {u, u', y} := by rw [pair_comm]
      rw [e1, e2, e3]
      tauto
    rw [← heq]
    exact .single hmv
  | cons z l ih =>
    intro x y q hnd hu hch hq
    rw [List.getLast?_cons_cons] at hq
    have hM0 := ih y z q (List.nodup_cons.mp hnd).2 (fun h => hu (List.mem_cons_of_mem _ h))
      (List.isChain_cons_cons.mp hch).2 hq
    -- the facts about the list
    have hxl : x ∉ y :: z :: l := (List.nodup_cons.mp hnd).1
    have hyl : y ∉ z :: l := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
    have hqmem : q ∈ z :: l := List.mem_of_getLast? hq
    have hqy : q ≠ y := fun h => hyl (h ▸ hqmem)
    have hqx : q ≠ x := fun h => hxl (h ▸ List.mem_cons_of_mem _ hqmem)
    have hqu : q ≠ u := fun h => hu (h ▸ List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hqmem))
    have hux : u ≠ x := fun h => hu (h ▸ List.mem_cons_self)
    have huy : u ≠ y := fun h => hu (h ▸ List.mem_cons_of_mem _ List.mem_cons_self)
    have hxy : x ≠ y := fun h => hxl (h ▸ List.mem_cons_self)
    have hxz : x ≠ z := fun h => hxl (h ▸ List.mem_cons_of_mem _ List.mem_cons_self)
    have huyl : u ∉ y :: z :: l := fun h => hu (List.mem_cons_of_mem _ h)
    have hverts := mem_verts2_of_chain hch
    have hu'L : ∀ τ ∈ L, u' ∉ τ := fun τ hτ h => hu' (mem_verts2.mpr ⟨τ, hτ, h⟩)
    have hτxy : ({u, x, y} : Finset V) ∈ L := (List.isChain_cons_cons.mp hch).1
    have hτyz : ({u, y, z} : Finset V) ∈ L :=
      (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp hch).2).1
    have huu' : u ≠ u' := fun h => hu'L _ hτxy (h ▸ by simp)
    have hxu' : x ≠ u' := fun h => hu'L _ hτxy (h ▸ by simp)
    have hyu' : y ≠ u' := fun h => hu'L _ hτxy (h ▸ by simp)
    have hqu' : q ≠ u' := fun h => hu' (h ▸ hverts q (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ hqmem)))
    set F := fanT u (y :: z :: l) with hF
    set F' := fanT u' (y :: z :: l) with hF'
    have hFu' : ∀ τ ∈ F', u ∉ τ := by
      intro τ hτ huτ
      rcases (mem_fanT hτ).2 u huτ with h | h
      · exact huu' h
      · exact huyl h
    have hFx : ∀ τ ∈ F, x ∉ τ := by
      intro τ hτ hxτ
      rcases (mem_fanT hτ).2 x hxτ with h | h
      · exact hux h.symm
      · exact hxl h
    have hFx' : ∀ τ ∈ F', x ∉ τ := by
      intro τ hτ hxτ
      rcases (mem_fanT hτ).2 x hxτ with h | h
      · exact hxu' h
      · exact hxl h
    have hyzF : ({u, y, z} : Finset V) ∈ F := by rw [hF, fanT]; exact mem_insert_self _ _
    have e1 : ({u, y, u'} : Finset V) = {u, u', y} := by rw [pair_comm]
    have e2 : ({u, y, x} : Finset V) = {u, x, y} := by rw [pair_comm]
    have e3 : ({y, u', x} : Finset V) = {u', x, y} := by
      ext w; simp only [mem_insert, mem_singleton]; tauto
    have h₁ : ({u, y, u'} : Finset V) ∈ splitV L u u' y q (y :: z :: l) := by
      rw [e1, splitV]; exact mem_insert_self _ _
    have h₂ : ({u, y, x} : Finset V) ∈ splitV L u u' y q (y :: z :: l) := by
      rw [e2, splitV]
      refine mem_insert_of_mem (mem_insert_of_mem (mem_union_left _ (mem_sdiff.mpr ⟨hτxy, ?_⟩)))
      exact fun h => hFx _ h (by simp)
    have hstar : ∀ τ ∈ splitV L u u' y q (y :: z :: l), ({u, y} : Finset V) ⊆ τ →
        τ = {u, y, u'} ∨ τ = {u, y, x} := by
      intro τ hτ hsub
      have huτ : u ∈ τ := hsub (by simp)
      have hyτ : y ∈ τ := hsub (by simp)
      rw [splitV, mem_insert, mem_insert, mem_union, mem_sdiff] at hτ
      rcases hτ with rfl | rfl | ⟨hτL, hτF⟩ | hτF'
      · exact Or.inl e1.symm
      · simp only [mem_insert, mem_singleton] at hyτ
        rcases hyτ with h | h | h
        · exact absurd h.symm huy
        · exact absurd h hyu'
        · exact absurd h.symm hqy
      · rcases hS.tris_at_edge (show ({u, y, x} : Finset V) ∈ L by rw [e2]; exact hτxy) hτyz
          hxz τ hτL hsub with h | h
        · exact Or.inr h
        · exact absurd (h ▸ hyzF) hτF
      · exact absurd huτ (hFu' _ hτF')
    have hfresh : ∀ τ ∈ splitV L u u' y q (y :: z :: l), ¬ ({u', x} : Finset V) ⊆ τ := by
      intro τ hτ hsub
      have hu'τ : u' ∈ τ := hsub (by simp)
      have hxτ : x ∈ τ := hsub (by simp)
      rw [splitV, mem_insert, mem_insert, mem_union, mem_sdiff] at hτ
      rcases hτ with rfl | rfl | ⟨hτL, -⟩ | hτF'
      · simp only [mem_insert, mem_singleton] at hxτ
        rcases hxτ with h | h | h
        · exact hux h.symm
        · exact hxu' h
        · exact hxy h
      · simp only [mem_insert, mem_singleton] at hxτ
        rcases hxτ with h | h | h
        · exact hux h.symm
        · exact hxu' h
        · exact hqx h.symm
      · exact hu'L τ hτL hu'τ
      · exact hFx' _ hτF' hxτ
    have hmv := Move2.flip22 huy huu' hux hyu' (Ne.symm hxy) (Ne.symm hxu') h₁ h₂ hstar hfresh
    -- the result of the flip is the split along `x :: y :: z :: l`
    have hQC : ({u, u', q} : Finset V) ≠ {u, x, y} := by
      intro h
      have : u' ∈ ({u, x, y} : Finset V) := h ▸ by simp
      simp only [mem_insert, mem_singleton] at this
      rcases this with h | h | h
      · exact huu' h.symm
      · exact hxu' h.symm
      · exact hyu' h.symm
    have hQD : ({u, u', q} : Finset V) ≠ {u, u', y} := by
      intro h
      have : q ∈ ({u, u', y} : Finset V) := h ▸ by simp
      simp only [mem_insert, mem_singleton] at this
      rcases this with h | h | h
      · exact hqu h
      · exact hqu' h
      · exact hqy h
    have hDL : ({u, u', y} : Finset V) ∉ L := fun h => hu'L _ h (by simp)
    have hCF' : ({u, x, y} : Finset V) ∉ F' := fun h => hFu' _ h (by simp)
    have hDF' : ({u, u', y} : Finset V) ∉ F' := fun h => hFu' _ h (by simp)
    have heq : insert {u, u', x} (insert {y, u', x}
        (((splitV L u u' y q (y :: z :: l)).erase {u, y, u'}).erase {u, y, x})) =
        splitV L u u' x q (x :: y :: z :: l) := by
      rw [e1, e2, e3]
      ext τ
      simp only [splitV, fanT, mem_insert, mem_union, mem_sdiff, mem_erase]
      constructor
      · rintro (h | h | ⟨h1, h2, h | h | ⟨hL, hnF⟩ | h⟩)
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact absurd h h2
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl ⟨hL, fun h => h.elim h1 hnF⟩))
        · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
      · rintro (h | h | ⟨hL, hn⟩ | h | h)
        · exact Or.inl h
        · subst h
          exact Or.inr (Or.inr ⟨hQC, hQD, Or.inr (Or.inl rfl)⟩)
        · refine Or.inr (Or.inr ⟨fun h => hn (Or.inl h), fun h => hDL (h ▸ hL),
            Or.inr (Or.inr (Or.inl ⟨hL, fun h => hn (Or.inr h)⟩))⟩)
        · exact Or.inr (Or.inl h)
        · have hτ : τ ∈ F' := by simp only [hF', fanT, mem_insert]; exact h
          exact Or.inr (Or.inr ⟨fun h' => hCF' (h' ▸ hτ), fun h' => hDF' (h' ▸ hτ),
            Or.inr (Or.inr (Or.inr h))⟩)
    rw [← heq]
    exact hM0.tail hmv

/-! ## Which triangles and edges the split changes -/

section facts

variable {L : Finset (Finset V)} {u u' p q : V} {l : List V}

/-- Putting an entry in front of a list only adds triangles to its fan. -/
lemma fanT_subset_cons (w c : V) : ∀ l : List V, fanT w l ⊆ fanT w (c :: l)
  | [] => by simp [fanT]
  | d :: l => by
    rw [show fanT w (c :: d :: l) = insert {w, c, d} (fanT w (d :: l)) from rfl]
    exact subset_insert _ _

/-- The triangle on two consecutive entries `a, b` of a list belongs to its fan. -/
lemma mem_fanT_append (w a b : V) (l₂ : List V) :
    ∀ l₁ : List V, ({w, a, b} : Finset V) ∈ fanT w (l₁ ++ a :: b :: l₂)
  | [] => by simp [fanT]
  | c :: l₁ => fanT_subset_cons w c _ (mem_fanT_append w a b l₂ l₁)

/-- **Renaming the centre of a fan**: if `w ∉ l`, a triangle `{w, a, b}` of the fan around `w`
becomes the triangle `{w', a, b}` of the fan around `w'`. -/
lemma fanT_rename (w' : V) {w : V} : ∀ {l : List V}, w ∉ l → ∀ τ ∈ fanT w l,
    insert w' (τ.erase w) ∈ fanT w' l
  | x :: y :: l, hw, τ, h => by
    rw [fanT, mem_insert] at h
    rw [fanT]
    rcases h with rfl | h
    · have hx : w ≠ x := fun h => hw (h ▸ List.mem_cons_self)
      have hy : w ≠ y := fun h => hw (h ▸ List.mem_cons_of_mem _ List.mem_cons_self)
      rw [erase_insert (by simp [hx, hy])]
      exact mem_insert_self _ _
    · exact mem_insert_of_mem (fanT_rename w' (fun h => hw (List.mem_cons_of_mem _ h)) τ h)
  | [], _, τ, h => by simp [fanT] at h
  | [_], _, τ, h => by simp [fanT] at h

/-- The only triangle of the fan along a list without repetitions that contains its first entry
is the first triangle. -/
lemma eq_of_mem_fanT_head {w x y : V} {l : List V} (hnd : (x :: y :: l).Nodup) (hwx : w ≠ x)
    {τ : Finset V} (h : τ ∈ fanT w (x :: y :: l)) (hx : x ∈ τ) : τ = {w, x, y} := by
  rw [fanT, mem_insert] at h
  rcases h with h | h
  · exact h
  · rcases (mem_fanT h).2 x hx with h' | h'
    · exact absurd h'.symm hwx
    · exact absurd h' (List.nodup_cons.mp hnd).1

/-- A triangle of the split complex is a triangle of `L` or contains the new vertex. -/
lemma mem_splitV_cases {τ : Finset V} (h : τ ∈ splitV L u u' p q l) : τ ∈ L ∨ u' ∈ τ := by
  simp only [splitV, mem_insert, mem_union, mem_sdiff] at h
  rcases h with rfl | rfl | h | h
  · right; simp
  · right; simp
  · exact Or.inl h.1
  · exact Or.inr (mem_fanT h).1

/-- A triangle of `L` without `u` is a triangle of the split complex. -/
lemma mem_splitV_of_notMem {τ : Finset V} (hτ : τ ∈ L) (hu : u ∉ τ) :
    τ ∈ splitV L u u' p q l := by
  simp only [splitV, mem_insert, mem_union, mem_sdiff]
  exact Or.inr (Or.inr (Or.inl ⟨hτ, fun h => hu (mem_fanT h).1⟩))

/-- A triangle of `L` outside the fan of `l` is a triangle of the split complex. -/
lemma mem_splitV_of_notMem_fanT {τ : Finset V} (hτ : τ ∈ L) (hu : τ ∉ fanT u l) :
    τ ∈ splitV L u u' p q l := by
  simp only [splitV, mem_insert, mem_union, mem_sdiff]
  exact Or.inr (Or.inr (Or.inl ⟨hτ, hu⟩))

/-- A triangle of the fan of `l` around `u'` is a triangle of the split complex. -/
lemma mem_splitV_of_mem_fanT {τ : Finset V} (hτ : τ ∈ fanT u' l) : τ ∈ splitV L u u' p q l := by
  simp only [splitV, mem_insert, mem_union]
  exact Or.inr (Or.inr (Or.inr hτ))

/-- A triangle of the split complex at the new vertex `u'` is one of the two added triangles, or
comes by renaming from a triangle of the fan around `u`. -/
lemma mem_splitV_new (hl : u' ∉ l) (hL : ∀ σ ∈ L, u' ∉ σ) {τ : Finset V}
    (h : τ ∈ splitV L u u' p q l) (hτ : u' ∈ τ) :
    τ = {u, u', p} ∨ τ = {u, u', q} ∨ insert u (τ.erase u') ∈ fanT u l := by
  simp only [splitV, mem_insert, mem_union, mem_sdiff] at h
  rcases h with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact absurd hτ (hL τ h.1)
  · exact Or.inr (Or.inr (fanT_rename u hl τ h))

/-- **Edges away from `u` and `u'` are unchanged by the split.** -/
lemma pair_splitV_iff (hl : u ∉ l) (hl' : u' ∉ l) (hF : fanT u l ⊆ L) {x y : V} (hxy : x ≠ y)
    (hxu : x ≠ u) (hxu' : x ≠ u') (hyu : y ≠ u) (hyu' : y ≠ u') :
    (∃ τ ∈ splitV L u u' p q l, x ∈ τ ∧ y ∈ τ) ↔ ∃ τ ∈ L, x ∈ τ ∧ y ∈ τ := by
  constructor
  · rintro ⟨τ, h, hx, hy⟩
    simp only [splitV, mem_insert, mem_union, mem_sdiff] at h
    rcases h with rfl | rfl | h | h
    · simp only [mem_insert, mem_singleton] at hx hy
      rcases hx with h | h | h <;> rcases hy with h' | h' | h' <;> simp_all
    · simp only [mem_insert, mem_singleton] at hx hy
      rcases hx with h | h | h <;> rcases hy with h' | h' | h' <;> simp_all
    · exact ⟨τ, h.1, hx, hy⟩
    · refine ⟨_, hF (fanT_rename u hl' τ h), ?_, ?_⟩
      · exact mem_insert_of_mem (mem_erase.mpr ⟨hxu', hx⟩)
      · exact mem_insert_of_mem (mem_erase.mpr ⟨hyu', hy⟩)
  · rintro ⟨τ, h, hx, hy⟩
    by_cases hf : τ ∈ fanT u l
    · refine ⟨_, mem_splitV_of_mem_fanT (fanT_rename u' hl τ hf), ?_, ?_⟩
      · exact mem_insert_of_mem (mem_erase.mpr ⟨hxu, hx⟩)
      · exact mem_insert_of_mem (mem_erase.mpr ⟨hyu, hy⟩)
    · exact ⟨τ, mem_splitV_of_notMem_fanT h hf, hx, hy⟩

omit [DecidableEq V] in
/-- An entry of a list other than its first and last entry sits between two entries. -/
lemma exists_interior_split {x p q : V} (hx : x ∈ l) (hp : l.head? = some p)
    (hq : l.getLast? = some q) (hxp : x ≠ p) (hxq : x ≠ q) :
    ∃ l₁ a b l₂, l = l₁ ++ a :: x :: b :: l₂ := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hx
  rcases List.eq_nil_or_concat s with rfl | ⟨s', a, rfl⟩
  · simp at hp; exact absurd hp hxp
  rcases t with _ | ⟨b, t'⟩
  · simp at hq; exact absurd hq hxq
  · exact ⟨s', a, b, t', by simp⟩

/-- At an entry `x` of `l` between two others, every triangle of the closed complex `L` containing
`u` and `x` is in the fan of `l`. -/
lemma mem_fanT_of_interior (hc : IsClosed2 L) (hnd : l.Nodup) (hul : u ∉ l) (hF : fanT u l ⊆ L)
    {l₁ l₂ : List V} {a x b : V} (hl : l = l₁ ++ a :: x :: b :: l₂) {τ : Finset V} (hτ : τ ∈ L)
    (hu : u ∈ τ) (hx : x ∈ τ) : τ ∈ fanT u l := by
  have h1 : ({u, a, x} : Finset V) ∈ fanT u l := hl ▸ mem_fanT_append u a x (b :: l₂) l₁
  have h2 : ({u, x, b} : Finset V) ∈ fanT u l := by
    rw [hl, show l₁ ++ a :: x :: b :: l₂ = (l₁ ++ [a]) ++ x :: b :: l₂ by simp]
    exact mem_fanT_append u x b l₂ _
  have hnd' : (a :: x :: b :: l₂).Nodup := (List.nodup_append.mp (hl ▸ hnd)).2.1
  have hab : a ≠ b := fun h => (List.nodup_cons.mp hnd').1 (by simp [h])
  have hax : a ≠ x := fun h => (List.nodup_cons.mp hnd').1 (by simp [h])
  have hua : u ≠ a := fun h => hul (by rw [hl]; simp [h])
  have hux : u ≠ x := fun h => hul (by rw [hl]; simp [h])
  have hne : ({u, a, x} : Finset V) ≠ ({u, x, b} : Finset V) := by
    intro h
    have : a ∈ ({u, x, b} : Finset V) := h ▸ (by simp)
    simp only [mem_insert, mem_singleton] at this
    rcases this with h | h | h
    · exact hua h.symm
    · exact hax h
    · exact hab h
  have he : ({u, x} : Finset V) ∈ edges2 L :=
    mem_edges2.mpr ⟨_, hF h1, by intro y; simp only [mem_insert, mem_singleton]; tauto,
      card_pair hux⟩
  have hcard := hc _ he
  have hsub : ({{u, a, x}, {u, x, b}} : Finset (Finset V)) ⊆ L.filter (({u, x} : Finset V) ⊆ ·) := by
    intro σ hσ
    simp only [mem_insert, mem_singleton] at hσ
    rcases hσ with rfl | rfl
    · exact mem_filter.mpr ⟨hF h1, by intro y; simp only [mem_insert, mem_singleton]; tauto⟩
    · exact mem_filter.mpr ⟨hF h2, by intro y; simp only [mem_insert, mem_singleton]; tauto⟩
  have heq := eq_of_subset_of_card_le hsub (by rw [hcard, card_pair hne])
  have : τ ∈ ({{u, a, x}, {u, x, b}} : Finset (Finset V)) := by
    rw [heq]
    exact mem_filter.mpr ⟨hτ, by
      intro y; simp only [mem_insert, mem_singleton]; rintro (rfl | rfl) <;> assumption⟩
  simp only [mem_insert, mem_singleton] at this
  rcases this with rfl | rfl
  · exact h1
  · exact h2

/-- **After the split, `u` is no longer adjacent to the entries of `l` between its ends.** -/
lemma notMem_splitV_interior (hc : IsClosed2 L) (hnd : l.Nodup) (hul : u ∉ l)
    (hF : fanT u l ⊆ L) {x : V} (hint : ∃ l₁ a b l₂, l = l₁ ++ a :: x :: b :: l₂) (hxp : x ≠ p)
    (hxq : x ≠ q) (hxu' : x ≠ u') (huu' : u ≠ u') :
    ∀ τ ∈ splitV L u u' p q l, ¬ (u ∈ τ ∧ x ∈ τ) := by
  obtain ⟨l₁, a, b, l₂, hl⟩ := hint
  have hxl : x ∈ l := by rw [hl]; simp
  have hux : u ≠ x := fun h => hul (h ▸ hxl)
  rintro τ h ⟨hu, hx⟩
  simp only [splitV, mem_insert, mem_union, mem_sdiff] at h
  rcases h with rfl | rfl | h | h
  · simp only [mem_insert, mem_singleton] at hx
    rcases hx with h | h | h
    · exact hux h.symm
    · exact hxu' h
    · exact hxp h
  · simp only [mem_insert, mem_singleton] at hx
    rcases hx with h | h | h
    · exact hux h.symm
    · exact hxu' h
    · exact hxq h
  · exact h.2 (mem_fanT_of_interior hc hnd hul hF hl h.1 hu hx)
  · rcases (mem_fanT h).2 u hu with h' | h'
    · exact huu' h'
    · exact hul h'

end facts

end Lightlike.Surfaces
