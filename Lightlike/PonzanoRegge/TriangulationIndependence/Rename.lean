import Lightlike.PonzanoRegge.TriangulationIndependence.Main
import Lightlike.PonzanoRegge.SphereInvariants
import Lightlike.PL.PachnerMoves

/-!
# Renaming a vertex by forward moves

Let `v` be a vertex of `K` whose link `L` is a 2-sphere, and `w` a label not used by `K`. If `L`
splits into two sets of triangles `Dv`, `Dw` that are *tree-shellable* with the same boundary edges
`B` (`IsTreeShelling D B`: each triangle after the first is attached along a boundary edge and
brings a new vertex), then `K` and `K` with `v` renamed to `w` have a common forward descendant
(`commonForward_rename_of_split`), namely

`N = (K without the star of v) ∪ {v, w} * B ∪ w * Dw ∪ v * Dv`.

From `K` the fresh vertex `w` grows over `Dw` (`forwardMoves_grown`): a 1-4 move puts `w` into
`v * τ₁`, then for each further triangle `{x, y, z}` of the shelling a 2-3 move on `{v, x, y}` with
apexes `w` and `z` adds the edge `wz`. From the renamed complex `v` grows over `Dv` in the same way.

Edges never disappear along forward moves, so in any common descendant of this shape every link
vertex is adjacent to both `v` and `w`: the common boundary `B` passes through every vertex of `L`.
-/

open Finset Lightlike.PL

namespace Lightlike.PR

variable {V : Type*} [DecidableEq V]

/-- A **tree shelling** `R` with boundary edges `B`: built from one triangle by adding, each time,
a triangle `{x, y, z}` along a boundary edge `{x, y}` whose third vertex `z` is new; the boundary
loses `{x, y}` and gains `{x, z}` and `{y, z}`. These are the triangulated polygons. -/
inductive IsTreeShelling : Finset (Finset V) → Finset (Finset V) → Prop
  | single {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
      IsTreeShelling {{a, b, c}} {{a, b}, {a, c}, {b, c}}
  | step {R B : Finset (Finset V)} {x y z : V} (hR : IsTreeShelling R B)
      (hxy : ({x, y} : Finset V) ∈ B) (hz : z ∉ verts2 R) :
      IsTreeShelling (insert {x, y, z} R) (insert {x, z} (insert {y, z} (B.erase {x, y})))

/-- Every boundary edge of a tree shelling has two vertices and lies in one of its triangles. -/
theorem IsTreeShelling.bdry {R B : Finset (Finset V)} (h : IsTreeShelling R B) :
    ∀ e ∈ B, #e = 2 ∧ ∃ σ ∈ R, e ⊆ σ := by
  induction h with
  | single hab hac hbc =>
    intro e he
    simp only [mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact ⟨card_pair hab, _, mem_singleton_self _, by intro a; simp; tauto⟩
    · exact ⟨card_pair hac, _, mem_singleton_self _, by intro a; simp; tauto⟩
    · exact ⟨card_pair hbc, _, mem_singleton_self _, by intro a; simp; tauto⟩
  | @step R B x y z hR hxy hz ih =>
    obtain ⟨hxy2, σ, hσ, hxyσ⟩ := ih _ hxy
    have hx : x ∈ verts2 R := mem_verts2.2 ⟨σ, hσ, hxyσ (by simp)⟩
    have hy : y ∈ verts2 R := mem_verts2.2 ⟨σ, hσ, hxyσ (by simp)⟩
    intro e he
    simp only [mem_insert, mem_erase] at he
    rcases he with rfl | rfl | ⟨-, he⟩
    · exact ⟨card_pair fun h => hz (h ▸ hx), _, mem_insert_self _ _, by intro a; simp; tauto⟩
    · exact ⟨card_pair fun h => hz (h ▸ hy), _, mem_insert_self _ _, by intro a; simp; tauto⟩
    · obtain ⟨h2, σ', hσ', heσ'⟩ := ih e he
      exact ⟨h2, σ', mem_insert_of_mem hσ', heσ'⟩

/-- The complex in which the fresh vertex `w` has grown over the triangles `R` (boundary edges
`B`) of the link of `v`: the tetrahedra of `K` away from `v`, the tetrahedra `{v, w} ∪ e` for
`e ∈ B`, `w * R`, and `v * (L \ R)`. -/
def grown (K : Complex3 V) (v w : V) (R B : Finset (Finset V)) : Complex3 V where
  tets := (K.tets.filter (v ∉ ·) ∪ B.image (fun e => insert v (insert w e)) ∪
    R.image (insert w) ∪ (K.link v \ R).image (insert v)).filter (#· = 4)
  card_eq _ h := (mem_filter.1 h).2

section Grown

variable {K : Complex3 V} {v w : V}

lemma card_of_mem_link {τ : Finset V} (h : τ ∈ K.link v) : #τ = 3 := by
  obtain ⟨hv, ht⟩ := Complex3.mem_link.1 h
  have := K.card_eq _ ht
  rw [card_insert_of_notMem hv] at this
  omega

lemma notMem_of_mem_link {τ : Finset V} (h : τ ∈ K.link v) {w : V} (hw : w ∉ K.verts) :
    w ∉ τ := by
  intro hwτ
  obtain ⟨-, ht⟩ := Complex3.mem_link.1 h
  exact hw (mem_biUnion.2 ⟨_, ht, mem_insert_of_mem hwτ⟩)

lemma mem_verts_of_mem_link {τ : Finset V} (h : τ ∈ K.link v) : v ∈ K.verts := by
  obtain ⟨-, ht⟩ := Complex3.mem_link.1 h
  exact mem_biUnion.2 ⟨_, ht, mem_insert_self v τ⟩

/-- Membership in `grown`, when `R` lies in the link of `v`, the edges of `B` lie in triangles of
`R`, and `w` is fresh. -/
lemma mem_grown {R B : Finset (Finset V)} (hR : R ⊆ K.link v)
    (hB : ∀ e ∈ B, #e = 2 ∧ ∃ σ ∈ R, e ⊆ σ) (hw : w ∉ K.verts) {t : Finset V} :
    t ∈ (grown K v w R B).tets ↔ (t ∈ K.tets ∧ v ∉ t) ∨
      (∃ e ∈ B, insert v (insert w e) = t) ∨ (∃ τ ∈ R, insert w τ = t) ∨
        (∃ τ ∈ K.link v, τ ∉ R ∧ insert v τ = t) := by
  simp only [grown, mem_filter, mem_union, mem_image, mem_sdiff]
  constructor
  · rintro ⟨((h | h) | h) | h, -⟩
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · obtain ⟨τ, ⟨h1, h2⟩, h3⟩ := h
      exact .inr (.inr (.inr ⟨τ, h1, h2, h3⟩))
  · rintro (h | ⟨e, he, rfl⟩ | ⟨τ, hτ, rfl⟩ | ⟨τ, hτ, hτR, rfl⟩)
    · exact ⟨.inl (.inl (.inl h)), K.card_eq t h.1⟩
    · refine ⟨.inl (.inl (.inr ⟨e, he, rfl⟩)), ?_⟩
      obtain ⟨he2, σ, hσ, heσ⟩ := hB e he
      have hvσ : v ∉ σ := (Complex3.mem_link.1 (hR hσ)).1
      have hwσ : w ∉ σ := notMem_of_mem_link (hR hσ) hw
      have hvw : v ≠ w := fun h => hw (h ▸ mem_verts_of_mem_link (hR hσ))
      rw [card_insert_of_notMem (by rw [mem_insert, not_or]; exact ⟨hvw, fun h => hvσ (heσ h)⟩),
        card_insert_of_notMem (fun h => hwσ (heσ h)), he2]
    · refine ⟨.inl (.inr ⟨τ, hτ, rfl⟩), ?_⟩
      rw [card_insert_of_notMem (notMem_of_mem_link (hR hτ) hw), card_of_mem_link (hR hτ)]
    · refine ⟨.inr ⟨τ, ⟨hτ, hτR⟩, rfl⟩, ?_⟩
      rw [card_insert_of_notMem (Complex3.mem_link.1 hτ).1, card_of_mem_link hτ]

/-- The tetrahedra of `K` through `v` are the cones on its link. -/
lemma mem_tets_iff_link {t : Finset V} :
    t ∈ K.tets ↔ (t ∈ K.tets ∧ v ∉ t) ∨ ∃ τ ∈ K.link v, insert v τ = t := by
  constructor
  · intro ht
    by_cases hv : v ∈ t
    · exact .inr ⟨t.erase v, Complex3.mem_link.2 ⟨notMem_erase v t, by rwa [insert_erase hv]⟩,
        insert_erase hv⟩
    · exact .inl ⟨ht, hv⟩
  · rintro (⟨ht, -⟩ | ⟨τ, hτ, rfl⟩)
    · exact ht
    · exact (Complex3.mem_link.1 hτ).2

end Grown


section Steps

variable {K : Complex3 V} {v w : V}

lemma complex3_eq {K L : Complex3 V} (h : ∀ t, t ∈ K.tets ↔ t ∈ L.tets) : K = L := by
  cases K; cases L; congr; ext t; exact h t

/-- Cones from a vertex `v` not in the bases agree only for equal bases. -/
lemma insert_left_inj {v : V} {s s' : Finset V} (hv : v ∉ s) (hv' : v ∉ s')
    (h : insert v s = insert v s') : s = s' := by
  have := congrArg (·.erase v) h
  simpa [erase_insert hv, erase_insert hv'] using this

/-- **The first step: a 1-4 move puts `w` into `v * τ₁`.** -/
theorem forwardStep_grown_single {a b c : V} (hτ : ({a, b, c} : Finset V) ∈ K.link v)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hw : w ∉ K.verts) :
    ForwardStep K (grown K v w {{a, b, c}} {{a, b}, {a, c}, {b, c}}) := by
  obtain ⟨hvτ, hmem⟩ := Complex3.mem_link.1 hτ
  have hwτ := notMem_of_mem_link hτ hw
  have hvτ' := hvτ
  simp only [mem_insert, mem_singleton, not_or] at hvτ' hwτ
  obtain ⟨hva, hvb, hvc⟩ := hvτ'
  obtain ⟨hwa, hwb, hwc⟩ := hwτ
  have hvw : v ≠ w := fun h => hw (h ▸ mem_verts_of_mem_link hτ)
  have h14 : IsMove14 K v a b c w :=
    ⟨hva, hvb, hvc, hvw, hab, hac, Ne.symm hwa, hbc, Ne.symm hwb, Ne.symm hwc, hmem,
      fun t ht hwt => hw (mem_biUnion.2 ⟨t, ht, hwt⟩)⟩
  have hR : ({{a, b, c}} : Finset (Finset V)) ⊆ K.link v := singleton_subset_iff.2 hτ
  have hB := (IsTreeShelling.single (V := V) hab hac hbc).bdry
  suffices e : move14 K h14 = grown K v w {{a, b, c}} {{a, b}, {a, c}, {b, c}} by
    rw [← e]; exact .m14 h14
  refine complex3_eq fun t => ?_
  rw [mem_grown hR hB hw]
  simp only [move14, mem_union, mem_insert, mem_singleton, mem_erase]
  have e1 : insert v (insert w ({a, b} : Finset V)) = {v, a, b, w} := by
    rw [insert_comm w a, pair_comm w b]
  have e2 : insert v (insert w ({a, c} : Finset V)) = {v, a, c, w} := by
    rw [insert_comm w a, pair_comm w c]
  have e3 : insert v (insert w ({b, c} : Finset V)) = {v, b, c, w} := by
    rw [insert_comm w b, pair_comm w c]
  have e4 : insert w ({a, b, c} : Finset V) = {a, b, c, w} := by
    rw [insert_comm w a, insert_comm w b, pair_comm w c]
  constructor
  · rintro ((rfl | rfl | rfl | rfl) | ⟨hne, ht⟩)
    · exact .inr (.inl ⟨{a, b}, by simp, e1⟩)
    · exact .inr (.inl ⟨{a, c}, by simp, e2⟩)
    · exact .inr (.inl ⟨{b, c}, by simp, e3⟩)
    · exact .inr (.inr (.inl ⟨{a, b, c}, rfl, e4⟩))
    · rcases (mem_tets_iff_link (v := v)).1 ht with h | ⟨τ, hτ', rfl⟩
      · exact .inl h
      · refine .inr (.inr (.inr ⟨τ, hτ', fun h => hne (by rw [h]), rfl⟩))
  · rintro (⟨ht, hvt⟩ | ⟨e, he, rfl⟩ | ⟨τ, hτ', rfl⟩ | ⟨τ, hτ', hτR, rfl⟩)
    · exact .inr ⟨fun h => hvt (h ▸ by simp), ht⟩
    · rcases he with rfl | rfl | rfl
      · exact .inl (.inl e1)
      · exact .inl (.inr (.inl e2))
      · exact .inl (.inr (.inr (.inl e3)))
    · subst hτ'
      exact .inl (.inr (.inr (.inr e4)))
    · refine .inr ⟨fun h => hτR ?_, (Complex3.mem_link.1 hτ').2⟩
      exact insert_left_inj (Complex3.mem_link.1 hτ').1 hvτ h

/-- **A growth step: a 2-3 move on `{v, x, y}` with apexes `w` and `z`** attaches the link
triangle `{x, y, z}` to the region of `w` along its boundary edge `{x, y}`. -/
theorem forwardStep_grown_step {R B : Finset (Finset V)} {x y z : V}
    (hR : R ⊆ K.link v) (hB : ∀ e ∈ B, #e = 2 ∧ ∃ σ ∈ R, e ⊆ σ)
    (hτ : ({x, y, z} : Finset V) ∈ K.link v) (hxy : ({x, y} : Finset V) ∈ B)
    (hz : z ∉ verts2 R) (hL : IsClosed2 (K.link v)) (hw : w ∉ K.verts) :
    ForwardStep (grown K v w R B)
      (grown K v w (insert {x, y, z} R) (insert {x, z} (insert {y, z} (B.erase {x, y})))) := by
  obtain ⟨hvτ, hmemτ⟩ := Complex3.mem_link.1 hτ
  have hwτ := notMem_of_mem_link hτ hw
  have hvτ' := hvτ
  have hwτ' := hwτ
  simp only [mem_insert, mem_singleton, not_or] at hvτ' hwτ'
  obtain ⟨hvx, hvy, hvz⟩ := hvτ'
  obtain ⟨hwx, hwy, hwz⟩ := hwτ'
  have hvw : v ≠ w := fun h => hw (h ▸ mem_verts_of_mem_link hτ)
  obtain ⟨hxy2, σ0, hσ0, hxyσ0⟩ := hB _ hxy
  have hxR : x ∈ verts2 R := mem_verts2.2 ⟨σ0, hσ0, hxyσ0 (by simp)⟩
  have hyR : y ∈ verts2 R := mem_verts2.2 ⟨σ0, hσ0, hxyσ0 (by simp)⟩
  have hzx : z ≠ x := fun h => hz (h ▸ hxR)
  have hzy : z ≠ y := fun h => hz (h ▸ hyR)
  have hxy' : x ≠ y := fun h => by simp [h] at hxy2
  have hτR : ({x, y, z} : Finset V) ∉ R := fun h => hz (mem_verts2.2 ⟨_, h, by simp⟩)
  have hzσ : ∀ σ ∈ R, z ∉ σ := fun σ hσ hzs => hz (mem_verts2.2 ⟨σ, hσ, hzs⟩)
  -- the two link triangles through `{x, y}` are `σ0 ∈ R` and `{x, y, z} ∉ R`
  have htwo : ∀ σ ∈ K.link v, ({x, y} : Finset V) ⊆ σ → σ ∉ R → σ = {x, y, z} := by
    intro σ hσ hxyσ hσR
    have hedge : ({x, y} : Finset V) ∈ edges2 (K.link v) :=
      mem_edges2.2 ⟨_, hτ, insert_subset_insert x (singleton_subset_iff.2 (mem_insert_self y {z})), hxy2⟩
    have h2 := hL _ hedge
    have hsub : ({σ0, {x, y, z}} : Finset (Finset V)) ⊆ (K.link v).filter (({x, y} : Finset V) ⊆ ·) := by
      intro s hs
      simp only [mem_insert, mem_singleton] at hs
      rcases hs with rfl | rfl
      · exact mem_filter.2 ⟨hR hσ0, hxyσ0⟩
      · exact mem_filter.2 ⟨hτ, insert_subset_insert x (singleton_subset_iff.2 (mem_insert_self y {z}))⟩
    have hne : σ0 ≠ {x, y, z} := fun h => hτR (h ▸ hσ0)
    have heq := eq_of_subset_of_card_le hsub (by rw [h2, card_pair hne])
    have : σ ∈ ({σ0, {x, y, z}} : Finset (Finset V)) := heq ▸ mem_filter.2 ⟨hσ, hxyσ⟩
    simp only [mem_insert, mem_singleton] at this
    rcases this with rfl | h
    · exact absurd hσ0 hσR
    · exact h
  have e1 : insert v (insert w ({x, y} : Finset V)) = {v, x, y, w} := by
    rw [insert_comm w x, pair_comm w y]
  have e2 : insert v ({x, y, z} : Finset V) = {v, x, y, z} := rfl
  have h23 : IsMove23 (grown K v w R B) v x y w z := by
    refine ⟨hvx, hvy, hvw, hvz, hxy', Ne.symm hwx, Ne.symm hzx, Ne.symm hwy, Ne.symm hzy,
      fun h => hwz (h ▸ by simp), ?_, ?_, ?_, ?_⟩
    · rw [mem_grown hR hB hw]; exact .inr (.inl ⟨_, hxy, e1⟩)
    · rw [mem_grown hR hB hw]; exact .inr (.inr (.inr ⟨_, hτ, hτR, e2⟩))
    · intro t ht hsub
      rw [mem_grown hR hB hw] at ht
      have hvt : v ∈ t := hsub (by simp)
      have hxyt : ({x, y} : Finset V) ⊆ t := (subset_insert v _).trans hsub
      rcases ht with ⟨-, hvt'⟩ | ⟨e, he, rfl⟩ | ⟨σ, hσ, rfl⟩ | ⟨σ, hσ, hσR, rfl⟩
      · exact absurd hvt hvt'
      · left
        obtain ⟨he2, σ', hσ', heσ'⟩ := hB e he
        have hve : v ∉ e := fun h => (Complex3.mem_link.1 (hR hσ')).1 (heσ' h)
        have hwe : w ∉ e := fun h => notMem_of_mem_link (hR hσ') hw (heσ' h)
        have : ({x, y} : Finset V) ⊆ e := fun a ha => by
          have := hxyt ha
          simp only [mem_insert] at this
          rcases this with rfl | rfl | h
          · simp at ha; rcases ha with rfl | rfl <;> contradiction
          · simp at ha; rcases ha with rfl | rfl <;> contradiction
          · exact h
        rw [← eq_of_subset_of_card_le this (by rw [he2, card_pair hxy']), e1]
      · exfalso
        rcases mem_insert.1 hvt with h | h
        · exact hvw h
        · exact (Complex3.mem_link.1 (hR hσ)).1 h
      · right
        have hσ' : ({x, y} : Finset V) ⊆ σ := fun a ha => by
          have := hxyt ha
          rcases mem_insert.1 this with h | h
          · simp at ha; rcases ha with rfl | rfl <;> exact absurd h.symm (by assumption)
          · exact h
        rw [htwo σ hσ hσ' hσR]
    · intro t ht hsub
      rw [mem_grown hR hB hw] at ht
      have hwt : w ∈ t := hsub (by simp)
      have hzt : z ∈ t := hsub (by simp)
      rcases ht with ⟨ht, -⟩ | ⟨e, he, rfl⟩ | ⟨σ, hσ, rfl⟩ | ⟨σ, hσ, -, rfl⟩
      · exact hw (mem_biUnion.2 ⟨t, ht, hwt⟩)
      · obtain ⟨-, σ', hσ', heσ'⟩ := hB e he
        simp only [mem_insert] at hzt
        rcases hzt with h | h | h
        · exact hvz h.symm
        · exact hwz h.symm
        · exact hzσ σ' hσ' (heσ' h)
      · rcases mem_insert.1 hzt with h | h
        · exact hwz h.symm
        · exact hzσ σ hσ h
      · rcases mem_insert.1 hwt with h | h
        · exact hvw h.symm
        · exact notMem_of_mem_link hσ hw h
  have hR' : insert {x, y, z} R ⊆ K.link v := insert_subset hτ hR
  have hB' : ∀ e ∈ insert {x, z} (insert {y, z} (B.erase {x, y})), #e = 2 ∧
      ∃ σ ∈ insert {x, y, z} R, e ⊆ σ := by
    intro e he
    simp only [mem_insert, mem_erase] at he
    rcases he with rfl | rfl | ⟨-, he⟩
    · exact ⟨card_pair (Ne.symm hzx), _, mem_insert_self _ _,
        insert_subset_insert x (singleton_subset_iff.2 (by simp))⟩
    · exact ⟨card_pair (Ne.symm hzy), _, mem_insert_self _ _, subset_insert x _⟩
    · obtain ⟨h2, σ, hσ, heσ⟩ := hB e he
      exact ⟨h2, σ, mem_insert_of_mem hσ, heσ⟩
  have f1 : insert v (insert w ({x, z} : Finset V)) = {v, x, w, z} := by
    rw [insert_comm w x]
  have f2 : insert w ({x, y, z} : Finset V) = {x, y, w, z} := by
    rw [insert_comm w x, insert_comm w y]
  have f3 : insert v (insert w ({y, z} : Finset V)) = {y, v, w, z} := by
    rw [insert_comm w y, insert_comm v y]
  have nv : ∀ s : Finset V, v ∉ s → s ≠ {v, x, y, z} := fun s hs h => hs (by rw [h]; simp)
  have nv' : ∀ s : Finset V, v ∉ s → s ≠ {v, x, y, w} := fun s hs h => hs (by rw [h]; simp)
  have nw : ∀ s : Finset V, w ∈ s → s ≠ {v, x, y, z} := fun s hs h => by
    rw [h] at hs
    simp only [mem_insert, mem_singleton] at hs
    rcases hs with h | h | h | h
    exacts [hvw h.symm, hwx h, hwy h, hwz h]
  suffices e : move23 _ h23 =
      grown K v w (insert {x, y, z} R) (insert {x, z} (insert {y, z} (B.erase {x, y}))) by
    rw [← e]; exact .m23 h23
  refine complex3_eq fun t => ?_
  rw [mem_grown hR' hB' hw]
  simp only [move23, mem_union, mem_insert, mem_singleton, mem_erase, mem_grown hR hB hw]
  constructor
  · rintro ((rfl | rfl | rfl) |
      ⟨h1, h2, h | ⟨e, he, rfl⟩ | ⟨σ, hσ, rfl⟩ | ⟨σ, hσ, hσR, rfl⟩⟩)
    · exact .inr (.inl ⟨{x, z}, .inl rfl, f1⟩)
    · exact .inr (.inr (.inl ⟨{x, y, z}, .inl rfl, f2⟩))
    · exact .inr (.inl ⟨{y, z}, .inr (.inl rfl), f3⟩)
    · exact .inl h
    · refine .inr (.inl ⟨e, .inr (.inr ⟨fun hexy => h2 ?_, he⟩), rfl⟩)
      rw [hexy, e1]
    · exact .inr (.inr (.inl ⟨σ, .inr hσ, rfl⟩))
    · refine .inr (.inr (.inr ⟨σ, hσ, not_or.2 ⟨fun hσ' => h1 ?_, hσR⟩, rfl⟩))
      rw [hσ']
  · rintro (⟨ht, hvt⟩ | ⟨e, he, rfl⟩ | ⟨σ, hσ, rfl⟩ | ⟨σ, hσ, hσR, rfl⟩)
    · exact .inr ⟨nv t hvt, nv' t hvt, .inl ⟨ht, hvt⟩⟩
    · rcases he with rfl | rfl | ⟨hne, he⟩
      · exact .inl (.inl f1)
      · exact .inl (.inr (.inr f3))
      · obtain ⟨-, σ', hσ', heσ'⟩ := hB e he
        have hve : v ∉ e := fun h => (Complex3.mem_link.1 (hR hσ')).1 (heσ' h)
        have hwe : w ∉ e := fun h => notMem_of_mem_link (hR hσ') hw (heσ' h)
        refine .inr ⟨nw _ (by simp), fun h => hne ?_, .inr (.inl ⟨e, he, rfl⟩)⟩
        rw [← e1] at h
        exact insert_left_inj hwe (by simp [hwx, hwy])
          (insert_left_inj (by simp [hvw, hve]) (by simp [hvw, hvx, hvy]) h)
    · rcases hσ with rfl | hσ
      · exact .inl (.inr (.inl f2))
      · have hvσ := (Complex3.mem_link.1 (hR hσ)).1
        have : v ∉ insert w σ := by simp [hvw, hvσ]
        exact .inr ⟨nv _ this, nv' _ this, .inr (.inr (.inl ⟨σ, hσ, rfl⟩))⟩
    · obtain ⟨hne, hσR⟩ := not_or.1 hσR
      have hvσ := (Complex3.mem_link.1 hσ).1
      refine .inr ⟨fun h => hne (insert_left_inj hvσ hvτ h), fun h => ?_,
        .inr (.inr (.inr ⟨σ, hσ, hσR, rfl⟩))⟩
      have : w ∈ insert v σ := by rw [h]; simp
      rcases mem_insert.1 this with h' | h'
      · exact hvw h'.symm
      · exact notMem_of_mem_link hσ hw h'

/-- **The fresh vertex `w` grows over a tree-shellable part `R` of the link of `v`** by forward
moves. -/
theorem forwardMoves_grown {R B : Finset (Finset V)} (hsh : IsTreeShelling R B)
    (hR : R ⊆ K.link v) (hL : IsClosed2 (K.link v)) (hw : w ∉ K.verts) :
    ForwardMoves K (grown K v w R B) := by
  induction hsh with
  | single hab hac hbc =>
    exact .single (forwardStep_grown_single (singleton_subset_iff.1 hR) hab hac hbc hw)
  | @step R B x y z hR0 hxy hz ih =>
    have hR0' : R ⊆ K.link v := (subset_insert _ _).trans hR
    exact (ih hR0').tail (forwardStep_grown_step hR0' hR0.bdry (hR (mem_insert_self _ _)) hxy hz
      hL hw)

end Steps

section Rename

variable {K : Complex3 V} {v w : V}

/-- The swap of `v` and a fresh `w` fixes every set avoiding both. -/
lemma map_swap_of_notMem {s : Finset V} (hv : v ∉ s) (hw : w ∉ s) :
    s.map (Equiv.swap v w).toEmbedding = s := by
  ext a
  simp only [mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨b, hb, rfl⟩
    rwa [Equiv.swap_apply_of_ne_of_ne (fun h => hv (by rw [← h]; exact hb))
      (fun h => hw (by rw [← h]; exact hb))]
  · intro ha
    exact ⟨a, ha, Equiv.swap_apply_of_ne_of_ne (fun h => hv (by rw [← h]; exact ha))
      (fun h => hw (by rw [← h]; exact ha))⟩

/-- The tetrahedra of `K` with `v` renamed to the fresh label `w`. -/
lemma mem_rename {hw : w ∉ K.verts} {t : Finset V} :
    t ∈ (mapComplex3 K (Equiv.swap v w).toEmbedding).tets ↔
      (t ∈ K.tets ∧ v ∉ t) ∨ ∃ τ ∈ K.link v, insert w τ = t := by
  have hwt : ∀ s ∈ K.tets, w ∉ s := fun s hs hws => hw (mem_biUnion.2 ⟨s, hs, hws⟩)
  simp only [mapComplex3, mem_image]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rcases (mem_tets_iff_link (v := v)).1 hs with ⟨-, hvs⟩ | ⟨τ, hτ, rfl⟩
    · exact .inl (by rw [map_swap_of_notMem hvs (hwt s hs)]; exact ⟨hs, hvs⟩)
    · refine .inr ⟨τ, hτ, ?_⟩
      rw [Finset.map_insert, Equiv.coe_toEmbedding, Equiv.swap_apply_left,
        map_swap_of_notMem (Complex3.mem_link.1 hτ).1 (notMem_of_mem_link hτ hw)]
  · rintro (⟨ht, hvt⟩ | ⟨τ, hτ, rfl⟩)
    · exact ⟨t, ht, map_swap_of_notMem hvt (hwt t ht)⟩
    · refine ⟨insert v τ, (Complex3.mem_link.1 hτ).2, ?_⟩
      rw [Finset.map_insert, Equiv.coe_toEmbedding, Equiv.swap_apply_left,
        map_swap_of_notMem (Complex3.mem_link.1 hτ).1 (notMem_of_mem_link hτ hw)]

lemma link_rename (hw : w ∉ K.verts) :
    (mapComplex3 K (Equiv.swap v w).toEmbedding).link w = K.link v := by
  ext τ
  rw [Complex3.mem_link, mem_rename (hw := hw)]
  constructor
  · rintro ⟨hwτ, (⟨ht, -⟩ | ⟨τ', hτ', h⟩)⟩
    · exact absurd (mem_biUnion.2 ⟨_, ht, mem_insert_self w τ⟩) hw
    · rwa [← insert_left_inj (notMem_of_mem_link hτ' hw) hwτ h]
  · intro hτ
    exact ⟨notMem_of_mem_link hτ hw, .inr ⟨τ, hτ, rfl⟩⟩

lemma notMem_verts_rename (hw : w ∉ K.verts) (hvw : v ≠ w) :
    v ∉ (mapComplex3 K (Equiv.swap v w).toEmbedding).verts := by
  intro hv
  obtain ⟨t, ht, hvt⟩ := mem_biUnion.1 hv
  rcases (mem_rename (hw := hw)).1 ht with ⟨-, hvt'⟩ | ⟨τ, hτ, rfl⟩
  · exact hvt' hvt
  · rcases mem_insert.1 hvt with h | h
    · exact hvw h
    · exact (Complex3.mem_link.1 hτ).1 h

/-- **Renaming a vertex by forward moves.** If the link of `v` is a 2-sphere that splits into two
tree-shellable parts `Dv`, `Dw` with the same boundary edges `B`, and `w` is a label `K` does not
use, then `K` and `K` with `v` renamed to `w` have a common forward descendant:
`(K without the star of v) ∪ {v, w} * B ∪ w * Dw ∪ v * Dv`. -/
theorem commonForward_rename_of_split (hL : IsSphere2 (K.link v)) (hw : w ∉ K.verts)
    {Dv Dw B : Finset (Finset V)} (hsplit : K.link v = Dv ∪ Dw) (hdisj : Disjoint Dv Dw)
    (hv : IsTreeShelling Dv B) (hwsh : IsTreeShelling Dw B) :
    CommonForward K (mapComplex3 K (Equiv.swap v w).toEmbedding) := by
  set K' := mapComplex3 K (Equiv.swap v w).toEmbedding with hK'
  have hlink : K'.link w = K.link v := link_rename hw
  have hDv : Dv ⊆ K.link v := hsplit ▸ subset_union_left
  have hDw : Dw ⊆ K.link v := hsplit ▸ subset_union_right
  have hvw : v ≠ w := by
    obtain ⟨τ, hτ⟩ : Dv.Nonempty := by cases hv <;> simp
    exact fun h => hw (h ▸ mem_verts_of_mem_link (hDv hτ))
  have hv' : v ∉ K'.verts := notMem_verts_rename hw hvw
  have hwK : ∀ s ∈ K.tets, w ∉ s := fun s hs hws => hw (mem_biUnion.2 ⟨s, hs, hws⟩)
  refine ⟨grown K v w Dw B, forwardMoves_grown hwsh hDw hL.closed hw, ?_⟩
  have heq : grown K' w v Dv B = grown K v w Dw B := by
    refine complex3_eq fun t => ?_
    rw [mem_grown (by rw [hlink]; exact hDv) hv.bdry hv', mem_grown hDw hwsh.bdry hw, hlink]
    have h1 : t ∈ K'.tets ∧ w ∉ t ↔ t ∈ K.tets ∧ v ∉ t := by
      rw [hK', mem_rename (hw := hw)]
      constructor
      · rintro ⟨⟨ht, hvt⟩ | ⟨τ, -, rfl⟩, hwt⟩
        · exact ⟨ht, hvt⟩
        · exact absurd (mem_insert_self w τ) hwt
      · rintro ⟨ht, hvt⟩
        exact ⟨.inl ⟨ht, hvt⟩, hwK t ht⟩
    rw [h1]
    constructor
    · rintro (h | ⟨e, he, rfl⟩ | ⟨τ, hτ, rfl⟩ | ⟨τ, hτ, hτD, rfl⟩)
      · exact .inl h
      · exact .inr (.inl ⟨e, he, insert_comm _ _ _⟩)
      · refine .inr (.inr (.inr ⟨τ, hDv hτ, disjoint_left.1 hdisj hτ, rfl⟩))
      · have : τ ∈ Dw := by
          rw [hsplit] at hτ
          exact (mem_union.1 hτ).resolve_left hτD
        exact .inr (.inr (.inl ⟨τ, this, rfl⟩))
    · rintro (h | ⟨e, he, rfl⟩ | ⟨τ, hτ, rfl⟩ | ⟨τ, hτ, hτD, rfl⟩)
      · exact .inl h
      · exact .inr (.inl ⟨e, he, insert_comm _ _ _⟩)
      · exact .inr (.inr (.inr ⟨τ, hDw hτ, disjoint_right.1 hdisj hτ, rfl⟩))
      · have : τ ∈ Dv := by
          rw [hsplit] at hτ
          exact (mem_union.1 hτ).resolve_right hτD
        exact .inr (.inr (.inl ⟨τ, this, rfl⟩))
  rw [← heq]
  exact forwardMoves_grown hv (by rw [hlink]; exact hDv) (by rw [hlink]; exact hL.closed) hv'

end Rename

/-! ## Non-vacuity: the boundary of the 4-simplex -/

/-- The boundary of the 4-simplex on `{0, 1, 2, 3, 4}`. -/
def bdry4 : Complex3 ℕ where
  tets := {{0, 1, 2, 3}, {0, 1, 2, 4}, {0, 1, 3, 4}, {0, 2, 3, 4}, {1, 2, 3, 4}}
  card_eq := by decide

/-- **Non-vacuity of `commonForward_rename_of_split`**: renaming the vertex `0` of the boundary of
the 4-simplex to `5`; the link `∂(1234)` splits into `{123, 134}` and `{124, 234}`, both with
boundary `12, 23, 34, 14`. -/
theorem commonForward_rename_bdry4 :
    CommonForward bdry4 (mapComplex3 bdry4 (Equiv.swap 0 5).toEmbedding) := by
  have hlink : bdry4.link 0 = bdry 1 2 3 4 := by decide
  have hDv : IsTreeShelling (V := ℕ) (insert {1, 3, 4} {{1, 2, 3}})
      (insert {1, 4} (insert {3, 4} (({{1, 2}, {1, 3}, {2, 3}} : Finset (Finset ℕ)).erase {1, 3}))) :=
    .step (.single (by decide) (by decide) (by decide)) (by decide) (by decide)
  have hDw : IsTreeShelling (V := ℕ) (insert {2, 4, 3} {{1, 2, 4}})
      (insert {2, 3} (insert {4, 3} (({{1, 2}, {1, 4}, {2, 4}} : Finset (Finset ℕ)).erase {2, 4}))) :=
    .step (.single (by decide) (by decide) (by decide)) (by decide) (by decide)
  have hB : (insert {2, 3} (insert {4, 3} (({{1, 2}, {1, 4}, {2, 4}} : Finset (Finset ℕ)).erase
      {2, 4}))) = insert {1, 4} (insert {3, 4} (({{1, 2}, {1, 3}, {2, 3}} : Finset (Finset ℕ)).erase
      {1, 3})) := by decide
  rw [hB] at hDw
  have hsph : IsSphere2 (bdry4.link 0) := by
    rw [hlink]
    exact isSphere2_bdry (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hsplit : bdry4.link 0 = insert {1, 3, 4} {{1, 2, 3}} ∪ insert {2, 4, 3} {{1, 2, 4}} := by
    rw [hlink]; decide
  exact commonForward_rename_of_split hsph (by decide) hsplit (by decide) hDv hDw

end Lightlike.PR
