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
      rw [card_insert_of_notMem (by simp [hvw, fun h => hvσ (heσ h)]),
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

end Lightlike.PR
