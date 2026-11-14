import Lightlike.Surfaces.Basic

/-!
# The dual graph of a closed surface

Two triangles of a complex are *dual-adjacent* (`DAdj`) when they are distinct and share an edge.
For a closed surface the dual graph is connected:

* `IsSurface.dconn_vertex`: two triangles at a common vertex are joined by dual edges (through
  the triangles at that vertex, using that its link is connected);
* `IsSurface.dconn`: any two triangles are joined by dual edges (using that the 1-skeleton is
  connected);
* `IsSurface.exists_path_avoid`: a triangle `t ≠ σ` is joined to a neighbour of `σ` by a dual
  path that never visits `σ`.

These are used to move a gluing site or the end of a tube from one triangle to another, one
dual edge at a time. `tri_of_two` and `DAdj.split` write two adjacent triangles as `{w, x, y}`
and `{x, y, z}`.
-/

open Finset Relation

namespace Lightlike.Surfaces

open Lightlike.PR

variable {V : Type*} [DecidableEq V]

/-- Two triangles `s` and `t` of `M` are **dual-adjacent**: they are distinct and share two
distinct vertices. -/
def DAdj (M : Finset (Finset V)) (s t : Finset V) : Prop :=
  s ∈ M ∧ t ∈ M ∧ s ≠ t ∧ ∃ x y, x ≠ y ∧ x ∈ s ∧ y ∈ s ∧ x ∈ t ∧ y ∈ t

omit [DecidableEq V] in
/-- Dual adjacency is symmetric. -/
lemma DAdj.symm {M : Finset (Finset V)} {s t : Finset V} (h : DAdj M s t) : DAdj M t s := by
  obtain ⟨hs, ht, hst, x, y, hxy, hxs, hys, hxt, hyt⟩ := h
  exact ⟨ht, hs, Ne.symm hst, x, y, hxy, hxt, hyt, hxs, hys⟩

/-- Two triangles of `M` with two common vertices are joined by a dual path (of length 0 or 1). -/
lemma dconn_of_two {M : Finset (Finset V)} {s t : Finset V} (hs : s ∈ M) (ht : t ∈ M) {x y : V}
    (hxy : x ≠ y) (hxs : x ∈ s) (hys : y ∈ s) (hxt : x ∈ t) (hyt : y ∈ t) :
    ReflTransGen (DAdj M) s t := by
  by_cases hst : s = t
  · exact hst ▸ ReflTransGen.refl
  · exact ReflTransGen.single ⟨hs, ht, hst, x, y, hxy, hxs, hys, hxt, hyt⟩

/-- A triangle containing `v` has another vertex. -/
lemma exists_ne_of_tri {s : Finset V} (hs : #s = 3) {v : V} (hv : v ∈ s) : ∃ p ∈ s, p ≠ v := by
  have : 0 < #(s.erase v) := by rw [card_erase_of_mem hv, hs]; omega
  obtain ⟨p, hp⟩ := card_pos.mp this
  exact ⟨p, mem_of_mem_erase hp, ne_of_mem_erase hp⟩

/-- **Triangles at a common vertex are dual-connected.** In a closed surface, two triangles
through the vertex `v` are joined by a path of dual edges. -/
theorem IsSurface.dconn_vertex {M : Finset (Finset V)} (hS : IsSurface M) {v : V}
    {s t : Finset V} (hs : s ∈ M) (ht : t ∈ M) (hvs : v ∈ s) (hvt : v ∈ t) :
    ReflTransGen (DAdj M) s t := by
  obtain ⟨p, hps, hpv⟩ := exists_ne_of_tri (hS.card _ hs) hvs
  obtain ⟨q, hqt, hqv⟩ := exists_ne_of_tri (hS.card _ ht) hvt
  have hlk : ∀ τ ∈ M, v ∈ τ → ∀ w ∈ τ, w ≠ v → w ∈ verts2 (lk2 M v) := by
    intro τ hτ hvτ w hw hwv
    refine mem_verts2.mpr ⟨τ.erase v, mem_lk2.mpr ⟨notMem_erase v τ, ?_⟩, mem_erase.mpr ⟨hwv, hw⟩⟩
    rwa [insert_erase hvτ]
  have hpath := hS.link v (mem_verts2.mpr ⟨s, hs, hvs⟩) p (hlk s hs hvs p hps hpv) q
    (hlk t ht hvt q hqt hqv)
  -- every triangle through `v` and a vertex of the path is reached from `s`
  suffices h : ∀ b, ReflTransGen (fun p q => ({p, q} : Finset V) ∈ lk2 M v) p b →
      b ≠ v → ∀ τ ∈ M, v ∈ τ → b ∈ τ → ReflTransGen (DAdj M) s τ from
    h q hpath hqv t ht hvt hqt
  intro b hb
  induction hb with
  | refl => exact fun _ τ hτ hvτ hpτ => dconn_of_two hs hτ hpv.symm hvs hps hvτ hpτ
  | @tail b c _ hbc ih =>
    intro _ τ hτ hvτ hcτ
    obtain ⟨hv, hmem⟩ := mem_lk2.mp hbc
    have hvb : b ≠ v := fun h => hv (h ▸ mem_insert_self _ _)
    have hvc : c ≠ v := fun h => hv (h ▸ mem_insert_of_mem (mem_singleton_self _))
    refine (ih hvb _ hmem (mem_insert_self _ _) (mem_insert_of_mem (mem_insert_self _ _))).trans ?_
    exact dconn_of_two hmem hτ hvc.symm (mem_insert_self _ _)
      (mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _))) hvτ hcτ

/-- **The dual graph of a closed surface is connected.** Any two triangles are joined by a path
of dual edges. -/
theorem IsSurface.dconn {M : Finset (Finset V)} (hS : IsSurface M) {s t : Finset V} (hs : s ∈ M)
    (ht : t ∈ M) : ReflTransGen (DAdj M) s t := by
  obtain ⟨u, hu⟩ := card_pos.mp (by rw [hS.card _ hs]; omega : 0 < #s)
  obtain ⟨w, hw⟩ := card_pos.mp (by rw [hS.card _ ht]; omega : 0 < #t)
  have hpath := hS.connected u (mem_verts2.mpr ⟨s, hs, hu⟩) w (mem_verts2.mpr ⟨t, ht, hw⟩)
  suffices h : ∀ b, ReflTransGen (fun x y => ({x, y} : Finset V) ∈ edges2 M) u b →
      ∀ τ ∈ M, b ∈ τ → ReflTransGen (DAdj M) s τ from h w hpath t ht hw
  intro b hb
  induction hb with
  | refl => exact fun τ hτ huτ => hS.dconn_vertex hs hτ hu huτ
  | @tail b c _ hbc ih =>
    intro τ hτ hcτ
    obtain ⟨ρ, hρ, hsub, -⟩ := mem_edges2.mp hbc
    exact (ih ρ hρ (hsub (mem_insert_self _ _))).trans
      (hS.dconn_vertex hρ hτ (hsub (mem_insert_of_mem (mem_singleton_self _))) hcτ)

/-- **A dual path avoiding a triangle.** In a closed surface, a triangle `t ≠ σ` is joined to a
dual neighbour `e` of `σ` by a path of dual edges none of whose triangles is `σ`. -/
theorem IsSurface.exists_path_avoid {M : Finset (Finset V)} (hS : IsSurface M) {σ t : Finset V}
    (hσ : σ ∈ M) (ht : t ∈ M) (htσ : t ≠ σ) :
    ∃ e, DAdj M e σ ∧ ReflTransGen (fun a b => DAdj M a b ∧ a ≠ σ ∧ b ≠ σ) t e := by
  have hpath := hS.dconn ht hσ
  suffices h : ∀ a, ReflTransGen (DAdj M) a σ → a ≠ σ →
      ∃ e, DAdj M e σ ∧ ReflTransGen (fun a b => DAdj M a b ∧ a ≠ σ ∧ b ≠ σ) a e from
    h t hpath htσ
  intro a ha
  induction ha using ReflTransGen.head_induction_on with
  | refl => exact fun h => absurd rfl h
  | @head a c hac _ ih =>
    intro haσ
    by_cases hcσ : c = σ
    · exact ⟨a, hcσ ▸ hac, ReflTransGen.refl⟩
    · obtain ⟨e, he, hce⟩ := ih hcσ
      exact ⟨e, he, ReflTransGen.head ⟨hac, haσ, hcσ⟩ hce⟩

/-- A triangle `s` through two distinct vertices `x`, `y` is `{w, x, y}` for a third vertex `w`. -/
lemma tri_of_two {s : Finset V} (hs : #s = 3) {x y : V} (hxy : x ≠ y) (hx : x ∈ s) (hy : y ∈ s) :
    ∃ w, w ≠ x ∧ w ≠ y ∧ s = {w, x, y} := by
  have hsub : ({x, y} : Finset V) ⊆ s := pair_subset_of_mem hx hy
  have hc : #(s \ {x, y}) = 1 := by rw [card_sdiff_of_subset hsub, hs, card_pair hxy]
  obtain ⟨w, hw⟩ := card_eq_one.mp hc
  have hws : w ∈ s \ {x, y} := hw ▸ mem_singleton_self w
  simp only [mem_sdiff, mem_insert, mem_singleton, not_or] at hws
  refine ⟨w, hws.2.1, hws.2.2, ?_⟩
  ext z
  simp only [mem_insert, mem_singleton]
  constructor
  · intro hz
    by_cases hzxy : z = x ∨ z = y
    · exact Or.inr hzxy
    · have : z ∈ s \ {x, y} := by simpa [mem_sdiff, hz] using hzxy
      rw [hw, mem_singleton] at this
      exact Or.inl this
  · rintro (rfl | rfl | rfl)
    · exact hws.1
    · exact hx
    · exact hy

/-- **Two dual-adjacent triangles** of a complex of triangles are `{w, x, y}` and `{x, y, z}` with
`x, y, z, w` such that `w ≠ z`, `x ≠ y` and `w, z ∉ {x, y}`. -/
lemma DAdj.split {M : Finset (Finset V)} (hT : IsTri2 M) {s t : Finset V} (h : DAdj M s t) :
    ∃ w x y z, s = {w, x, y} ∧ t = {x, y, z} ∧ w ≠ z ∧ x ≠ y ∧ w ≠ x ∧ w ≠ y ∧ z ≠ x ∧ z ≠ y := by
  obtain ⟨hs, ht, hst, x, y, hxy, hxs, hys, hxt, hyt⟩ := h
  obtain ⟨w, hwx, hwy, rfl⟩ := tri_of_two (hT _ hs) hxy hxs hys
  obtain ⟨z, hzx, hzy, rfl⟩ := tri_of_two (hT _ ht) hxy hxt hyt
  refine ⟨w, x, y, z, rfl, ?_, fun hwz => hst (by rw [hwz]), hxy, hwx, hwy, hzx, hzy⟩
  ext u
  simp only [mem_insert, mem_singleton]
  tauto

end Lightlike.Surfaces
