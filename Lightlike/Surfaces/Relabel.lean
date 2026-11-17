import Lightlike.Surfaces.PLMoves

/-!
# Relabelling the vertices of a surface

Placing the triangles of a family in another vertex type by an injective map keeps the Euler
characteristic and orientability. The vertices of the moves of `PL/` are taken in `V ⊕ ℕ`, so these
two invariants are carried between `V` and `V ⊕ ℕ`.

## Main results

* `euler2_mapTri`: the Euler characteristic of `mapTri L f` is that of `L`.
* `isOrientable_mapTri_iff`: `mapTri L f` is orientable exactly when `L` is.
-/

open Finset Lightlike.PR Lightlike.PL

namespace Lightlike.Surfaces

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

lemma mem_mapTri {L : Finset (Finset V)} {f : V ↪ W} {s : Finset W} :
    s ∈ mapTri L f ↔ ∃ t ∈ L, t.map f = s := by simp [mapTri]

lemma map_mem_mapTri {L : Finset (Finset V)} {f : V ↪ W} {t : Finset V} :
    t.map f ∈ mapTri L f ↔ t ∈ L := by
  rw [mem_mapTri]
  exact ⟨fun ⟨u, hu, e⟩ => map_injective f e ▸ hu, fun h => ⟨t, h, rfl⟩⟩

lemma verts2_mapTri (f : V ↪ W) (L : Finset (Finset V)) :
    verts2 (mapTri L f) = (verts2 L).map f := by
  ext x
  simp only [mem_verts2, mem_mapTri, mem_map]
  constructor
  · rintro ⟨s, ⟨t, ht, rfl⟩, hx⟩
    obtain ⟨n, hn, rfl⟩ := mem_map.mp hx
    exact ⟨n, ⟨t, ht, hn⟩, rfl⟩
  · rintro ⟨n, ⟨t, ht, hn⟩, rfl⟩
    exact ⟨t.map f, ⟨t, ht, rfl⟩, mem_map_of_mem f hn⟩

lemma edges2_mapTri (f : V ↪ W) (L : Finset (Finset V)) :
    edges2 (mapTri L f) = (edges2 L).image (Finset.map f) := by
  ext e
  simp only [mem_edges2, mem_mapTri, mem_image]
  constructor
  · rintro ⟨s, ⟨t, ht, rfl⟩, hs, hc⟩
    refine ⟨t.filter (f · ∈ e), ⟨t, ht, filter_subset _ _, ?_⟩, ?_⟩
    · rw [← hc, ← card_map f]
      congr 1
      ext y
      simp only [mem_map, mem_filter]
      constructor
      · rintro ⟨n, ⟨-, hn⟩, rfl⟩
        exact hn
      · intro hy
        obtain ⟨n, hn, rfl⟩ := mem_map.mp (hs hy)
        exact ⟨n, ⟨hn, hy⟩, rfl⟩
    · ext y
      simp only [mem_map, mem_filter]
      constructor
      · rintro ⟨n, ⟨-, hn⟩, rfl⟩
        exact hn
      · intro hy
        obtain ⟨n, hn, rfl⟩ := mem_map.mp (hs hy)
        exact ⟨n, ⟨hn, hy⟩, rfl⟩
  · rintro ⟨e', ⟨t, ht, hs, hc⟩, rfl⟩
    exact ⟨t.map f, ⟨t, ht, rfl⟩, map_subset_map.mpr hs, by rw [card_map, hc]⟩

/-- **Relabelling does not change the Euler characteristic.** -/
lemma euler2_mapTri (f : V ↪ W) (L : Finset (Finset V)) : euler2 (mapTri L f) = euler2 L := by
  rw [euler2, euler2, verts2_mapTri f, card_map, edges2_mapTri f,
    card_image_of_injective _ (map_injective f), mapTri, card_image_of_injective _ (map_injective f)]

lemma tri_map' (f : V ↪ W) (a b c : V) : ({a, b, c} : Finset V).map f = {f a, f b, f c} := by simp

open Classical in
/-- An orientation of `L`, placed in `W` by `f` (`0` off the image of `f`). -/
noncomputable def pushG [Nonempty V] (f : V ↪ W) (o : V → V → V → ℤ) (x y z : W) : ℤ :=
  if x ∈ Set.range f ∧ y ∈ Set.range f ∧ z ∈ Set.range f then
    o (Function.invFun f x) (Function.invFun f y) (Function.invFun f z) else 0

section push

variable [Nonempty V] {f : V ↪ W} {o : V → V → V → ℤ}

omit [DecidableEq W] [DecidableEq V] in
lemma pushG_apply (a b c : V) : pushG f o (f a) (f b) (f c) = o a b c := by
  simp only [pushG, Set.mem_range_self, and_self, ite_true,
    Function.leftInverse_invFun f.injective a, Function.leftInverse_invFun f.injective b,
    Function.leftInverse_invFun f.injective c]

omit [DecidableEq W] [DecidableEq V] in
lemma pushG_eq_zero {x y z : W}
    (h : ¬ (x ∈ Set.range f ∧ y ∈ Set.range f ∧ z ∈ Set.range f)) : pushG f o x y z = 0 := by
  simp only [pushG, h, ite_false]

end push

/-- **An orientation survives placing the triangles in another vertex type.** -/
theorem isOrientation_pushG [Nonempty V] {L : Finset (Finset V)} {o : V → V → V → ℤ} (ho : IsOrientation L o)
    (f : V ↪ W) : IsOrientation (mapTri L f) (pushG f o) where
  rot x y z := by
    by_cases h : x ∈ Set.range f ∧ y ∈ Set.range f ∧ z ∈ Set.range f
    · obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩, ⟨c, rfl⟩⟩ := h
      rw [pushG_apply, pushG_apply, ho.rot]
    · rw [pushG_eq_zero h, pushG_eq_zero (by tauto)]
  swap x y z := by
    by_cases h : x ∈ Set.range f ∧ y ∈ Set.range f ∧ z ∈ Set.range f
    · obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩, ⟨c, rfl⟩⟩ := h
      rw [pushG_apply, pushG_apply, ho.swap]
    · rw [pushG_eq_zero h, pushG_eq_zero (by tauto), neg_zero]
  supp x y z h := by
    by_cases hr : x ∈ Set.range f ∧ y ∈ Set.range f ∧ z ∈ Set.range f
    · obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩, ⟨c, rfl⟩⟩ := hr
      rw [pushG_apply] at h
      rw [← tri_map']
      exact map_mem_mapTri.mpr (ho.supp a b c h)
    · exact absurd (pushG_eq_zero hr) h
  unit x y z h := by
    obtain ⟨t, ht, he⟩ := mem_mapTri.mp h
    have hr : ∀ {w : W}, w ∈ ({x, y, z} : Finset W) → w ∈ Set.range f := by
      intro w hw
      rw [← he] at hw
      obtain ⟨n, -, rfl⟩ := mem_map.mp hw
      exact Set.mem_range_self n
    obtain ⟨a, rfl⟩ := hr (show x ∈ ({x, y, z} : Finset W) by simp)
    obtain ⟨b, rfl⟩ := hr (show y ∈ ({f a, y, z} : Finset W) by simp)
    obtain ⟨c, rfl⟩ := hr (show z ∈ ({f a, f b, z} : Finset W) by simp)
    have hte : t = {a, b, c} := by
      apply map_injective f
      rw [he, tri_map']
    subst hte
    rw [pushG_apply]
    exact ho.unit a b c ht
  cycle u v := by
    rw [verts2_mapTri]
    by_cases huv : u ∈ Set.range f ∧ v ∈ Set.range f
    · obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := huv
      rw [sum_map]
      simp only [pushG_apply]
      exact ho.cycle a b
    · exact sum_eq_zero fun w _ => pushG_eq_zero (by tauto)

/-- **An orientation of the placed triangles pulls back.** -/
theorem isOrientation_pull {f : V ↪ W} {L : Finset (Finset V)} {o : W → W → W → ℤ}
    (ho : IsOrientation (mapTri L f) o) :
    IsOrientation L (fun a b c => o (f a) (f b) (f c)) where
  rot x y z := ho.rot _ _ _
  swap x y z := ho.swap _ _ _
  supp x y z h := by
    have := ho.supp _ _ _ h
    rw [← tri_map'] at this
    exact map_mem_mapTri.mp this
  unit x y z h := by
    apply ho.unit
    rw [← tri_map']
    exact map_mem_mapTri.mpr h
  cycle u v := by
    have := ho.cycle (f u) (f v)
    rw [verts2_mapTri, sum_map] at this
    exact this

/-- **Relabelling does not change orientability.** -/
theorem isOrientable_mapTri_iff [Nonempty V] (f : V ↪ W) {L : Finset (Finset V)} :
    IsOrientable (mapTri L f) ↔ IsOrientable L :=
  ⟨fun ⟨_, ho⟩ => ⟨_, isOrientation_pull ho⟩, fun ⟨_, ho⟩ => ⟨_, isOrientation_pushG ho f⟩⟩

end Lightlike.Surfaces
