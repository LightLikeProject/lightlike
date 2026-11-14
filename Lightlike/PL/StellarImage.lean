import Lightlike.PL.Join
import Mathlib.Data.Set.Card

/-!
# Stellar equivalence is reflected by embeddings of the vertices

An injective map `f : V ↪ W` of the vertices carries stellar equivalent complexes to stellar
equivalent complexes (`StellarEquivIn.map`). This file proves the converse: if `K.map f` and
`L.map f` are stellar equivalent inside `W` and `V` is infinite, then `K` and `L` are stellar
equivalent inside `V`. A chain of moves in `W` may use vertices outside the image of `f`, but only
finitely many (`StellarEquivIn.exists_within`); a map `W → V` that inverts `f` and is injective
on these finitely many vertices renames the whole chain into `V`.

This is what lets a statement about complexes whose vertices are points of a vector space (the
geometric realisation, `Lightlike/PL/Realisation.lean`) come back to the abstract complexes.

## Main results

* `SComplex.image`: the image of a complex under an arbitrary map of the vertices.
* `SComplex.image_starAt`: stellar subdivision commutes with a map injective on the vertices.
* `StellarEquivIn.of_map`: an embedding into any vertex type reflects stellar equivalence inside
  an infinite vertex type.
* `StellarEquiv.map_iff`: `K.map f` and `L.map f` are stellar equivalent exactly when `K` and `L`
  are.
-/

open Finset

namespace Lightlike.PL

namespace SComplex

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

/-! ## Images under arbitrary maps of the vertices -/

/-- The **image** of a complex under a map `g` of the vertices: its faces are the images of the
faces of `K`. For an embedding this is `K.map`; in general faces may collapse. -/
def image (K : SComplex W) (g : W → V) : SComplex V where
  faces := K.faces.image (Finset.image g)
  down s hs t ht := by
    simp only [Finset.mem_image, mem_faces] at hs ⊢
    obtain ⟨u, hu, rfl⟩ := hs
    refine ⟨u.filter (fun x => g x ∈ t), down_mem hu (filter_subset _ _), ?_⟩
    ext y
    simp only [Finset.mem_image, mem_filter]
    constructor
    · rintro ⟨x, ⟨-, hx⟩, rfl⟩
      exact hx
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (ht hy)
      exact ⟨x, ⟨hx, hy⟩, rfl⟩

omit [DecidableEq W] in
lemma mem_image {K : SComplex W} {g : W → V} {s : Finset V} :
    s ∈ K.image g ↔ ∃ t ∈ K, t.image g = s := by
  change s ∈ K.faces.image _ ↔ _
  simp

omit [DecidableEq W] in
lemma image_mem_image {K : SComplex W} {g : W → V} {t : Finset W} (ht : t ∈ K) :
    t.image g ∈ K.image g :=
  mem_image.2 ⟨t, ht, rfl⟩

/-- The vertices of the image are the images of the vertices. -/
lemma verts_image (K : SComplex W) (g : W → V) : (K.image g).verts = K.verts.image g := by
  ext x
  rw [mem_verts, mem_image, Finset.mem_image]
  constructor
  · rintro ⟨t, ht, he⟩
    have hx : x ∈ t.image g := by rw [he]; exact mem_singleton_self x
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    exact ⟨y, mem_verts.2 (down_mem ht (singleton_subset_iff.2 hy)), rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨{y}, mem_verts.1 hy, image_singleton g y⟩

/-- A map that inverts an embedding on the vertices undoes it. -/
lemma image_map {K : SComplex V} {f : V ↪ W} {g : W → V} (h : ∀ x ∈ K.verts, g (f x) = x) :
    (K.map f).image g = K := by
  have key : ∀ u ∈ K, (u.map f).image g = u := fun u hu => by
    ext x
    simp only [Finset.mem_image, Finset.mem_map]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      rwa [h z (subset_verts hu hz)]
    · intro hx
      exact ⟨f x, ⟨x, hx, rfl⟩, h x (subset_verts hu hx)⟩
  refine ext_mem fun s => ?_
  rw [mem_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨u, hu, rfl⟩ := mem_map.1 ht
    rwa [key u hu]
  · intro hs
    exact ⟨s.map f, map_mem_map.2 hs, key s hs⟩

/-- **Stellar subdivision commutes with a map injective on the vertices**: if `g` is injective
on a set `U` containing the vertices of `K`, the image of `(A, a) K` is `(g A, g a) (g K)`. -/
theorem image_starAt {K : SComplex W} {A : Finset W} {a : W} {U : Finset W} {g : W → V}
    (hg : Set.InjOn g ↑U) (hK : K.verts ⊆ U) (hA : A ∈ K) :
    (K.starAt A a).image g = (K.image g).starAt (A.image g) (g a) := by
  have sub : ∀ t ∈ K, t ⊆ U := fun t ht => (subset_verts ht).trans hK
  have hAU := sub A hA
  have imgsub : ∀ {t t' : Finset W}, t ⊆ U → t' ⊆ U → (t.image g ⊆ t'.image g ↔ t ⊆ t') :=
    fun h₁ h₂ => by
      rw [← coe_subset, coe_image, coe_image,
        hg.image_subset_image_iff (coe_subset.2 h₁) (coe_subset.2 h₂), coe_subset]
  have imgeq : ∀ {t t' : Finset W}, t ⊆ U → t' ⊆ U → (t.image g = t'.image g ↔ t = t') :=
    fun h₁ h₂ => by
      rw [← coe_inj, coe_image, coe_image,
        hg.image_eq_image_iff (coe_subset.2 h₁) (coe_subset.2 h₂), coe_inj]
  have memimg : ∀ {t : Finset W}, t ⊆ U → (t.image g ∈ K.image g ↔ t ∈ K) := fun ht =>
    ⟨fun h => by
      obtain ⟨u, hu, he⟩ := mem_image.1 h
      rwa [(imgeq (sub u hu) ht).1 he] at hu, image_mem_image⟩
  refine ext_mem fun s => ?_
  rw [mem_image, mem_starAt]
  constructor
  · rintro ⟨t, ht, rfl⟩
    rcases mem_starAt.1 ht with ⟨ht, hAt⟩ | ⟨u, hu, hAu, hAuK, rfl⟩
    · exact .inl ⟨image_mem_image ht, fun h => hAt ((imgsub hAU (sub t ht)).1 h)⟩
    · refine .inr ⟨u.image g, image_mem_image hu, fun h => hAu ((imgsub hAU (sub u hu)).1 h),
        ?_, (image_insert g a u).symm⟩
      rw [← image_union]
      exact image_mem_image hAuK
  · rintro (⟨hs, hAs⟩ | ⟨t', ht', hAt', hAtK, rfl⟩)
    · obtain ⟨t, ht, rfl⟩ := mem_image.1 hs
      exact ⟨t, mem_starAt.2 (.inl ⟨ht, fun h => hAs (image_subset_image h)⟩), rfl⟩
    · obtain ⟨u, hu, rfl⟩ := mem_image.1 ht'
      rw [← image_union, memimg (union_subset hAU (sub u hu))] at hAtK
      exact ⟨insert a u, mem_starAt.2 (.inr ⟨u, hu, fun h => hAt' (image_subset_image h), hAtK,
        rfl⟩), image_insert g a u⟩

/-- The apex of a stellar subdivision at a nonempty face is a vertex of it. -/
lemma apex_mem_verts_starAt {K : SComplex W} {A : Finset W} {a : W} (hA : A ∈ K)
    (hne : A.Nonempty) : a ∈ (K.starAt A a).verts := by
  rw [mem_verts, mem_starAt]
  refine .inr ⟨∅, empty_mem hA, fun h => hne.ne_empty (subset_empty.1 h), by rwa [union_empty],
    insert_empty⟩

/-- A stellar step within `U` is carried by a map injective on `U` to a stellar step. -/
lemma StepWithin.image {U : Finset W} {K L : SComplex W} (h : StepWithin U K L) {g : W → V}
    (hg : Set.InjOn g ↑U) : StellarStep (K.image g) (L.image g) := by
  obtain ⟨hst, hK, hL⟩ := h
  cases hst with
  | @starAt A a hA hne ha =>
    have haU : a ∈ U := hL (apex_mem_verts_starAt hA hne)
    rw [image_starAt hg hK hA]
    refine .starAt (image_mem_image hA) (hne.image g) ?_
    rw [verts_image]
    intro hmem
    obtain ⟨y, hy, hya⟩ := Finset.mem_image.1 hmem
    exact ha (hg (mem_coe.2 (hK hy)) (mem_coe.2 haU) hya ▸ hy)

lemma eqvGen_stepWithin_image {U : Finset W} {K L : SComplex W}
    (h : Relation.EqvGen (StepWithin U) K L) {g : W → V} (hg : Set.InjOn g ↑U) :
    StellarEquivIn (K.image g) (L.image g) := by
  induction h with
  | rel K L h => exact Relation.EqvGen.rel _ _ (h.image hg)
  | refl K => exact StellarEquivIn.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

omit [DecidableEq V] [DecidableEq W] in
/-- For an embedding `f : V ↪ W` with `V` infinite and a finite set `U ⊆ W`, some map `W → V`
inverts `f` and is injective on `U`: the points of `U` outside the image of `f` are sent
injectively to points of `V` whose images lie outside `U`. -/
lemma exists_inv_injOn [Infinite V] (f : V ↪ W) (U : Finset W) :
    ∃ g : W → V, (∀ x, g (f x) = x) ∧ Set.InjOn g ↑U := by
  classical
  set Q : Set W := ↑U \ Set.range f
  set T : Set V := (f ⁻¹' ↑U)ᶜ
  have hQ : Q.Finite := U.finite_toSet.sdiff
  have hT : T.Infinite := (U.finite_toSet.preimage f.injective.injOn).infinite_compl
  obtain ⟨g₀, hg₀T, hg₀⟩ := hQ.exists_injOn_of_encard_le (t := T) (by rw [hT.encard_eq]; exact le_top)
  refine ⟨Function.extend f id g₀, fun x => f.injective.extend_apply _ _ x, ?_⟩
  have hout : ∀ w, w ∉ Set.range f → Function.extend f id g₀ w = g₀ w := fun w hw =>
    Function.extend_apply' _ _ _ (by simpa using hw)
  intro w₁ hw₁ w₂ hw₂ he
  by_cases h₁ : w₁ ∈ Set.range f <;> by_cases h₂ : w₂ ∈ Set.range f
  · obtain ⟨x₁, rfl⟩ := h₁
    obtain ⟨x₂, rfl⟩ := h₂
    rw [f.injective.extend_apply, f.injective.extend_apply] at he
    exact congrArg f he
  · obtain ⟨x₁, rfl⟩ := h₁
    rw [f.injective.extend_apply, hout w₂ h₂] at he
    have hx : f (g₀ w₂) ∈ (U : Set W) := by rw [← show x₁ = g₀ w₂ from he]; exact hw₁
    exact absurd hx (hg₀T ⟨hw₂, h₂⟩)
  · obtain ⟨x₂, rfl⟩ := h₂
    rw [f.injective.extend_apply, hout w₁ h₁] at he
    have hx : f (g₀ w₁) ∈ (U : Set W) := by rw [show g₀ w₁ = x₂ from he]; exact hw₂
    exact absurd hx (hg₀T ⟨hw₁, h₁⟩)
  · rw [hout w₁ h₁, hout w₂ h₂] at he
    exact hg₀ ⟨hw₁, h₁⟩ ⟨hw₂, h₂⟩ he

/-- **Embeddings reflect stellar equivalence** into an infinite vertex type: if the images of `K`
and `L` under an embedding `f` are stellar equivalent inside `W`, then `K` and `L` are stellar
equivalent inside `V`. -/
theorem StellarEquivIn.of_map [Infinite V] {K L : SComplex V} (f : V ↪ W)
    (h : StellarEquivIn (K.map f) (L.map f)) : StellarEquivIn K L := by
  obtain ⟨U, hU⟩ := h.exists_within
  obtain ⟨g, hgf, hg⟩ := exists_inv_injOn f U
  have := eqvGen_stepWithin_image hU hg
  rwa [image_map (fun x _ => hgf x), image_map (fun x _ => hgf x)] at this

/-- The lift of an image is the image of the lift. -/
lemma lift_map (K : SComplex V) (f : V ↪ W) :
    (K.map f).lift = K.lift.map (f.sumMap (Function.Embedding.refl ℕ)) := by
  unfold lift
  rw [map_map, map_map]
  rfl

/-- **Stellar equivalence is invariant under embeddings of the vertices**: `K.map f` and `L.map f`
are stellar equivalent exactly when `K` and `L` are. -/
theorem StellarEquiv.map_iff {K L : SComplex V} (f : V ↪ W) :
    StellarEquiv (K.map f) (L.map f) ↔ StellarEquiv K L := by
  unfold StellarEquiv
  rw [lift_map, lift_map]
  exact ⟨StellarEquivIn.of_map _, fun h => h.map _⟩

end SComplex

end Lightlike.PL
