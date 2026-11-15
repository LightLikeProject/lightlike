import Lightlike.PL.StellarImage

/-!
# Spheres and balls are reflected by maps injective on the vertices

If a map `f` of the vertices is injective on the vertices of a complex `D`, and the image `D.image f`
is a stellar sphere or ball inside any vertex type `W`, then `D` is one inside an infinite vertex
type `V`. The chain of stellar moves in `W` involves finitely many vertices, and a map `W → V`
that undoes `f` on `D` and is injective on them renames the chain into `V`.

This is the passage from a geometric complex (vertices are points) back to an abstract complex,
for complexes that are only *isomorphic*, not equal, after choosing vertices.

## Main results

* `SComplex.exists_leftInv_injOn`: a left inverse of `f` on a finite set, injective on a larger
  finite set.
* `SComplex.isSB_of_image`: `IsSB` is reflected by maps injective on the vertices.
-/

open Finset

namespace Lightlike.PL
namespace SComplex

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] [DecidableEq W] in
/-- **A left inverse on a finite set that stays injective on a larger finite set.** For `f`
injective on a finite set `Vs` of an infinite type `V`, some `g : W → V` inverts `f` on `Vs` and is
injective on any given finite `U ⊆ W` together with `f '' Vs`. -/
lemma exists_leftInv_injOn [Infinite V] (Vs : Finset V) (f : V → W) (hf : Set.InjOn f ↑Vs)
    (U : Finset W) :
    ∃ g : W → V, (∀ x ∈ Vs, g (f x) = x) ∧ Set.InjOn g (↑U ∪ f '' ↑Vs) := by
  classical
  set Q : Set W := ↑U \ f '' ↑Vs
  set T : Set V := (↑Vs : Set V)ᶜ
  have hQ : Q.Finite := U.finite_toSet.sdiff
  have hT : T.Infinite := Vs.finite_toSet.infinite_compl
  obtain ⟨g₀, hg₀T, hg₀⟩ := hQ.exists_injOn_of_encard_le (t := T) (by rw [hT.encard_eq]; exact le_top)
  let g : W → V := fun w => if w ∈ f '' ↑Vs then Function.invFunOn f ↑Vs w else g₀ w
  have hgin : ∀ w ∈ f '' (↑Vs : Set V), g w = Function.invFunOn f ↑Vs w := fun w hw => by
    simp only [g, hw, ↓reduceIte]
  have hgout : ∀ w, w ∉ f '' (↑Vs : Set V) → g w = g₀ w := fun w hw => by
    simp only [g, hw, ↓reduceIte]
  refine ⟨g, fun x hx => ?_, ?_⟩
  · rw [hgin _ ⟨x, hx, rfl⟩]
    exact hf.leftInvOn_invFunOn hx
  · have hmem : ∀ w ∈ f '' (↑Vs : Set V), g w ∈ (↑Vs : Set V) := fun w hw => by
      rw [hgin w hw]
      exact Function.invFunOn_mem (by simpa using hw)
    have hnot : ∀ w ∈ (↑U : Set W) ∪ f '' ↑Vs, w ∉ f '' (↑Vs : Set V) → g w ∉ (↑Vs : Set V) := by
      intro w hw hwn
      rw [hgout w hwn]
      exact hg₀T ⟨hw.resolve_right hwn, hwn⟩
    intro w₁ h₁ w₂ h₂ he
    by_cases a₁ : w₁ ∈ f '' (↑Vs : Set V) <;> by_cases a₂ : w₂ ∈ f '' (↑Vs : Set V)
    · obtain ⟨x₁, hx₁, rfl⟩ := a₁
      obtain ⟨x₂, hx₂, rfl⟩ := a₂
      rw [hgin _ ⟨x₁, hx₁, rfl⟩, hgin _ ⟨x₂, hx₂, rfl⟩, hf.leftInvOn_invFunOn hx₁,
        hf.leftInvOn_invFunOn hx₂] at he
      exact congrArg f he
    · exact absurd (he ▸ hmem _ a₁) (hnot _ h₂ a₂)
    · exact absurd (he ▸ hmem _ a₂) (hnot _ h₁ a₁)
    · rw [hgout _ a₁, hgout _ a₂] at he
      exact hg₀ ⟨h₁.resolve_right a₁, a₁⟩ ⟨h₂.resolve_right a₂, a₂⟩ he

omit [DecidableEq W] in
/-- A map fixing the vertices does not change the complex. -/
lemma image_eq_self_of_fixed {K : SComplex V} {g : V → V} (h : ∀ x ∈ K.verts, g x = x) :
    K.image g = K := by
  have := image_map (K := K) (f := Function.Embedding.refl V) (g := g) h
  rwa [map_refl] at this

omit [DecidableEq V] in
/-- The image of an image is the image under the composite. -/
lemma image_image_eq {U : Type*} [DecidableEq U] (K : SComplex V) (f : V → W) (g : W → U) :
    (K.image f).image g = K.image (g ∘ f) := by
  refine ext_mem fun s => ?_
  simp only [mem_image]
  constructor
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨t, ht, Finset.image_image.symm⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨_, ⟨t, ht, rfl⟩, Finset.image_image⟩

omit [DecidableEq W] in
/-- A map carries the simplex on `A` to the simplex on its image. -/
lemma image_simplex (A : Finset W) (g : W → V) : (simplex A).image g = simplex (A.image g) := by
  refine ext_mem fun s => ?_
  rw [mem_image, mem_simplex]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact Finset.image_subset_image (mem_simplex.1 ht)
  · intro hs
    refine ⟨A.filter fun x => g x ∈ s, mem_simplex.2 (filter_subset _ _), ?_⟩
    ext y
    simp only [Finset.mem_image, mem_filter]
    constructor
    · rintro ⟨x, ⟨-, hx⟩, rfl⟩
      exact hx
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (hs hy)
      exact ⟨x, ⟨hx, hy⟩, rfl⟩

/-- A map injective on `A` carries the boundary of the simplex on `A` to the boundary of the
simplex on its image. -/
lemma image_boundary (A : Finset W) {g : W → V} (hg : Set.InjOn g ↑A) :
    (boundary A).image g = boundary (A.image g) := by
  refine ext_mem fun s => ?_
  rw [mem_image, mem_boundary]
  constructor
  · rintro ⟨t, ht, rfl⟩
    have hts : t ⊂ A := mem_boundary.1 ht
    refine Finset.ssubset_iff_subset_ne.2 ⟨Finset.image_subset_image hts.subset, fun hEq => ?_⟩
    refine hts.ne (Finset.Subset.antisymm hts.subset fun a ha => ?_)
    have : g a ∈ t.image g := hEq ▸ Finset.mem_image_of_mem g ha
    obtain ⟨b, hb, hba⟩ := Finset.mem_image.1 this
    exact (hg (hts.subset hb) ha hba) ▸ hb
  · intro hs
    have hsub : s ⊆ A.image g := hs.subset
    refine ⟨A.filter fun x => g x ∈ s, mem_boundary.2 ?_, ?_⟩
    · refine Finset.ssubset_iff_subset_ne.2 ⟨filter_subset _ _, fun hEq => ?_⟩
      have : A.image g ⊆ s := by
        intro y hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
        have : x ∈ A.filter fun x => g x ∈ s := by rw [hEq]; exact hx
        exact (mem_filter.1 this).2
      exact hs.ne (Finset.Subset.antisymm hsub this)
    · ext y
      simp only [Finset.mem_image, mem_filter]
      constructor
      · rintro ⟨x, ⟨-, hx⟩, rfl⟩
        exact hx
      · intro hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (hsub hy)
        exact ⟨x, ⟨hx, hy⟩, rfl⟩

/-- **Renaming a stellar equivalence into `V`.** If the image of `D` under a map `f` injective on
the vertices of `D` is stellar equivalent to `L` inside `W`, then `D` is stellar equivalent to the
image of `L` under a suitable map `g : W → V`, injective on the finite set `A`. -/
lemma exists_rename [Infinite V] {D : SComplex V} {f : V → W} (hf : Set.InjOn f ↑D.verts)
    {L : SComplex W} (h : StellarEquivIn (D.image f) L) (A : Finset W) :
    ∃ g : W → V, Set.InjOn g ↑A ∧ StellarEquivIn D (L.image g) := by
  obtain ⟨U, hU⟩ := h.exists_within
  obtain ⟨g, hgf, hg⟩ := exists_leftInv_injOn D.verts f hf (U ∪ A)
  have hU' : Set.InjOn g ↑U := hg.mono fun x hx => Or.inl (by simpa using Or.inl hx)
  have := eqvGen_stepWithin_image hU hU'
  rw [image_image_eq] at this
  have e : D.image (g ∘ f) = D := image_eq_self_of_fixed (fun x hx => hgf x hx)
  rw [e] at this
  exact ⟨g, hg.mono fun x hx => Or.inl (by simpa using Or.inr hx), this⟩

/-- **Spheres and balls are reflected by maps injective on the vertices.** If `f` is injective on
the vertices of `D` and `D.image f` is a stellar sphere or ball (inside any vertex type), then
`D` is one, inside the infinite vertex type `V`. -/
theorem isSB_of_image [Infinite V] {b : Bool} {m : ℕ} {D : SComplex V} {f : V → W}
    (hf : Set.InjOn f ↑D.verts) (h : IsSB b m (D.image f)) : IsSB b m D := by
  rcases h with ⟨A, hA, hDA⟩ | ⟨hb, A, hA, hDA⟩
  · obtain ⟨g, hg, hD⟩ := exists_rename hf hDA A
    rw [image_boundary A hg] at hD
    exact .inl ⟨A.image g, by rw [Finset.card_image_of_injOn hg, hA], hD⟩
  · obtain ⟨g, hg, hD⟩ := exists_rename hf hDA A
    rw [image_simplex] at hD
    exact .inr ⟨hb, A.image g, by rw [Finset.card_image_of_injOn hg, hA], hD⟩

end SComplex
end Lightlike.PL
