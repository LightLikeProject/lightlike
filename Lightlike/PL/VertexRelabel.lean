import Lightlike.PL.ImageSB
import Lightlike.PL.PachnerPL

/-!
# Relabelling the vertices by maps injective on the vertex set

A **relabelling** of a complex `K` on `V` along `f : V → W` is the image `K.image f` for a map that
is injective on the vertices of `K` only (`Set.InjOn f K.verts`), not an embedding of the vertex
types; `IsRelabelling K C` says that `C` is such a relabelling of `K`.

* `StellarEquivIn.image_iso`: two injective images of one complex inside an infinite vertex type
  are stellar equivalent (they are isomorphic).
* `StellarEquiv.image`: relabellings carry stellar equivalent complexes to stellar equivalent
  complexes, across vertex types.
* `IsClosedCombManifold.image`: a relabelling of a closed combinatorial `n`-manifold is one.
* `bistellarEquiv_iff_of_isRelabelling`: **transport of bistellar equivalence**: if `C`, `D` (on `W`)
  are relabellings of `A`, `B` (on `V`) and `A` is a closed combinatorial `n`-manifold, then `A` and
  `B` are bistellar equivalent exactly when `C` and `D` are.
-/

open Finset

namespace Lightlike.PL

namespace SComplex

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

/-- `C` is a **relabelling** of `K`: the image of `K` under a map injective on the vertices of `K`. -/
def IsRelabelling (K : SComplex V) (C : SComplex W) : Prop :=
  ∃ f : V → W, Set.InjOn f K.verts ∧ C = K.image f

/-- Images only depend on the map on the vertices. -/
lemma image_congr_verts {K : SComplex V} {f g : V → W} (h : ∀ x ∈ K.verts, f x = g x) :
    K.image f = K.image g := by
  refine ext_mem fun s => ?_
  simp only [mem_image]
  refine exists_congr fun t => and_congr_right fun ht => ?_
  rw [Finset.image_congr fun x hx => h x (subset_verts ht hx)]

/-- The lift of an image is the image of the lift. -/
lemma lift_image (K : SComplex V) (f : V → W) : (K.image f).lift = K.lift.image (Sum.map f id) := by
  unfold lift
  refine ext_mem fun s => ?_
  simp only [mem_map, mem_image]
  constructor
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨t.map Function.Embedding.inl, ⟨t, ht, rfl⟩, ?_⟩
    ext y; simp
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨t.image f, ⟨t, ht, rfl⟩, ?_⟩
    ext y; simp

omit [DecidableEq W] in
/-- A relabelling of `K` lifts to a map injective on the vertices of the lift. -/
lemma injOn_sumMap {K : SComplex V} {f : V → W} (hf : Set.InjOn f K.verts) :
    Set.InjOn (Sum.map f (id : ℕ → ℕ)) (K.lift.verts : Set (V ⊕ ℕ)) := by
  rw [verts_lift]
  rintro _ hx _ hy he
  simp only [coe_map, Function.Embedding.inl_apply, Set.mem_image, mem_coe] at hx hy
  obtain ⟨x, hx, rfl⟩ := hx
  obtain ⟨y, hy, rfl⟩ := hy
  simp only [Sum.map_inl, Sum.inl.injEq] at he
  rw [hf hx hy he]

/-- **Isomorphic images are stellar equivalent**: two images of one complex under maps injective on
its vertices, inside an infinite vertex type. -/
theorem StellarEquivIn.image_iso [Infinite W] [Nonempty V] (P : SComplex V) {φ ψ : V → W}
    (hφ : Set.InjOn φ P.verts) (hψ : Set.InjOn ψ P.verts) :
    StellarEquivIn (P.image φ) (P.image ψ) := by
  classical
  set θ : W → W := ψ ∘ Function.invFunOn φ P.verts with hθ
  have hθφ : ∀ x ∈ P.verts, θ (φ x) = ψ x := fun x hx => by
    simp only [hθ, Function.comp_apply, hφ.leftInvOn_invFunOn (mem_coe.2 hx)]
  have hinj : Set.InjOn θ (P.image φ).verts := by
    rw [verts_image]
    intro a ha b hb hab
    simp only [coe_image, Set.mem_image, mem_coe] at ha hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    rw [hθφ x hx, hθφ y hy] at hab
    rw [hψ (mem_coe.2 hx) (mem_coe.2 hy) hab]
  have himg : (P.image ψ).faces = (P.image φ).faces.image (Finset.image θ) := by
    have := image_image_eq P φ θ
    rw [image_congr_verts (f := θ ∘ φ) (g := ψ) (fun x hx => hθφ x hx)] at this
    rw [← this]; rfl
  obtain ⟨e, he⟩ := exists_perm_eq_of_iso hinj himg
  rw [← he]
  exact StellarEquivIn.map_perm _ e

/-- **An inverse relabelling**: for `f` injective on the vertices of `P`, a map back that is
injective on the vertices of `P.image f` and undoes the relabelling. -/
lemma exists_inv_relabel [Nonempty V] {P : SComplex V} {f : V → W} (hf : Set.InjOn f P.verts) :
    ∃ g : W → V, Set.InjOn g (P.image f).verts ∧ (P.image f).image g = P := by
  classical
  set g : W → V := Function.invFunOn f P.verts with hg
  have hgf : ∀ x ∈ P.verts, g (f x) = x := fun x hx => hf.leftInvOn_invFunOn (mem_coe.2 hx)
  refine ⟨g, ?_, ?_⟩
  · rw [verts_image]
    intro a ha b hb hab
    simp only [coe_image, Set.mem_image, mem_coe] at ha hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    rw [hgf x hx, hgf y hy] at hab
    rw [hab]
  · rw [image_image_eq]
    exact image_eq_self_of_fixed fun x hx => hgf x hx

/-- **Relabellings preserve stellar equivalence inside an infinite type**: if `P` and `Q` are
stellar equivalent inside `V` and `φ`, `ψ` are injective on their vertices, then `P.image φ` and
`Q.image ψ` are stellar equivalent inside the infinite type `W`. -/
theorem StellarEquivIn.image₂ [Infinite W] [Nonempty V] {P Q : SComplex V} (h : StellarEquivIn P Q)
    {φ ψ : V → W} (hφ : Set.InjOn φ P.verts) (hψ : Set.InjOn ψ Q.verts) :
    StellarEquivIn (P.image φ) (Q.image ψ) := by
  classical
  obtain ⟨φ', hφ', hφ'P⟩ := exists_inv_relabel hφ
  have h' : StellarEquivIn ((P.image φ).image φ') Q := by rw [hφ'P]; exact h
  obtain ⟨g', hg', hD⟩ := exists_rename hφ' h' Q.verts
  exact hD.trans (StellarEquivIn.image_iso Q hg' hψ)

/-- **Relabellings preserve stellar equivalence**, across vertex types: if `K` and `L` are stellar
equivalent and `f`, `g` are injective on the vertices of `K` and of `L`, then `K.image f` and
`L.image g` are stellar equivalent. -/
theorem StellarEquiv.image {K L : SComplex V} (h : StellarEquiv K L) {f g : V → W}
    (hf : Set.InjOn f K.verts) (hg : Set.InjOn g L.verts) : StellarEquiv (K.image f) (L.image g) := by
  unfold StellarEquiv
  rw [lift_image, lift_image]
  exact StellarEquivIn.image₂ h (injOn_sumMap hf) (injOn_sumMap hg)

/-- Under a map injective on the vertices, a vertex set of `K` is a face of the image exactly when it
is a face of `K`. -/
lemma image_mem_image_iff {K : SComplex V} {f : V → W} (hf : Set.InjOn f K.verts) {t : Finset V}
    (ht : (t : Set V) ⊆ K.verts) : t.image f ∈ K.image f ↔ t ∈ K := by
  refine ⟨fun h => ?_, image_mem_image⟩
  obtain ⟨u, hu, he⟩ := mem_image.1 h
  have hu' : (u : Set V) ⊆ K.verts := fun x hx => subset_verts hu hx
  rw [← coe_inj, coe_image, coe_image, hf.image_eq_image_iff hu' ht, coe_inj] at he
  rwa [he] at hu

/-- **Links commute with relabellings**: the link of `f v` in `K.image f` is the image of the link
of `v`. -/
lemma image_link_singleton {K : SComplex V} {f : V → W} (hf : Set.InjOn f K.verts) {v : V}
    (hv : v ∈ K.verts) : (K.image f).link {f v} = (K.link {v}).image f := by
  have sub : ∀ t ∈ K, (t : Set V) ⊆ K.verts := fun t ht x hx => subset_verts ht hx
  refine ext_mem fun s => ?_
  rw [mem_link']
  constructor
  · rintro ⟨hd, hs⟩
    obtain ⟨t, ht, rfl⟩ := mem_image.1 (down_mem hs subset_union_right)
    have hvt : v ∉ t := fun h => disjoint_singleton_left.1 hd (Finset.mem_image_of_mem f h)
    have hsub : (({v} ∪ t : Finset V) : Set V) ⊆ K.verts := by
      rw [coe_union, coe_singleton]
      exact Set.union_subset (Set.singleton_subset_iff.2 (mem_coe.2 hv)) (sub t ht)
    rw [← image_singleton f v, ← image_union, image_mem_image_iff hf hsub] at hs
    exact mem_image.2 ⟨t, mem_link'.2 ⟨disjoint_singleton_left.2 hvt, hs⟩, rfl⟩
  · intro hs
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hs
    obtain ⟨hd, hvt⟩ := mem_link'.1 ht
    refine ⟨disjoint_singleton_left.2 fun hm => ?_, ?_⟩
    · obtain ⟨y, hy, hyv⟩ := Finset.mem_image.1 hm
      have hyK : y ∈ K.verts := subset_verts (down_mem hvt subset_union_right) hy
      rw [hf (mem_coe.2 hyK) (mem_coe.2 hv) hyv] at hy
      exact disjoint_singleton_left.1 hd hy
    · rw [← image_singleton f v, ← image_union]
      exact image_mem_image hvt

/-- **Relabellings preserve closed combinatorial manifolds**: if `K` is a closed combinatorial
`n`-manifold and `f` is injective on the vertices of `K`, then `K.image f` is one. -/
theorem IsClosedCombManifold.image {n : ℕ} {K : SComplex V} (hK : IsClosedCombManifold n K) {f : V → W}
    (hf : Set.InjOn f K.verts) : IsClosedCombManifold n (K.image f) := by
  rw [isClosedCombManifold_iff] at hK ⊢
  intro w hw
  rw [verts_image, Finset.mem_image] at hw
  obtain ⟨v, hv, rfl⟩ := hw
  rw [image_link_singleton hf hv]
  have hfl : Set.InjOn f (K.link {v}).verts := hf.mono fun x hx => by
    have h1 := mem_verts.1 (mem_coe.1 hx)
    exact subset_verts (mem_link'.1 h1).2 (mem_union_right _ (mem_singleton_self x))
  obtain ⟨g, hg, hgK⟩ := exists_inv_relabel (injOn_sumMap hfl)
  rw [← lift_image] at hg hgK
  obtain ⟨A, hA, hLA⟩ := hK v hv
  have hsb : IsSB false n (((K.link {v}).image f).lift.image g) := by rw [hgK]; exact .inl ⟨A, hA, hLA⟩
  rcases isSB_of_image hg hsb with h | ⟨hb, -⟩
  · exact h
  · exact absurd hb (by decide)

/-- **Transport of bistellar equivalence along relabellings**: let `C` and `D` be relabellings of
`A` and `B` (by maps injective on their vertices, into another vertex type). If `A` is a closed
combinatorial `n`-manifold, then `A` and `B` are bistellar equivalent exactly when `C` and `D` are. -/
theorem bistellarEquiv_iff_of_isRelabelling {n : ℕ} {A B : SComplex V} {C D : SComplex W}
    (hAC : IsRelabelling A C) (hBD : IsRelabelling B D) (hA : IsClosedCombManifold n A) :
    BistellarEquiv A B ↔ BistellarEquiv C D := by
  obtain ⟨f, hf, rfl⟩ := hAC
  obtain ⟨g, hg, rfl⟩ := hBD
  have hC := hA.image hf
  rw [← pachner hA, ← pachner hC]
  refine ⟨fun h => h.image hf hg, fun h => ?_⟩
  have hf' := injOn_sumMap hf
  have hg' := injOn_sumMap hg
  obtain ⟨f', hf'i, hf'A⟩ := exists_inv_relabel hf'
  obtain ⟨g', hg'i, hg'B⟩ := exists_inv_relabel hg'
  unfold StellarEquiv at h ⊢
  rw [lift_image, lift_image] at h
  have := StellarEquivIn.image₂ h hf'i hg'i
  rwa [hf'A, hg'B] at this

end SComplex

end Lightlike.PL
