import Lightlike.PL.SubdivSphere
import Lightlike.PL.CommonSub
import Lightlike.PL.Projective
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Equal spaces and renamed spheres

Two small steps used when a stellar sphere is moved along a radial map.

## Main results

* `SComplex.stellarEquiv_of_space_eq`: given the subdivision statement `SubdivStellar E n`, two
  geometric complexes of dimension at most `n` with the same underlying set are stellar
  equivalent (they have a common subdivision, which is stellar equivalent to each).
* `SComplex.isSB_image`: a stellar sphere stays one under a vertex map that is injective on it.
-/

open Finset

namespace Lightlike.PL
namespace SComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]

/-- **Complexes with the same space are stellar equivalent**, given the subdivision statement in
their dimension. -/
theorem stellarEquiv_of_space_eq {n : ℕ} (hT : SubdivStellar E n) {K L : SComplex E}
    (hK : IsGeom K) (hL : IsGeom L) (h : K.space = L.space) (h₀K : ∅ ∈ K) (h₀L : ∅ ∈ L)
    (hKn : ∀ s ∈ K, #s ≤ n + 1) (hLn : ∀ s ∈ L, #s ≤ n + 1) : StellarEquiv K L := by
  obtain ⟨M, hMK, hML, h₀M⟩ := hK.exists_common_subdivision_empty hL h h₀K h₀L
  exact (hT M K hMK h₀M h₀K hKn).symm.trans (hT M L hML h₀M h₀L hLn)

variable {W : Type*} [DecidableEq W]

/-- **Stellar spheres are invariant under injective renaming of vertices.** -/
theorem isSB_image [Infinite E] [Infinite W] {b : Bool} {m : ℕ} {D : SComplex E} {f : E → W}
    (hf : Set.InjOn f ↑D.verts) (h : IsSB b m D) : IsSB b m (D.image f) := by
  obtain ⟨g, hgf, hg⟩ := exists_leftInv_injOn D.verts f hf ∅
  have hg' : Set.InjOn g ↑(D.image f).verts := by
    rw [verts_image, coe_image]
    simpa using hg
  refine isSB_of_image hg' ?_
  have e : D.image (g ∘ f) = D := image_eq_self_of_fixed (g := g ∘ f) fun x hx => hgf x hx
  rwa [image_image_eq, e]

/-- A complex stellar equivalent to a stellar sphere is a stellar sphere. -/
lemma isSB_of_stellarEquiv [Infinite E] {b : Bool} {m : ℕ} {K L : SComplex E}
    (hKL : StellarEquiv K L) (h : IsSB b m K) : IsSB b m L := by
  have hKL' : StellarEquivIn K L := hKL.in_of_infinite
  rcases h with ⟨A, hA, hK⟩ | ⟨hb, A, hA, hK⟩
  · exact .inl ⟨A, hA, hKL'.symm.trans hK⟩
  · exact .inr ⟨hb, A, hA, hKL'.symm.trans hK⟩

/-- The simplices of a geometric subdivision of the boundary of a `d`-simplex have at most `d`
vertices. -/
lemma card_le_of_subdivision_boundary {d : ℕ} {σ : Finset E} (hσ : #σ = d + 1)
    {β : SComplex E} (hβ : IsSubdivision β (boundary σ)) {s : Finset E} (hs : s ∈ β) :
    #s ≤ d := by
  obtain ⟨t, ht, hst⟩ := hβ.le s hs
  have h1 : #t ≤ d := by
    have := Finset.card_lt_card (mem_boundary.1 ht)
    omega
  refine le_trans (AffineIndependent.card_le_card_of_subset_affineSpan (hβ.geom'.indep s hs) ?_) h1
  exact fun x hx => convexHull_subset_affineSpan (t : Set E) (hst (subset_convexHull ℝ _ hx))

/-- **Spheres from a radial map.** Let `β` be a geometric subdivision of the boundary of a
`d`-simplex `σ`, with a radial scale `m` centred at `v` on which the radial map is injective on the
underlying set of `β`. If a geometric complex `γ` with at most `d` vertices per simplex has the
same underlying set as the radial image of `β`, then `γ` is a stellar sphere of dimension `d`,
provided subdivisions of complexes of dimension `d - 1` are stellar. -/
theorem isSB_of_radial [Infinite E] {d : ℕ} (hT : SubdivStellar E (d - 1)) {σ : Finset E}
    (hσ : AffineIndependent ℝ ((↑) : σ → E)) (hcard : #σ = d + 1) {β : SComplex E}
    (hβ : IsSubdivision β (boundary σ)) (h₀β : ∅ ∈ β) {v : E} {m : E → ℝ} (hr : IsRadialOn β v m)
    (hinj : Set.InjOn (projMap v m) β.space) {γ : SComplex E} (hγ : IsGeom γ)
    (h₀γ : ∅ ∈ γ) (hγn : ∀ s ∈ γ, #s ≤ d) (hspace : γ.space = projMap v m '' β.space) :
    IsSB false d γ := by
  have hδ : IsGeom (β.image (projMap v m)) := isGeom_image_projMap hβ.geom' hr hinj
  have hδn : ∀ s ∈ β.image (projMap v m), #s ≤ d := fun s hs => by
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hs
    exact (Finset.card_image_le).trans (card_le_of_subdivision_boundary hcard hβ ht)
  have hsp : (β.image (projMap v m)).space = γ.space := by
    rw [hspace, hr.space_image hinj]
  have hsp' : StellarEquiv (β.image (projMap v m)) γ := by
    refine stellarEquiv_of_space_eq hT hδ hγ hsp (mem_image.2 ⟨∅, h₀β, by simp⟩) h₀γ (fun s hs => ?_) (fun s hs => ?_)
    · have := hδn s hs; omega
    · have := hγn s hs; omega
  have hβS : IsSB false d β := isSB_of_subdivision_boundary hT hσ hcard hβ h₀β
  have hv : Set.InjOn (projMap v m) ↑β.verts := hinj.mono fun x hx =>
    mem_space.2 ⟨{x}, mem_verts.1 hx, by simp⟩
  exact isSB_of_stellarEquiv hsp' (isSB_image hv hβS)

end SComplex
end Lightlike.PL
