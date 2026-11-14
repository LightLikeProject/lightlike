import Lightlike.PL.StellarImage
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.Basic.Real.Basic

/-!
# Geometric realisations, subdivisions and PL homeomorphisms

A complex `K : SComplex E` whose vertices are points of a real vector space `E` is **geometric**
(`IsGeom`) when every face is affinely independent and any two faces meet in the convex hull of
their common vertices; these are the conditions of Mathlib's `Geometry.SimplicialComplex`
(`IsGeom.toSimplicialComplex`). Its **underlying set** `|K|` (`space`) is the union of the convex
hulls of the faces. All the combinatorics of `SComplex` (stellar subdivision, links, joins)
applies to geometric complexes unchanged, because the vertices are the points themselves.

* `real K`: the **geometric realisation** of an abstract complex `K : SComplex V`, with the vertex
  `v` at the basis vector `Finsupp.single v 1` of `V →₀ ℝ`. It is geometric (`isGeom_real`), and
  its points are the nonnegative finitely supported functions with sum one whose support is a
  face (`mem_space_real`): the barycentric coordinates.
* `IsSubdivision K' K`: `K'` and `K` are geometric with the same underlying set, and every simplex
  of `K'` lies in a simplex of `K`.
* `IsPLMap K f`: `f` is affine on every simplex of some subdivision of `K`.
* `IsPLHomeo K L f`: `f` is piecewise linear on `K` and maps `|K|` bijectively onto `|L|`.
* `PLHomeomorphic K L`: the realisations of the abstract complexes `K` and `L` are PL
  homeomorphic.

No topology on `E` is used: in finite dimensions a map that is affine on each simplex of a finite
complex is continuous on the underlying set, so these are the usual notions of PL topology
(Rourke–Sanderson, *Introduction to piecewise-linear topology*, ch. 2; Lickorish, *Simplicial
moves on complexes and manifolds*, §4).
-/

open Finset

namespace Lightlike.PL

namespace SComplex

section Geometric

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- The **underlying set** `|K|` of a complex whose vertices are points of a real vector space:
the union of the convex hulls of its faces. -/
def space (K : SComplex E) : Set E := ⋃ s ∈ K, convexHull ℝ (s : Set E)

lemma mem_space {K : SComplex E} {x : E} :
    x ∈ K.space ↔ ∃ s ∈ K, x ∈ convexHull ℝ (s : Set E) := by
  simp only [space, Set.mem_iUnion, exists_prop]

lemma convexHull_subset_space {K : SComplex E} {s : Finset E} (hs : s ∈ K) :
    convexHull ℝ (s : Set E) ⊆ K.space := fun _ hx => mem_space.2 ⟨s, hs, hx⟩

/-- A complex whose vertices are points of a real vector space is **geometric** when every face
is affinely independent and any two faces meet in the convex hull of their common vertices. -/
structure IsGeom (K : SComplex E) : Prop where
  /-- Every face is affinely independent. -/
  indep : ∀ s ∈ K, AffineIndependent ℝ ((↑) : s → E)
  /-- Two faces meet in the convex hull of their common vertices. -/
  inter : ∀ s ∈ K, ∀ t ∈ K,
    convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆ convexHull ℝ ((s : Set E) ∩ t)

/-- A geometric complex as a Mathlib `Geometry.SimplicialComplex` (which has no empty face). -/
noncomputable def IsGeom.toSimplicialComplex {K : SComplex E} (hK : IsGeom K) :
    Geometry.SimplicialComplex ℝ E :=
  Geometry.SimplicialComplex.ofErase {s | s ∈ K} (fun s hs => hK.indep s hs)
    (fun _ _ hts hs => down_mem hs hts) (fun s hs t ht => hK.inter s hs t ht)

/-- The Mathlib simplicial complex of a geometric complex has the same underlying set. -/
lemma IsGeom.space_toSimplicialComplex {K : SComplex E} (hK : IsGeom K) :
    hK.toSimplicialComplex.space = K.space := by
  ext x
  rw [Geometry.SimplicialComplex.mem_space_iff, mem_space]
  constructor
  · rintro ⟨s, hs, hx⟩
    exact ⟨s, hs.1, hx⟩
  · rintro ⟨s, hs, hx⟩
    refine ⟨s, ⟨hs, fun h => ?_⟩, hx⟩
    rw [Set.mem_singleton_iff] at h
    subst h
    simp at hx

/-- A complex whose vertices are affinely independent is geometric. -/
lemma IsGeom.of_indep [DecidableEq E] {K : SComplex E}
    (h : AffineIndependent ℝ ((↑) : K.verts → E)) : IsGeom K where
  indep _ hs := AffineIndependent.mono (t := (K.verts : Set E)) h (coe_subset.2 (subset_verts hs))
  inter _ hs _ ht := (h.convexHull_inter (subset_verts hs) (subset_verts ht)).symm.subset

/-! ## Subdivisions and PL maps -/

/-- `K'` is a **subdivision** of `K`: both are geometric, they have the same underlying set, and
every simplex of `K'` lies in a simplex of `K`. -/
structure IsSubdivision (K' K : SComplex E) : Prop where
  /-- The subdividing complex is geometric. -/
  geom' : IsGeom K'
  /-- The subdivided complex is geometric. -/
  geom : IsGeom K
  /-- The underlying sets agree. -/
  space_eq : K'.space = K.space
  /-- Every simplex of `K'` lies in a simplex of `K`. -/
  le : ∀ s ∈ K', ∃ t ∈ K, convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E)

/-- A geometric complex subdivides itself. -/
lemma IsSubdivision.refl {K : SComplex E} (hK : IsGeom K) : IsSubdivision K K :=
  ⟨hK, hK, rfl, fun s hs => ⟨s, hs, le_rfl⟩⟩

/-- A subdivision of a subdivision is a subdivision. -/
lemma IsSubdivision.trans {K'' K' K : SComplex E} (h₁ : IsSubdivision K'' K')
    (h₂ : IsSubdivision K' K) : IsSubdivision K'' K := by
  refine ⟨h₁.geom', h₂.geom, h₁.space_eq.trans h₂.space_eq, fun s hs => ?_⟩
  obtain ⟨t, ht, hst⟩ := h₁.le s hs
  obtain ⟨u, hu, htu⟩ := h₂.le t ht
  exact ⟨u, hu, hst.trans htu⟩

/-- A map `f : E → F` is **piecewise linear on** `K` when it is affine on every simplex of some
subdivision of `K`. -/
def IsPLMap (K : SComplex E) (f : E → F) : Prop :=
  ∃ K' : SComplex E, IsSubdivision K' K ∧
    ∀ s ∈ K', ∃ g : E →ᵃ[ℝ] F, Set.EqOn f g (convexHull ℝ (s : Set E))

/-- An affine map is piecewise linear on every geometric complex. -/
lemma IsPLMap.of_affine {K : SComplex E} (hK : IsGeom K) (g : E →ᵃ[ℝ] F) : IsPLMap K g :=
  ⟨K, .refl hK, fun _ _ => ⟨g, Set.eqOn_refl _ _⟩⟩

/-- A map piecewise linear on `K` is piecewise linear on every complex that `K` subdivides. -/
lemma IsPLMap.of_subdivision {K' K : SComplex E} {f : E → F} (hf : IsPLMap K' f)
    (h : IsSubdivision K' K) : IsPLMap K f := by
  obtain ⟨K'', h'', hg⟩ := hf
  exact ⟨K'', h''.trans h, hg⟩

/-- A **PL homeomorphism** from `|K|` onto `|L|`: a map that is piecewise linear on `K` and maps
`|K|` bijectively onto `|L|`, for geometric complexes `K` and `L`. -/
structure IsPLHomeo (K : SComplex E) (L : SComplex F) (f : E → F) : Prop where
  /-- The map is piecewise linear on `K` (in particular `K` is geometric). -/
  pl : IsPLMap K f
  /-- The target complex is geometric. -/
  geom : IsGeom L
  /-- The map is a bijection between the underlying sets. -/
  bij : Set.BijOn f K.space L.space

lemma IsPLMap.isGeom {K : SComplex E} {f : E → F} (hf : IsPLMap K f) : IsGeom K := by
  obtain ⟨_, h, -⟩ := hf
  exact h.geom

/-- The identity is a PL homeomorphism of every geometric complex. -/
lemma IsPLHomeo.refl {K : SComplex E} (hK : IsGeom K) : IsPLHomeo K K id :=
  ⟨IsPLMap.of_affine hK (AffineMap.id ℝ E), hK, Set.bijOn_id _⟩

/-- **A subdivision is PL homeomorphic to the subdivided complex**, by the identity. -/
lemma IsSubdivision.isPLHomeo {K' K : SComplex E} (h : IsSubdivision K' K) :
    IsPLHomeo K K' id := by
  refine ⟨IsPLMap.of_affine h.geom (AffineMap.id ℝ E), h.geom', ?_⟩
  rw [h.space_eq]
  exact Set.bijOn_id _

end Geometric

/-! ## The geometric realisation of an abstract complex -/

section Realisation

variable {V : Type*} [DecidableEq V]

/-- The **vertex embedding** of `V` into `V →₀ ℝ`: the vertex `v` goes to the basis vector
`Finsupp.single v 1`. -/
noncomputable def vertexEmb (V : Type*) : V ↪ (V →₀ ℝ) :=
  ⟨fun v => Finsupp.single v 1, Finsupp.single_left_injective one_ne_zero⟩

omit [DecidableEq V] in
lemma vertexEmb_apply (v : V) : vertexEmb V v = Finsupp.single v 1 := rfl

/-- The **geometric realisation** of an abstract complex: the vertex `v` is placed at the basis
vector `Finsupp.single v 1` of `V →₀ ℝ`, and every face spans a simplex. -/
noncomputable def real (K : SComplex V) : SComplex (V →₀ ℝ) := K.map (vertexEmb V)

lemma mem_real {K : SComplex V} {s : Finset (V →₀ ℝ)} :
    s ∈ K.real ↔ ∃ t ∈ K, t.map (vertexEmb V) = s := mem_map

/-- A point lies in the simplex spanned by the basis vectors of `s` exactly when its coordinates
are nonnegative, vanish outside `s` and sum to one over `s`. -/
lemma mem_convexHull_vertexEmb {s : Finset V} {x : V →₀ ℝ} :
    x ∈ convexHull ℝ ((s.map (vertexEmb V) : Finset (V →₀ ℝ)) : Set (V →₀ ℝ)) ↔
      (∀ v, 0 ≤ x v) ∧ (∀ v ∉ s, x v = 0) ∧ ∑ v ∈ s, x v = 1 := by
  constructor
  · intro hx
    refine convexHull_min (t := {x : V →₀ ℝ | (∀ v, 0 ≤ x v) ∧ (∀ v ∉ s, x v = 0) ∧
      ∑ v ∈ s, x v = 1}) ?_ ?_ hx
    · intro y hy
      rw [coe_map, Set.mem_image] at hy
      obtain ⟨v, hv, rfl⟩ := hy
      rw [mem_coe] at hv
      refine ⟨fun w => ?_, fun w hw => ?_, ?_⟩
      · rw [vertexEmb_apply, Finsupp.single_apply]
        split_ifs <;> norm_num
      · have hvw : v ≠ w := fun h => hw (h ▸ hv)
        simp [vertexEmb_apply, hvw]
      · simp [vertexEmb_apply, Finsupp.single_apply, hv]
    · intro y hy z hz a b ha hb hab
      refine ⟨fun w => ?_, fun w hw => ?_, ?_⟩
      · simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        exact add_nonneg (mul_nonneg ha (hy.1 w)) (mul_nonneg hb (hz.1 w))
      · simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          hy.2.1 w hw, hz.2.1 w hw, mul_zero, add_zero]
      · simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hy.2.2, hz.2.2, mul_one,
          mul_one, hab]
  · rintro ⟨h0, hs, h1⟩
    have hx : x = ∑ v ∈ s, x v • vertexEmb V v := by
      ext w
      simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply,
        vertexEmb_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq']
      split_ifs with hw
      · rfl
      · exact hs w hw
    rw [hx]
    refine (convex_convexHull ℝ _).sum_mem (fun v _ => h0 v) h1 fun v hv => ?_
    exact subset_convexHull ℝ _ (by rw [coe_map]; exact Set.mem_image_of_mem _ hv)

/-- **The realisation is geometric**: the basis vectors are linearly, hence affinely, independent. -/
theorem isGeom_real (K : SComplex V) : IsGeom K.real := by
  apply IsGeom.of_indep
  have hai : AffineIndependent ℝ (vertexEmb V) :=
    (Finsupp.linearIndependent_single_one (R := ℝ) (ι := V)).affineIndependent
  refine AffineIndependent.mono (t := Set.range (vertexEmb V)) hai.range fun x hx => ?_
  rw [mem_coe, real, verts_map, Finset.mem_map] at hx
  obtain ⟨v, -, rfl⟩ := hx
  exact Set.mem_range_self v

/-- **The points of the realisation** are the nonnegative finitely supported functions on `V`
whose support is a face of `K` and whose values sum to one: barycentric coordinates. -/
theorem mem_space_real {K : SComplex V} {x : V →₀ ℝ} :
    x ∈ K.real.space ↔ (∀ v, 0 ≤ x v) ∧ x.support ∈ K ∧ ∑ v ∈ x.support, x v = 1 := by
  rw [mem_space]
  constructor
  · rintro ⟨s', hs', hx⟩
    obtain ⟨s, hs, rfl⟩ := mem_real.1 hs'
    obtain ⟨h0, hout, h1⟩ := mem_convexHull_vertexEmb.1 hx
    have hsupp : x.support ⊆ s := fun v hv => by
      by_contra h
      exact Finsupp.mem_support_iff.1 hv (hout v h)
    refine ⟨h0, down_mem hs hsupp, ?_⟩
    rw [← h1]
    exact Finset.sum_subset hsupp fun v _ hv => Finsupp.notMem_support_iff.1 hv
  · rintro ⟨h0, hK, h1⟩
    exact ⟨x.support.map (vertexEmb V), mem_real.2 ⟨_, hK, rfl⟩,
      mem_convexHull_vertexEmb.2 ⟨h0, fun v hv => Finsupp.notMem_support_iff.1 hv, h1⟩⟩

/-- Abstract complexes are **PL homeomorphic** when their geometric realisations are: some map
`V →₀ ℝ → W →₀ ℝ` is piecewise linear on `real K` and maps `|real K|` bijectively onto
`|real L|`. -/
def PLHomeomorphic {W : Type*} [DecidableEq W] (K : SComplex V) (L : SComplex W) : Prop :=
  ∃ f : (V →₀ ℝ) → (W →₀ ℝ), IsPLHomeo K.real L.real f

/-- Every complex is PL homeomorphic to itself, by the identity. -/
lemma PLHomeomorphic.refl (K : SComplex V) : PLHomeomorphic K K :=
  ⟨id, IsPLHomeo.refl (isGeom_real K)⟩

end Realisation

end SComplex

end Lightlike.PL
