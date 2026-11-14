import Lightlike.PL.CommonSub

/-!
# Images of complexes under simplexwise-affine maps

A map `f : E → F` is **affine on** a complex `K` when it agrees with an affine map on each closed
simplex of `K`. If `K` is geometric and `f` is affine on `K` and injective on `|K|`, then the
images of the simplices of `K` form a geometric complex `K.image f` whose underlying set is
`f '' |K|`; the inverse of `f` is affine on `K.image f`; and every subdivision of `K.image f` pulls
back to a subdivision of `K` (Rourke–Sanderson, *Introduction to piecewise-linear topology*,
§2). These are the facts behind the inverse and the composite of PL homeomorphisms.

## Main results

* `affineIndependent_image_of_injOn`: an affine map injective on a simplex keeps its vertices
  affinely independent.
* `exists_affineMap_eqOn`: an affine map can take any values on an affinely independent set.
* `SComplex.isGeom_image`, `SComplex.space_image`: the image complex.
* `SComplex.isAffineOn_invFunOn`: the inverse is affine on the image complex.
* `SComplex.isSubdivision_image_invFunOn`: subdivisions of the image pull back.
-/

open Finset

namespace Lightlike.PL

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-! ## Affine maps on simplices -/

/-- An affine map commutes with convex combinations (weights summing to one). -/
lemma map_sum_smul_of_sum_eq_one (g : E →ᵃ[ℝ] F) {s : Finset E} {u : E → ℝ}
    (hu : ∑ v ∈ s, u v = 1) : g (∑ v ∈ s, u v • v) = ∑ v ∈ s, u v • g v := by
  have h := s.map_affineCombination (fun v => v) u hu g
  rw [s.affineCombination_eq_linear_combination _ _ hu,
    s.affineCombination_eq_linear_combination _ _ hu] at h
  exact h

/-- Two affine maps that agree on the vertices of a simplex agree on the closed simplex. -/
lemma eqOn_convexHull_of_eqOn {A B : E →ᵃ[ℝ] F} {s : Finset E} (h : ∀ v ∈ s, A v = B v) :
    Set.EqOn A B (convexHull ℝ (s : Set E)) := by
  intro x hx
  obtain ⟨w, -, hw1, rfl⟩ := Finset.mem_convexHull'.1 hx
  rw [map_sum_smul_of_sum_eq_one A hw1, map_sum_smul_of_sum_eq_one B hw1]
  exact sum_congr rfl fun v hv => by rw [h v hv]

/-- The weight criterion for the affine independence of a finite set of points. -/
lemma affineIndependent_of_forall {t : Finset F}
    (h : ∀ w : F → ℝ, ∑ y ∈ t, w y = 0 → ∑ y ∈ t, w y • y = 0 → ∀ y ∈ t, w y = 0) :
    AffineIndependent ℝ ((↑) : t → F) := by
  classical
  rw [affineIndependent_iff_of_fintype]
  intro w hw0 hws i
  rw [Finset.weightedVSub_eq_linear_combination _ hw0] at hws
  let W : F → ℝ := fun y => if hy : y ∈ t then w ⟨y, hy⟩ else 0
  have h0 : ∑ y ∈ t, W y = 0 := by
    rw [← Finset.sum_coe_sort t W]
    simpa [W] using hw0
  have h1 : ∑ y ∈ t, W y • y = 0 := by
    rw [← Finset.sum_coe_sort t (fun y => W y • y)]
    simpa [W] using hws
  simpa [W] using h W h0 h1 i i.2

/-- **An affine map that is injective on a closed simplex keeps its vertices affinely
independent.** The proof splits a vanishing weighted sum into its positive and negative parts,
which give two points of the simplex with the same image. -/
lemma affineIndependent_image_of_injOn [DecidableEq F] {s : Finset E}
    (hs : AffineIndependent ℝ ((↑) : s → E)) (g : E →ᵃ[ℝ] F)
    (hg : Set.InjOn g (convexHull ℝ (s : Set E))) :
    AffineIndependent ℝ ((↑) : (s.image g) → F) := by
  have hgs : Set.InjOn g (s : Set E) := hg.mono (subset_convexHull ℝ _)
  refine affineIndependent_of_forall fun W hW0 hW1 => ?_
  rw [sum_image hgs] at hW0 hW1
  let P : E → ℝ := fun v => max (W (g v)) 0
  let N : E → ℝ := fun v => max (-W (g v)) 0
  have hPN : ∀ v, W (g v) = P v - N v := fun v => (max_zero_sub_max_neg_zero_eq_self _).symm
  have hP0 : ∀ v, 0 ≤ P v := fun v => le_max_right _ _
  have hN0 : ∀ v, 0 ≤ N v := fun v => le_max_right _ _
  have hsum : ∑ v ∈ s, P v = ∑ v ∈ s, N v := by
    have h : ∑ v ∈ s, (P v - N v) = 0 := by simpa only [hPN] using hW0
    rw [sum_sub_distrib] at h
    linarith
  have hsmul : ∑ v ∈ s, P v • g v = ∑ v ∈ s, N v • g v := by
    have h : ∑ v ∈ s, (P v - N v) • g v = 0 := by simpa only [hPN] using hW1
    simp_rw [sub_smul, sum_sub_distrib] at h
    exact sub_eq_zero.1 h
  suffices hPN' : ∀ v ∈ s, P v = N v by
    intro y hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hy
    rw [hPN, hPN' v hv, sub_self]
  rcases (sum_nonneg fun v _ => hP0 v : 0 ≤ ∑ v ∈ s, P v).eq_or_lt with hc | hc
  · have hP := (sum_eq_zero_iff_of_nonneg fun v _ => hP0 v).1 hc.symm
    have hN := (sum_eq_zero_iff_of_nonneg fun v _ => hN0 v).1 (hsum ▸ hc.symm)
    intro v hv
    rw [hP v hv, hN v hv]
  set c := ∑ v ∈ s, P v with hcdef
  have hc0 : c⁻¹ ≠ 0 := inv_ne_zero hc.ne'
  have hu₁ : ∑ v ∈ s, c⁻¹ * P v = 1 := by rw [← mul_sum, inv_mul_cancel₀ hc.ne']
  have hu₂ : ∑ v ∈ s, c⁻¹ * N v = 1 := by rw [← mul_sum, ← hsum, inv_mul_cancel₀ hc.ne']
  have hp : ∑ v ∈ s, (c⁻¹ * P v) • v ∈ convexHull ℝ (s : Set E) :=
    Finset.mem_convexHull'.2 ⟨_, fun v _ => mul_nonneg (inv_nonneg.2 hc.le) (hP0 v), hu₁, rfl⟩
  have hq : ∑ v ∈ s, (c⁻¹ * N v) • v ∈ convexHull ℝ (s : Set E) :=
    Finset.mem_convexHull'.2 ⟨_, fun v _ => mul_nonneg (inv_nonneg.2 hc.le) (hN0 v), hu₂, rfl⟩
  have heq : g (∑ v ∈ s, (c⁻¹ * P v) • v) = g (∑ v ∈ s, (c⁻¹ * N v) • v) := by
    rw [map_sum_smul_of_sum_eq_one g hu₁, map_sum_smul_of_sum_eq_one g hu₂]
    simp_rw [mul_smul, ← smul_sum]
    rw [hsmul]
  have hw := hs.eq_of_sum_eq_sum_subtype (w₁ := fun v => c⁻¹ * P v) (w₂ := fun v => c⁻¹ * N v)
    (hu₁.trans hu₂.symm) (hg hp hq heq)
  exact fun v hv => mul_left_cancel₀ hc0 (hw v hv)

/-- **An affine map can take any values on an affinely independent set.** The differences from a
base vertex are linearly independent, so a linear map with the required values exists on their
span and extends to the whole space. -/
lemma exists_affineMap_eqOn {t : Finset F} (ht : AffineIndependent ℝ ((↑) : t → F))
    (φ : F → E) : ∃ B : F →ᵃ[ℝ] E, ∀ y ∈ t, B y = φ y := by
  classical
  rcases t.eq_empty_or_nonempty with rfl | ⟨y₀, hy₀⟩
  · exact ⟨AffineMap.const ℝ F (0 : E), by simp⟩
  have hli := (affineIndependent_iff_linearIndependent_vsub ℝ _ (⟨y₀, hy₀⟩ : t)).1 ht
  obtain ⟨L, hL⟩ := LinearMap.exists_extend
    ((Finsupp.linearCombination ℝ fun i : {x : t // x ≠ ⟨y₀, hy₀⟩} => φ i.1 - φ y₀) ∘ₗ hli.repr)
  refine ⟨AffineMap.mk' (fun y => L (y - y₀) + φ y₀) L y₀ fun y => by simp, fun y hy => ?_⟩
  by_cases hyy : y = y₀
  · subst hyy
    simp
  have hne : (⟨y, hy⟩ : t) ≠ ⟨y₀, hy₀⟩ := fun h => hyy (congrArg Subtype.val h)
  have hmem : (y - y₀ : F) ∈ Submodule.span ℝ (Set.range fun i : {x : t // x ≠ ⟨y₀, hy₀⟩} =>
      ((i.1 : F) -ᵥ ((⟨y₀, hy₀⟩ : t) : F))) :=
    Submodule.subset_span ⟨⟨⟨y, hy⟩, hne⟩, rfl⟩
  have hLy := LinearMap.congr_fun hL ⟨_, hmem⟩
  rw [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.comp_apply,
    hli.repr_eq_single ⟨⟨y, hy⟩, hne⟩ ⟨_, hmem⟩ rfl, Finsupp.linearCombination_single,
    one_smul] at hLy
  simp only [AffineMap.coe_mk', hLy, sub_add_cancel]

namespace SComplex

/-! ## The image complex -/

/-- A map is **affine on** a complex when it agrees with an affine map on each closed
simplex. -/
def IsAffineOn (K : SComplex E) (f : E → F) : Prop :=
  ∀ s ∈ K, ∃ g : E →ᵃ[ℝ] F, Set.EqOn f g (convexHull ℝ (s : Set E))

variable {K : SComplex E} {f : E → F}

/-- Being affine on a complex passes to every complex whose simplices lie in its simplices. -/
lemma IsAffineOn.mono {K' : SComplex E} (hf : IsAffineOn K f)
    (h : ∀ s ∈ K', ∃ t ∈ K, convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E)) :
    IsAffineOn K' f := by
  intro s hs
  obtain ⟨t, ht, hst⟩ := h s hs
  obtain ⟨g, hg⟩ := hf t ht
  exact ⟨g, hg.mono hst⟩

/-- A PL map is affine on some subdivision. -/
lemma isPLMap_iff {f : E → F} :
    IsPLMap K f ↔ ∃ K' : SComplex E, IsSubdivision K' K ∧ IsAffineOn K' f := Iff.rfl

variable [DecidableEq F]

/-- A map affine on a simplex sends the closed simplex onto the closed simplex of the image
vertices. -/
lemma IsAffineOn.image_convexHull (hf : IsAffineOn K f) {s : Finset E} (hs : s ∈ K) :
    f '' convexHull ℝ (s : Set E) = convexHull ℝ (↑(s.image f) : Set F) := by
  obtain ⟨g, hg⟩ := hf s hs
  rw [hg.image_eq, AffineMap.image_convexHull, coe_image,
    (hg.mono (subset_convexHull ℝ _)).image_eq]

/-- The underlying set of the image complex is the image of the underlying set. -/
lemma IsAffineOn.space_image (hf : IsAffineOn K f) : (K.image f).space = f '' K.space := by
  ext y
  simp only [mem_space, mem_image, Set.mem_image]
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, hy⟩
    rw [← hf.image_convexHull hs] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, ⟨s, hs, hx⟩, rfl⟩
  · rintro ⟨x, ⟨s, hs, hx⟩, rfl⟩
    exact ⟨_, ⟨s, hs, rfl⟩, hf.image_convexHull hs ▸ Set.mem_image_of_mem f hx⟩

/-- **The image of a geometric complex under a map affine on it and injective on its underlying
set is a geometric complex.** -/
theorem isGeom_image (hK : IsGeom K) (hf : IsAffineOn K f) (hinj : Set.InjOn f K.space) :
    IsGeom (K.image f) where
  indep s' hs' := by
    obtain ⟨s, hs, rfl⟩ := mem_image.1 hs'
    obtain ⟨g, hg⟩ := hf s hs
    have hsub : convexHull ℝ (s : Set E) ⊆ K.space := fun x hx => mem_space.2 ⟨s, hs, hx⟩
    rw [Finset.image_congr (hg.mono (subset_convexHull ℝ _))]
    exact affineIndependent_image_of_injOn (hK.indep s hs) g ((hinj.mono hsub).congr hg)
  inter s' hs' t' ht' := by
    classical
    obtain ⟨s, hs, rfl⟩ := mem_image.1 hs'
    obtain ⟨t, ht, rfl⟩ := mem_image.1 ht'
    rintro y ⟨hys, hyt⟩
    rw [← hf.image_convexHull hs] at hys
    rw [← hf.image_convexHull ht] at hyt
    obtain ⟨a, ha, rfl⟩ := hys
    obtain ⟨b, hb, hab⟩ := hyt
    have hba : b = a := hinj (mem_space.2 ⟨t, ht, hb⟩) (mem_space.2 ⟨s, hs, ha⟩) hab
    subst hba
    have hst : s ∩ t ∈ K := down_mem hs inter_subset_left
    have hy : f b ∈ convexHull ℝ (↑((s ∩ t).image f) : Set F) := by
      rw [← hf.image_convexHull hst, coe_inter]
      exact Set.mem_image_of_mem f (hK.inter s hs t ht ⟨ha, hb⟩)
    refine convexHull_mono ?_ hy
    rw [← coe_inter]
    exact coe_subset.2 (image_inter_subset _ _ _)

/-! ## The inverse map -/

/-- **The inverse of a map affine on `K` and injective on `|K|` is affine on the image
complex.** On a simplex where `f` is the affine map `A`, the inverse is an affine map `B` with
`B (A v) = v` on the vertices, which exists because the image vertices are affinely
independent. -/
theorem isAffineOn_invFunOn (hK : IsGeom K) (hf : IsAffineOn K f)
    (hinj : Set.InjOn f K.space) : IsAffineOn (K.image f) (Function.invFunOn f K.space) := by
  intro s' hs'
  obtain ⟨s, hs, rfl⟩ := mem_image.1 hs'
  obtain ⟨A, hA⟩ := hf s hs
  have hsub : convexHull ℝ (s : Set E) ⊆ K.space := fun x hx => mem_space.2 ⟨s, hs, hx⟩
  have hAinj : Set.InjOn A (convexHull ℝ (s : Set E)) := (hinj.mono hsub).congr hA
  have hind := affineIndependent_image_of_injOn (hK.indep s hs) A hAinj
  obtain ⟨B, hB⟩ := exists_affineMap_eqOn hind (Function.invFunOn f K.space)
  have hleft := hinj.leftInvOn_invFunOn
  have hBA : Set.EqOn (B.comp A) (AffineMap.id ℝ E) (convexHull ℝ (s : Set E)) := by
    refine eqOn_convexHull_of_eqOn fun v hv => ?_
    have hvs := subset_convexHull ℝ (s : Set E) (mem_coe.2 hv)
    rw [AffineMap.comp_apply, hB _ (Finset.mem_image_of_mem A hv), ← hA hvs,
      hleft (hsub hvs), AffineMap.id_apply]
  refine ⟨B, fun y hy => ?_⟩
  rw [← hf.image_convexHull hs] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  rw [hleft (hsub hx), hA hx]
  exact (hBA hx).symm

/-- **Subdivisions of the image pull back.** If `N` subdivides `K.image f`, its image under the
inverse of `f` subdivides `K`. -/
theorem isSubdivision_image_invFunOn [DecidableEq E] (hK : IsGeom K) (hf : IsAffineOn K f)
    (hinj : Set.InjOn f K.space) {N : SComplex F} (hN : IsSubdivision N (K.image f)) :
    IsSubdivision (N.image (Function.invFunOn f K.space)) K := by
  have hg := (isAffineOn_invFunOn hK hf hinj).mono hN.le
  have hleft := hinj.leftInvOn_invFunOn
  have hNsp : N.space = f '' K.space := hN.space_eq.trans hf.space_image
  have hginj : Set.InjOn (Function.invFunOn f K.space) N.space :=
    hNsp ▸ Function.invFunOn_injOn_image f K.space
  refine ⟨isGeom_image hN.geom' hg hginj, hK, ?_, fun u hu => ?_⟩
  · rw [hg.space_image, hNsp, hleft.image_image]
  · obtain ⟨v, hv, rfl⟩ := mem_image.1 hu
    obtain ⟨t', ht', hvt⟩ := hN.le v hv
    obtain ⟨t, ht, rfl⟩ := mem_image.1 ht'
    have hsub : convexHull ℝ (t : Set E) ⊆ K.space := fun x hx => mem_space.2 ⟨t, ht, hx⟩
    refine ⟨t, ht, ?_⟩
    rw [← hg.image_convexHull hv]
    calc Function.invFunOn f K.space '' convexHull ℝ (v : Set F)
        ⊆ Function.invFunOn f K.space '' convexHull ℝ (↑(t.image f) : Set F) :=
          Set.image_mono hvt
      _ = convexHull ℝ (t : Set E) := by
          rw [← hf.image_convexHull ht, (hleft.mono hsub).image_image]


/-! ## Inverses and composites of PL homeomorphisms -/

variable {G : Type*} [AddCommGroup G] [Module ℝ G]

/-- **The inverse of a PL homeomorphism is a PL homeomorphism.** If `f` is affine on a
subdivision `K'` of `K`, the inverse is affine on `f(K')` and hence on a common subdivision of
`f(K')` and `L`. -/
theorem IsPLHomeo.symm [DecidableEq E] {L : SComplex F} (h : IsPLHomeo K L f) :
    IsPLHomeo L K (Function.invFunOn f K.space) := by
  obtain ⟨K', hK', hf⟩ := isPLMap_iff.1 h.pl
  have hinj : Set.InjOn f K'.space := hK'.space_eq ▸ h.bij.injOn
  have hsp : (K'.image f).space = L.space := by
    rw [hf.space_image, hK'.space_eq, h.bij.image_eq]
  obtain ⟨N, hN₁, hN₂⟩ :=
    (isGeom_image hK'.geom' hf hinj).exists_common_subdivision h.geom hsp
  have hg := (isAffineOn_invFunOn hK'.geom' hf hinj).mono hN₁.le
  rw [hK'.space_eq] at hg
  exact ⟨⟨N, hN₂, hg⟩, h.pl.isGeom, h.bij.symm h.bij.invOn_invFunOn.symm⟩

/-- **The composite of PL homeomorphisms is a PL homeomorphism.** With `f` affine on `K'` and `g`
affine on `L'`, take a common subdivision `N` of `f(K')` and `L'` and pull it back to `K'`: the
composite is affine on each pulled-back simplex. -/
theorem IsPLHomeo.trans [DecidableEq E] {L : SComplex F} {M : SComplex G} {g : F → G}
    (h₁ : IsPLHomeo K L f) (h₂ : IsPLHomeo L M g) : IsPLHomeo K M (g ∘ f) := by
  obtain ⟨K', hK', hf⟩ := isPLMap_iff.1 h₁.pl
  obtain ⟨L', hL', hg⟩ := isPLMap_iff.1 h₂.pl
  have hinj : Set.InjOn f K'.space := hK'.space_eq ▸ h₁.bij.injOn
  have hsp : (K'.image f).space = L'.space := by
    rw [hf.space_image, hK'.space_eq, h₁.bij.image_eq, hL'.space_eq]
  obtain ⟨N, hN₁, hN₂⟩ :=
    (isGeom_image hK'.geom' hf hinj).exists_common_subdivision hL'.geom' hsp
  have hP := isSubdivision_image_invFunOn hK'.geom' hf hinj hN₁
  have hfP := hf.mono hP.le
  have hinv := (isAffineOn_invFunOn hK'.geom' hf hinj).mono hN₁.le
  have hgN := hg.mono hN₂.le
  have hright := (Set.surjOn_image f K'.space).rightInvOn_invFunOn
  have hNsp : N.space = f '' K'.space := hN₁.space_eq.trans hf.space_image
  refine ⟨⟨_, hP.trans hK', fun u hu => ?_⟩, h₂.geom, h₂.bij.comp h₁.bij⟩
  obtain ⟨v, hv, rfl⟩ := mem_image.1 hu
  obtain ⟨A, hA⟩ := hfP _ hu
  obtain ⟨B, hB⟩ := hgN v hv
  have hvsub : convexHull ℝ (v : Set F) ⊆ f '' K'.space :=
    fun y hy => hNsp ▸ mem_space.2 ⟨v, hv, hy⟩
  have himg : f '' convexHull ℝ (↑(v.image (Function.invFunOn f K'.space)) : Set E) =
      convexHull ℝ (v : Set F) := by
    rw [← hinv.image_convexHull hv]
    exact Set.LeftInvOn.image_image (hright.mono hvsub)
  refine ⟨B.comp A, fun x hx => ?_⟩
  have hfx : f x ∈ convexHull ℝ (v : Set F) := himg ▸ Set.mem_image_of_mem f hx
  rw [Function.comp_apply, hB hfx, AffineMap.comp_apply, hA hx]

end SComplex

/-! ## PL homeomorphism of abstract complexes is an equivalence relation -/

namespace SComplex

variable {V W X : Type*} [DecidableEq V] [DecidableEq W] [DecidableEq X]

/-- PL homeomorphism of realisations is symmetric. -/
theorem PLHomeomorphic.symm {K : SComplex V} {L : SComplex W} (h : PLHomeomorphic K L) :
    PLHomeomorphic L K := by
  classical
  obtain ⟨f, hf⟩ := h
  exact ⟨_, hf.symm⟩

/-- PL homeomorphism of realisations is transitive. -/
theorem PLHomeomorphic.trans {K : SComplex V} {L : SComplex W} {M : SComplex X}
    (h₁ : PLHomeomorphic K L) (h₂ : PLHomeomorphic L M) : PLHomeomorphic K M := by
  classical
  obtain ⟨f, hf⟩ := h₁
  obtain ⟨g, hg⟩ := h₂
  exact ⟨_, hf.trans hg⟩

end SComplex

end Lightlike.PL
