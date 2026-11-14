import Lightlike.PL.Image

/-!
# Stellar equivalence implies PL homeomorphism

This file proves the easy direction of Newman's theorem: stellar equivalent complexes are PL
homeomorphic (Lickorish, *Simplicial moves on complexes and manifolds*, 1999, §§2–4).

Both steps are explicit linear maps of the realisations `real K ⊆ V →₀ ℝ`, checked in barycentric
coordinates (`mem_space_real`):

* `realMap f` for an embedding `f : V ↪ W` of vertex types sends the basis vector of `v` to that
  of `f v`; it is a PL homeomorphism `real K → real (K.map f)`.
* `starMap A a` sends the basis vector of the new vertex `a` to the barycentre of `A` and fixes the
  other basis vectors; it is a PL homeomorphism `real (starAt K A a) → real K`. The new
  coordinate is recovered from the image as `#A` times the smallest coordinate on `A`, because
  every face of `starAt K A a` misses a vertex of `A`.

Since PL homeomorphism is an equivalence relation (`PLHomeomorphic.symm`, `.trans`), induction
over the stellar moves gives `PLHomeomorphic.of_stellarEquiv`.

## Main results

* `SComplex.isPLHomeo_realMap`, `SComplex.PLHomeomorphic.map`: isomorphic complexes.
* `SComplex.isPLHomeo_starMap`, `SComplex.PLHomeomorphic.starAt`: a stellar subdivision is PL
  homeomorphic to the complex.
* `SComplex.PLHomeomorphic.of_stellarEquiv`: stellar equivalence implies PL homeomorphism.
* `SComplex.StellarEquiv.of_plHomeomorphic_of_subdivision`: the converse follows once every
  subdivision of a geometric complex is known to be stellar equivalent to it.
-/

open Finset

namespace Lightlike.PL

namespace SComplex

variable {V : Type*} [DecidableEq V]

/-! ## Total mass -/

/-- The **total mass** of a finitely supported function: the sum of its values. On the
realisation of a complex it is the sum of the barycentric coordinates, which is one. -/
noncomputable def mass : (V →₀ ℝ) →ₗ[ℝ] ℝ := Finsupp.linearCombination ℝ fun _ => (1 : ℝ)

omit [DecidableEq V] in
lemma mass_apply (x : V →₀ ℝ) : mass x = ∑ v ∈ x.support, x v := by
  simp [mass, Finsupp.linearCombination_apply, Finsupp.sum]

omit [DecidableEq V] in
lemma mass_single (v : V) (r : ℝ) : mass (Finsupp.single v r) = r := by
  simp [mass]

/-- The points of `|real K|`, with the total mass in place of the sum over the support. -/
lemma mem_space_real_iff {K : SComplex V} {x : V →₀ ℝ} :
    x ∈ K.real.space ↔ (∀ v, 0 ≤ x v) ∧ x.support ∈ K ∧ mass x = 1 := by
  rw [mem_space_real, mass_apply]

/-! ## Isomorphic complexes -/

section Map

variable {W : Type*} [DecidableEq W]

/-- The linear map of realisations induced by an embedding `f : V ↪ W` of vertex types: the basis
vector of `v` goes to the basis vector of `f v`. -/
noncomputable def realMap (f : V ↪ W) : (V →₀ ℝ) →ₗ[ℝ] (W →₀ ℝ) := Finsupp.lmapDomain ℝ ℝ f

omit [DecidableEq V] [DecidableEq W] in
lemma realMap_apply (f : V ↪ W) (x : V →₀ ℝ) : realMap f x = Finsupp.embDomain f x := by
  rw [Finsupp.embDomain_eq_mapDomain]
  rfl

/-- **Isomorphic complexes have PL homeomorphic realisations**: `realMap f` maps `|real K|`
bijectively onto `|real (K.map f)|`. -/
theorem isPLHomeo_realMap (K : SComplex V) (f : V ↪ W) :
    IsPLHomeo K.real (K.map f).real (realMap f) := by
  refine ⟨IsPLMap.of_affine (isGeom_real K) (realMap f).toAffineMap, isGeom_real _, ?_, ?_, ?_⟩
  · intro x hx
    rw [mem_space_real_iff] at hx ⊢
    obtain ⟨h0, hK, h1⟩ := hx
    rw [realMap_apply]
    refine ⟨fun w => ?_, ?_, ?_⟩
    · by_cases hw : w ∈ Set.range f
      · obtain ⟨v, rfl⟩ := hw
        rw [Finsupp.embDomain_apply_self]
        exact h0 v
      · rw [Finsupp.embDomain_of_notMem_range _ _ _ hw]
    · rw [Finsupp.support_embDomain]
      exact SComplex.mem_map.2 ⟨_, hK, rfl⟩
    · rw [mass_apply, Finsupp.support_embDomain, Finset.sum_map]
      simp only [Finsupp.embDomain_apply_self]
      rwa [← mass_apply]
  · intro x _ y _ h
    rw [realMap_apply, realMap_apply] at h
    exact Finsupp.embDomain_injective f h
  · intro y hy
    rw [mem_space_real_iff] at hy
    obtain ⟨h0, hK, h1⟩ := hy
    obtain ⟨t, ht, hts⟩ := SComplex.mem_map.1 hK
    have hsub : (y.support : Set W) ⊆ Set.range f := by
      intro w hw
      rw [mem_coe, ← hts, Finset.mem_map] at hw
      obtain ⟨v, -, rfl⟩ := hw
      exact ⟨v, rfl⟩
    set x := Finsupp.comapDomain f y f.injective.injOn
    have hxy : Finsupp.embDomain f x = y := Finsupp.embDomain_comapDomain hsub
    refine ⟨x, ?_, by rw [realMap_apply, hxy]⟩
    have hsx : x.support = t := by
      apply Finset.map_injective f
      rw [← Finsupp.support_embDomain, hxy, hts]
    rw [mem_space_real_iff]
    refine ⟨fun v => ?_, hsx ▸ ht, ?_⟩
    · rw [← Finsupp.embDomain_apply_self f x v, hxy]
      exact h0 _
    · rw [← h1, mass_apply, mass_apply, ← hxy, Finsupp.support_embDomain, Finset.sum_map]
      simp only [Finsupp.embDomain_apply_self]

/-- Isomorphic complexes are PL homeomorphic. -/
theorem PLHomeomorphic.map (K : SComplex V) (f : V ↪ W) : PLHomeomorphic K (K.map f) :=
  ⟨_, isPLHomeo_realMap K f⟩

/-- A complex is PL homeomorphic to its lift to `V ⊕ ℕ`. -/
theorem PLHomeomorphic.lift (K : SComplex V) : PLHomeomorphic K K.lift :=
  PLHomeomorphic.map K _

end Map

/-! ## A stellar subdivision -/

section Star

variable {K : SComplex V} {A : Finset V} {a : V}

/-- The correction vector `e_a − b_A`, where `b_A` is the barycentre of the basis vectors of `A`. -/
noncomputable def starVec (A : Finset V) (a : V) : V →₀ ℝ :=
  Finsupp.single a 1 - (#A : ℝ)⁻¹ • ∑ w ∈ A, Finsupp.single w 1

/-- The linear map `real (starAt K A a) → real K` that sends the basis vector of the new vertex
`a` to the barycentre of `A` and fixes the other basis vectors. -/
noncomputable def starMap (A : Finset V) (a : V) : (V →₀ ℝ) →ₗ[ℝ] (V →₀ ℝ) :=
  LinearMap.id - (Finsupp.lapply a).smulRight (starVec A a)

omit [DecidableEq V] in
lemma starMap_apply (x : V →₀ ℝ) : starMap A a x = x - x a • starVec A a := by
  simp [starMap]

lemma sum_single_one_apply (A : Finset V) (w : V) :
    (∑ u ∈ A, Finsupp.single u (1 : ℝ)) w = if w ∈ A then 1 else 0 := by
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  exact Finset.sum_ite_eq' A w fun _ => (1 : ℝ)

lemma starVec_self (haA : a ∉ A) : starVec A a a = 1 := by
  rw [starVec, Finsupp.coe_sub, Finsupp.coe_smul, Pi.sub_apply, Pi.smul_apply,
    sum_single_one_apply, ite_eq_right haA, Finsupp.single_eq_same, smul_zero, sub_zero]

lemma starVec_of_ne {w : V} (hw : w ≠ a) :
    starVec A a w = -(if w ∈ A then (#A : ℝ)⁻¹ else 0) := by
  simp only [starVec, Finsupp.coe_sub, Finsupp.coe_smul, Pi.sub_apply, Pi.smul_apply,
    sum_single_one_apply, Finsupp.single_apply, ite_eq_right (Ne.symm hw), smul_eq_mul, mul_ite,
    mul_one, mul_zero, zero_sub]

omit [DecidableEq V] in
lemma mass_starVec (hne : A.Nonempty) : mass (starVec A a) = 0 := by
  have hA : (#A : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (card_ne_zero.2 hne)
  simp only [starVec, map_sub, map_smul, map_sum, mass_single, sum_const, nsmul_eq_mul, mul_one,
    smul_eq_mul, inv_mul_cancel₀ hA, sub_self]

lemma starMap_self (haA : a ∉ A) (x : V →₀ ℝ) : starMap A a x a = 0 := by
  rw [starMap_apply, Finsupp.coe_sub, Finsupp.coe_smul, Pi.sub_apply, Pi.smul_apply,
    starVec_self haA, smul_eq_mul, mul_one, sub_self]

lemma starMap_of_ne {w : V} (hw : w ≠ a) (x : V →₀ ℝ) :
    starMap A a x w = x w + x a * (if w ∈ A then (#A : ℝ)⁻¹ else 0) := by
  rw [starMap_apply, Finsupp.coe_sub, Finsupp.coe_smul, Pi.sub_apply, Pi.smul_apply,
    starVec_of_ne hw, smul_eq_mul]
  ring

omit [DecidableEq V] in
lemma mass_starMap (hne : A.Nonempty) (x : V →₀ ℝ) : mass (starMap A a x) = mass x := by
  rw [starMap_apply, map_sub, map_smul, mass_starVec hne, smul_zero, sub_zero]

lemma exists_zero_of_mem_starAt (haA : a ∉ A) {x : V →₀ ℝ} (hx : x.support ∈ K.starAt A a) :
    ∃ w ∈ A, x w = 0 := by
  obtain ⟨w, hw, hwx⟩ := Finset.not_subset.1 (not_subset_of_mem_starAt haA hx)
  exact ⟨w, hw, Finsupp.notMem_support_iff.1 hwx⟩

/-- **A stellar subdivision is PL homeomorphic to the complex**: `starMap A a` maps
`|real (starAt K A a)|` bijectively onto `|real K|`. -/
theorem isPLHomeo_starMap (hA : A ∈ K) (hne : A.Nonempty) (ha : a ∉ K.verts) :
    IsPLHomeo (K.starAt A a).real K.real (starMap A a) := by
  have haA : a ∉ A := notMem_of_notMem_verts ha hA
  have hcard : (0 : ℝ) < #A := Nat.cast_pos.2 (card_pos.2 hne)
  have hzero : ∀ z : V →₀ ℝ, z.support ∈ K → z a = 0 := fun z hz =>
    Finsupp.notMem_support_iff.1 (notMem_of_notMem_verts ha hz)
  refine ⟨IsPLMap.of_affine (isGeom_real _) (starMap A a).toAffineMap, isGeom_real K, ?_, ?_, ?_⟩
  · -- maps into `|real K|`
    intro x hx
    rw [mem_space_real_iff] at hx ⊢
    obtain ⟨h0, hS, h1⟩ := hx
    refine ⟨fun w => ?_, ?_, by rw [mass_starMap hne, h1]⟩
    · by_cases hw : w = a
      · rw [hw, starMap_self haA]
      · rw [starMap_of_ne hw]
        have : 0 ≤ if w ∈ A then (#A : ℝ)⁻¹ else 0 := by split_ifs <;> positivity
        exact add_nonneg (h0 w) (mul_nonneg (h0 a) this)
    · rcases mem_starAt.1 hS with ⟨hK, -⟩ | ⟨t, -, -, hAtK, hts⟩
      · have : starMap A a x = x := by rw [starMap_apply, hzero x hK, zero_smul, sub_zero]
        rwa [this]
      · refine down_mem hAtK fun w hw => ?_
        have hwa : w ≠ a := by
          rintro rfl
          exact Finsupp.mem_support_iff.1 hw (starMap_self haA x)
        by_cases hwA : w ∈ A
        · exact mem_union_left _ hwA
        · rw [Finsupp.mem_support_iff, starMap_of_ne hwa, ite_eq_right hwA, mul_zero, add_zero] at hw
          have : w ∈ insert a t := hts ▸ Finsupp.mem_support_iff.2 hw
          exact mem_union_right _ ((mem_insert.1 this).resolve_left hwa)
  · -- injective
    intro x hx y hy hxy
    rw [mem_space_real_iff] at hx hy
    have key : ∀ x y : V →₀ ℝ, x.support ∈ K.starAt A a → (∀ v, 0 ≤ y v) →
        starMap A a x = starMap A a y → y a ≤ x a := by
      intro x y hx hy0 hxy
      obtain ⟨w, hwA, hw0⟩ := exists_zero_of_mem_starAt haA hx
      have hwa : w ≠ a := fun h => haA (h ▸ hwA)
      have := congrArg (· w) hxy
      simp only [starMap_of_ne hwa, ite_eq_left hwA, hw0, zero_add] at this
      have h' : y a * (#A : ℝ)⁻¹ ≤ x a * (#A : ℝ)⁻¹ := by
        rw [this]
        exact le_add_of_nonneg_left (hy0 w)
      exact le_of_mul_le_mul_right h' (inv_pos.2 hcard)
    have hxa : x a = y a :=
      le_antisymm (key y x hy.2.1 hx.1 hxy.symm) (key x y hx.2.1 hy.1 hxy)
    ext w
    by_cases hw : w = a
    · rw [hw, hxa]
    · have := congrArg (· w) hxy
      simp only [starMap_of_ne hw, hxa] at this
      exact add_right_cancel this
  · -- onto `|real K|`
    intro z hz
    rw [mem_space_real_iff] at hz
    obtain ⟨h0, hK, h1⟩ := hz
    obtain ⟨w₀, hw₀, hmin⟩ := A.exists_min_image z hne
    set l : ℝ := #A * z w₀
    set x := z + l • starVec A a
    have hxa : x a = l := by
      simp only [x, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply,
        hzero z hK, starVec_self haA, smul_eq_mul, mul_one, zero_add]
    have hxw : ∀ w, w ≠ a → x w = z w - if w ∈ A then z w₀ else 0 := by
      intro w hw
      simp only [x, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply,
        starVec_of_ne hw, smul_eq_mul, l]
      split_ifs
      · field_simp
        ring
      · ring
    refine ⟨x, ?_, ?_⟩
    · rw [mem_space_real_iff]
      refine ⟨fun w => ?_, ?_, ?_⟩
      · by_cases hw : w = a
        · rw [hw, hxa]
          exact mul_nonneg hcard.le (h0 w₀)
        · rw [hxw w hw]
          split_ifs with hwA
          · exact sub_nonneg.2 (hmin w hwA)
          · rw [sub_zero]
            exact h0 w
      · by_cases hz₀ : z w₀ = 0
        · have : x = z := by simp only [x, l, hz₀, mul_zero, zero_smul, add_zero]
          rw [this]
          exact mem_starAt.2 (.inl ⟨hK, fun h => Finsupp.mem_support_iff.1 (h hw₀) hz₀⟩)
        · have hpos : 0 < z w₀ := lt_of_le_of_ne (h0 w₀) (Ne.symm hz₀)
          have hAz : A ⊆ z.support := fun w hw =>
            Finsupp.mem_support_iff.2 (ne_of_gt (lt_of_lt_of_le hpos (hmin w hw)))
          have hax : a ∈ x.support := by
            rw [Finsupp.mem_support_iff, hxa]
            exact ne_of_gt (mul_pos hcard hpos)
          have hsub : x.support.erase a ⊆ z.support := by
            intro w hw
            have hwa := ne_of_mem_erase hw
            have hxw' := Finsupp.mem_support_iff.1 (mem_of_mem_erase hw)
            by_cases hwA : w ∈ A
            · exact hAz hwA
            · rw [hxw w hwa, ite_eq_right hwA, sub_zero] at hxw'
              exact Finsupp.mem_support_iff.2 hxw'
          have hw₀x : w₀ ∉ x.support.erase a := by
            intro h
            have := Finsupp.mem_support_iff.1 (mem_of_mem_erase h)
            rw [hxw w₀ (ne_of_mem_erase h), ite_eq_left hw₀, sub_self] at this
            exact this rfl
          refine mem_starAt.2 (.inr ⟨x.support.erase a, down_mem hK hsub,
            fun h => hw₀x (h hw₀), down_mem hK (union_subset hAz hsub), insert_erase hax⟩)
      · rw [map_add, map_smul, mass_starVec hne, smul_zero, add_zero, h1]
    · rw [starMap_apply, hxa]
      simp only [x, add_sub_cancel_right]

/-- **A stellar subdivision is PL homeomorphic to the complex** (Lickorish, §3). -/
theorem PLHomeomorphic.starAt (hA : A ∈ K) (hne : A.Nonempty) (ha : a ∉ K.verts) :
    PLHomeomorphic K (K.starAt A a) :=
  PLHomeomorphic.symm ⟨_, isPLHomeo_starMap hA hne ha⟩

end Star

/-! ## Stellar equivalence -/

/-- Complexes that are stellar equivalent inside `V` are PL homeomorphic. -/
theorem PLHomeomorphic.of_stellarEquivIn {K L : SComplex V} (h : StellarEquivIn K L) :
    PLHomeomorphic K L := by
  induction h with
  | rel K L h =>
    cases h with
    | starAt hA hne ha => exact PLHomeomorphic.starAt hA hne ha
  | refl K => exact .refl K
  | symm K L _ ih => exact ih.symm
  | trans K L M _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **Stellar equivalent complexes are PL homeomorphic**: the easy direction of Newman's theorem
(Lickorish, Theorem 4.5). -/
theorem PLHomeomorphic.of_stellarEquiv {K L : SComplex V} (h : StellarEquiv K L) :
    PLHomeomorphic K L :=
  ((PLHomeomorphic.lift K).trans (PLHomeomorphic.of_stellarEquivIn h)).trans
    (PLHomeomorphic.lift L).symm

/-! ## Reduction of the hard direction to subdivisions -/

/-- **The hard direction of Newman's theorem reduces to subdivisions.** If every subdivision of a
geometric complex in `V →₀ ℝ` is stellar equivalent to it, then PL homeomorphic complexes are
stellar equivalent.

For a PL homeomorphism `f : |real K| → |real L|`, affine on a subdivision `K'` of `real K`, take a
common subdivision `N` of `f(K')` and `real L` and pull it back along `f` to a subdivision `P` of
`K'`. Then `real K ~ P ≅ N ~ real L`, where `f` is the isomorphism `P ≅ N`, and an embedding
reflects stellar equivalence (`StellarEquiv.map_iff`). -/
theorem StellarEquiv.of_plHomeomorphic_of_subdivision
    (key : ∀ M N : SComplex (V →₀ ℝ), IsSubdivision M N → StellarEquiv M N)
    {K L : SComplex V} (h : PLHomeomorphic K L) : StellarEquiv K L := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨K', hK', hfK'⟩ := isPLMap_iff.1 hf.pl
  have hinj : Set.InjOn f K'.space := hK'.space_eq ▸ hf.bij.injOn
  have hsp : (K'.image f).space = L.real.space := by
    rw [hfK'.space_image, hK'.space_eq, hf.bij.image_eq]
  obtain ⟨N, hN₁, hN₂⟩ :=
    (isGeom_image hK'.geom' hfK' hinj).exists_common_subdivision hf.geom hsp
  have hP := isSubdivision_image_invFunOn hK'.geom' hfK' hinj hN₁
  have hright := (Set.surjOn_image f K'.space).rightInvOn_invFunOn
  have hNsp : N.space = f '' K'.space := hN₁.space_eq.trans hfK'.space_image
  have hfg : ∀ s ∈ N, ((s.image (Function.invFunOn f K'.space)).image f) = s := by
    intro s hs
    rw [Finset.image_image]
    refine (Finset.image_congr fun x hx => ?_).trans Finset.image_id
    have hx' : x ∈ N.space := convexHull_subset_space hs (subset_convexHull ℝ _ hx)
    rw [hNsp] at hx'
    exact hright hx'
  have hiso : StellarEquiv (N.image (Function.invFunOn f K'.space)) N := by
    refine StellarEquiv.of_iso (f := f) ?_ ?_
    · intro x hx y hy hxy
      have hsp' := hP.space_eq
      have mem : ∀ z, z ∈ (N.image (Function.invFunOn f K'.space)).verts → z ∈ K'.space :=
        fun z hz => hsp' ▸ convexHull_subset_space (mem_verts.1 hz)
          (subset_convexHull ℝ _ (Finset.mem_coe.2 (Finset.mem_singleton_self z)))
      exact hinj (mem x hx) (mem y hy) hxy
    · show N.faces = (N.faces.image (Finset.image _)).image (Finset.image f)
      rw [Finset.image_image]
      exact Finset.image_id.symm.trans
        (Finset.image_congr fun s hs => (hfg s (Finset.mem_coe.1 hs)).symm)
  have h₁ := key _ _ (hP.trans hK')
  have h₂ := key _ _ hN₂
  exact (StellarEquiv.map_iff (vertexEmb V)).1 ((h₁.symm.trans hiso).trans h₂)

end SComplex

end Lightlike.PL
