import Lightlike.PL.SliceStellar

/-!
# Subdivisions and slicings

A geometric subdivision `M` of a geometric complex `N` is cut out, inside `N`, by finitely many
affine functionals: the barycentric coordinates of the faces of `M` with respect to a completion
to a basis of the simplex of `N` that carries them. The cells of `N` and of `M` for these
functionals are the same sets, and the order of cells is determined by the sets, so the two
slicings are isomorphic.

## Main results

* `SComplex.exists_completion`: an independent face inside the span of a simplex extends to an
  independent set of vertices spanning it.
-/

open Finset Module

universe u

namespace Lightlike.PL
namespace SComplex

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [DecidableEq E]

/-- **Completion.** An affinely independent finite set `σ` extends,
by points of `σ ∪ τ`, to an affinely independent set whose affine span contains that of `τ`. -/
lemma exists_completion {σ τ : Finset E} (hσ : AffineIndependent ℝ ((↑) : σ → E)) :
    ∃ t : Finset E, σ ⊆ t ∧ AffineIndependent ℝ ((↑) : t → E) ∧
      (τ : Set E) ⊆ affineSpan ℝ (t : Set E) := by
  classical
  set S : Finset (Finset E) := (σ ∪ τ).powerset.filter fun t =>
    σ ⊆ t ∧ AffineIndependent ℝ ((↑) : t → E) with hS
  have hσS : σ ∈ S := by
    simp only [hS, mem_filter, mem_powerset]
    exact ⟨subset_union_left, subset_rfl, hσ⟩
  obtain ⟨t, htS, hmax⟩ := Finset.exists_max_image S Finset.card ⟨σ, hσS⟩
  simp only [hS, mem_filter, mem_powerset] at htS
  obtain ⟨htU, hσt, hti⟩ := htS
  refine ⟨t, hσt, hti, fun v hv => ?_⟩
  by_contra hvt
  have hvt' : v ∉ t := fun h => hvt (subset_affineSpan ℝ _ (mem_coe.2 h))
  have hind : AffineIndepOn ℝ (id : E → E) (↑(insert v t) : Set E) := by
    rw [coe_insert]
    refine AffineIndepOn.insert hti ?_
    simpa using hvt
  have hmem : insert v t ∈ S := by
    simp only [hS, mem_filter, mem_powerset]
    refine ⟨insert_subset (mem_union_right _ hv) htU, hσt.trans (subset_insert _ _), ?_⟩
    exact hind
  have := hmax _ hmem
  rw [card_insert_of_notMem hvt'] at this
  omega

omit [DecidableEq E] in
/-- An affine function applied to an affine combination. -/
lemma aff_sum (f : E →ᵃ[ℝ] ℝ) {s : Finset E} (u : E → ℝ) (hu : ∑ y ∈ s, u y = 1) :
    f (∑ y ∈ s, u y • y) = ∑ y ∈ s, u y * f y := by
  have h1 : ∀ x, f x = f.linear x + f 0 := fun x => by
    simpa using f.map_vadd (0 : E) x
  rw [h1, map_sum]
  simp_rw [map_smul, smul_eq_mul]
  have : ∑ y ∈ s, u y * f y = ∑ y ∈ s, (u y * f.linear y + u y * f 0) := by
    refine sum_congr rfl fun y _ => ?_
    rw [h1 y]; ring
  rw [this, sum_add_distrib, ← sum_mul, hu]
  ring

variable {T : Finset E}

/-- **Barycentric coordinates of a point of an open face.** A point of the open simplex of
`s ⊆ T` has positive coordinates on `s` and zero coordinates on the rest of `T`. -/
lemma coord_of_mem_openHull {w : E → (E →ᵃ[ℝ] ℝ)}
    (hw : ∀ u : E → ℝ, ∑ y ∈ T, u y = 1 → ∀ y ∈ T, w y (∑ z ∈ T, u z • z) = u y)
    {s : Finset E} (hsT : s ⊆ T) {x : E} (hx : x ∈ openHull s) :
    (∀ z ∈ T, z ∉ s → w z x = 0) ∧ ∀ z ∈ s, 0 < w z x := by
  classical
  obtain ⟨u, hu0, hu1, rfl⟩ := hx
  obtain ⟨h1, h2⟩ := sum_extend_zero hsT u
  have key := fun z hz => hw (fun y => if y ∈ s then u y else 0) (by rw [h1, hu1]) z hz
  rw [h2] at key
  refine ⟨fun z hz hzs => ?_, fun z hz => ?_⟩
  · rw [key z hz]; simp [hzs]
  · rw [key z (hsT hz)]; simp [hz, hu0 z hz]

omit [DecidableEq E] in
/-- The barycentric coordinates of a point of the closed simplex are nonnegative. -/
lemma coord_nonneg_of_mem_convexHull {w : E → (E →ᵃ[ℝ] ℝ)}
    (hw : ∀ u : E → ℝ, ∑ y ∈ T, u y = 1 → ∀ y ∈ T, w y (∑ z ∈ T, u z • z) = u y)
    {p : E} (hp : p ∈ convexHull ℝ (T : Set E)) {z : E} (hz : z ∈ T) : 0 ≤ w z p := by
  obtain ⟨u, hu0, hu1, rfl⟩ := Finset.mem_convexHull'.1 hp
  rw [hw u hu1 z hz]; exact hu0 z hz

/-- **A face of a simplex carries the open simplices that meet it.** If the vertices of `σ` lie in
the closed simplex of an independent `T`, and a point of the open simplex of `σ` lies in the open
simplex of a face `τ ⊆ T`, then the whole open simplex of `σ` lies in the open simplex of `τ`. -/
lemma openHull_subset_of_face (hT : AffineIndependent ℝ ((↑) : T → E)) {τ σ : Finset E}
    (hτT : τ ⊆ T) (hσ : ∀ v ∈ σ, v ∈ convexHull ℝ (T : Set E)) {x : E} (hxσ : x ∈ openHull σ)
    (hxτ : x ∈ openHull τ) : openHull σ ⊆ openHull τ := by
  classical
  obtain ⟨w, hw⟩ := exists_barycentric T hT
  obtain ⟨hx0, hxp⟩ := coord_of_mem_openHull hw hτT hxτ
  intro p hp
  obtain ⟨m, hm0, hm1, rfl⟩ := hp
  obtain ⟨u, hu0, hu1, hux⟩ := hxσ
  have hvT : ∀ z ∈ T, ∀ v ∈ σ, 0 ≤ w z v := fun z hz v hv =>
    coord_nonneg_of_mem_convexHull hw (hσ v hv) hz
  have hxs : ∀ z ∈ T, w z x = ∑ v ∈ σ, u v * w z v := fun z hz => by
    rw [← hux]; exact aff_sum (w z) u hu1
  have hps : ∀ z ∈ T, w z (∑ v ∈ σ, m v • v) = ∑ v ∈ σ, m v * w z v := fun z hz =>
    aff_sum (w z) m hm1
  -- coordinates of a point of the open simplex of `σ`, off `τ` and on `τ`
  have hzero : ∀ z ∈ T, z ∉ τ → ∀ v ∈ σ, w z v = 0 := by
    intro z hz hzτ v hv
    have h0 := hx0 z hz hzτ
    rw [hxs z hz] at h0
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun v hv => mul_nonneg (hu0 v hv).le
      (hvT z hz v hv))).1 h0 v hv
    exact (mul_eq_zero.1 this).resolve_left (hu0 v hv).ne'
  have hpos : ∀ z ∈ τ, ∃ v ∈ σ, 0 < w z v := by
    intro z hz
    by_contra hcon
    push Not at hcon
    have := hxp z hz
    rw [hxs z (hτT hz)] at this
    have h0 : ∑ v ∈ σ, u v * w z v ≤ 0 :=
      sum_nonpos fun v hv => mul_nonpos_of_nonneg_of_nonpos (hu0 v hv).le (hcon v hv)
    linarith
  -- the point `p` has positive coordinates on `τ` and zero elsewhere, and lies in `conv T`
  have hpT : (∑ v ∈ σ, m v • v) ∈ convexHull ℝ (T : Set E) := by
    refine (convex_convexHull ℝ _).sum_mem (fun v hv => (hm0 v hv).le) hm1 fun v hv => hσ v hv
  obtain ⟨c, hc0, hc1, hcp⟩ := Finset.mem_convexHull'.1 hpT
  have hcw : ∀ z ∈ T, w z (∑ v ∈ σ, m v • v) = c z := fun z hz => by
    rw [← hcp]; exact hw c hc1 z hz
  have hcz : ∀ z ∈ T, z ∉ τ → c z = 0 := fun z hz hzτ => by
    rw [← hcw z hz, hps z hz]
    exact sum_eq_zero fun v hv => by rw [hzero z hz hzτ v hv, mul_zero]
  have hcp' : ∀ z ∈ τ, 0 < c z := fun z hz => by
    rw [← hcw z (hτT hz), hps z (hτT hz)]
    obtain ⟨v, hv, hvp⟩ := hpos z hz
    refine lt_of_lt_of_le (mul_pos (hm0 v hv) hvp) ?_
    exact single_le_sum (f := fun v => m v * w z v)
      (fun v hv => mul_nonneg (hm0 v hv).le (hvT z (hτT hz) v hv)) hv
  refine ⟨c, hcp', ?_, ?_⟩
  · rw [← hc1]
    exact sum_subset hτT fun z hz hzτ => hcz z hz hzτ
  · rw [← hcp]
    exact sum_subset hτT fun z hz hzτ => by rw [hcz z hz hzτ, zero_smul]

/-- **Isomorphic order complexes are stellar equivalent**: a map `Φ` of a poset to itself that is
injective on `S`, maps `S` onto `T` and preserves and reflects the order on `S` makes the order
complexes of `S` and `T` stellar equivalent. -/
theorem stellarEquiv_orderComplex_of_iso {P : Type*} [PartialOrder P] [DecidableEq P]
    {S T : Finset P} {Φ : P → P} (hinj : Set.InjOn Φ (S : Set P)) (hmaps : ∀ a ∈ S, Φ a ∈ T)
    (hsurj : ∀ c ∈ T, ∃ a ∈ S, Φ a = c) (hord : ∀ a ∈ S, ∀ b ∈ S, a ≤ b ↔ Φ a ≤ Φ b) :
    StellarEquiv (orderComplex S) (orderComplex T) := by
  classical
  refine StellarEquiv.of_iso (f := Φ) ?_ ?_
  · intro a ha b hb hab
    have ha' : a ∈ S := by
      exact (mem_orderComplex.1 (mem_verts.1 ha)).1 (mem_singleton_self a)
    have hb' : b ∈ S := (mem_orderComplex.1 (mem_verts.1 hb)).1 (mem_singleton_self b)
    exact hinj ha' hb' hab
  · refine Finset.ext fun C => ?_
    rw [mem_faces, Finset.mem_image]
    constructor
    · intro hC
      obtain ⟨hCT, hch⟩ := mem_orderComplex.1 hC
      choose! g hgS hg using fun c (hc : c ∈ C) => hsurj c (hCT hc)
      refine ⟨C.image g, mem_orderComplex.2 ⟨?_, ?_⟩, ?_⟩
      · intro a ha
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 ha
        exact hgS c hc
      · intro a ha b hb
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 ha
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hb
        rcases hch c hc d hd with h | h
        · left; rw [hord _ (hgS c hc) _ (hgS d hd), hg c hc, hg d hd]; exact h
        · right; rw [hord _ (hgS d hd) _ (hgS c hc), hg c hc, hg d hd]; exact h
      · rw [Finset.image_image]
        refine (Finset.image_congr (g := id) ?_).trans Finset.image_id
        intro c hc
        simp [hg c hc]
    · rintro ⟨D, hD, rfl⟩
      obtain ⟨hDS, hch⟩ := mem_orderComplex.1 hD
      refine mem_orderComplex.2 ⟨?_, ?_⟩
      · intro c hc
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hc
        exact hmaps a (hDS ha)
      · intro c hc d hd
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hc
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hd
        rcases hch a ha b hb with h | h
        · left; exact (hord a (hDS ha) b (hDS hb)).1 h
        · right; exact (hord b (hDS hb) a (hDS ha)).1 h

/-- A number below zero at `0` and below zero along the segment is nonpositive at the end. -/
lemma nonpos_of_segment {a b : ℝ} (ha : a < 0)
    (h : ∀ l : ℝ, 0 < l → l ≤ 1 → l * a + (1 - l) * b < 0) : b ≤ 0 := by
  by_contra hb
  have hb' : 0 < b := not_le.1 hb
  have hl : 0 < b - a := by linarith
  have h1 := h (b / (b - a)) (by positivity) (by rw [div_le_one hl]; linarith)
  have e : b / (b - a) * a + (1 - b / (b - a)) * b = 0 := by field_simp; ring
  linarith

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {K : SComplex E}

omit [DecidableEq E] [Fintype ι] [DecidableEq ι] in
/-- **The closed part is the closure of the open part, in terms of segments.** If a point `p` of
the open part of a cell and a point `y` are such that all points strictly between them (and `p`)
are in the open part, then `y` is in the closed part. -/
lemma mem_sliceHull_of_segments (hK : IsGeom K) (H : ι → E →ᵃ[ℝ] ℝ) {b : CellIdx E ι}
    (hb : b.1 ∈ K) {p y : E} (hp : p ∈ cellSet (fun i => ⇑(H i)) b)
    (h : ∀ l : ℝ, 0 < l → l ≤ 1 → l • p + (1 - l) • y ∈ cellSet (fun i => ⇑(H i)) b) :
    y ∈ sliceHull H b := by
  classical
  obtain ⟨w, hw⟩ := exists_barycentric b.1 (hK.indep b.1 hb)
  rw [sliceHull_eq H b w hw]
  rw [cellSet_eq H b w hw] at hp h
  have hq := h (1 / 2) (by norm_num) (by norm_num)
  refine ⟨?_, fun k => ?_⟩
  · have h2 := (cellA H b).smul_vsub_vadd_mem (2 : ℝ) hq.1 hp.1 hp.1
    have e : (2 : ℝ) • ((1 / 2 : ℝ) • p + (1 - 1 / 2 : ℝ) • y -ᵥ p) +ᵥ p = y := by
      simp only [vsub_eq_sub, vadd_eq_add]; module
    rwa [e] at h2
  · refine nonpos_of_segment (a := cellG H b w k p) (b := cellG H b w k y) (hp.2 k) fun l hl hl1 => ?_
    rw [← aff_combo]
    exact (h l hl hl1).2 k

/-- **The order of cells is determined by the cell sets.** For cells `a` and `b` of a slicing, `a`
is below `b` exactly when a point of `b` sees the cell `a` through points of `b`. -/
lemma cell_le_iff_segments (hK : IsGeom K) (H : ι → E →ᵃ[ℝ] ℝ) {a b : CellIdx E ι}
    (ha : a ∈ cells K (fun i => ⇑(H i))) (hb : b ∈ cells K (fun i => ⇑(H i))) :
    a ≤ b ↔ ∃ p ∈ cellSet (fun i => ⇑(H i)) b, ∀ y ∈ cellSet (fun i => ⇑(H i)) a,
      ∀ l : ℝ, 0 < l → l ≤ 1 → l • p + (1 - l) • y ∈ cellSet (fun i => ⇑(H i)) b := by
  constructor
  · intro hab
    obtain ⟨p, hp⟩ := (mem_cells.1 hb).2
    refine ⟨p, hp, fun y hy l hl hl1 => ?_⟩
    exact (sliceStructure K hK H).combo_mem b hb hp
      (sliceHull_mono H hab (cellSet_subset_sliceHull H a hy)) hl hl1
  · rintro ⟨p, hp, h⟩
    obtain ⟨y, hy⟩ := (mem_cells.1 ha).2
    have hyH := mem_sliceHull_of_segments hK H (mem_cells.1 hb).1 hp (h y hy)
    obtain ⟨c', hc'b, hc'K, hyc'⟩ := exists_cell_of_mem_sliceHull H (mem_cells.1 hb).1 hyH
    have hc' : c' ∈ cells K (fun i => ⇑(H i)) := mem_cells.2 ⟨hc'K, ⟨y, hyc'⟩⟩
    have : a = c' := (sliceStructure K hK H).cell_inj a ha c' hc' y hy hyc'
    exact this ▸ hc'b

omit [DecidableEq E] in
/-- **Cutting a complex along the faces of a subdivision.** For a geometric subdivision `M` of
`N` there are finitely many affine functionals `H` such that, whenever the open simplex of a face
`σ` of `M` meets the open simplex of a face `τ` of `N`, the points of the open simplex of `τ`
with the same signs as a point `x` of both are exactly the points of the open simplex of `σ` with
those signs. -/
theorem exists_cutting {M N : SComplex E} (hsub : IsSubdivision M N) :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (H : ι → E →ᵃ[ℝ] ℝ),
      ∀ σ ∈ M, ∀ τ ∈ N, ∀ x : E, x ∈ openHull σ → x ∈ openHull τ →
        openHull τ ∩ {y | ∀ i, SignType.sign (H i y) = SignType.sign (H i x)} =
          openHull σ ∩ {y | ∀ i, SignType.sign (H i y) = SignType.sign (H i x)} := by
  classical
  have hex : ∀ σ : Finset E, ∃ (T : Finset E) (w : E → (E →ᵃ[ℝ] ℝ)), σ ∈ M →
      σ ⊆ T ∧ AffineIndependent ℝ ((↑) : T → E) ∧
      (∃ τσ ∈ N, (∀ v ∈ σ, v ∈ convexHull ℝ (τσ : Set E)) ∧ (τσ : Set E) ⊆ affineSpan ℝ (T : Set E)) ∧
      ∀ u : E → ℝ, ∑ y ∈ T, u y = 1 → ∀ y ∈ T, w y (∑ z ∈ T, u z • z) = u y := by
    intro σ
    by_cases hσ : σ ∈ M
    · obtain ⟨τσ, hτσ, hle⟩ := hsub.le σ hσ
      obtain ⟨T, hσT, hTi, hτT⟩ := exists_completion (τ := τσ) (hsub.geom'.indep σ hσ)
      obtain ⟨w, hw⟩ := exists_barycentric T hTi
      exact ⟨T, w, fun _ => ⟨hσT, hTi, ⟨τσ, hτσ, fun v hv => hle (subset_convexHull ℝ _ hv), hτT⟩, hw⟩⟩
    · exact ⟨∅, fun _ => 0, fun h => absurd h hσ⟩
  choose T w hTw using hex
  refine ⟨↥(M.faces.sigma fun σ => T σ), inferInstance, inferInstance,
    fun p => w p.1.1 p.1.2, ?_⟩
  intro σ hσ τ hτ x hxσ hxτ
  obtain ⟨hσT, hTi, ⟨τσ, hτσ, hστ, hτT⟩, hw⟩ := hTw σ hσ
  have hτsub : τ ⊆ τσ := by
    refine hsub.geom.subset_of_mem_openHull hτσ hτ ?_ hxτ
    obtain ⟨m, hm0, hm1, rfl⟩ := hxσ
    exact (convex_convexHull ℝ _).sum_mem (fun v hv => (hm0 v hv).le) hm1 fun v hv => hστ v hv
  ext y
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hyτ, hys⟩
    refine ⟨?_, hys⟩
    have hyA : y ∈ affineSpan ℝ (T σ : Set E) := by
      refine affineSpan_le.2 (fun z hz => hτT (hτsub hz)) ?_
      exact convexHull_subset_affineSpan _ (openHull_subset_convexHull _ hyτ)
    obtain ⟨v, hv1, hvy⟩ := exists_weights_of_mem_affineSpan hyA
    obtain ⟨hx0, hxp⟩ := coord_of_mem_openHull hw hσT hxσ
    have hvw : ∀ z ∈ T σ, w σ z y = v z := fun z hz => by
      rw [← hvy]; exact hw v hv1 z hz
    have hvs : ∀ z ∈ T σ, SignType.sign (v z) = SignType.sign (w σ z x) := fun z hz => by
      rw [← hvw z hz]; exact hys ⟨⟨σ, z⟩, Finset.mem_sigma.2 ⟨hσ, hz⟩⟩
    have hvpos : ∀ z ∈ σ, 0 < v z := fun z hz => by
      have := hvs z (hσT hz)
      rw [sign_pos (hxp z hz)] at this
      exact sign_eq_one_iff.1 this
    have hv0 : ∀ z ∈ T σ, z ∉ σ → v z = 0 := fun z hz hzσ => by
      have := hvs z hz
      rw [hx0 z hz hzσ, sign_zero] at this
      exact sign_eq_zero_iff.1 this
    refine ⟨v, hvpos, ?_, ?_⟩
    · rw [← hv1]; exact sum_subset hσT fun z hz hzσ => hv0 z hz hzσ
    · rw [← hvy]; exact sum_subset hσT fun z hz hzσ => by rw [hv0 z hz hzσ, zero_smul]
  · rintro ⟨hyσ, hys⟩
    exact ⟨openHull_subset_of_face (hsub.geom.indep τσ hτσ) hτsub hστ hxσ hxτ hyσ, hys⟩

/-- The cutting property of a family of functionals for a subdivision `M` of `N`, as produced by
`exists_cutting`. -/
def IsCutting (M N : SComplex E) (H : ι → E →ᵃ[ℝ] ℝ) : Prop :=
  ∀ σ ∈ M, ∀ τ ∈ N, ∀ x : E, x ∈ openHull σ → x ∈ openHull τ →
    openHull τ ∩ {y | ∀ i, SignType.sign (H i y) = SignType.sign (H i x)} =
      openHull σ ∩ {y | ∀ i, SignType.sign (H i y) = SignType.sign (H i x)}

omit [Fintype ι] [DecidableEq ι] in
/-- A cell of the slicing of `N` is a cell of the slicing of `M`, as a set. -/
lemma exists_cell_of_cell {M N : SComplex E} (hsub : IsSubdivision M N) {H : ι → E →ᵃ[ℝ] ℝ}
    (hcut : IsCutting M N H) {a : CellIdx E ι} (ha : a.1 ∈ N)
    (hne : (cellSet (fun i => ⇑(H i)) a).Nonempty) :
    ∃ c : CellIdx E ι, c.1 ∈ M ∧ cellSet (fun i => ⇑(H i)) c = cellSet (fun i => ⇑(H i)) a := by
  obtain ⟨x, hxa⟩ := hne
  have hxN : x ∈ N.space := mem_space.2 ⟨a.1, ha, openHull_subset_convexHull _ hxa.1⟩
  rw [← hsub.space_eq] at hxN
  obtain ⟨σ, hσ, hxσ⟩ := exists_carrier hxN
  have hc := hcut σ hσ a.1 ha x hxσ hxa.1
  refine ⟨(σ, a.2), hσ, ?_⟩
  ext y
  have h1 := Set.ext_iff.1 hc y
  have hs : ∀ i, SignType.sign (H i x) = a.2 i := hxa.2
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, hs] at h1
  simp only [cellSet, Set.mem_inter_iff, Set.mem_ofPred_eq]
  exact h1.symm

omit [Fintype ι] [DecidableEq ι] in
/-- A cell of the slicing of `M` is a cell of the slicing of `N`, as a set. -/
lemma exists_cell_of_cell' {M N : SComplex E} (hsub : IsSubdivision M N) {H : ι → E →ᵃ[ℝ] ℝ}
    (hcut : IsCutting M N H) {c : CellIdx E ι} (hc : c.1 ∈ M)
    (hne : (cellSet (fun i => ⇑(H i)) c).Nonempty) :
    ∃ a : CellIdx E ι, a.1 ∈ N ∧ cellSet (fun i => ⇑(H i)) a = cellSet (fun i => ⇑(H i)) c := by
  obtain ⟨x, hxc⟩ := hne
  have hxM : x ∈ M.space := mem_space.2 ⟨c.1, hc, openHull_subset_convexHull _ hxc.1⟩
  rw [hsub.space_eq] at hxM
  obtain ⟨τ, hτ, hxτ⟩ := exists_carrier hxM
  have h0 := hcut c.1 hc τ hτ x hxc.1 hxτ
  refine ⟨(τ, c.2), hτ, ?_⟩
  ext y
  have h1 := Set.ext_iff.1 h0 y
  have hs : ∀ i, SignType.sign (H i x) = c.2 i := hxc.2
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, hs] at h1
  simp only [cellSet, Set.mem_inter_iff, Set.mem_ofPred_eq]
  exact h1

/-- **Two slicings by a cutting family are isomorphic, so the complexes are stellar equivalent.**
If `M` subdivides `N`, `H` cuts `M` along `N`, and both complexes are stellar equivalent to
their slicings by `H`, then `M` and `N` are stellar equivalent. -/
theorem stellarEquiv_of_cutting [Infinite E] {M N : SComplex E} (hsub : IsSubdivision M N)
    {H : ι → E →ᵃ[ℝ] ℝ} (hcut : IsCutting M N H) (hM : SliceEq M (fun i => ⇑(H i)))
    (hN : SliceEq N (fun i => ⇑(H i))) : StellarEquiv M N := by
  classical
  haveI : Nonempty (CellIdx E ι) := ⟨((∅ : Finset E), fun _ => (0 : SignType))⟩
  have hmatch : ∀ a, a ∈ cells N (fun i => ⇑(H i)) → ∃ c, c ∈ cells M (fun i => ⇑(H i)) ∧
      cellSet (fun i => ⇑(H i)) c = cellSet (fun i => ⇑(H i)) a := by
    intro a ha
    obtain ⟨c, hc, hca⟩ := exists_cell_of_cell hsub hcut (mem_cells.1 ha).1 (mem_cells.1 ha).2
    exact ⟨c, mem_cells.2 ⟨hc, hca ▸ (mem_cells.1 ha).2⟩, hca⟩
  choose! Φ hΦ using hmatch
  have hiso : StellarEquiv (sliceComplex N (fun i => ⇑(H i))) (sliceComplex M (fun i => ⇑(H i))) := by
    refine stellarEquiv_orderComplex_of_iso (Φ := Φ) ?_ (fun a ha => (hΦ a ha).1) ?_ ?_
    · intro a ha b hb hab
      obtain ⟨x, hxa⟩ := (mem_cells.1 ha).2
      have hxb : x ∈ cellSet (fun i => ⇑(H i)) b := by
        rw [← (hΦ b hb).2, ← hab, (hΦ a ha).2]; exact hxa
      exact (sliceStructure N hsub.geom H).cell_inj a ha b hb x hxa hxb
    · intro c hc
      obtain ⟨a, ha, hac⟩ := exists_cell_of_cell' hsub hcut (mem_cells.1 hc).1 (mem_cells.1 hc).2
      have haN : a ∈ cells N (fun i => ⇑(H i)) :=
        mem_cells.2 ⟨ha, hac ▸ (mem_cells.1 hc).2⟩
      refine ⟨a, haN, ?_⟩
      obtain ⟨x, hxc⟩ := (mem_cells.1 hc).2
      have hxΦ : x ∈ cellSet (fun i => ⇑(H i)) (Φ a) := by
        rw [(hΦ a haN).2, hac]; exact hxc
      exact (sliceStructure M hsub.geom' H).cell_inj _ (hΦ a haN).1 c hc x hxΦ hxc
    · intro a ha b hb
      have e1 := cell_le_iff_segments hsub.geom H ha hb
      have e2 := cell_le_iff_segments hsub.geom' H (hΦ a ha).1 (hΦ b hb).1
      rw [(hΦ a ha).2, (hΦ b hb).2] at e2
      exact e1.trans e2.symm
  have h1 := (StellarEquiv.map_iff (Function.Embedding.inr : CellIdx E ι ↪ E ⊕ CellIdx E ι)).2 hiso
  have h2 : StellarEquiv (M.map (Function.Embedding.inl : E ↪ E ⊕ CellIdx E ι))
      (N.map (Function.Embedding.inl : E ↪ E ⊕ CellIdx E ι)) :=
    hM.trans (h1.symm.trans hN.symm)
  exact (StellarEquiv.map_iff (Function.Embedding.inl : E ↪ E ⊕ CellIdx E ι)).1 h2


omit [DecidableEq E] in
/-- **A subdivision has no larger faces.** If every face of `N` has at most `m` vertices, so does
every face of a geometric subdivision `M` of `N`: the face lies in the affine span of a face of
`N`. -/
lemma card_le_of_subdivision {M N : SComplex E} (hsub : IsSubdivision M N) {m : ℕ}
    (hN : ∀ s ∈ N, #s ≤ m) : ∀ s ∈ M, #s ≤ m := by
  classical
  intro s hs
  obtain ⟨τ, hτ, hle⟩ := hsub.le s hs
  exact ((hsub.geom'.indep s hs).card_le_card_of_subset_affineSpan (t := τ)
    (fun x hx => convexHull_subset_affineSpan _ (hle (subset_convexHull ℝ _ hx)))).trans (hN τ hτ)

/-- A point of the underlying set of a complex whose faces have at most one vertex is a vertex. -/
lemma singleton_mem_of_mem_space {L : SComplex E} (hL : ∀ s ∈ L, #s ≤ 1) {v : E}
    (hv : v ∈ L.space) : ({v} : Finset E) ∈ L := by
  obtain ⟨τ, hτ, hvτ⟩ := mem_space.1 hv
  rcases τ.eq_empty_or_nonempty with rfl | hne
  · simp at hvτ
  · obtain ⟨u, rfl⟩ := Finset.card_eq_one.1 (le_antisymm (hL τ hτ) (Finset.card_pos.2 hne))
    have : v = u := by simpa using hvτ
    rw [this]; exact hτ

/-- **The base case: subdivisions of complexes with at most one vertex per face are equal.** -/
theorem subdivStellar_zero : SubdivStellar E 0 := by
  intro M N hsub h0M h0N hN
  have hM : ∀ s ∈ M, #s ≤ 1 := card_le_of_subdivision hsub hN
  have hN' : ∀ s ∈ N, #s ≤ 1 := hN
  have key : ∀ {K L : SComplex E}, (∀ s ∈ K, #s ≤ 1) → (∀ s ∈ L, #s ≤ 1) → ∅ ∈ L →
      K.space ⊆ L.space → ∀ s ∈ K, s ∈ L := by
    intro K L hK hL h0 hsp s hs
    rcases s.eq_empty_or_nonempty with rfl | hne
    · exact h0
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.1 (le_antisymm (hK s hs) (Finset.card_pos.2 hne))
      exact singleton_mem_of_mem_space hL (hsp (mem_space.2 ⟨{v}, hs, by simp⟩))
  have : M = N := ext_mem fun s => ⟨key hM hN' h0N hsub.space_eq.le s,
    key hN' hM h0M hsub.space_eq.ge s⟩
  rw [this]

/-- **The inductive step.** Stellar equivalence of subdivisions of complexes with faces of at most
`n + 1` vertices gives it for faces of at most `n + 2` vertices. -/
theorem subdivStellar_succ [Infinite E] {n : ℕ} (hT : SubdivStellar E n) :
    SubdivStellar E (n + 1) := by
  intro M N hsub h0M h0N hN
  obtain ⟨ι, _, _, H, hH⟩ := exists_cutting hsub
  exact stellarEquiv_of_cutting hsub (H := H) hH
    (stellarEquiv_slice (n := n + 1) hT hsub.geom' h0M (card_le_of_subdivision hsub hN) H)
    (stellarEquiv_slice (n := n + 1) hT hsub.geom h0N hN H)

/-- **Newman's key step: geometric subdivisions are stellar equivalent**, in every dimension, for
complexes containing the empty face. -/
theorem subdivStellar [Infinite E] (n : ℕ) : SubdivStellar E n := by
  induction n with
  | zero => exact subdivStellar_zero
  | succ n ih => exact subdivStellar_succ ih

end SComplex
end Lightlike.PL
