import Lightlike.PL.Image

/-!
# Radial (projective) images of geometric complexes

A radial map `x ↦ v + (x - v) / m x`, where `m` is positive and affine on every simplex of a
complex, is not affine on a simplex but is **projective** there: it sends the closed simplex onto
the closed simplex spanned by the image vertices, with explicit change of barycentric weights.
This is the fact behind Lickorish's Lemma 4.2 ("projecting radially ... though such a projection is
not linear when restricted to an actual simplex").

## Main results

* `SComplex.projMap`: the radial map.
* `SComplex.projMap_image_convexHull`: the image of a closed simplex is the closed simplex on the
  image vertices.
* `SComplex.isGeom_image_projMap`: the image of a geometric complex under a radial map that is
  injective on the underlying set is geometric.
-/

open Finset

namespace Lightlike.PL
namespace SComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The **radial map** with centre `v` and scale `m`: `x ↦ v + (x - v) / m x`. -/
noncomputable def projMap (v : E) (m : E → ℝ) (x : E) : E := v + (m x)⁻¹ • (x - v)

section Combo

variable {v : E} {m : E → ℝ} {s : Finset E} {t : E → ℝ}

omit [AddCommGroup E] [Module ℝ E] in
/-- A convex combination of points where `m` is positive has positive `m`-mass. -/
lemma mass_pos_of_convex (hpos : ∀ y ∈ s, 0 < m y) (ht0 : ∀ y ∈ s, 0 ≤ t y)
    (ht1 : ∑ y ∈ s, t y = 1) : 0 < ∑ y ∈ s, t y * m y := by
  obtain ⟨y, hy, hty⟩ : ∃ y ∈ s, 0 < t y := by
    by_contra h
    have h0 : ∀ y ∈ s, t y = 0 := fun y hy =>
      le_antisymm (not_lt.1 fun hp => h ⟨y, hy, hp⟩) (ht0 y hy)
    rw [Finset.sum_eq_zero h0] at ht1
    exact zero_ne_one ht1
  exact Finset.sum_pos' (fun y hy => mul_nonneg (ht0 y hy) (hpos y hy).le)
    ⟨y, hy, mul_pos hty (hpos y hy)⟩

/-- **A radial map is projective on a simplex.** If `m` is positive on the vertices and affine on
the closed simplex, the radial image of a point with barycentric weights `t` has weights
`t y * m y / ∑ t z * m z` with respect to the image vertices. -/
lemma projMap_sum {g : E →ᵃ[ℝ] ℝ} (hg : ∀ y ∈ convexHull ℝ (s : Set E), m y = g y)
    (hpos : ∀ y ∈ s, 0 < m y) (ht0 : ∀ y ∈ s, 0 ≤ t y) (ht1 : ∑ y ∈ s, t y = 1) :
    projMap v m (∑ y ∈ s, t y • y) =
      ∑ y ∈ s, (t y * m y / ∑ z ∈ s, t z * m z) • projMap v m y := by
  set M := ∑ z ∈ s, t z * m z with hMdef
  have hM : 0 < M := mass_pos_of_convex hpos ht0 ht1
  have hx : (∑ y ∈ s, t y • y) ∈ convexHull ℝ (s : Set E) :=
    Finset.mem_convexHull'.2 ⟨t, ht0, ht1, rfl⟩
  have hmx : m (∑ y ∈ s, t y • y) = M := by
    rw [hg _ hx, map_sum_smul_of_sum_eq_one g ht1]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [← hg y (subset_convexHull ℝ _ hy), smul_eq_mul]
  have h1 : ∑ y ∈ s, (t y * m y / M) • v = v := by
    have : ∑ y ∈ s, t y * m y / M = 1 := by
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul, ← hMdef, mul_inv_cancel₀ hM.ne']
    rw [← Finset.sum_smul, this, one_smul]
  have h2 : ∑ y ∈ s, (t y * m y / M) • ((m y)⁻¹ • (y - v)) =
      M⁻¹ • (∑ y ∈ s, t y • y - v) := by
    have : ∀ y ∈ s, (t y * m y / M) • ((m y)⁻¹ • (y - v)) = M⁻¹ • (t y • y - t y • v) := by
      intro y hy
      have hmy : m y ≠ 0 := (hpos y hy).ne'
      rw [smul_smul, ← smul_sub, smul_smul]
      congr 1
      field_simp
    rw [Finset.sum_congr rfl this, ← Finset.smul_sum, Finset.sum_sub_distrib, ← Finset.sum_smul,
      ht1, one_smul]
  have h3 : ∑ y ∈ s, (t y * m y / M) • projMap v m y =
      ∑ y ∈ s, (t y * m y / M) • v + ∑ y ∈ s, (t y * m y / M) • ((m y)⁻¹ • (y - v)) := by
    simp only [projMap, smul_add, Finset.sum_add_distrib]
  rw [h3, h1, h2]
  simp only [projMap, hmx]

/-- **Every convex combination of the image vertices is the radial image of a point of the
simplex** (the inverse change of weights of `projMap_sum`). -/
lemma exists_projMap_eq_sum {g : E →ᵃ[ℝ] ℝ} (hg : ∀ y ∈ convexHull ℝ (s : Set E), m y = g y)
    (hpos : ∀ y ∈ s, 0 < m y) {l : E → ℝ} (hl0 : ∀ y ∈ s, 0 ≤ l y) (hl1 : ∑ y ∈ s, l y = 1) :
    ∃ x ∈ convexHull ℝ (s : Set E), projMap v m x = ∑ y ∈ s, l y • projMap v m y := by
  set S := ∑ z ∈ s, l z * (m z)⁻¹ with hSdef
  have hS : 0 < S := mass_pos_of_convex (m := fun y => (m y)⁻¹) (fun y hy => inv_pos.2 (hpos y hy))
    hl0 hl1
  set t : E → ℝ := fun y => l y * (m y)⁻¹ / S with ht
  have ht0 : ∀ y ∈ s, 0 ≤ t y := fun y hy =>
    div_nonneg (mul_nonneg (hl0 y hy) (inv_pos.2 (hpos y hy)).le) hS.le
  have ht1 : ∑ y ∈ s, t y = 1 := by
    simp only [ht, div_eq_mul_inv]
    rw [← Finset.sum_mul, ← hSdef, mul_inv_cancel₀ hS.ne']
  have htm : ∀ y ∈ s, t y * m y = l y * S⁻¹ := by
    intro y hy
    have : m y ≠ 0 := (hpos y hy).ne'
    simp only [ht]
    field_simp
  have hM : ∑ z ∈ s, t z * m z = S⁻¹ := by
    rw [Finset.sum_congr rfl htm, ← Finset.sum_mul, hl1, one_mul]
  refine ⟨∑ y ∈ s, t y • y, Finset.mem_convexHull'.2 ⟨t, ht0, ht1, rfl⟩, ?_⟩
  rw [projMap_sum hg hpos ht0 ht1]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [hM, htm y hy, mul_div_assoc, div_self (inv_ne_zero hS.ne'), mul_one]

end Combo

section Simplex

variable {v : E} {m : E → ℝ} {s : Finset E}

/-- **A radial map keeps the vertices of a simplex affinely independent**, provided the centre
does not lie in the affine span of the simplex and the map is injective on the vertices. -/
lemma affineIndependent_image_projMap [DecidableEq E] (hs : AffineIndependent ℝ ((↑) : s → E))
    (hpos : ∀ y ∈ s, 0 < m y) (hv : v ∉ affineSpan ℝ (s : Set E))
    (hinj : Set.InjOn (projMap v m) (s : Set E)) :
    AffineIndependent ℝ ((↑) : (s.image (projMap v m)) → E) := by
  refine affineIndependent_of_forall fun W hW0 hW1 => ?_
  rw [sum_image hinj] at hW0 hW1
  set b : E → ℝ := fun y => W (projMap v m y) * (m y)⁻¹ with hb
  have hsum : ∑ y ∈ s, b y • y = (∑ y ∈ s, b y) • v := by
    have h : ∑ y ∈ s, W (projMap v m y) • (projMap v m y - v) = 0 := by
      simp only [smul_sub, Finset.sum_sub_distrib, hW1, ← Finset.sum_smul, hW0, zero_smul,
        sub_zero]
    have h2 : ∀ y ∈ s, W (projMap v m y) • (projMap v m y - v) = b y • (y - v) := by
      intro y hy
      simp only [projMap, add_sub_cancel_left, smul_smul, hb]
    rw [Finset.sum_congr rfl h2] at h
    simpa only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, sub_eq_zero] using h
  have hb0 : ∑ y ∈ s, b y = 0 := by
    by_contra hne
    apply hv
    have h1 : ∑ y ∈ s, (b y / ∑ z ∈ s, b z) = 1 := by
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul, mul_inv_cancel₀ hne]
    have hmem := affineCombination_mem_affineSpan_image (k := ℝ) (s := s)
      (w := fun y => b y / ∑ z ∈ s, b z) h1 (s' := (s : Set E)) (fun i hi hni => absurd hi hni)
      (id : E → E)
    rw [s.affineCombination_eq_linear_combination _ _ h1] at hmem
    have : ∑ y ∈ s, (b y / ∑ z ∈ s, b z) • id y = v := by
      have e : ∀ y : E, (b y / ∑ z ∈ s, b z) • id y = (∑ z ∈ s, b z)⁻¹ • (b y • y) := fun y => by
        rw [div_eq_inv_mul, mul_smul]; rfl
      rw [Finset.sum_congr rfl fun y _ => e y, ← Finset.smul_sum, hsum, smul_smul,
        inv_mul_cancel₀ hne, one_smul]
    rw [this] at hmem
    simpa using hmem
  have hz := hs.eq_of_sum_eq_sum_subtype (w₁ := b) (w₂ := fun _ => 0)
    (by simpa using hb0) (by simpa [hb0] using hsum)
  intro z hz'
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz'
  have := hz y hy
  simp only [hb, mul_eq_zero, inv_eq_zero] at this
  exact this.resolve_right (hpos y hy).ne'

/-- **A radial map sends a closed simplex onto the closed simplex spanned by the image
vertices.** -/
lemma projMap_image_convexHull [DecidableEq E] {g : E →ᵃ[ℝ] ℝ}
    (hg : ∀ y ∈ convexHull ℝ (s : Set E), m y = g y) (hpos : ∀ y ∈ s, 0 < m y)
    (hinj : Set.InjOn (projMap v m) (s : Set E)) :
    projMap v m '' convexHull ℝ (s : Set E) = convexHull ℝ (↑(s.image (projMap v m)) : Set E) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨t, ht0, ht1, rfl⟩ := Finset.mem_convexHull'.1 hx
    rw [projMap_sum hg hpos ht0 ht1]
    have hM := mass_pos_of_convex hpos ht0 ht1
    refine (convex_convexHull ℝ _).sum_mem (fun y hy => ?_) ?_ (fun y hy => ?_)
    · exact div_nonneg (mul_nonneg (ht0 y hy) (hpos y hy).le) hM.le
    · simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul, mul_inv_cancel₀ hM.ne']
    · exact subset_convexHull ℝ _ (by simpa using Finset.mem_image_of_mem _ hy)
  · intro hz
    obtain ⟨W, hW0, hW1, rfl⟩ := Finset.mem_convexHull'.1 hz
    rw [sum_image hinj] at hW1 ⊢
    obtain ⟨x, hx, hxz⟩ := exists_projMap_eq_sum (v := v) hg hpos
      (l := fun y => W (projMap v m y))
      (fun y hy => hW0 _ (Finset.mem_image_of_mem _ hy)) hW1
    exact ⟨x, hx, hxz⟩

end Simplex

section Complex

variable {K : SComplex E} {v : E} {m : E → ℝ}

/-- The scale `m` is **radial on** `K` with centre `v`: on every simplex it is positive on the
vertices and affine, and the centre does not lie in the affine span of the simplex. -/
def IsRadialOn (K : SComplex E) (v : E) (m : E → ℝ) : Prop :=
  ∀ s ∈ K, (∀ y ∈ s, 0 < m y) ∧ (∃ g : E →ᵃ[ℝ] ℝ, ∀ y ∈ convexHull ℝ (s : Set E), m y = g y) ∧
    v ∉ affineSpan ℝ (s : Set E)

variable [DecidableEq E]

/-- On every simplex of `K` the radial map sends the closed simplex onto the closed simplex of
the image vertices. -/
lemma IsRadialOn.image_convexHull (hr : IsRadialOn K v m) (hinj : Set.InjOn (projMap v m) K.space)
    {s : Finset E} (hs : s ∈ K) :
    projMap v m '' convexHull ℝ (s : Set E) = convexHull ℝ (↑(s.image (projMap v m)) : Set E) := by
  obtain ⟨hpos, ⟨g, hg⟩, -⟩ := hr s hs
  exact projMap_image_convexHull hg hpos
    (hinj.mono fun x hx => mem_space.2 ⟨s, hs, subset_convexHull ℝ _ hx⟩)

/-- The underlying set of the radial image is the radial image of the underlying set. -/
lemma IsRadialOn.space_image (hr : IsRadialOn K v m) (hinj : Set.InjOn (projMap v m) K.space) :
    (K.image (projMap v m)).space = projMap v m '' K.space := by
  ext y
  simp only [mem_space, mem_image, Set.mem_image]
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, hy⟩
    rw [← hr.image_convexHull hinj hs] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, ⟨s, hs, hx⟩, rfl⟩
  · rintro ⟨x, ⟨s, hs, hx⟩, rfl⟩
    exact ⟨_, ⟨s, hs, rfl⟩, hr.image_convexHull hinj hs ▸ Set.mem_image_of_mem _ hx⟩

/-- **The radial image of a geometric complex is a geometric complex**, when the radial map is
injective on the underlying set. -/
theorem isGeom_image_projMap (hK : IsGeom K) (hr : IsRadialOn K v m)
    (hinj : Set.InjOn (projMap v m) K.space) : IsGeom (K.image (projMap v m)) where
  indep s' hs' := by
    obtain ⟨s, hs, rfl⟩ := mem_image.1 hs'
    obtain ⟨hpos, -, hv⟩ := hr s hs
    exact affineIndependent_image_projMap (hK.indep s hs) hpos hv
      (hinj.mono fun x hx => mem_space.2 ⟨s, hs, subset_convexHull ℝ _ hx⟩)
  inter s' hs' t' ht' := by
    obtain ⟨s, hs, rfl⟩ := mem_image.1 hs'
    obtain ⟨t, ht, rfl⟩ := mem_image.1 ht'
    rintro y ⟨hys, hyt⟩
    rw [← hr.image_convexHull hinj hs] at hys
    rw [← hr.image_convexHull hinj ht] at hyt
    obtain ⟨a, ha, rfl⟩ := hys
    obtain ⟨b, hb, hab⟩ := hyt
    have hba : b = a := hinj (mem_space.2 ⟨t, ht, hb⟩) (mem_space.2 ⟨s, hs, ha⟩) hab
    subst hba
    have hst : s ∩ t ∈ K := down_mem hs inter_subset_left
    have hy : projMap v m b ∈ convexHull ℝ (↑((s ∩ t).image (projMap v m)) : Set E) := by
      rw [← hr.image_convexHull hinj hst, coe_inter]
      exact Set.mem_image_of_mem _ (hK.inter s hs t ht ⟨ha, hb⟩)
    refine convexHull_mono ?_ hy
    rw [← coe_inter]
    exact coe_subset.2 (image_inter_subset _ _ _)

end Complex

end SComplex
end Lightlike.PL
