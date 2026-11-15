import Lightlike.PL.Gauge
import Lightlike.PL.RadialBoundary

/-!
# The radial map from a simplex boundary to a polytope boundary

Let `σ` be an affinely independent finite set, `v` a point of its open simplex and `g` a finite
family of affine functions negative at `v`. The scale `polyScale g v` measures how far a point is
from `v` in units of the polytope `{g ≤ 0}`. When it is positive on the boundary of the simplex,
the radial map `projMap v (polyScale g v)` is a bijection from that boundary onto the boundary
of the polytope inside the affine span of `σ`.

## Main results

* `SComplex.mem_space_boundary`: the underlying set of the boundary of a simplex is the closed
  simplex minus the open one.
* `SComplex.injOn_projMap_boundary`: the radial map is injective on the boundary of the simplex.
-/

open Finset

namespace Lightlike.PL
namespace SComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]

/-- **The boundary of a simplex as a set**: the closed simplex minus the open simplex. -/
lemma mem_space_boundary {σ : Finset E} (hσ : AffineIndependent ℝ ((↑) : σ → E)) {y : E} :
    y ∈ (boundary σ).space ↔ y ∈ convexHull ℝ (σ : Set E) ∧ y ∉ openHull σ := by
  constructor
  · intro hy
    obtain ⟨t, ht, hyt⟩ := mem_space.1 hy
    have hts := (mem_boundary.1 ht)
    refine ⟨convexHull_mono (by exact_mod_cast hts.subset) hyt, fun hyo => ?_⟩
    obtain ⟨t', ht't, hyt'⟩ := exists_openHull_of_mem_convexHull hyt
    have := eq_of_mem_openHull hσ (ht't.trans hts.subset) subset_rfl hyt' hyo
    exact hts.ne (Finset.Subset.antisymm hts.subset (this ▸ ht't))
  · rintro ⟨hy, hyo⟩
    obtain ⟨t, hts, hyt⟩ := exists_openHull_of_mem_convexHull hy
    have hne : t ≠ σ := fun h => hyo (h ▸ hyt)
    exact mem_space.2 ⟨t, mem_boundary.2 (Finset.ssubset_iff_subset_ne.2 ⟨hts, hne⟩),
      openHull_subset_convexHull _ hyt⟩

/-- **Two boundary points on one ray from an interior point coincide.** -/
lemma eq_of_ray_boundary {σ : Finset E} {v y₁ y₂ : E} (hv : v ∈ openHull σ)
    (h₁ : y₁ ∈ convexHull ℝ (σ : Set E)) (h₂ : y₂ ∈ convexHull ℝ (σ : Set E))
    (hn₂ : y₂ ∉ openHull σ) {l : ℝ} (hl : 0 < l) (hy : y₁ - v = l • (y₂ - v)) (hl1 : 1 ≤ l) :
    l = 1 := by
  by_contra hne
  have hl1' : 1 < l := lt_of_le_of_ne hl1 (Ne.symm hne)
  apply hn₂
  have hl0 : 0 < 1 - l⁻¹ := by
    have : l⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1'
    linarith
  have hl2 : 1 - l⁻¹ ≤ 1 := by have := inv_pos.2 hl; linarith
  have e : y₂ = (1 - l⁻¹) • v + (1 - (1 - l⁻¹)) • y₁ := by
    have h1 : y₁ = v + l • (y₂ - v) := by rw [← hy]; abel
    rw [h1]
    have hl' : l ≠ 0 := hl.ne'
    match_scalars <;> field_simp <;> ring
  rw [e]
  exact combo_mem_openHull hv h₁ hl0 hl2

variable {κ : Type*} [Fintype κ] [Nonempty κ]

/-- The case of `injOn_projMap_boundary` in which the second scale is the smaller. -/
lemma eq_of_projMap_eq_of_le {σ : Finset E} (hσ : AffineIndependent ℝ ((↑) : σ → E)) {v : E}
    (hv : v ∈ openHull σ) {m : E → ℝ} {y₁ y₂ : E} (c₁ : y₁ ∈ convexHull ℝ (σ : Set E))
    (c₂ : y₂ ∈ convexHull ℝ (σ : Set E)) (n₂ : y₂ ∉ openHull σ) (p₁ : 0 < m y₁)
    (p₂ : 0 < m y₂) (h : projMap v m y₁ = projMap v m y₂) (hle : m y₂ ≤ m y₁) : y₁ = y₂ := by
  have e : (m y₁)⁻¹ • (y₁ - v) = (m y₂)⁻¹ • (y₂ - v) := add_left_cancel h
  have hy : y₁ - v = (m y₁ / m y₂) • (y₂ - v) := by
    have := congrArg (fun z => m y₁ • z) e
    simp only [smul_smul, mul_inv_cancel₀ p₁.ne', one_smul] at this
    rw [this, div_eq_mul_inv]
  have := eq_of_ray_boundary hv c₁ c₂ n₂ (div_pos p₁ p₂) hy ((one_le_div p₂).2 hle)
  rw [this, one_smul] at hy
  simpa using hy

/-- **The radial map is injective on the boundary of the simplex**, for any positive scale. -/
theorem injOn_projMap_boundary {σ : Finset E} (hσ : AffineIndependent ℝ ((↑) : σ → E)) {v : E}
    (hv : v ∈ openHull σ) {m : E → ℝ} (hpos : ∀ y ∈ (boundary σ).space, 0 < m y) :
    Set.InjOn (projMap v m) (boundary σ).space := by
  intro y₁ h₁ y₂ h₂ h
  obtain ⟨c₁, n₁⟩ := (mem_space_boundary hσ).1 h₁
  obtain ⟨c₂, n₂⟩ := (mem_space_boundary hσ).1 h₂
  rcases le_total (m y₂) (m y₁) with hle | hle
  · exact eq_of_projMap_eq_of_le hσ hv c₁ c₂ n₂ (hpos _ h₁) (hpos _ h₂) h hle
  · exact (eq_of_projMap_eq_of_le hσ hv c₂ c₁ n₁ (hpos _ h₂) (hpos _ h₁) h.symm hle).symm

/-- **The scale is homogeneous along rays from the centre.** -/
lemma polyScale_ray (g : κ → E →ᵃ[ℝ] ℝ) {v : E} (hv : ∀ k, g k v < 0) (x : E) {τ : ℝ}
    (hτ : 0 < τ) : polyScale g v (v + τ • (x - v)) = τ * polyScale g v x := by
  have key : ∀ k, 1 - g k (v + τ • (x - v)) / g k v = τ * (1 - g k x / g k v) := by
    intro k
    have h := affine_projMap (g k) v x τ⁻¹
    rw [inv_inv] at h
    rw [h]
    have := (hv k).ne
    field_simp
    ring
  refine le_antisymm ?_ ?_
  · obtain ⟨k, hk⟩ := exists_polyScale_eq g v (v + τ • (x - v))
    rw [hk, key k]
    exact mul_le_mul_of_nonneg_left (polyScale_apply_le g v k x) hτ.le
  · obtain ⟨k, hk⟩ := exists_polyScale_eq g v x
    rw [hk, ← key k]
    exact polyScale_apply_le g v k _

/-- **The scale is `1` on the boundary of the polytope.** -/
lemma polyScale_eq_one (g : κ → E →ᵃ[ℝ] ℝ) {v : E} (hv : ∀ k, g k v < 0) {x : E}
    (hx : ∀ k, g k x ≤ 0) (hk : ∃ k, g k x = 0) : polyScale g v x = 1 := by
  obtain ⟨k₀, hk₀⟩ := hk
  refine le_antisymm ?_ ?_
  · obtain ⟨k, hk⟩ := exists_polyScale_eq g v x
    rw [hk]
    have : 0 ≤ g k x / g k v := div_nonneg_of_nonpos (hx k) (hv k).le
    linarith
  · have := polyScale_apply_le g v k₀ x
    rwa [hk₀, zero_div, sub_zero] at this

/-- **A short step from the centre of a simplex towards a point of its affine span stays in the
simplex.** -/
lemma exists_pos_mem_ray {σ : Finset E} {v x : E} (hv : v ∈ openHull σ)
    (hx : x ∈ affineSpan ℝ (σ : Set E)) :
    ∃ t : ℝ, 0 < t ∧ v + t • (x - v) ∈ convexHull ℝ (σ : Set E) := by
  obtain ⟨w, hw, hw1, rfl⟩ := hv
  obtain ⟨u, hu1, rfl⟩ := exists_weights_of_mem_affineSpan hx
  have hne : σ.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.1 h] at hw1
    simp at hw1
  obtain ⟨t, ht0, ht⟩ : ∃ t : ℝ, 0 < t ∧ ∀ y ∈ σ, t * |u y - w y| < w y := by
    refine ⟨σ.inf' hne fun y => w y / (|u y - w y| + 1) / 2, ?_, fun y hy => ?_⟩
    · exact (Finset.lt_inf'_iff _).2 fun y hy => by
        have := hw y hy
        positivity
    · have h1 := Finset.inf'_le (fun y => w y / (|u y - w y| + 1) / 2) hy
      have hy0 := hw y hy
      have h2 : 0 < |u y - w y| + 1 := by positivity
      calc _ ≤ w y / (|u y - w y| + 1) / 2 * |u y - w y| :=
            mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ < w y := by
            rw [div_div, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
            nlinarith [abs_nonneg (u y - w y)]
  refine ⟨t, ht0, Finset.mem_convexHull'.2 ⟨fun y => w y + t * (u y - w y), fun y hy => ?_, ?_, ?_⟩⟩
  · have := ht y hy
    have := neg_abs_le (u y - w y)
    nlinarith [hw y hy]
  · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hw1, hu1]
    ring
  · simp only [add_smul, Finset.sum_add_distrib, mul_smul, ← Finset.smul_sum, smul_sub, sub_smul,
      Finset.sum_sub_distrib]

/-- **The radial map sends the boundary of the simplex onto the boundary of the polytope** inside
the affine span of the simplex. -/
theorem projMap_image_boundary {σ : Finset E} (hσ : AffineIndependent ℝ ((↑) : σ → E)) {v : E}
    (hv : v ∈ openHull σ) (g : κ → E →ᵃ[ℝ] ℝ) (hneg : ∀ k, g k v < 0)
    (hpos : ∀ y ∈ (boundary σ).space, 0 < polyScale g v y) :
    projMap v (polyScale g v) '' (boundary σ).space =
      {x | x ∈ affineSpan ℝ (σ : Set E) ∧ (∀ k, g k x ≤ 0) ∧ ∃ k, g k x = 0} := by
  have hvA : v ∈ affineSpan ℝ (σ : Set E) :=
    convexHull_subset_affineSpan (σ : Set E) (openHull_subset_convexHull _ hv)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, -⟩ := (mem_space_boundary hσ).1 hy
    have hyA : y ∈ affineSpan ℝ (σ : Set E) := convexHull_subset_affineSpan _ c
    refine ⟨?_, projMap_mem_polytope g hneg (hpos y hy), exists_projMap_face g hneg (hpos y hy)⟩
    have h : projMap v (polyScale g v) y = AffineMap.lineMap v y (polyScale g v y)⁻¹ := by
      unfold projMap
      rw [AffineMap.lineMap_apply_module']
      simp [add_comm]
    rw [h]
    exact AffineMap.lineMap_mem _ hvA hyA
  · rintro ⟨hxA, hxle, k, hk⟩
    have hxv : x ≠ v := by
      rintro rfl
      exact (hneg k).ne hk
    obtain ⟨t, ht, hp⟩ := exists_pos_mem_ray hv hxA
    have hpv : v + t • (x - v) ≠ v := by
      intro h
      have : t • (x - v) = 0 := by simpa using h
      rcases smul_eq_zero.1 this with h0 | h0
      · exact ht.ne' h0
      · exact hxv (sub_eq_zero.1 h0)
    obtain ⟨s, hs1, hsc, hsn⟩ := exists_exit hσ hv hp hpv
    have e : v + s • (v + t • (x - v) - v) = v + (s * t) • (x - v) := by
      rw [add_sub_cancel_left, smul_smul]
    rw [e] at hsc hsn
    have hst : 0 < s * t := mul_pos (by linarith) ht
    refine ⟨v + (s * t) • (x - v), (mem_space_boundary hσ).2 ⟨hsc, hsn⟩, ?_⟩
    have h1 : polyScale g v (v + (s * t) • (x - v)) = s * t := by
      rw [polyScale_ray g hneg x hst, polyScale_eq_one g hneg hxle ⟨k, hk⟩, mul_one]
    unfold projMap
    rw [h1, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hst.ne', one_smul]
    abel

end SComplex
end Lightlike.PL
