import Lightlike.PL.Image
import Lightlike.PL.StellarHomeo

/-!
# A geometric complex is PL homeomorphic to its abstract realisation

For a geometric complex `K` whose vertices are points of a real vector space `E`, the linear map
`x ↦ ∑ v, x v • v` from finitely supported weights to `E` is a PL homeomorphism from the
geometric realisation `K.real` of the abstract complex onto `K`. It is linear, hence piecewise
linear; it maps the simplex of `K.real` on a face `s` onto the convex hull of `s`; and it is
injective on `|K.real|` because the faces of `K` are affinely independent and meet in common
faces (Lickorish, Definition 2.1 and the definition of piecewise linear homeomorphism, p. 301-302).

## Main results

* `Lightlike.PL.linearSum`
* `Lightlike.PL.SComplex.isPLHomeo_real_geom`
-/

open Finset

namespace Lightlike.PL
namespace SComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]

/-- The linear map from finitely supported weights to the vector space, `x ↦ ∑ v, x v • v`. -/
noncomputable def linearSum (E : Type*) [AddCommGroup E] [Module ℝ E] : (E →₀ ℝ) →ₗ[ℝ] E :=
  Finsupp.linearCombination ℝ id

omit [DecidableEq E] in
lemma linearSum_apply (x : E →₀ ℝ) : linearSum E x = ∑ v ∈ x.support, x v • v := by
  simp [linearSum, Finsupp.linearCombination_apply, Finsupp.sum]

omit [DecidableEq E] in
/-- On a point supported in `s`, the linear map is the sum over `s`. -/
lemma linearSum_eq_sum {s : Finset E} {x : E →₀ ℝ} (hx : ∀ v ∉ s, x v = 0) :
    linearSum E x = ∑ v ∈ s, x v • v := by
  rw [linearSum_apply]
  refine Finset.sum_subset (fun v hv => ?_) (fun v _ hv => ?_)
  · by_contra h; exact (Finsupp.mem_support_iff.1 hv) (hx v h)
  · rw [Finsupp.notMem_support_iff.1 hv, zero_smul]

omit [DecidableEq E] in
/-- **Uniqueness of barycentric coordinates.** -/
lemma bary_unique {s : Finset E} (hs : AffineIndependent ℝ ((↑) : s → E)) {w₁ w₂ : E → ℝ}
    (h1 : ∑ v ∈ s, w₁ v = 1) (h2 : ∑ v ∈ s, w₂ v = 1)
    (h : ∑ v ∈ s, w₁ v • v = ∑ v ∈ s, w₂ v • v) : ∀ v ∈ s, w₁ v = w₂ v := by
  have e1 : ∑ i : s, w₁ i = 1 := by rw [Finset.sum_coe_sort s w₁]; exact h1
  have e2 : ∑ i : s, w₂ i = 1 := by rw [Finset.sum_coe_sort s w₂]; exact h2
  have e3 : ∑ i : s, w₁ i • (i : E) = ∑ i : s, w₂ i • (i : E) := by
    rw [Finset.sum_coe_sort s (fun v => w₁ v • v), Finset.sum_coe_sort s (fun v => w₂ v • v)]
    exact h
  have key := (affineIndependent_iff_eq_of_fintype_affineCombination_eq ℝ ((↑) : s → E)).1 hs
    (fun i => w₁ i) (fun i => w₂ i) e1 e2 (by
      rw [Finset.affineCombination_eq_linear_combination _ _ _ e1,
        Finset.affineCombination_eq_linear_combination _ _ _ e2]
      exact e3)
  intro v hv
  exact congrFun key ⟨v, hv⟩

/-- The linear map sends the simplex on the basis vectors of `s` into the hull of `s`. -/
lemma linearSum_mem_hull {s : Finset E} {x : E →₀ ℝ}
    (hx : x ∈ convexHull ℝ ((s.map (vertexEmb E) : Finset (E →₀ ℝ)) : Set (E →₀ ℝ))) :
    linearSum E x ∈ convexHull ℝ (s : Set E) := by
  obtain ⟨h0, hs0, h1⟩ := mem_convexHull_vertexEmb.1 hx
  rw [linearSum_eq_sum hs0]
  exact Finset.mem_convexHull'.2 ⟨fun v => x v, fun y _ => h0 y, h1, rfl⟩

/-- Every point of the hull of `s` comes from the simplex on the basis vectors of `s`. -/
lemma exists_preimage_hull {s : Finset E} {y : E} (hy : y ∈ convexHull ℝ (s : Set E)) :
    ∃ x ∈ convexHull ℝ ((s.map (vertexEmb E) : Finset (E →₀ ℝ)) : Set (E →₀ ℝ)),
      linearSum E x = y := by
  obtain ⟨w, hw0, hw1, hwy⟩ := Finset.mem_convexHull'.1 hy
  set x : E →₀ ℝ := ∑ v ∈ s, Finsupp.single v (w v) with hx
  have hxv : ∀ v, x v = if v ∈ s then w v else 0 := by
    intro v
    simp only [hx, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
  have h0 : ∀ v, 0 ≤ x v := fun v => by
    rw [hxv]; split_ifs with h
    · exact hw0 v h
    · exact le_rfl
  have hout : ∀ v ∉ s, x v = 0 := fun v hv => by simp [hxv, hv]
  have hxs : ∀ v ∈ s, x v = w v := fun v hv => by simp [hxv, hv]
  refine ⟨x, mem_convexHull_vertexEmb.2 ⟨h0, hout, ?_⟩, ?_⟩
  · rw [Finset.sum_congr rfl hxs]
    exact hw1
  · rw [linearSum_eq_sum hout, Finset.sum_congr rfl fun v hv => congrArg (· • v) (hxs v hv)]
    exact hwy

/-- **A geometric complex is PL homeomorphic to its abstract realisation.** For a geometric
complex `K` whose vertices are points of `E`, the linear map `x ↦ ∑ v, x v • v` is a PL
homeomorphism from the geometric realisation `K.real` onto `K`. -/
theorem isPLHomeo_real_geom {K : SComplex E} (hK : IsGeom K) :
    IsPLHomeo K.real K (linearSum E) := by
  refine ⟨?_, hK, ?_⟩
  · exact IsPLMap.of_affine (isGeom_real K) (linearSum E).toAffineMap
  · refine ⟨?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨s', hs', hxs⟩ := mem_space.1 hx
      obtain ⟨t, ht, rfl⟩ := mem_real.1 hs'
      exact convexHull_subset_space ht (linearSum_mem_hull hxs)
    · intro x hx x' hx' hxx
      obtain ⟨s₁, hs₁, hxs⟩ := mem_space.1 hx
      obtain ⟨t, ht, rfl⟩ := mem_real.1 hs₁
      obtain ⟨s₂, hs₂, hxs'⟩ := mem_space.1 hx'
      obtain ⟨t', ht', rfl⟩ := mem_real.1 hs₂
      have hy : linearSum E x ∈ convexHull ℝ ((t ∩ t' : Finset E) : Set E) := by
        rw [Finset.coe_inter]
        exact hK.inter t ht t' ht' ⟨linearSum_mem_hull hxs, hxx ▸ linearSum_mem_hull hxs'⟩
      obtain ⟨c, hc0, hc1, hcy⟩ := Finset.mem_convexHull'.1 hy
      set c' : E → ℝ := fun v => if v ∈ t ∩ t' then c v else 0 with hc'
      obtain ⟨hx0, hxout, hx1⟩ := mem_convexHull_vertexEmb.1 hxs
      obtain ⟨hx0', hxout', hx1'⟩ := mem_convexHull_vertexEmb.1 hxs'
      have hsum : ∀ u : Finset E, t ∩ t' ⊆ u → ∑ v ∈ u, c' v = 1 ∧ ∑ v ∈ u, c' v • v = linearSum E x := by
        intro u hu
        have e1 : ∑ v ∈ u, c' v = ∑ v ∈ t ∩ t', c v := by
          simp only [hc']
          rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hu]
        have e2 : ∑ v ∈ u, c' v • v = ∑ v ∈ t ∩ t', c v • v := by
          simp only [hc', ite_smul, zero_smul]
          rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hu]
        exact ⟨by rw [e1]; exact hc1, by rw [e2]; exact hcy⟩
      have hxc : ∀ v, x v = c' v := by
        intro v
        by_cases hv : v ∈ t
        · have := bary_unique (hK.indep t ht) (w₁ := fun v => x v) (w₂ := c') hx1
            (hsum t Finset.inter_subset_left).1
            (by rw [← linearSum_eq_sum hxout]; exact (hsum t Finset.inter_subset_left).2.symm) v hv
          exact this
        · rw [hxout v hv]; simp [hc', hv]
      have hxc' : ∀ v, x' v = c' v := by
        intro v
        by_cases hv : v ∈ t'
        · have := bary_unique (hK.indep t' ht') (w₁ := fun v => x' v) (w₂ := c') hx1'
            (hsum t' Finset.inter_subset_right).1
            (by rw [← linearSum_eq_sum hxout', ← hxx]; exact (hsum t' Finset.inter_subset_right).2.symm) v hv
          exact this
        · rw [hxout' v hv]; simp [hc', hv]
      exact Finsupp.ext fun v => (hxc v).trans (hxc' v).symm
    · intro y hy
      obtain ⟨s, hs, hys⟩ := mem_space.1 hy
      obtain ⟨x, hx, hxy⟩ := exists_preimage_hull hys
      exact ⟨x, convexHull_subset_space (mem_real.2 ⟨s, hs, rfl⟩) hx, hxy⟩

end SComplex

end Lightlike.PL
