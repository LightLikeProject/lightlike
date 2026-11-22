import Lightlike.Upstream.GeodesicExpansion.Corollaries
import Lightlike.Upstream.GeodesicExpansion.Jet
import Mathlib

/-!
# Regge edge lengths from the expansion of the squared distance (Tier 2)

First step towards the Cheeger–Müller–Schrader programme (milestone RC6): the geodesic edge lengths
of a small coordinate simplex are, to leading order, the flat edge lengths of the metric frozen at
one vertex.

* `IsRiemMetric.exists_lipschitz_entries`: uniform Lipschitz bound of the entries of `g` for base
  points of a compact `K ⊆ U` and nearby points.
* `IsRiemMetric.abs_normSq_sub_le`: `|g_a(w, w) - g_x(w, w)| ≤ C ‖a - x‖ ‖w‖²`.
-/

open Matrix Set Filter Topology Metric

noncomputable section

namespace Lightlike.Upstream.GeodesicExpansion

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
  {U : TopologicalSpace.Opens (Fin n → ℝ)}

/-- **Uniform Lipschitz bound for the metric entries.** For a compact `K ⊆ U` there are `L ≥ 0` and
`ε > 0` such that for `x ∈ K` and `‖a - x‖ ≤ ε` we have `a ∈ U` and
`|g_a(i, j) - g_x(i, j)| ≤ L ‖a - x‖`. -/
theorem IsRiemMetric.exists_lipschitz_entries (hg : IsRiemMetric g U) {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ L ε : ℝ, 0 ≤ L ∧ 0 < ε ∧ ∀ x ∈ K, ∀ a : Fin n → ℝ, ‖a - x‖ ≤ ε →
      a ∈ (U : Set (Fin n → ℝ)) ∧ ∀ i j, |g a i j - g x i j| ≤ L * ‖a - x‖ := by
  obtain ⟨ε, hε, hsub⟩ := hK.exists_cthickening_subset_open hg.coord.isOpen hKU
  have hloc : ∀ i j, ∃ Lc : NNReal, LipschitzOnWith Lc (fun y => g y i j) (cthickening ε K) := by
    intro i j
    have hl : LocallyLipschitzOn (U : Set (Fin n → ℝ)) (fun y => g y i j) := by
      intro x hx
      have hcd : ContDiffAt ℝ 1 (fun y => g y i j) x :=
        ((hg.coord.smooth i j).contDiffAt (hg.coord.isOpen.mem_nhds hx)).of_le
          (by exact_mod_cast le_top)
      obtain ⟨Kc, t, ht, hl⟩ := hcd.exists_lipschitzOnWith
      exact ⟨Kc, t, mem_nhdsWithin_of_mem_nhds ht, hl⟩
    exact LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK.cthickening (hl.mono hsub)
  choose Lc hLc using hloc
  refine ⟨∑ i, ∑ j, (Lc i j : ℝ), ε, Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => (Lc i j).2, hε, fun x hx a ha => ?_⟩
  have hdist : dist a x ≤ ε := by rwa [dist_eq_norm]
  have hmem : a ∈ cthickening ε K := mem_cthickening_of_dist_le a x ε K hx hdist
  refine ⟨hsub hmem, fun i j => ?_⟩
  have h1 := (hLc i j).dist_le_mul a hmem x (self_subset_cthickening _ hx)
  rw [Real.dist_eq, dist_eq_norm] at h1
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  have hij : (Lc i j : ℝ) ≤ ∑ j', (Lc i j' : ℝ) :=
    Finset.single_le_sum (f := fun j' => (Lc i j' : ℝ)) (fun j' _ => (Lc i j').2)
      (Finset.mem_univ j)
  have hi : (∑ j', (Lc i j' : ℝ)) ≤ ∑ i', ∑ j', (Lc i' j' : ℝ) :=
    Finset.single_le_sum (f := fun i' => ∑ j', (Lc i' j' : ℝ))
      (fun i' _ => Finset.sum_nonneg fun j' _ => (Lc i' j').2) (Finset.mem_univ i)
  exact hij.trans hi

/-- **The quadratic form varies Lipschitz-continuously with the base point.** For a compact
`K ⊆ U` there are `C ≥ 0` and `ε > 0` such that for `x ∈ K`, `‖a - x‖ ≤ ε`, `a ∈ U` and all `w`:
`|g_a(w, w) - g_x(w, w)| ≤ C ‖a - x‖ ‖w‖²`. -/
theorem IsRiemMetric.abs_normSq_sub_le (hg : IsRiemMetric g U) {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧ ∀ x ∈ K, ∀ a : Fin n → ℝ, ‖a - x‖ ≤ ε →
      a ∈ (U : Set (Fin n → ℝ)) ∧ ∀ w : Fin n → ℝ,
        |w ⬝ᵥ (g a *ᵥ w) - w ⬝ᵥ (g x *ᵥ w)| ≤ C * ‖a - x‖ * ‖w‖ ^ 2 := by
  obtain ⟨L, ε, hL, hε, h⟩ := hg.exists_lipschitz_entries hK hKU
  refine ⟨n ^ 2 * L, ε, by positivity, hε, fun x hx a ha => ⟨(h x hx a ha).1, fun w => ?_⟩⟩
  have hM : ∀ i j, |(g a - g x) i j| ≤ L * ‖a - x‖ := fun i j => by
    simpa using (h x hx a ha).2 i j
  have := abs_dot_mulVec_le (mul_nonneg hL (norm_nonneg _)) hM w w
  rw [sub_mulVec, dotProduct_sub] at this
  calc _ ≤ _ := this
    _ = _ := by ring

/-- **Edge expansion with a frozen metric.** For a compact `K ⊆ U` there are `C`, `r > 0`, `ε > 0`
such that for `x ∈ K`, `‖a - x‖ ≤ ε`, `‖b - a‖ ≤ r`:
`|d(a, b)² - g_x(b - a, b - a)| ≤ C (‖b - a‖³ + ‖a - x‖ ‖b - a‖²)`. -/
theorem IsRiemMetric.chartDist_sq_edge (hg : IsRiemMetric g U) {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C r ε : ℝ, 0 < r ∧ 0 < ε ∧ ∀ x ∈ K, ∀ a b : Fin n → ℝ, ‖a - x‖ ≤ ε → ‖b - a‖ ≤ r →
      |chartDist g U a b ^ 2 - (b - a) ⬝ᵥ (g x *ᵥ (b - a))| ≤
        C * (‖b - a‖ ^ 3 + ‖a - x‖ * ‖b - a‖ ^ 2) := by
  obtain ⟨ε0, hε0, hsub⟩ := hK.exists_cthickening_subset_open hg.coord.isOpen hKU
  obtain ⟨C1, r, hr, h1⟩ := hg.chartDist_sq_third hK.cthickening hsub
  obtain ⟨C2, ε1, hC2, hε1, h2⟩ := hg.abs_normSq_sub_le hK hKU
  refine ⟨|C1| + C2, r, min ε0 ε1, hr, lt_min hε0 hε1, fun x hx a b ha hb => ?_⟩
  have haε0 : ‖a - x‖ ≤ ε0 := ha.trans (min_le_left _ _)
  have haε1 : ‖a - x‖ ≤ ε1 := ha.trans (min_le_right _ _)
  have hmem : a ∈ cthickening ε0 K :=
    mem_cthickening_of_dist_le a x ε0 K hx (by rwa [dist_eq_norm])
  have e1 := h1 a hmem (b - a) hb
  rw [add_sub_cancel] at e1
  have e2 := (h2 x hx a haε1).2 (b - a)
  have hn3 : 0 ≤ ‖b - a‖ ^ 3 := by positivity
  have hn2 : 0 ≤ ‖a - x‖ * ‖b - a‖ ^ 2 := by positivity
  have hC1 : C1 * ‖b - a‖ ^ 3 ≤ |C1| * ‖b - a‖ ^ 3 :=
    mul_le_mul_of_nonneg_right (le_abs_self C1) hn3
  calc |chartDist g U a b ^ 2 - (b - a) ⬝ᵥ (g x *ᵥ (b - a))|
      = |(chartDist g U a b ^ 2 - (b - a) ⬝ᵥ (g a *ᵥ (b - a))) +
          ((b - a) ⬝ᵥ (g a *ᵥ (b - a)) - (b - a) ⬝ᵥ (g x *ᵥ (b - a)))| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ C1 * ‖b - a‖ ^ 3 + C2 * ‖a - x‖ * ‖b - a‖ ^ 2 := add_le_add e1 e2
    _ ≤ (|C1| + C2) * (‖b - a‖ ^ 3 + ‖a - x‖ * ‖b - a‖ ^ 2) := by
      have : |C1| * ‖b - a‖ ^ 3 ≥ C1 * ‖b - a‖ ^ 3 := hC1
      nlinarith [mul_nonneg (abs_nonneg C1) hn2]

end Lightlike.Upstream.GeodesicExpansion
