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

/-- **Edge lengths of a small coordinate simplex.** For a compact `K ⊆ U` and `R ≥ 0` there are `C`
and `h₀ > 0` such that for `x ∈ K`, `0 < h ≤ h₀` and `‖u‖, ‖v‖ ≤ R`, the squared geodesic distance
between `x + h u` and `x + h v` is `h² g_x(v - u, v - u) + O(h³)`:
`|d(x + h u, x + h v)² - h² g_x(v - u, v - u)| ≤ C h³`. -/
theorem IsRiemMetric.chartDist_sq_simplex_edge (hg : IsRiemMetric g U) {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKU : K ⊆ U) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C h₀ : ℝ, 0 < h₀ ∧ ∀ x ∈ K, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ u v : Fin n → ℝ,
      ‖u‖ ≤ R → ‖v‖ ≤ R →
      |chartDist g U (x + h • u) (x + h • v) ^ 2 - h ^ 2 * ((v - u) ⬝ᵥ (g x *ᵥ (v - u)))| ≤
        C * h ^ 3 := by
  obtain ⟨C, r, ε, hr, hε, hE⟩ := hg.chartDist_sq_edge hK hKU
  have hR1 : 0 < R + 1 := by linarith
  refine ⟨|C| * (12 * R ^ 3), min ε r / (2 * (R + 1)), by positivity,
    fun x hx h hh hh0 u v hu hv => ?_⟩
  have hmin : h * (2 * (R + 1)) ≤ min ε r := by
    rwa [le_div_iff₀ (by positivity)] at hh0
  have hεm : min ε r ≤ ε := min_le_left _ _
  have hrm : min ε r ≤ r := min_le_right _ _
  have hau : ‖x + h • u - x‖ = h * ‖u‖ := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hh.le]
  have hba : (x + h • v) - (x + h • u) = h • (v - u) := by
    rw [add_sub_add_left_eq_sub, smul_sub]
  have hvu : ‖v - u‖ ≤ 2 * R := by
    calc ‖v - u‖ ≤ ‖v‖ + ‖u‖ := norm_sub_le _ _
      _ ≤ 2 * R := by linarith
  have hbn : ‖(x + h • v) - (x + h • u)‖ = h * ‖v - u‖ := by
    rw [hba, norm_smul, Real.norm_of_nonneg hh.le]
  have hu' : h * ‖u‖ ≤ h * R := mul_le_mul_of_nonneg_left hu hh.le
  have hvu' : h * ‖v - u‖ ≤ h * (2 * R) := mul_le_mul_of_nonneg_left hvu hh.le
  have h1 : ‖x + h • u - x‖ ≤ ε := by
    rw [hau]; nlinarith
  have h2 : ‖(x + h • v) - (x + h • u)‖ ≤ r := by
    rw [hbn]; nlinarith
  have e := hE x hx (x + h • u) (x + h • v) h1 h2
  rw [hbn, hau, hba] at e
  have hq : (h • (v - u)) ⬝ᵥ (g x *ᵥ (h • (v - u))) = h ^ 2 * ((v - u) ⬝ᵥ (g x *ᵥ (v - u))) := by
    rw [mulVec_smul, dotProduct_smul, smul_dotProduct]; simp only [smul_eq_mul]; ring
  rw [hq] at e
  refine e.trans ?_
  have hn : 0 ≤ ‖v - u‖ := norm_nonneg _
  have hnu : 0 ≤ ‖u‖ := norm_nonneg _
  have hb3 : (h * ‖v - u‖) ^ 3 ≤ (h * (2 * R)) ^ 3 := by gcongr
  have hb2 : h * ‖u‖ * (h * ‖v - u‖) ^ 2 ≤ h * R * (h * (2 * R)) ^ 2 := by gcongr
  have hsum : (h * ‖v - u‖) ^ 3 + h * ‖u‖ * (h * ‖v - u‖) ^ 2 ≤ (12 * R ^ 3) * h ^ 3 := by
    nlinarith
  calc C * ((h * ‖v - u‖) ^ 3 + h * ‖u‖ * (h * ‖v - u‖) ^ 2)
      ≤ |C| * ((h * ‖v - u‖) ^ 3 + h * ‖u‖ * (h * ‖v - u‖) ^ 2) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * ((12 * R ^ 3) * h ^ 3) := mul_le_mul_of_nonneg_left hsum (abs_nonneg C)
    _ = |C| * (12 * R ^ 3) * h ^ 3 := by ring

end Lightlike.Upstream.GeodesicExpansion
