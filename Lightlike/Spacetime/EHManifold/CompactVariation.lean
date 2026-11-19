import Mathlib.Geometry.Manifold.PartitionOfUnity
import Lightlike.Spacetime.EHManifold.CoverVariation

/-!
# The first variation of the Einstein–Hilbert action for a perturbation with compact support

`eh_first_variation_manifold_compact`: for a metric `g` (of any signature) on a manifold `M` and a smooth
symmetric tensor field `h` that vanishes outside a compact set `K`,

`d/dt ∫_K (R(g + t h) - 2Λ) d vol_{g + t h} = -∫_K ⟨G + Λ g, h⟩_g d vol_g` at `t = 0`,

with `G` the Einstein tensor of `g` and `⟨·, ·⟩_g` the contraction with the inverse metric. Both sides are
intrinsic, and there is no condition on `K` beyond compactness.

The proof covers `K` by finitely many small coordinate balls, cuts it into disjoint measurable pieces, and
uses a smooth partition of unity (`SmoothPartitionOfUnity.exists_isSubordinate`) with
`eh_first_variation_of_cover`.

## References

* S. M. Carroll, *Lecture Notes on General Relativity*, arXiv gr-qc/9712019, chapter 4, eqs. (4.54) to
  (4.67), pp. 114 to 116.
-/

open MeasureTheory Set Manifold TopologicalSpace Matrix Filter Metric
open scoped ContDiff ENNReal Topology

noncomputable section

namespace Lightlike

set_option synthInstance.maxHeartbeats 400000

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]

/-- The open neighbourhood of `p` used in the cover: the points of the chart at `p` whose coordinates are
within `r / 4` of those of `p`. -/
def coverU (p : M) (r : ℝ) : Set M :=
  (extChartAt 𝓘(ℝ, Fin n → ℝ) p).source ∩
    extChartAt 𝓘(ℝ, Fin n → ℝ) p ⁻¹' ball (extChartAt 𝓘(ℝ, Fin n → ℝ) p p) (r / 4)

/-- The compact set around `p` used in the cover: the inverse chart image of the closed coordinate ball of
radius `r / 4`. -/
def coverC (p : M) (r : ℝ) : Set M :=
  (extChartAt 𝓘(ℝ, Fin n → ℝ) p).symm '' closedBall (extChartAt 𝓘(ℝ, Fin n → ℝ) p p) (r / 4)

/-- The bump data at the coordinates of `p` with radii `r / 2 < r`. -/
def coverBump (p : M) (r : ℝ) (hr : 0 < r) : ContDiffBump (extChartAt 𝓘(ℝ, Fin n → ℝ) p p) :=
  ⟨r / 2, r, half_pos hr, half_lt_self hr⟩

variable (p : M) {r : ℝ} (hr : 0 < r)
  (hrb : ball (extChartAt 𝓘(ℝ, Fin n → ℝ) p p) r ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) p).target)

include hr hrb

lemma closedBall_quarter_subset_target :
    closedBall (extChartAt 𝓘(ℝ, Fin n → ℝ) p p) (r / 4) ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) p).target :=
  (closedBall_subset_ball (by linarith)).trans hrb

lemma isCompact_coverC : IsCompact (coverC p r) :=
  (isCompact_closedBall _ _).image_of_continuousOn
    ((continuousOn_extChartAt_symm p).mono (closedBall_quarter_subset_target p hr hrb))

lemma coverC_subset_source : coverC p r ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) p).source := by
  rintro _ ⟨z, hz, rfl⟩
  exact (extChartAt 𝓘(ℝ, Fin n → ℝ) p).map_target (closedBall_quarter_subset_target p hr hrb hz)

lemma image_coverC_subset :
    extChartAt 𝓘(ℝ, Fin n → ℝ) p '' coverC p r ⊆ ball (extChartAt 𝓘(ℝ, Fin n → ℝ) p p) (r / 2) := by
  rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  rw [(extChartAt 𝓘(ℝ, Fin n → ℝ) p).right_inv (closedBall_quarter_subset_target p hr hrb hz)]
  exact closedBall_subset_ball (by linarith) hz

omit hr hrb in
lemma coverU_subset_coverC : coverU p r ⊆ coverC p r := fun q hq =>
  ⟨extChartAt 𝓘(ℝ, Fin n → ℝ) p q, ball_subset_closedBall hq.2,
    (extChartAt 𝓘(ℝ, Fin n → ℝ) p).left_inv hq.1⟩

omit hr hrb in
lemma isOpen_coverU : IsOpen (coverU p r) :=
  (continuousOn_extChartAt p).isOpen_inter_preimage (isOpen_extChartAt_source p) isOpen_ball

omit hrb in
lemma coverU_mem_nhds : coverU p r ∈ 𝓝 p :=
  (isOpen_coverU p).mem_nhds ⟨mem_extChartAt_source p, mem_ball_self (by linarith)⟩

omit hr hrb

variable [SecondCountableTopology M] [T2Space M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]
  [MeasurableSpace M] [BorelSpace M]

/-- **The first variation of the Einstein–Hilbert action on a manifold**, for a perturbation of the metric
by a symmetric tensor field with compact support. -/
theorem eh_first_variation_manifold_compact (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)
    (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) {K : Set M} (hK : IsCompact K)
    (hsupp : ∀ p, p ∉ K → h.h p = 0) (Λ : ℝ) :
    HasDerivAt (fun t : ℝ => ehAction (g.perturb h t) Λ K)
      (-∫ p in K, ehIntegrand g h Λ p ∂(NondegMetric.volumeMeasure g)) 0 := by
  classical
  rcases isEmpty_or_nonempty M with hM | hM
  · have hKe : K = ∅ := Set.eq_empty_of_isEmpty K
    subst hKe
    simp only [ehAction, Measure.restrict_empty, integral_zero_measure, neg_zero]
    exact hasDerivAt_const 0 0
  obtain ⟨p₀⟩ := hM
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (Fin n → ℝ) M
  have hrex : ∀ p : M, ∃ r > 0, ball (extChartAt 𝓘(ℝ, Fin n → ℝ) p p) r ⊆
      (extChartAt 𝓘(ℝ, Fin n → ℝ) p).target := fun p =>
    Metric.isOpen_iff.1 (isOpen_extChartAt_target p) _ (mem_extChartAt_target p)
  choose r hr0 hrball using hrex
  obtain ⟨t, -, htK⟩ := hK.elim_nhds_subcover (fun p => coverU p (r p))
    (fun p _ => coverU_mem_nhds p (hr0 p))
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = t.toList.length := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : ℕ → M, x = fun k => t.toList.getD k p₀ := ⟨_, rfl⟩
  have hcov : ∀ q ∈ K, ∃ k, k < N ∧ q ∈ coverU (x k) (r (x k)) := by
    intro q hq
    obtain ⟨p, hp, hqU⟩ := mem_iUnion₂.1 (htK hq)
    obtain ⟨k, hk, hkp⟩ := List.getElem_of_mem (Finset.mem_toList.2 hp)
    refine ⟨k, by rw [hN]; exact hk, ?_⟩
    have hxk : x k = p := by
      rw [hx]
      show t.toList.getD k p₀ = p
      rw [List.getD_eq_getElem _ _ hk, hkp]
    rw [hxk]
    exact hqU
  -- the pieces
  obtain ⟨F, hF⟩ : ∃ F : ℕ → Set M,
      F = fun k => if k < N then K ∩ coverC (x k) (r (x k)) else ∅ := ⟨_, rfl⟩
  have hCc : ∀ k, IsCompact (coverC (x k) (r (x k))) := fun k =>
    isCompact_coverC (x k) (hr0 (x k)) (hrball (x k))
  have hTc : ∀ k, IsCompact (K ∩ coverC (x k) (r (x k))) := fun k =>
    hK.inter_right (hCc k).isClosed
  have hFsub : ∀ k, F k ⊆ K ∩ coverC (x k) (r (x k)) := by
    intro k
    rw [hF]
    by_cases hk : k < N
    · simp only [if_pos hk]
      exact subset_rfl
    · simp only [if_neg hk]
      exact empty_subset _
  have hFm : ∀ k, MeasurableSet (F k) := by
    intro k
    rw [hF]
    by_cases hk : k < N
    · simp only [if_pos hk]
      exact (hTc k).measurableSet
    · simp only [if_neg hk]
      exact MeasurableSet.empty
  have hFN : ∀ k, ¬ k < N → F k = ∅ := by
    intro k hk
    rw [hF]
    simp only [if_neg hk]
  have hAT : ∀ k, disjointed F k ⊆ K ∩ coverC (x k) (r (x k)) := fun k =>
    (disjointed_le F k).trans (hFsub k)
  have hAK : K = ⋃ k ∈ Finset.range N, disjointed F k := by
    ext q
    constructor
    · intro hq
      obtain ⟨k, hk, hqU⟩ := hcov q hq
      have hqF : q ∈ ⋃ k, F k := by
        refine mem_iUnion.2 ⟨k, ?_⟩
        rw [hF]
        simp only [if_pos hk]
        exact ⟨hq, coverU_subset_coverC _ hqU⟩
      rw [← iUnion_disjointed] at hqF
      obtain ⟨j, hj⟩ := mem_iUnion.1 hqF
      have hjN : j < N := by
        by_contra hjN
        have := disjointed_le F j hj
        rw [hFN j hjN] at this
        exact this
      exact mem_iUnion₂.2 ⟨j, Finset.mem_range.2 hjN, hj⟩
    · intro hq
      obtain ⟨k, -, hqk⟩ := mem_iUnion₂.1 hq
      exact (hAT k hqk).1
  -- the partition of unity
  obtain ⟨U', hU'⟩ : ∃ U' : ℕ → Set M,
      U' = fun k => if k < N then coverU (x k) (r (x k)) else ∅ := ⟨_, rfl⟩
  have hU'o : ∀ k, IsOpen (U' k) := by
    intro k
    rw [hU']
    by_cases hk : k < N
    · simp only [if_pos hk]
      exact isOpen_coverU _
    · simp only [if_neg hk]
      exact isOpen_empty
  have hU'sub : ∀ k, U' k ⊆ coverC (x k) (r (x k)) := by
    intro k
    rw [hU']
    by_cases hk : k < N
    · simp only [if_pos hk]
      exact coverU_subset_coverC _
    · simp only [if_neg hk]
      exact empty_subset _
  have hU'N : ∀ k, ¬ k < N → U' k = ∅ := by
    intro k hk
    rw [hU']
    simp only [if_neg hk]
  have hU'c : K ⊆ ⋃ k, U' k := by
    intro q hq
    obtain ⟨k, hk, hqU⟩ := hcov q hq
    refine mem_iUnion.2 ⟨k, ?_⟩
    rw [hU']
    simp only [if_pos hk]
    exact hqU
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Fin n → ℝ) hK.isClosed U'
    hU'o hU'c
  have hρ1 : ∀ q ∈ K, ∑ i ∈ Finset.range N, f i q = 1 := by
    intro q hq
    rw [← f.sum_eq_one hq]
    refine (finsum_eq_sum_of_support_subset _ fun i hi => ?_).symm
    have hqi : q ∈ U' i := hf i (subset_tsupport _ hi)
    by_contra hiN
    rw [hU'N i fun hlt => hiN (Finset.mem_coe.2 (Finset.mem_range.2 hlt))] at hqi
    exact hqi
  have hρT : ∀ i, K ∩ tsupport (f i) ⊆ K ∩ coverC (x i) (r (x i)) := fun i q hq =>
    ⟨hq.1, hU'sub i (hf i hq.2)⟩
  exact eh_first_variation_of_cover g hK Λ N x (fun k => extChartAt 𝓘(ℝ, Fin n → ℝ) (x k) (x k))
    (fun k => coverBump (x k) (r (x k)) (hr0 (x k))) (fun k => hrball (x k))
    (fun k => K ∩ coverC (x k) (r (x k))) (disjointed F) hTc
    (fun k => inter_subset_right.trans (coverC_subset_source (x k) (hr0 (x k)) (hrball (x k))))
    (fun k => (image_mono inter_subset_right).trans
      (image_coverC_subset (x k) (hr0 (x k)) (hrball (x k))))
    (fun k => MeasurableSet.disjointed hFm k) hAT (disjoint_disjointed F) hAK h hsupp
    (fun i q => f i q) (fun i => (f i).contMDiff) hρ1 hρT

end Lightlike
