import Lightlike.Spacetime.EHManifold.CompactVariation
import Lightlike.Spacetime.EHManifold.FRCover

/-!
# The first variation of the `f(R)` action on a manifold, for a perturbation with compact support

`fR_first_variation_manifold_compact`: let `g` be a nondegenerate metric on a manifold `M` and `h` a
symmetric tensor field vanishing outside a compact set `K`. Then there are finitely many charts with small
coordinate balls and smooth functions `ρ_i ≥ 0` with `∑_i ρ_i = 1` on `K`, each `K ∩ supp ρ_i` inside the
ball of the chart `i`, such that

`d/dt|₀ ∫_K f(R(g + t h)) d vol_{g + t h} = -∑_i ∫_{φ_i(K ∩ supp ρ_i)} √|g| (ρ_i h)_{ab} (fRTensorUp)^{ab} dy`,

each term in the components of the chart `i`, where
`fRTensorUp = f'(R) R^{ab} - ½ f(R) g^{ab} - ∇^a ∇^b f'(R) + g^{ab} □ f'(R)` is the left side of the metric
`f(R)` field equations.

The right side is the integral of `h_{ab}` against the field-equation tensor, written in charts with a
partition of unity. An intrinsic form would need the covariance of the Hessian of a scalar under a change
of chart, which is not proved here.

## References

* T. P. Sotiriou, V. Faraoni, *f(R) theories of gravity*, arXiv:0805.1726, section II.A, (5)–(6), p. 5.
-/

open MeasureTheory Set Manifold TopologicalSpace Matrix Filter Metric
open scoped ContDiff ENNReal Topology

noncomputable section

namespace Lightlike

set_option synthInstance.maxHeartbeats 400000

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]

/-- **The first variation of the `f(R)` action on a manifold**, for a perturbation of the metric by a
symmetric tensor field with compact support; the result in charts with a partition of unity. -/
theorem fR_first_variation_manifold_compact [Nonempty M] (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)
    (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) {K : Set M} (hK : IsCompact K)
    (hsupp : ∀ p, p ∉ K → h.h p = 0) (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hf' : ContDiff ℝ 2 (deriv f)) :
    ∃ (N : ℕ) (x : ℕ → M) (c : ℕ → Fin n → ℝ) (φ : ∀ k, ContDiffBump (c k)) (ρ : ℕ → M → ℝ)
      (hρ : ∀ i, ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ (ρ i)),
      (∀ k, ball (c k) (φ k).rOut ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) (x k)).target) ∧
      (∀ i q, 0 ≤ ρ i q) ∧ (∀ p ∈ K, ∑ i ∈ Finset.range N, ρ i p = 1) ∧
      (∀ i, K ∩ tsupport (ρ i) ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) (x i)).source) ∧
      (∀ i, extChartAt 𝓘(ℝ, Fin n → ℝ) (x i) '' (K ∩ tsupport (ρ i)) ⊆ ball (c i) (φ i).rIn) ∧
      HasDerivAt (fun t : ℝ => fRAction (g.perturb h t) f K)
        (-∑ i ∈ Finset.range N,
          ∫ y in extChartAt 𝓘(ℝ, Fin n → ℝ) (x i) '' (K ∩ tsupport (ρ i)),
            √|(g.coordMetricR (x i) (φ i) y).det| *
              ∑ α, ∑ β, (h.smulFun (ρ i) (hρ i)).coordComp (x i) y α β *
                fRTensorUp (g.coordMetricR (x i) (φ i)) f y α β) 0 := by
  classical
  obtain ⟨p₀⟩ := ‹Nonempty M›
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (Fin n → ℝ) M
  have hrex : ∀ p : M, ∃ r > 0, ball (extChartAt 𝓘(ℝ, Fin n → ℝ) p p) r ⊆
      (extChartAt 𝓘(ℝ, Fin n → ℝ) p).target := fun p =>
    Metric.isOpen_iff.1 (isOpen_extChartAt_target p) _ (mem_extChartAt_target p)
  choose r hr0 hrball using hrex
  obtain ⟨t, -, htK⟩ := hK.elim_nhds_subcover (fun p => coverU n p (r p))
    (fun p _ => coverU_mem_nhds p (hr0 p))
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = t.toList.length := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : ℕ → M, x = fun k => t.toList.getD k p₀ := ⟨_, rfl⟩
  have hcov : ∀ q ∈ K, ∃ k, k < N ∧ q ∈ coverU n (x k) (r (x k)) := by
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
      F = fun k => if k < N then K ∩ coverC n (x k) (r (x k)) else ∅ := ⟨_, rfl⟩
  have hCc : ∀ k, IsCompact (coverC n (x k) (r (x k))) := fun k =>
    isCompact_coverC (x k) (hr0 (x k)) (hrball (x k))
  have hTc : ∀ k, IsCompact (K ∩ coverC n (x k) (r (x k))) := fun k =>
    hK.inter_right (hCc k).isClosed
  have hFsub : ∀ k, F k ⊆ K ∩ coverC n (x k) (r (x k)) := by
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
  have hAT : ∀ k, disjointed F k ⊆ K ∩ coverC n (x k) (r (x k)) := fun k =>
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
      U' = fun k => if k < N then coverU n (x k) (r (x k)) else ∅ := ⟨_, rfl⟩
  have hU'o : ∀ k, IsOpen (U' k) := by
    intro k
    rw [hU']
    by_cases hk : k < N
    · simp only [if_pos hk]
      exact isOpen_coverU _
    · simp only [if_neg hk]
      exact isOpen_empty
  have hU'sub : ∀ k, U' k ⊆ coverC n (x k) (r (x k)) := by
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
  obtain ⟨pu, hpu⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Fin n → ℝ) hK.isClosed U'
    hU'o hU'c
  have hρ1 : ∀ q ∈ K, ∑ i ∈ Finset.range N, pu i q = 1 := by
    intro q hq
    rw [← pu.sum_eq_one hq]
    refine (finsum_eq_sum_of_support_subset _ fun i hi => ?_).symm
    have hqi : q ∈ U' i := hpu i (subset_tsupport _ hi)
    by_contra hiN
    rw [hU'N i fun hlt => hiN (Finset.mem_coe.2 (Finset.mem_range.2 hlt))] at hqi
    exact hqi
  have hρT : ∀ i, K ∩ tsupport (pu i) ⊆ K ∩ coverC n (x i) (r (x i)) := fun i q hq =>
    ⟨hq.1, hU'sub i (hpu i hq.2)⟩
  refine ⟨N, x, fun k => extChartAt 𝓘(ℝ, Fin n → ℝ) (x k) (x k),
    fun k => coverBump (x k) (r (x k)) (hr0 (x k)), fun i q => pu i q, fun i => (pu i).contMDiff,
    fun k => hrball (x k), fun i q => pu.nonneg i q, hρ1,
    fun i => (hρT i).trans (inter_subset_right.trans
      (coverC_subset_source (x i) (hr0 (x i)) (hrball (x i)))),
    fun i => (image_mono ((hρT i).trans inter_subset_right)).trans
      (image_coverC_subset (x i) (hr0 (x i)) (hrball (x i))), ?_⟩
  exact fR_first_variation_of_cover g hK f hf hf' N x
    (fun k => extChartAt 𝓘(ℝ, Fin n → ℝ) (x k) (x k))
    (fun k => coverBump (x k) (r (x k)) (hr0 (x k))) (fun k => hrball (x k))
    (fun k => K ∩ coverC n (x k) (r (x k))) (disjointed F) hTc
    (fun k => inter_subset_right.trans (coverC_subset_source (x k) (hr0 (x k)) (hrball (x k))))
    (fun k => (image_mono inter_subset_right).trans
      (image_coverC_subset (x k) (hr0 (x k)) (hrball (x k))))
    (fun k => MeasurableSet.disjointed hFm k) hAT (disjoint_disjointed F) hAK h hsupp
    (fun i q => pu i q) (fun i => (pu i).contMDiff) hρ1 hρT

end Lightlike
