import Lightlike.Spacetime.EHManifold.ActionPieces
import Lightlike.Spacetime.EHManifold.FluxLocal
import Lightlike.Spacetime.EHManifold.IntegrandLinear
import Lightlike.Spacetime.EHManifold.IntrinsicVariation

/-!
# The first variation for a perturbation with compact support, given a cover by small chart balls

`eh_first_variation_of_cover`: let `h` be a symmetric tensor field vanishing outside a compact set `K`, and
suppose `K` is cut into finitely many disjoint measurable pieces `A k`, each inside a compact set `T k` in a
small coordinate ball of a chart, with smooth functions `ρ i` summing to `1` on `K` such that
`K ∩ tsupport (ρ i) ⊆ T i`. Then

`d/dt ehAction (g + t h) Λ K = -∫_K ⟨G + Λ g, h⟩_g d vol_g` at `t = 0`.

The proof: over a piece, the derivative of the action is the chart integral of the Einstein term plus a
divergence (`hasDerivAt_ehAction_piece`); the resulting formula is additive in `h` (`pieceVar_sum`); and for
`ρ i h`, supported in one small ball, it agrees with `eh_first_variation_manifold_intrinsic`.

The existence of such a cover is a separate statement.
-/

open MeasureTheory Set Manifold TopologicalSpace Matrix Filter Metric
open scoped ContDiff ENNReal Topology

noncomputable section

namespace Lightlike

set_option synthInstance.maxHeartbeats 400000

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]

variable (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) {K : Set M} (hK : IsCompact K) (Λ : ℝ)
  (N : ℕ) (x : ℕ → M) (c : ℕ → Fin n → ℝ) (φ : ∀ k, ContDiffBump (c k))
  (hball : ∀ k, ball (c k) (φ k).rOut ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) (x k)).target)
  (T A : ℕ → Set M) (hT : ∀ k, IsCompact (T k))
  (hT0 : ∀ k, T k ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) (x k)).source)
  (hTball : ∀ k, extChartAt 𝓘(ℝ, Fin n → ℝ) (x k) '' T k ⊆ ball (c k) (φ k).rIn)
  (hA : ∀ k, MeasurableSet (A k)) (hAT : ∀ k, A k ⊆ T k) (hAd : Pairwise (Function.onFun Disjoint A))
  (hAK : K = ⋃ k ∈ Finset.range N, A k)

include hK hball hT hT0 hTball hA hAT hAd hAK in
/-- The derivative of the action over `K` as a sum over the pieces, for any perturbation vanishing outside
`K`. -/
theorem hasDerivAt_ehAction_pieces (f : SymBilinField 𝓘(ℝ, Fin n → ℝ) M)
    (hf : ∀ p, p ∉ K → f.h p = 0) :
    HasDerivAt (fun t : ℝ => ehAction (g.perturb f t) Λ K)
      (∑ k ∈ Finset.range N, pieceVar g f (x k) (φ k) Λ (T k) (A k)) 0 := by
  obtain ⟨ε, hε, hnd⟩ := g.exists_addSmul_nondegenerate f hK hf
  have hfun : (fun t : ℝ => ehAction (g.perturb f t) Λ K) =
      fun t => ∑ k ∈ Finset.range N, ehAction (g.perturb f t) Λ (A k) := by
    funext t
    rw [hAK]
    exact ehAction_biUnion (g.perturb f t) Λ (Finset.range N) A T x (fun k _ => hA k)
      (fun i _ j _ hij => hAd hij) (fun k _ => hT k) (fun k _ => hT0 k) (fun k _ => hAT k)
  rw [hfun]
  exact HasDerivAt.fun_sum fun k _ =>
    hasDerivAt_ehAction_piece g f (x k) (φ k) (hball k) (hT k) (hT0 k) (hTball k) (hA k) (hAT k) Λ
      hε hnd

include hK hball hT hT0 hTball hA hAT hAd hAK in
/-- The derivative of the action over `K` for the perturbation `ρ h`, when `K ∩ tsupport ρ` lies in the
compact set `T i` of one small coordinate ball. -/
theorem hasDerivAt_ehAction_smulFun (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M)
    (hsupp : ∀ p, p ∉ K → h.h p = 0) (ρ : M → ℝ) (hρ : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ ρ) (i : ℕ)
    (hρT : K ∩ tsupport ρ ⊆ T i) :
    HasDerivAt (fun t : ℝ => ehAction (g.perturb (h.smulFun ρ hρ) t) Λ K)
      (-∫ p in K ∩ tsupport ρ, ehIntegrand g (h.smulFun ρ hρ) Λ p ∂(NondegMetric.volumeMeasure g)) 0 := by
  have hS : MeasurableSet (tsupport ρ) := (isClosed_tsupport ρ).measurableSet
  have hzero : ∀ p, p ∉ K ∩ tsupport ρ → (h.smulFun ρ hρ).h p = 0 := by
    intro p hp
    by_cases hpK : p ∈ K
    · exact h.smulFun_eq_zero_of_fun ρ hρ
        (image_eq_zero_of_notMem_tsupport fun hpS => hp ⟨hpK, hpS⟩)
    · exact h.smulFun_eq_zero_of_field ρ hρ (hsupp p hpK)
  have hzeroK : ∀ p, p ∉ K → (h.smulFun ρ hρ).h p = 0 := fun p hp =>
    hzero p fun hp' => hp hp'.1
  obtain ⟨ε, hε, hnd⟩ := g.exists_addSmul_nondegenerate (h.smulFun ρ hρ) hK hzeroK
  have hKS : IsCompact (K ∩ tsupport ρ) := hK.inter_right (isClosed_tsupport ρ)
  -- the part inside the support of `ρ`
  have h1 := eh_first_variation_manifold_intrinsic g (h.smulFun ρ hρ) (x i) hKS
    (hρT.trans (hT0 i)) (φ i) (hball i) ((image_mono hρT).trans (hTball i)) hzero Λ
  -- the part outside
  have h2 : HasDerivAt (fun t : ℝ => ∑ k ∈ Finset.range N,
      ehAction (g.perturb (h.smulFun ρ hρ) t) Λ (A k \ tsupport ρ)) 0 0 := by
    have h3 := HasDerivAt.fun_sum (u := Finset.range N) fun k _ =>
      hasDerivAt_ehAction_piece g (h.smulFun ρ hρ) (x k) (φ k) (hball k) (hT k) (hT0 k) (hTball k)
        ((hA k).diff hS) (diff_subset.trans (hAT k)) Λ hε hnd
    have h4 : ∑ k ∈ Finset.range N,
        pieceVar g (h.smulFun ρ hρ) (x k) (φ k) Λ (T k) (A k \ tsupport ρ) = 0 :=
      Finset.sum_eq_zero fun k _ =>
        pieceVar_eq_zero g (h.smulFun ρ hρ) (x k) (φ k) (hball k) Λ (hT k) (hT0 k) (hTball k)
          (diff_subset.trans (hAT k)) (isClosed_tsupport ρ).isOpen_compl (fun p hp => hp.2)
          (fun p hp => h.smulFun_eq_zero_of_fun ρ hρ (image_eq_zero_of_notMem_tsupport hp))
    rw [h4] at h3
    exact h3
  have hsum := h1.add h2
  rw [add_zero] at hsum
  refine hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  show ehAction (g.perturb (h.smulFun ρ hρ) t) Λ K =
    ehAction (g.perturb (h.smulFun ρ hρ) t) Λ (K ∩ tsupport ρ) +
      ∑ k ∈ Finset.range N, ehAction (g.perturb (h.smulFun ρ hρ) t) Λ (A k \ tsupport ρ)
  have hKi : K ∩ tsupport ρ = ⋃ k ∈ Finset.range N, (A k ∩ tsupport ρ) := by
    rw [hAK, iUnion₂_inter]
  have hd1 : Set.Pairwise (↑(Finset.range N)) (Function.onFun Disjoint fun k => A k ∩ tsupport ρ) :=
    fun i _ j _ hij => (hAd hij).mono inter_subset_left inter_subset_left
  have e1 := ehAction_biUnion (g.perturb (h.smulFun ρ hρ) t) Λ (Finset.range N)
    (fun k => A k ∩ tsupport ρ) T x (fun k _ => (hA k).inter hS) hd1 (fun k _ => hT k)
    (fun k _ => hT0 k) (fun k _ => inter_subset_left.trans (hAT k))
  have e0 := ehAction_biUnion (g.perturb (h.smulFun ρ hρ) t) Λ (Finset.range N) A T x
    (fun k _ => hA k) (fun i _ j _ hij => hAd hij) (fun k _ => hT k) (fun k _ => hT0 k)
    (fun k _ => hAT k)
  rw [hKi, e1, ← Finset.sum_add_distrib]
  nth_rewrite 1 [hAK]
  rw [e0]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold ehAction
  exact (integral_inter_add_diff hS
    (NondegMetric.integrableOn_of_continuousOn (g.perturb (h.smulFun ρ hρ) t) (x k) (hT k) (hT0 k)
      ((continuousOn_ehLagrangian (g.perturb (h.smulFun ρ hρ) t) Λ (x k)).mono (hT0 k)) (hAT k))).symm

include hK hball hT hT0 hTball hA hAT hAd hAK in
/-- **The first variation of the Einstein–Hilbert action for a perturbation with compact support**, given
a cover of the support by small chart balls with a subordinate family of functions summing to `1`. -/
theorem eh_first_variation_of_cover (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M)
    (hsupp : ∀ p, p ∉ K → h.h p = 0) (ρ : ℕ → M → ℝ)
    (hρ : ∀ i, ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ (ρ i))
    (hρ1 : ∀ p ∈ K, ∑ i ∈ Finset.range N, ρ i p = 1) (hρT : ∀ i, K ∩ tsupport (ρ i) ⊆ T i) :
    HasDerivAt (fun t : ℝ => ehAction (g.perturb h t) Λ K)
      (-∫ p in K, ehIntegrand g h Λ p ∂(NondegMetric.volumeMeasure g)) 0 := by
  have hP := hasDerivAt_ehAction_pieces g hK Λ N x c φ hball T A hT hT0 hTball hA hAT hAd hAK h hsupp
  have hzero : ∀ i p, p ∉ K → (h.smulFun (ρ i) (hρ i)).h p = 0 := fun i p hp =>
    h.smulFun_eq_zero_of_field (ρ i) (hρ i) (hsupp p hp)
  -- the chart components of `h` are the sum of those of the `ρ i h`
  have hH : ∀ k y, h.coordCompR (x k) (φ k) y =
      ∑ i ∈ Finset.range N, (h.smulFun (ρ i) (hρ i)).coordCompR (x k) (φ k) y := by
    intro k y
    show h.coordComp (x k) (ballRetract (φ k) y) =
      ∑ i ∈ Finset.range N, (h.smulFun (ρ i) (hρ i)).coordComp (x k) (ballRetract (φ k) y)
    simp only [SymBilinField.coordComp_smulFun]
    rw [← Finset.sum_smul]
    by_cases hp : (extChartAt 𝓘(ℝ, Fin n → ℝ) (x k)).symm (ballRetract (φ k) y) ∈ K
    · rw [hρ1 _ hp, one_smul]
    · have h0 : h.coordComp (x k) (ballRetract (φ k) y) = 0 := by
        ext a b
        simp only [SymBilinField.coordComp, hsupp _ hp, ContinuousLinearMap.zero_apply,
          Matrix.zero_apply]
      rw [h0, smul_zero]
  have hA1 : ∀ k, pieceVar g h (x k) (φ k) Λ (T k) (A k) =
      ∑ i ∈ Finset.range N, pieceVar g (h.smulFun (ρ i) (hρ i)) (x k) (φ k) Λ (T k) (A k) := fun k =>
    pieceVar_sum g (x k) (φ k) (hball k) (Finset.range N) h (fun i => h.smulFun (ρ i) (hρ i)) (hH k) Λ
      (hT k) (hT0 k) (A k)
  have hB : ∀ i, ∑ k ∈ Finset.range N,
        pieceVar g (h.smulFun (ρ i) (hρ i)) (x k) (φ k) Λ (T k) (A k) =
      -∫ p in K ∩ tsupport (ρ i), ehIntegrand g (h.smulFun (ρ i) (hρ i)) Λ p
        ∂(NondegMetric.volumeMeasure g) := fun i =>
    (hasDerivAt_ehAction_pieces g hK Λ N x c φ hball T A hT hT0 hTball hA hAT hAd hAK
      (h.smulFun (ρ i) (hρ i)) (hzero i)).unique
    (hasDerivAt_ehAction_smulFun g hK Λ N x c φ hball T A hT hT0 hTball hA hAT hAd hAK h hsupp
      (ρ i) (hρ i) i (hρT i))
  have hC : ∀ i, ∫ p in K ∩ tsupport (ρ i), ehIntegrand g (h.smulFun (ρ i) (hρ i)) Λ p
        ∂(NondegMetric.volumeMeasure g) =
      ∫ p in K, ρ i p * ehIntegrand g h Λ p ∂(NondegMetric.volumeMeasure g) := by
    intro i
    rw [← setIntegral_eq_of_subset_of_forall_diff_eq_zero hK.measurableSet inter_subset_left
      (fun p hp => ehIntegrand_eq_zero g (h.smulFun (ρ i) (hρ i)) Λ
        (h.smulFun_eq_zero_of_fun (ρ i) (hρ i)
          (image_eq_zero_of_notMem_tsupport fun hS => hp.2 ⟨hp.1, hS⟩)))]
    exact setIntegral_congr_fun hK.measurableSet fun p _ => ehIntegrand_smulFun g h (ρ i) (hρ i) Λ p
  have hint : ∀ i ∈ Finset.range N, IntegrableOn (fun p => ρ i p * ehIntegrand g h Λ p) K
      (NondegMetric.volumeMeasure g) := by
    intro i _
    have h1 : IntegrableOn (fun p => ρ i p * ehIntegrand g h Λ p) (⋃ k ∈ Finset.range N, A k)
        (NondegMetric.volumeMeasure g) :=
      integrableOn_finset_iUnion.2 fun k _ =>
        NondegMetric.integrableOn_of_continuousOn g (x k) (hT k) (hT0 k)
          ((hρ i).continuous.continuousOn.mul ((continuousOn_ehIntegrand g h Λ (x k)).mono (hT0 k)))
          (hAT k)
    rwa [← hAK] at h1
  have hD : ∑ i ∈ Finset.range N, ∫ p in K, ρ i p * ehIntegrand g h Λ p
        ∂(NondegMetric.volumeMeasure g) =
      ∫ p in K, ehIntegrand g h Λ p ∂(NondegMetric.volumeMeasure g) := by
    rw [← integral_finsetSum _ hint]
    refine setIntegral_congr_fun hK.measurableSet fun p hp => ?_
    show ∑ i ∈ Finset.range N, ρ i p * ehIntegrand g h Λ p = ehIntegrand g h Λ p
    rw [← Finset.sum_mul, hρ1 p hp, one_mul]
  have hfinal : ∑ k ∈ Finset.range N, pieceVar g h (x k) (φ k) Λ (T k) (A k) =
      -∫ p in K, ehIntegrand g h Λ p ∂(NondegMetric.volumeMeasure g) := by
    rw [Finset.sum_congr rfl fun k _ => hA1 k, Finset.sum_comm, Finset.sum_congr rfl fun i _ => hB i,
      Finset.sum_neg_distrib, Finset.sum_congr rfl fun i _ => hC i, hD]
  rw [hfinal] at hP
  exact hP

end Lightlike
