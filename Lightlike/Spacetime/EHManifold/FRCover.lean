import Lightlike.Spacetime.EHManifold.FRManifoldBall
import Lightlike.Spacetime.EHManifold.FRPieceLinear

/-!
# The first variation of the `f(R)` action on a manifold, given a cover by small chart balls

`fR_first_variation_of_cover`: let `h` be a symmetric tensor field on a manifold vanishing outside a compact
set `K`, and suppose `K` is cut into finitely many disjoint measurable pieces `A k`, each inside a compact
set `T k` in a small coordinate ball of a chart, with smooth functions `ρ i` summing to `1` on `K` such that
`K ∩ tsupport (ρ i) ⊆ T i`. Then

`d/dt|₀ ∫_K f(R(g + t h)) d vol = -∑_i ∫_{φ_i(K ∩ supp ρ_i)} √|g| (ρ_i h)_{ab} (fRTensorUp)^{ab} dy`,

each term in the components of the chart `i`, with
`fRTensorUp = f'(R) R^{ab} - ½ f(R) g^{ab} - ∇^a ∇^b f'(R) + g^{ab} □ f'(R)`.

The proof follows `eh_first_variation_of_cover`: over a piece, the derivative of the action is a chart
integral (`hasDerivAt_fRAction_piece`); the formula is additive in `h` (`fRPieceVar_sum`); and for `ρ i h`,
supported in one small ball, it agrees with `fR_first_variation_manifold` by uniqueness of the derivative.

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

variable (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) {K : Set M} (hK : IsCompact K)
  (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hf' : ContDiff ℝ 2 (deriv f))
  (N : ℕ) (x : ℕ → M) (c : ℕ → Fin n → ℝ) (φ : ∀ k, ContDiffBump (c k))
  (hball : ∀ k, ball (c k) (φ k).rOut ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) (x k)).target)
  (T A : ℕ → Set M) (hT : ∀ k, IsCompact (T k))
  (hT0 : ∀ k, T k ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) (x k)).source)
  (hTball : ∀ k, extChartAt 𝓘(ℝ, Fin n → ℝ) (x k) '' T k ⊆ ball (c k) (φ k).rIn)
  (hA : ∀ k, MeasurableSet (A k)) (hAT : ∀ k, A k ⊆ T k) (hAd : Pairwise (Function.onFun Disjoint A))
  (hAK : K = ⋃ k ∈ Finset.range N, A k)

include hK hf hball hT hT0 hTball hA hAT hAd hAK in
/-- The derivative of the `f(R)` action over `K` as a sum over the pieces, for any perturbation vanishing
outside `K`. -/
theorem hasDerivAt_fRAction_pieces (F : SymBilinField 𝓘(ℝ, Fin n → ℝ) M)
    (hF : ∀ p, p ∉ K → F.h p = 0) :
    HasDerivAt (fun t : ℝ => fRAction (g.perturb F t) f K)
      (∑ k ∈ Finset.range N, fRPieceVar g F (x k) (φ k) f (T k) (A k)) 0 := by
  obtain ⟨ε, hε, hnd⟩ := g.exists_addSmul_nondegenerate F hK hF
  have hfun : (fun t : ℝ => fRAction (g.perturb F t) f K) =
      fun t => ∑ k ∈ Finset.range N, fRAction (g.perturb F t) f (A k) := by
    funext t
    rw [hAK]
    exact fRAction_biUnion (g.perturb F t) f hf.continuous (Finset.range N) A T x (fun k _ => hA k)
      (fun i _ j _ hij => hAd hij) (fun k _ => hT k) (fun k _ => hT0 k) (fun k _ => hAT k)
  rw [hfun]
  exact HasDerivAt.fun_sum fun k _ =>
    hasDerivAt_fRAction_piece g F (x k) (φ k) (hball k) f hf (hT k) (hT0 k) (hTball k) (hA k) (hAT k)
      hε hnd

include hK hf hf' hball hT hT0 hTball hA hAT hAd hAK in
/-- The derivative of the `f(R)` action over `K` for the perturbation `ρ h`, when `K ∩ tsupport ρ` lies in
the compact set `T i` of one small coordinate ball. -/
theorem hasDerivAt_fRAction_smulFun (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M)
    (hsupp : ∀ p, p ∉ K → h.h p = 0) (ρ : M → ℝ) (hρ : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ ρ) (i : ℕ)
    (hρT : K ∩ tsupport ρ ⊆ T i) :
    HasDerivAt (fun t : ℝ => fRAction (g.perturb (h.smulFun ρ hρ) t) f K)
      (-∫ y in extChartAt 𝓘(ℝ, Fin n → ℝ) (x i) '' (K ∩ tsupport ρ),
        √|(g.coordMetricR (x i) (φ i) y).det| * ∑ α, ∑ β, (h.smulFun ρ hρ).coordComp (x i) y α β *
          fRTensorUp (g.coordMetricR (x i) (φ i)) f y α β) 0 := by
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
  have h1 := fR_first_variation_manifold g (h.smulFun ρ hρ) (x i) hKS
    (hρT.trans (hT0 i)) (φ i) (hball i) ((image_mono hρT).trans (hTball i)) hzero f hf hf'
  -- the part outside
  have h2 : HasDerivAt (fun t : ℝ => ∑ k ∈ Finset.range N,
      fRAction (g.perturb (h.smulFun ρ hρ) t) f (A k \ tsupport ρ)) 0 0 := by
    have h3 := HasDerivAt.fun_sum (u := Finset.range N) fun k _ =>
      hasDerivAt_fRAction_piece g (h.smulFun ρ hρ) (x k) (φ k) (hball k) f hf (hT k) (hT0 k)
        (hTball k) ((hA k).diff hS) (diff_subset.trans (hAT k)) hε hnd
    have h4 : ∑ k ∈ Finset.range N,
        fRPieceVar g (h.smulFun ρ hρ) (x k) (φ k) f (T k) (A k \ tsupport ρ) = 0 :=
      Finset.sum_eq_zero fun k _ =>
        fRPieceVar_eq_zero g (x k) (φ k) (h.smulFun ρ hρ) (hball k) f (hT k) (hT0 k) (hTball k)
          (diff_subset.trans (hAT k)) (isClosed_tsupport ρ).isOpen_compl (fun p hp => hp.2)
          (fun p hp => h.smulFun_eq_zero_of_fun ρ hρ (image_eq_zero_of_notMem_tsupport hp))
    rw [h4] at h3
    exact h3
  have hsum := h1.add h2
  rw [add_zero] at hsum
  refine hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  show fRAction (g.perturb (h.smulFun ρ hρ) t) f K =
    fRAction (g.perturb (h.smulFun ρ hρ) t) f (K ∩ tsupport ρ) +
      ∑ k ∈ Finset.range N, fRAction (g.perturb (h.smulFun ρ hρ) t) f (A k \ tsupport ρ)
  have hKi : K ∩ tsupport ρ = ⋃ k ∈ Finset.range N, (A k ∩ tsupport ρ) := by
    rw [hAK, iUnion₂_inter]
  have hd1 : Set.Pairwise (↑(Finset.range N)) (Function.onFun Disjoint fun k => A k ∩ tsupport ρ) :=
    fun i _ j _ hij => (hAd hij).mono inter_subset_left inter_subset_left
  have e1 : fRAction (g.perturb (h.smulFun ρ hρ) t) f (⋃ k ∈ Finset.range N, (A k ∩ tsupport ρ)) =
      ∑ k ∈ Finset.range N, fRAction (g.perturb (h.smulFun ρ hρ) t) f (A k ∩ tsupport ρ) :=
    fRAction_biUnion (g.perturb (h.smulFun ρ hρ) t) f hf.continuous (Finset.range N)
      (fun k => A k ∩ tsupport ρ) T x (fun k _ => (hA k).inter hS) hd1 (fun k _ => hT k)
      (fun k _ => hT0 k) (fun k _ => inter_subset_left.trans (hAT k))
  have e0 : fRAction (g.perturb (h.smulFun ρ hρ) t) f (⋃ k ∈ Finset.range N, A k) =
      ∑ k ∈ Finset.range N, fRAction (g.perturb (h.smulFun ρ hρ) t) f (A k) :=
    fRAction_biUnion (g.perturb (h.smulFun ρ hρ) t) f hf.continuous (Finset.range N) A T x
      (fun k _ => hA k) (fun i _ j _ hij => hAd hij) (fun k _ => hT k) (fun k _ => hT0 k)
      (fun k _ => hAT k)
  rw [hKi, e1, ← Finset.sum_add_distrib]
  nth_rewrite 1 [hAK]
  rw [e0]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold fRAction
  exact (integral_inter_add_diff hS
    (NondegMetric.integrableOn_of_continuousOn (g.perturb (h.smulFun ρ hρ) t) (x k) (hT k) (hT0 k)
      ((continuousOn_fR (g.perturb (h.smulFun ρ hρ) t) f hf.continuous (x k)).mono (hT0 k))
      (hAT k))).symm

include hK hf hf' hball hT hT0 hTball hA hAT hAd hAK in
/-- **The first variation of the `f(R)` action on a manifold for a perturbation with compact support**,
given a cover of the support by small chart balls with a subordinate family of functions summing to `1`. -/
theorem fR_first_variation_of_cover (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M)
    (hsupp : ∀ p, p ∉ K → h.h p = 0) (ρ : ℕ → M → ℝ)
    (hρ : ∀ i, ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ (ρ i))
    (hρ1 : ∀ p ∈ K, ∑ i ∈ Finset.range N, ρ i p = 1) (hρT : ∀ i, K ∩ tsupport (ρ i) ⊆ T i) :
    HasDerivAt (fun t : ℝ => fRAction (g.perturb h t) f K)
      (-∑ i ∈ Finset.range N, ∫ y in extChartAt 𝓘(ℝ, Fin n → ℝ) (x i) '' (K ∩ tsupport (ρ i)),
        √|(g.coordMetricR (x i) (φ i) y).det| *
          ∑ α, ∑ β, (h.smulFun (ρ i) (hρ i)).coordComp (x i) y α β *
            fRTensorUp (g.coordMetricR (x i) (φ i)) f y α β) 0 := by
  have hP := hasDerivAt_fRAction_pieces g hK f hf N x c φ hball T A hT hT0 hTball hA hAT hAd hAK h hsupp
  have hzero : ∀ i p, p ∉ K → (h.smulFun (ρ i) (hρ i)).h p = 0 := fun i p hp =>
    h.smulFun_eq_zero_of_field (ρ i) (hρ i) (hsupp p hp)
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
  have hdf : Continuous (deriv f) := hf'.continuous
  have hA1 : ∀ k, fRPieceVar g h (x k) (φ k) f (T k) (A k) =
      ∑ i ∈ Finset.range N, fRPieceVar g (h.smulFun (ρ i) (hρ i)) (x k) (φ k) f (T k) (A k) := fun k =>
    fRPieceVar_sum g (x k) (φ k) (hball k) (Finset.range N) h (fun i => h.smulFun (ρ i) (hρ i)) (hH k) f
      hf.continuous hdf (hT k) (hT0 k) (A k)
  have hB : ∀ i, ∑ k ∈ Finset.range N,
        fRPieceVar g (h.smulFun (ρ i) (hρ i)) (x k) (φ k) f (T k) (A k) =
      -∫ y in extChartAt 𝓘(ℝ, Fin n → ℝ) (x i) '' (K ∩ tsupport (ρ i)),
        √|(g.coordMetricR (x i) (φ i) y).det| *
          ∑ α, ∑ β, (h.smulFun (ρ i) (hρ i)).coordComp (x i) y α β *
            fRTensorUp (g.coordMetricR (x i) (φ i)) f y α β := fun i =>
    (hasDerivAt_fRAction_pieces g hK f hf N x c φ hball T A hT hT0 hTball hA hAT hAd hAK
      (h.smulFun (ρ i) (hρ i)) (hzero i)).unique
    (hasDerivAt_fRAction_smulFun g hK f hf hf' N x c φ hball T A hT hT0 hTball hA hAT hAd hAK h hsupp
      (ρ i) (hρ i) i (hρT i))
  have hfinal : ∑ k ∈ Finset.range N, fRPieceVar g h (x k) (φ k) f (T k) (A k) =
      -∑ i ∈ Finset.range N, ∫ y in extChartAt 𝓘(ℝ, Fin n → ℝ) (x i) '' (K ∩ tsupport (ρ i)),
        √|(g.coordMetricR (x i) (φ i) y).det| *
          ∑ α, ∑ β, (h.smulFun (ρ i) (hρ i)).coordComp (x i) y α β *
            fRTensorUp (g.coordMetricR (x i) (φ i)) f y α β := by
    rw [Finset.sum_congr rfl fun k _ => hA1 k, Finset.sum_comm, Finset.sum_congr rfl fun i _ => hB i,
      Finset.sum_neg_distrib]
  rw [hfinal] at hP
  exact hP

end Lightlike
