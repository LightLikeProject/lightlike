import Lightlike.OperatorAlgebras.TraceClass.HilbertSchmidt
import Lightlike.OperatorAlgebras.FiniteRankApprox

/-!
# Hilbert–Schmidt operators are compact

G. Teschl, *Mathematical Methods in Quantum Mechanics*, Section 6.3, p. 139: the expansion (6.12) "shows that `K` can be
approximated by finite rank operators (take finitely many terms in the sum) and is hence compact".

* `isCompactOperator_of_isHilbertSchmidt`: a Hilbert–Schmidt operator (`TraceClass.HilbertSchmidt.IsHilbertSchmidt`, the
  square sum `∑ᵢ ‖K bᵢ‖²` converges in a Hilbert basis) is the norm limit of `K_F x = ∑_{i ∈ F} ⟪bᵢ, x⟫ K bᵢ`, with
  `‖K - K_F‖² ≤ ∑_{i ∉ F} ‖K bᵢ‖²`, and so it is compact.
-/

open scoped InnerProductSpace

namespace Lightlike.OperatorAlgebras.CompactSpectral

open TraceClass.HilbertSchmidt

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **A Hilbert–Schmidt operator is compact** (Teschl, Section 6.3, p. 139): it is the norm limit of the finite-rank
operators `K_F x = ∑_{i ∈ F} ⟪bᵢ, x⟫ K bᵢ`, with `‖K x - K_F x‖ ≤ (∑_{i ∉ F} ‖K bᵢ‖²)^{1/2} ‖x‖`. -/
theorem isCompactOperator_of_isHilbertSchmidt {K : H →L[ℂ] H} (hK : IsHilbertSchmidt K) : IsCompactOperator K := by
  classical
  obtain ⟨w, b, hb⟩ := hK
  let KF : Finset w → H →L[ℂ] H := fun F => ∑ i ∈ F, InnerProductSpace.rankOne ℂ (K (b i)) (b i)
  have hKF : ∀ F x, KF F x = ∑ i ∈ F, ⟪b i, x⟫_ℂ • K (b i) := by
    intro F x
    simp [KF, InnerProductSpace.rankOne_apply]
  have hcomp : ∀ F, IsCompactOperator (KF F) := by
    intro F
    have : KF F ∈ compactOperator (RingHom.id ℂ) H H :=
      Submodule.sum_mem _ fun i _ => isCompactOperator_rankOne (K (b i)) (b i)
    exact this
  have htail : ∀ F x, ‖K x - KF F x‖ ≤ Real.sqrt (∑' i : {i // i ∉ F}, ‖K (b i)‖ ^ 2) * ‖x‖ := by
    intro F x
    have h := (b.hasSum_repr x).mapL K
    simp only [map_smul, HilbertBasis.repr_apply_apply] at h
    have hF : HasSum (fun i => if i ∈ F then ⟪b i, x⟫_ℂ • K (b i) else 0) (KF F x) := by
      have h0 : HasSum (fun i => if i ∈ F then ⟪b i, x⟫_ℂ • K (b i) else 0)
          (∑ i ∈ F, if i ∈ F then ⟪b i, x⟫_ℂ • K (b i) else 0) :=
        hasSum_sum_of_ne_finset_zero fun i hi => if_neg hi
      rwa [Finset.sum_congr rfl fun i hi => if_pos hi, ← hKF] at h0
    have hd := h.sub hF
    let f : w → ℝ := fun i => ‖⟪b i, x⟫_ℂ‖
    let g : w → ℝ := fun i => if i ∈ F then 0 else ‖K (b i)‖
    have hg0 : ∀ i, 0 ≤ g i := fun i => by simp only [g]; split_ifs <;> simp
    have hpars := TraceClass.hasSum_norm_sq_inner_basis b x
    have hf2 : Summable (fun i => f i ^ 2) := hpars.summable
    have hg2 : Summable (fun i => g i ^ 2) := by
      refine Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => ?_) hb
      simp only [g]; split_ifs <;> simp
    have hfg := summable_norm_mul_of_square_sums f g hf2 hg2 (fun i => norm_nonneg _) hg0
    have hle : ‖K x - KF F x‖ ≤ ∑' i, f i * g i := by
      refine hd.norm_le_of_bounded hfg.hasSum fun i => ?_
      simp only [f, g]
      split_ifs with hi
      · simp
      · rw [sub_zero, norm_smul]
    have hcs := tsum_mul_le_sqrt_mul_sqrt hf2 hg2 (fun i => norm_nonneg _) hg0
    have hfx : Real.sqrt (∑' i, f i ^ 2) = ‖x‖ := by
      rw [hpars.tsum_eq, Real.sqrt_sq (norm_nonneg _)]
    have hgt : ∑' i, g i ^ 2 = ∑' i : {i // i ∉ F}, ‖K (b i)‖ ^ 2 := by
      have hs := tsum_subtype ({i | i ∉ F} : Set w) (fun i : w => ‖K (b i)‖ ^ 2)
      rw [show (∑' i : {i // i ∉ F}, ‖K (b i)‖ ^ 2) = ∑' i : ({i | i ∉ F} : Set w), ‖K (b i)‖ ^ 2 from rfl, hs]
      refine tsum_congr fun i => ?_
      simp only [g, Set.indicator_apply, Set.mem_setOf_eq]
      split_ifs <;> simp_all
    rw [hfx, hgt] at hcs
    nlinarith [mul_comm ‖x‖ (Real.sqrt (∑' i : {i // i ∉ F}, ‖K (b i)‖ ^ 2))]
  have hlim : Filter.Tendsto KF Filter.atTop (nhds K) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have ht := tendsto_tsum_compl_atTop_zero (fun i : w => ‖K (b i)‖ ^ 2)
    have ht' : Filter.Tendsto (fun F : Finset w => Real.sqrt (∑' i : {i // i ∉ F}, ‖K (b i)‖ ^ 2))
        Filter.atTop (nhds 0) := by
      have h := (Real.continuous_sqrt.tendsto 0).comp ht
      rw [Real.sqrt_zero] at h
      exact h
    refine squeeze_zero (fun F => norm_nonneg _) (fun F => ?_) ht'
    rw [norm_sub_rev]
    exact ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => by
      rw [ContinuousLinearMap.sub_apply]; exact htail F x
  exact isCompactOperator_of_tendsto hlim (Filter.Eventually.of_forall hcomp)

end Lightlike.OperatorAlgebras.CompactSpectral
