import Lightlike.Gauge.Connection.Basic
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Parallel transport along a segment

Svetlichny, *Preparation for Gauge Theory*, arXiv:math-ph/9902027v1, p. 40: parallel transport solves
`df/dt = -Γ(x(t), f) dx/dt`; for a principal bundle the transport is the group element `P exp(-∫ A)`. Here, along the
segment `t ↦ x + t ξ` (`t ∈ [0, 1]`), the transport is a solution `U` of `U' = -A(x + t ξ)(ξ) U`, `U(0) = 1`
(`IsSegmentTransport`).

* `exists_segmentTransport`: if `‖A(x + t ξ) ξ‖ ≤ 1/2` on the segment (a short leg), a transport exists
  (Picard–Lindelöf, Mathlib's `IsPicardLindelof`).
* `segmentTransport_unique`: two transports agree on `[0, 1]` (Mathlib's `ODE_solution_unique_of_mem_Icc_right`).
-/

open Set Metric NNReal

noncomputable section

namespace Lightlike.Gauge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄]

/-- `U` is the parallel transport of `A` along the segment `t ↦ x + t ξ`, `t ∈ [0, 1]`:
`U(0) = 1` and `U'(t) = -A(x + t ξ)(ξ) U(t)` (Svetlichny p. 40). -/
def IsSegmentTransport (A : E → E →L[ℝ] 𝔄) (x ξ : E) (U : ℝ → 𝔄) : Prop :=
  U 0 = 1 ∧ ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt U (-(A (x + t • ξ) ξ * U t)) (Icc 0 1) t

/-- **Existence of the transport along a short leg.** -/
theorem exists_segmentTransport [CompleteSpace 𝔄] [NormOneClass 𝔄] {A : E → E →L[ℝ] 𝔄} (hA : Continuous A)
    (x ξ : E) (hsmall : ∀ t ∈ Icc (0 : ℝ) 1, ‖A (x + t • ξ) ξ‖ ≤ 1 / 2) :
    ∃ U : ℝ → 𝔄, IsSegmentTransport A x ξ U := by
  set f : ℝ → 𝔄 → 𝔄 := fun t u => -(A (x + t • ξ) ξ * u) with hf
  have hcont : Continuous fun t : ℝ => A (x + t • ξ) ξ :=
    (hA.comp (by fun_prop : Continuous fun t : ℝ => x + t • ξ)).clm_apply continuous_const
  have hPL : IsPicardLindelof f (⟨0, by simp⟩ : Icc (0 : ℝ) 1) (1 : 𝔄) 1 0 1 (1 / 2) := by
    refine ⟨fun t ht => ?_, fun u _ => ?_, fun t ht u hu => ?_, ?_⟩
    · refine LipschitzWith.lipschitzOnWith (LipschitzWith.of_dist_le_mul fun u v => ?_)
      simp only [hf, dist_eq_norm, neg_sub_neg, ← mul_sub]
      rw [norm_sub_rev u v]
      calc ‖A (x + t • ξ) ξ * (v - u)‖ ≤ ‖A (x + t • ξ) ξ‖ * ‖v - u‖ := norm_mul_le _ _
        _ ≤ (1 / 2 : ℝ) * ‖v - u‖ := mul_le_mul_of_nonneg_right (hsmall t ht) (norm_nonneg _)
        _ = _ := by first | norm_num | (push_cast; ring)
    · exact ((hcont.mul continuous_const).neg).continuousOn
    · have hu' : ‖u‖ ≤ 2 := by
        have := mem_closedBall.1 hu
        rw [dist_eq_norm] at this
        calc ‖u‖ = ‖(u - 1) + 1‖ := by rw [sub_add_cancel]
          _ ≤ ‖u - 1‖ + ‖(1 : 𝔄)‖ := norm_add_le _ _
          _ ≤ 1 + 1 := by rw [norm_one]; push_cast at this; linarith
          _ = 2 := by norm_num
      simp only [hf, norm_neg]
      calc ‖A (x + t • ξ) ξ * u‖ ≤ ‖A (x + t • ξ) ξ‖ * ‖u‖ := norm_mul_le _ _
        _ ≤ (1 / 2) * 2 := mul_le_mul (hsmall t ht) hu' (norm_nonneg _) (by norm_num)
        _ = ((1 : ℝ≥0) : ℝ) := by norm_num
    · simp
  obtain ⟨U, hU0, hU⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨U, hU0, hU⟩

/-- **Uniqueness of the transport.** -/
theorem segmentTransport_unique {A : E → E →L[ℝ] 𝔄} {x ξ : E} {B : ℝ≥0}
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, ‖A (x + t • ξ) ξ‖ ≤ B) {U V : ℝ → 𝔄}
    (hU : IsSegmentTransport A x ξ U) (hV : IsSegmentTransport A x ξ V) :
    EqOn U V (Icc 0 1) := by
  have hLip : ∀ t ∈ Ico (0 : ℝ) 1, LipschitzOnWith B (fun u : 𝔄 => -(A (x + t • ξ) ξ * u)) univ := by
    intro t ht
    refine LipschitzWith.lipschitzOnWith (LipschitzWith.of_dist_le_mul fun u v => ?_)
    simp only [dist_eq_norm, neg_sub_neg, ← mul_sub]
    rw [norm_sub_rev u v]
    exact (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (hB t (Ico_subset_Icc_self ht)) (norm_nonneg _))
  have hderiv : ∀ W : ℝ → 𝔄, IsSegmentTransport A x ξ W →
      ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt W (-(A (x + t • ξ) ξ * W t)) (Ici t) t := by
    intro W hW t ht
    exact (hW.2 t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ⟨ht.1, ht.2⟩)
  have hcontW : ∀ W : ℝ → 𝔄, IsSegmentTransport A x ξ W → ContinuousOn W (Icc 0 1) :=
    fun W hW t ht => (hW.2 t ht).continuousWithinAt
  exact ODE_solution_unique_of_mem_Icc_right hLip (hcontW U hU) (hderiv U hU) (fun _ _ => mem_univ _)
    (hcontW V hV) (hderiv V hV) (fun _ _ => mem_univ _) (hU.1.trans hV.1.symm)

end Lightlike.Gauge

namespace Lightlike.Gauge

open Set MeasureTheory intervalIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄]

omit [CompleteSpace 𝔄] in
/-- A transport is continuous on `[0, 1]`. -/
lemma IsSegmentTransport.continuousOn {A : E → E →L[ℝ] 𝔄} {x ξ : E} {U : ℝ → 𝔄}
    (hU : IsSegmentTransport A x ξ U) : ContinuousOn U (Icc 0 1) :=
  fun t ht => (hU.2 t ht).continuousWithinAt

/-- **The integral equation of the transport**: `U(t) = 1 - ∫₀ᵗ A(x + s ξ)(ξ) U(s) ds` for `t ∈ [0, 1]`. -/
theorem IsSegmentTransport.eq_one_sub_integral {A : E → E →L[ℝ] 𝔄} (hA : Continuous A) {x ξ : E}
    {U : ℝ → 𝔄} (hU : IsSegmentTransport A x ξ U) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    U t = 1 - ∫ s in (0 : ℝ)..t, A (x + s • ξ) ξ * U s := by
  have hcM : Continuous fun s : ℝ => A (x + s • ξ) ξ :=
    (hA.comp (by fun_prop : Continuous fun s : ℝ => x + s • ξ)).clm_apply continuous_const
  have hsub : Icc 0 t ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc le_rfl ht.2
  have hFTC := integral_eq_sub_of_hasDeriv_right_of_le ht.1 (hU.continuousOn.mono hsub)
    (fun s hs => ((hU.2 s (hsub (Ioo_subset_Icc_self hs))).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGT_of_mem ⟨hs.1.le, lt_of_lt_of_le hs.2 ht.2⟩)))
    ((hcM.continuousOn.mul (hU.continuousOn.mono hsub)).neg.intervalIntegrable_of_Icc ht.1)
  rw [intervalIntegral.integral_neg, hU.1] at hFTC
  calc U t = (U t - 1) + 1 := by abel
    _ = _ := by rw [← hFTC]; abel

end Lightlike.Gauge
