import Lightlike.Gauge.Connection.Transport
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing

/-!
# The holonomy of a small parallelogram is the curvature to second order

`squareHolonomy_eq`: for a `C²` connection `A`, any transports `U₁, …, U₄` along the legs
`x → x + εξ → x + εξ + εη → x + εη → x` satisfy `‖U₄ U₃ U₂ U₁ - (1 + ε² F(η, ξ))‖ ≤ C ε³` for small `ε`, with
`F(η, ξ) = dA(η, ξ) + [A(η), A(ξ)]` (`curvature`). This is Svetlichny, *Preparation for Gauge Theory*,
arXiv:math-ph/9902027v1, p. 42, eq. (62) (transport around the parallelogram is `exp(F(η, ξ))` to second order),
with an explicit `O(ε³)` remainder.

Steps:
1. `norm_sub_one_le` (Gronwall-lite): if `‖A(x + tξ)ξ‖ ≤ m ≤ 1/2` on `[0, 1]` then `‖U t‖ ≤ 2` and `‖U t - 1‖ ≤ 2 m t`.
   From the integral equation and `‖∫‖ ≤ ∫ ‖‖`, by a bootstrap (`‖U‖ ≤ 1 + m sup ‖U‖`).
2. `transport_second_order`: `‖U 1 - (1 - ∫₀¹ M + ∫₀¹ M(s) ∫₀ˢ M(r) dr ds)‖ ≤ 4 m³` where `M(s) = A(x + sξ)ξ`
   (substitute the integral equation into itself twice).
3. `taylor_leg` (A of class C² near the base point `x₀`, `‖y - x₀‖, ‖ζ‖ ≤ ε`):
   `‖∫₀¹ A(y + sζ)ζ ds - (A x₀ ζ + DA(x₀)(y - x₀)(ζ) + ½ DA(x₀)(ζ)(ζ))‖ ≤ C ε³` and
   `‖∫₀¹ M(s) ∫₀ˢ M(r) dr ds - ½ (A x₀ ζ)²‖ ≤ C ε³`
   (Mathlib's `Convex.norm_image_sub_le_of_norm_fderiv_le` for the first-order Taylor remainder of `A` and of `DA`).
4. Multiply the four leg expansions (legs `εξ, εη, -εξ, -εη` from `x, x + εξ, x + εξ + εη, x + εη`); the first-order
   terms cancel (`A x₀ ξ - A x₀ ξ`), and the `ε²` terms sum to `DA(x)(ξ)(η) - DA(x)(η)(ξ) + A(η)A(ξ) - A(ξ)A(η)`,
   which is `curvature A x η ξ` (`(fderiv A x η) ξ - (fderiv A x ξ) η + [A η, A ξ]`).
-/

namespace Lightlike.Gauge

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]


end Lightlike.Gauge

namespace Lightlike.Gauge

open Set MeasureTheory intervalIntegral
open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]

/-- **Step 1: the transport of a short leg stays bounded**: if `‖A(x + tξ)ξ‖ ≤ m ≤ 1/2` then `‖U t‖ ≤ 2`. -/
lemma IsSegmentTransport.norm_le_two {A : E → E →L[ℝ] 𝔄} (hA : Continuous A) {x ξ : E} {U : ℝ → 𝔄}
    (hU : IsSegmentTransport A x ξ U) {m : ℝ} (hm : ∀ t ∈ Icc (0 : ℝ) 1, ‖A (x + t • ξ) ξ‖ ≤ m)
    (hm2 : m ≤ 1 / 2) : ∀ t ∈ Icc (0 : ℝ) 1, ‖U t‖ ≤ 2 := by
  obtain ⟨t₀, ht₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 zero_le_one)
    (hU.continuousOn.norm)
  set S := ‖U t₀‖ with hS
  have hm0 : 0 ≤ m := le_trans (norm_nonneg _) (hm 0 ⟨le_rfl, zero_le_one⟩)
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖U t‖ ≤ 1 + m * S := by
    intro t ht
    rw [hU.eq_one_sub_integral hA ht]
    have hint : ‖∫ s in (0 : ℝ)..t, A (x + s • ξ) ξ * U s‖ ≤ m * S * |t - 0| := by
      refine norm_integral_le_of_norm_le_const fun s hs => ?_
      have hs' : s ∈ Icc (0 : ℝ) 1 := by
        rw [uIoc_of_le ht.1] at hs; exact ⟨hs.1.le, hs.2.trans ht.2⟩
      calc ‖A (x + s • ξ) ξ * U s‖ ≤ ‖A (x + s • ξ) ξ‖ * ‖U s‖ := norm_mul_le _ _
        _ ≤ m * S := mul_le_mul (hm s hs') (hmax hs') (norm_nonneg _) hm0
    have ht1 : |t - 0| ≤ 1 := by rw [sub_zero, abs_of_nonneg ht.1]; exact ht.2
    calc ‖1 - ∫ s in (0 : ℝ)..t, A (x + s • ξ) ξ * U s‖
        ≤ ‖(1 : 𝔄)‖ + ‖∫ s in (0 : ℝ)..t, A (x + s • ξ) ξ * U s‖ := norm_sub_le _ _
      _ ≤ 1 + m * S * 1 := by
          rw [norm_one]
          have := mul_le_mul_of_nonneg_left ht1 (mul_nonneg hm0 (norm_nonneg (U t₀)))
          linarith
      _ = 1 + m * S := by ring
  have hS2 : S ≤ 2 := by
    have h1 : S ≤ 1 + m * S := hbound t₀ ht₀
    have hS0 : 0 ≤ S := norm_nonneg _
    have h2 : m * S ≤ 1 / 2 * S := mul_le_mul_of_nonneg_right hm2 hS0
    linarith
  intro t ht
  exact le_trans (hmax ht) hS2

end Lightlike.Gauge

namespace Lightlike.Gauge

open Set MeasureTheory intervalIntegral
open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]

/-- **Step 1b**: `‖U t - 1‖ ≤ 2 m t`. -/
lemma IsSegmentTransport.norm_sub_one_le {A : E → E →L[ℝ] 𝔄} (hA : Continuous A) {x ξ : E} {U : ℝ → 𝔄}
    (hU : IsSegmentTransport A x ξ U) {m : ℝ} (hm : ∀ t ∈ Icc (0 : ℝ) 1, ‖A (x + t • ξ) ξ‖ ≤ m)
    (hm2 : m ≤ 1 / 2) : ∀ t ∈ Icc (0 : ℝ) 1, ‖U t - 1‖ ≤ 2 * m * t := by
  intro t ht
  have h2 := hU.norm_le_two hA hm hm2
  have hm0 : 0 ≤ m := le_trans (norm_nonneg _) (hm 0 ⟨le_rfl, zero_le_one⟩)
  rw [hU.eq_one_sub_integral hA ht, sub_sub_cancel_left, norm_neg]
  have := norm_integral_le_of_norm_le_const (a := 0) (b := t) (C := m * 2)
    (f := fun s => A (x + s • ξ) ξ * U s) fun s hs => by
      have hs' : s ∈ Icc (0 : ℝ) 1 := by
        rw [uIoc_of_le ht.1] at hs; exact ⟨hs.1.le, hs.2.trans ht.2⟩
      calc ‖A (x + s • ξ) ξ * U s‖ ≤ ‖A (x + s • ξ) ξ‖ * ‖U s‖ := norm_mul_le _ _
        _ ≤ m * 2 := mul_le_mul (hm s hs') (h2 s hs') (norm_nonneg _) hm0
  rw [sub_zero, abs_of_nonneg ht.1] at this
  linarith

/-- The Dyson terms of a leg: `D₁ = ∫₀¹ M`, `D₂ = ∫₀¹ M(s) ∫₀ˢ M(r) dr ds` with `M(s) = A(x + sξ)ξ`. -/
noncomputable def dyson1 (A : E → E →L[ℝ] 𝔄) (x ξ : E) : 𝔄 := ∫ s in (0 : ℝ)..1, A (x + s • ξ) ξ

/-- The second Dyson term. -/
noncomputable def dyson2 (A : E → E →L[ℝ] 𝔄) (x ξ : E) : 𝔄 :=
  ∫ s in (0 : ℝ)..1, A (x + s • ξ) ξ * ∫ r in (0 : ℝ)..s, A (x + r • ξ) ξ

/-- **Step 2: the leg transport to second order**: `‖U 1 - (1 - D₁ + D₂)‖ ≤ m³`. -/
lemma IsSegmentTransport.second_order {A : E → E →L[ℝ] 𝔄} (hA : Continuous A) {x ξ : E} {U : ℝ → 𝔄}
    (hU : IsSegmentTransport A x ξ U) {m : ℝ} (hm : ∀ t ∈ Icc (0 : ℝ) 1, ‖A (x + t • ξ) ξ‖ ≤ m)
    (hm2 : m ≤ 1 / 2) : ‖U 1 - (1 - dyson1 A x ξ + dyson2 A x ξ)‖ ≤ 2 * m ^ 3 := by
  set M : ℝ → 𝔄 := fun s => A (x + s • ξ) ξ with hMdef
  have hcM : Continuous M :=
    (hA.comp (by fun_prop : Continuous fun s : ℝ => x + s • ξ)).clm_apply continuous_const
  have hm0 : 0 ≤ m := le_trans (norm_nonneg _) (hm 0 ⟨le_rfl, zero_le_one⟩)
  have hU1 := hU.norm_sub_one_le hA hm hm2
  have hUc := hU.continuousOn
  have h01 : (0 : ℝ) ≤ 1 := zero_le_one
  have hsub : ∀ {s : ℝ}, s ∈ uIcc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 := fun hs => by rwa [uIcc_of_le h01] at hs
  -- the integrands
  have iMU : IntervalIntegrable (fun s => M s * U s) volume 0 1 :=
    (hcM.continuousOn.mul (hUc.mono fun s hs => hsub hs)).intervalIntegrable
  have hprim : ∀ f : ℝ → 𝔄, ContinuousOn f (Icc 0 1) →
      ContinuousOn (fun s => ∫ r in (0 : ℝ)..s, f r) (Icc 0 1) := fun f hf =>
    (intervalIntegral.continuousOn_primitive_interval (by rw [uIcc_of_le h01]; exact hf.integrableOn_Icc)).mono
      (by rw [uIcc_of_le h01])
  have hcMU : ContinuousOn (fun s => M s * U s) (Icc 0 1) := hcM.continuousOn.mul hUc
  have hcMU1 : ContinuousOn (fun s => M s * (U s - 1)) (Icc 0 1) :=
    hcM.continuousOn.mul (hUc.sub continuousOn_const)
  -- `1 - U s = ∫₀ˢ M U`
  have hone : ∀ s ∈ Icc (0 : ℝ) 1, 1 - U s = ∫ r in (0 : ℝ)..s, M r * U r := by
    intro s hs; rw [hU.eq_one_sub_integral hA hs]; abel
  have hsplit : ∀ s ∈ Icc (0 : ℝ) 1,
      ∫ r in (0 : ℝ)..s, M r * U r = (∫ r in (0 : ℝ)..s, M r) + ∫ r in (0 : ℝ)..s, M r * (U r - 1) := by
    intro s hs
    rw [← intervalIntegral.integral_add (hcM.intervalIntegrable _ _)
      ((hcMU1.mono (Icc_subset_Icc le_rfl hs.2)).intervalIntegrable_of_Icc hs.1)]
    refine intervalIntegral.integral_congr fun r _ => ?_
    noncomm_ring
  have i2 : IntervalIntegrable (fun s => M s * ∫ r in (0 : ℝ)..s, M r) volume 0 1 :=
    (hcM.continuousOn.mul (hprim M hcM.continuousOn)).intervalIntegrable_of_Icc h01
  have i3 : IntervalIntegrable (fun s => M s * ∫ r in (0 : ℝ)..s, M r * (U r - 1)) volume 0 1 :=
    (hcM.continuousOn.mul (hprim _ hcMU1)).intervalIntegrable_of_Icc h01
  -- `∫₀¹ M U = D₁ - D₂ - R`
  have hMU : ∫ s in (0 : ℝ)..1, M s * U s =
      dyson1 A x ξ - (dyson2 A x ξ + ∫ s in (0 : ℝ)..1, M s * ∫ r in (0 : ℝ)..s, M r * (U r - 1)) := by
    have e : ∀ s ∈ uIcc (0 : ℝ) 1, M s * U s =
        M s - (M s * (∫ r in (0 : ℝ)..s, M r) + M s * ∫ r in (0 : ℝ)..s, M r * (U r - 1)) := by
      intro s hs
      rw [← mul_add, ← hsplit s (hsub hs), ← hone s (hsub hs)]
      noncomm_ring
    rw [intervalIntegral.integral_congr e, intervalIntegral.integral_sub (hcM.intervalIntegrable _ _)
      (i2.add i3), intervalIntegral.integral_add i2 i3]
    rfl
  have hR : ‖∫ s in (0 : ℝ)..1, M s * ∫ r in (0 : ℝ)..s, M r * (U r - 1)‖ ≤ 2 * m ^ 3 := by
    have := norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := m * (2 * m * m))
      (f := fun s => M s * ∫ r in (0 : ℝ)..s, M r * (U r - 1)) fun s hs => by
        have hs' : s ∈ Icc (0 : ℝ) 1 := by rw [uIoc_of_le h01] at hs; exact ⟨hs.1.le, hs.2⟩
        have hin : ‖∫ r in (0 : ℝ)..s, M r * (U r - 1)‖ ≤ (2 * m * m) := by
          have := norm_integral_le_of_norm_le_const (a := 0) (b := s) (C := m * (2 * m))
            (f := fun r => M r * (U r - 1)) fun r hr => by
              have hr' : r ∈ Icc (0 : ℝ) 1 := by
                rw [uIoc_of_le hs'.1] at hr; exact ⟨hr.1.le, hr.2.trans hs'.2⟩
              calc ‖M r * (U r - 1)‖ ≤ ‖M r‖ * ‖U r - 1‖ := norm_mul_le _ _
                _ ≤ m * (2 * m) := by
                    refine mul_le_mul (hm r hr') ?_ (norm_nonneg _) hm0
                    calc ‖U r - 1‖ ≤ 2 * m * r := hU1 r hr'
                      _ ≤ 2 * m * 1 := mul_le_mul_of_nonneg_left hr'.2 (by positivity)
                      _ = 2 * m := mul_one _
          rw [sub_zero, abs_of_nonneg hs'.1] at this
          nlinarith [hs'.2, mul_nonneg hm0 hm0]
        calc ‖M s * ∫ r in (0 : ℝ)..s, M r * (U r - 1)‖ ≤ ‖M s‖ * ‖∫ r in (0 : ℝ)..s, M r * (U r - 1)‖ :=
              norm_mul_le _ _
          _ ≤ m * (2 * m * m) := mul_le_mul (hm s hs') hin (norm_nonneg _) hm0
    rw [sub_zero, abs_one, mul_one] at this
    linarith [this]
  rw [hU.eq_one_sub_integral hA ⟨h01, le_rfl⟩, hMU]
  have : 1 - (dyson1 A x ξ - (dyson2 A x ξ + ∫ s in (0 : ℝ)..1, M s * ∫ r in (0 : ℝ)..s, M r * (U r - 1))) -
      (1 - dyson1 A x ξ + dyson2 A x ξ) = ∫ s in (0 : ℝ)..1, M s * ∫ r in (0 : ℝ)..s, M r * (U r - 1) := by abel
  rw [this]
  exact hR

end Lightlike.Gauge

namespace Lightlike.Gauge

open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Step 3a: first-order Taylor with a quadratic remainder** for a `C²` map near a point. -/
lemma taylor_one {f : E → F} (hf : ContDiff ℝ 2 f) (x : E) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧ ∀ z, ‖z - x‖ ≤ δ → ‖f z - f x - fderiv ℝ f x (z - x)‖ ≤ K * ‖z - x‖ ^ 2 := by
  have hD : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hDd : Differentiable ℝ (fderiv ℝ f) := hD.differentiable (by norm_num)
  have hD2c : Continuous (fderiv ℝ (fderiv ℝ f)) := (hD.continuous_fderiv (by norm_num))
  obtain ⟨δ, hδ, hball⟩ := (Metric.continuous_iff (α := E) (β := E →L[ℝ] E →L[ℝ] F)).1 hD2c x 1 one_pos
  set K := ‖fderiv ℝ (fderiv ℝ f) x‖ + 1 with hK
  refine ⟨K, δ / 2, by positivity, by positivity, fun z hz => ?_⟩
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  -- `‖Df w - Df x‖ ≤ K ‖w - x‖` on the closed ball of radius `δ/2`
  have hlip : ∀ w ∈ closedBall x (δ / 2), ‖fderiv ℝ f w - fderiv ℝ f x‖ ≤ K * ‖w - x‖ := by
    intro w hw
    refine (convex_closedBall x (δ / 2)).norm_image_sub_le_of_norm_fderiv_le (fun u _ => hDd u)
      (fun u hu => ?_) (mem_closedBall_self (by positivity)) hw
    have hu' : dist u x < δ := lt_of_le_of_lt (mem_closedBall.1 hu) (by linarith)
    have := hball u hu'
    replace this : ‖fderiv ℝ (fderiv ℝ f) u - fderiv ℝ (fderiv ℝ f) x‖ < 1 := by
      exact lt_of_eq_of_lt (dist_eq_norm (fderiv ℝ (fderiv ℝ f) u) (fderiv ℝ (fderiv ℝ f) x)).symm this
    calc ‖fderiv ℝ (fderiv ℝ f) u‖ = ‖(fderiv ℝ (fderiv ℝ f) u - fderiv ℝ (fderiv ℝ f) x) +
          fderiv ℝ (fderiv ℝ f) x‖ := by rw [sub_add_cancel]
      _ ≤ ‖fderiv ℝ (fderiv ℝ f) u - fderiv ℝ (fderiv ℝ f) x‖ + ‖fderiv ℝ (fderiv ℝ f) x‖ :=
          norm_add_le (fderiv ℝ (fderiv ℝ f) u - fderiv ℝ (fderiv ℝ f) x) (fderiv ℝ (fderiv ℝ f) x)
      _ ≤ K := by rw [hK]; linarith
  set ρ := ‖z - x‖ with hρ
  have hsub : closedBall x ρ ⊆ closedBall x (δ / 2) := closedBall_subset_closedBall hz
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hbd : ∀ u ∈ closedBall x ρ, ‖fderiv ℝ f u - fderiv ℝ f x‖ ≤ K * ρ := fun u hu =>
    calc ‖fderiv ℝ f u - fderiv ℝ f x‖ ≤ K * ‖u - x‖ := hlip u (hsub hu)
      _ ≤ K * ρ := mul_le_mul_of_nonneg_left (by rw [← dist_eq_norm]; exact mem_closedBall.1 hu) hK0
  have := (convex_closedBall x ρ).norm_image_sub_le_of_norm_fderiv_le' (φ := fderiv ℝ f x)
    (fun u _ => hfd u) hbd (mem_closedBall_self (norm_nonneg _)) (by
      rw [mem_closedBall, dist_eq_norm])
  refine this.trans (le_of_eq ?_)
  rw [hρ]; ring

end Lightlike.Gauge

namespace Lightlike.Gauge

open Set Metric MeasureTheory intervalIntegral
open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄]

/-- **Step 3b: the first Dyson term to second order.** -/
lemma dyson1_expansion {A : E → E →L[ℝ] 𝔄} (hA : ContDiff ℝ 2 A) (x : E) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧ ∀ y ζ : E, ‖y - x‖ + ‖ζ‖ ≤ δ →
      ‖dyson1 A y ζ - (A x ζ + fderiv ℝ A x (y - x) ζ + (1 / 2 : ℝ) • fderiv ℝ A x ζ ζ)‖ ≤
        K * (‖y - x‖ + ‖ζ‖) ^ 2 * ‖ζ‖ := by
  obtain ⟨K, δ, hK, hδ, hT⟩ := taylor_one hA x
  refine ⟨K, δ, hK, hδ, fun y ζ hyz => ?_⟩
  have hcA : Continuous A := hA.continuous
  set D := fderiv ℝ A x with hD
  have hpoly : ∫ s in (0 : ℝ)..1, (A x ζ + D (y - x) ζ + s • D ζ ζ) =
      A x ζ + D (y - x) ζ + (1 / 2 : ℝ) • D ζ ζ := by
    rw [intervalIntegral.integral_add (intervalIntegrable_const) (by
        exact (continuous_id.smul continuous_const).intervalIntegrable _ _),
      intervalIntegral.integral_const, intervalIntegral.integral_smul_const, integral_id]
    norm_num
  have hcf : Continuous fun s : ℝ => A (y + s • ζ) ζ :=
    (hcA.comp (by fun_prop : Continuous fun s : ℝ => y + s • ζ)).clm_apply continuous_const
  unfold dyson1
  rw [← hpoly, ← intervalIntegral.integral_sub (hcf.intervalIntegrable _ _) (by
      exact (continuous_const.add (continuous_id.smul continuous_const)).intervalIntegrable _ _)]
  have := norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := K * (‖y - x‖ + ‖ζ‖) ^ 2 * ‖ζ‖)
    (f := fun s => A (y + s • ζ) ζ - (A x ζ + D (y - x) ζ + s • D ζ ζ)) fun s hs => by
      have hs' : s ∈ Icc (0 : ℝ) 1 := by rw [uIoc_of_le zero_le_one] at hs; exact ⟨hs.1.le, hs.2⟩
      have hz : ‖(y + s • ζ) - x‖ ≤ ‖y - x‖ + ‖ζ‖ := by
        calc ‖(y + s • ζ) - x‖ = ‖(y - x) + s • ζ‖ := by congr 1; abel
          _ ≤ ‖y - x‖ + ‖s • ζ‖ := norm_add_le _ _
          _ ≤ ‖y - x‖ + ‖ζ‖ := by
              rw [norm_smul, Real.norm_of_nonneg hs'.1]
              nlinarith [norm_nonneg ζ, hs'.2]
      have h1 := hT (y + s • ζ) (hz.trans hyz)
      have e : A (y + s • ζ) ζ - (A x ζ + D (y - x) ζ + s • D ζ ζ) =
          (A (y + s • ζ) - A x - D ((y + s • ζ) - x)) ζ := by
        simp only [ContinuousLinearMap.sub_apply, map_add, map_sub, map_smul, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.smul_apply]
        abel
      rw [e]
      calc ‖(A (y + s • ζ) - A x - D ((y + s • ζ) - x)) ζ‖ ≤ ‖A (y + s • ζ) - A x - D ((y + s • ζ) - x)‖ * ‖ζ‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ K * ‖(y + s • ζ) - x‖ ^ 2 * ‖ζ‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ ≤ K * (‖y - x‖ + ‖ζ‖) ^ 2 * ‖ζ‖ := by
            gcongr
  rw [sub_zero, abs_one, mul_one] at this
  exact this

end Lightlike.Gauge

namespace Lightlike.Gauge

open Set Metric MeasureTheory intervalIntegral
open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄]

/-- First-order bound near `x`: `‖A z - A x‖ ≤ L ‖z - x‖`. -/
lemma lipschitz_near {A : E → E →L[ℝ] 𝔄} (hA : ContDiff ℝ 2 A) (x : E) :
    ∃ L δ : ℝ, 0 ≤ L ∧ 0 < δ ∧ ∀ z, ‖z - x‖ ≤ δ → ‖A z - A x‖ ≤ L * ‖z - x‖ := by
  obtain ⟨K, δ, hK, hδ, hT⟩ := taylor_one hA x
  refine ⟨‖fderiv ℝ A x‖ + K * δ, δ, by positivity, hδ, fun z hz => ?_⟩
  have h1 := hT z hz
  calc ‖A z - A x‖ = ‖(A z - A x - fderiv ℝ A x (z - x)) + fderiv ℝ A x (z - x)‖ := by rw [sub_add_cancel]
    _ ≤ ‖A z - A x - fderiv ℝ A x (z - x)‖ + ‖fderiv ℝ A x (z - x)‖ := norm_add_le _ _
    _ ≤ K * ‖z - x‖ ^ 2 + ‖fderiv ℝ A x‖ * ‖z - x‖ := add_le_add h1 (ContinuousLinearMap.le_opNorm _ _)
    _ ≤ (‖fderiv ℝ A x‖ + K * δ) * ‖z - x‖ := by
        have : K * ‖z - x‖ ^ 2 ≤ K * δ * ‖z - x‖ := by
          rw [sq, ← mul_assoc]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz hK) (norm_nonneg _)
        nlinarith

/-- **Step 3c: the second Dyson term to second order**: `‖D₂(y, ζ) - ½ (A x ζ)²‖ ≤ C (‖y - x‖ + ‖ζ‖)³`. -/
lemma dyson2_expansion {A : E → E →L[ℝ] 𝔄} (hA : ContDiff ℝ 2 A) (x : E) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ y ζ : E, ‖y - x‖ + ‖ζ‖ ≤ δ →
      ‖dyson2 A y ζ - (1 / 2 : ℝ) • (A x ζ * A x ζ)‖ ≤ C * (‖y - x‖ + ‖ζ‖) ^ 3 := by
  obtain ⟨L, δ, hL, hδ, hLip⟩ := lipschitz_near hA x
  refine ⟨2 * ‖A x‖ * L + L ^ 2 * δ, δ, by positivity, hδ, fun y ζ hyz => ?_⟩
  set r := ‖y - x‖ + ‖ζ‖ with hr
  have hr0 : 0 ≤ r := by positivity
  have hζr : ‖ζ‖ ≤ r := by rw [hr]; linarith [norm_nonneg (y - x)]
  set a : 𝔄 := A x ζ with ha
  set M : ℝ → 𝔄 := fun s => A (y + s • ζ) ζ with hM
  have hcM : Continuous M := (hA.continuous.comp (by fun_prop : Continuous fun s : ℝ => y + s • ζ)).clm_apply
    continuous_const
  -- `‖M s - a‖ ≤ L r ‖ζ‖` on `[0, 1]`
  have he : ∀ s ∈ Icc (0 : ℝ) 1, ‖M s - a‖ ≤ L * r * ‖ζ‖ := by
    intro s hs
    have hz : ‖(y + s • ζ) - x‖ ≤ r := by
      calc ‖(y + s • ζ) - x‖ = ‖(y - x) + s • ζ‖ := by congr 1; abel
        _ ≤ ‖y - x‖ + ‖s • ζ‖ := norm_add_le _ _
        _ ≤ r := by rw [norm_smul, Real.norm_of_nonneg hs.1]; nlinarith [norm_nonneg ζ, hs.2]
    have h1 := hLip (y + s • ζ) (hz.trans hyz)
    calc ‖M s - a‖ = ‖(A (y + s • ζ) - A x) ζ‖ := by simp [hM, ha]
      _ ≤ ‖A (y + s • ζ) - A x‖ * ‖ζ‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ L * ‖(y + s • ζ) - x‖ * ‖ζ‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ ≤ L * r * ‖ζ‖ := by gcongr
  have hna : ‖a‖ ≤ ‖A x‖ * ‖ζ‖ := ContinuousLinearMap.le_opNorm _ _
  have h01 : (0 : ℝ) ≤ 1 := zero_le_one
  have hprim : Continuous fun s => ∫ r in (0 : ℝ)..s, M r :=
    intervalIntegral.continuous_primitive (fun _ _ => hcM.intervalIntegrable _ _) 0
  have hpoly : ∫ s in (0 : ℝ)..1, s • (a * a) = (1 / 2 : ℝ) • (a * a) := by
    rw [intervalIntegral.integral_smul_const, integral_id]; norm_num
  have hdiff : dyson2 A y ζ - (1 / 2 : ℝ) • (a * a) =
      ∫ s in (0 : ℝ)..1, ((M s - a) * (∫ r in (0 : ℝ)..s, M r) + a * ∫ r in (0 : ℝ)..s, (M r - a)) := by
    rw [← hpoly]
    unfold dyson2
    rw [← intervalIntegral.integral_sub (f := fun s => A (y + s • ζ) ζ * ∫ r in (0 : ℝ)..s, A (y + r • ζ) ζ)
      (g := fun s => s • (a * a)) ((hcM.mul hprim).intervalIntegrable _ _)
      ((continuous_id.smul continuous_const).intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [intervalIntegral.integral_sub (hcM.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, sub_zero]
    noncomm_ring
  rw [hdiff]
  have hbd : ∀ s ∈ Ι (0 : ℝ) 1, ‖(M s - a) * (∫ r in (0 : ℝ)..s, M r) + a * ∫ r in (0 : ℝ)..s, (M r - a)‖ ≤
      2 * ‖A x‖ * L * r * ‖ζ‖ ^ 2 + L ^ 2 * r ^ 2 * ‖ζ‖ ^ 2 := by
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := by rw [uIoc_of_le h01] at hs; exact ⟨hs.1.le, hs.2⟩
    have hsub : ∀ t ∈ Ι (0 : ℝ) s, t ∈ Icc (0 : ℝ) 1 := fun t ht => by
      rw [uIoc_of_le hs'.1] at ht; exact ⟨ht.1.le, ht.2.trans hs'.2⟩
    have hs1 : |s - 0| ≤ 1 := by rw [sub_zero, abs_of_nonneg hs'.1]; exact hs'.2
    have hint1 : ‖∫ r in (0 : ℝ)..s, M r‖ ≤ ‖A x‖ * ‖ζ‖ + L * r * ‖ζ‖ := by
      have := norm_integral_le_of_norm_le_const (a := 0) (b := s) (C := ‖A x‖ * ‖ζ‖ + L * r * ‖ζ‖)
        (f := M) fun t ht => by
          calc ‖M t‖ = ‖(M t - a) + a‖ := by rw [sub_add_cancel]
            _ ≤ ‖M t - a‖ + ‖a‖ := norm_add_le _ _
            _ ≤ L * r * ‖ζ‖ + ‖A x‖ * ‖ζ‖ := add_le_add (he t (hsub t ht)) hna
            _ = _ := by ring
      calc _ ≤ (‖A x‖ * ‖ζ‖ + L * r * ‖ζ‖) * |s - 0| := this
        _ ≤ (‖A x‖ * ‖ζ‖ + L * r * ‖ζ‖) * 1 := mul_le_mul_of_nonneg_left hs1 (by positivity)
        _ = _ := mul_one _
    have hint2 : ‖∫ r in (0 : ℝ)..s, (M r - a)‖ ≤ L * r * ‖ζ‖ := by
      have := norm_integral_le_of_norm_le_const (a := 0) (b := s) (C := L * r * ‖ζ‖)
        (f := fun t => M t - a) fun t ht => he t (hsub t ht)
      calc _ ≤ L * r * ‖ζ‖ * |s - 0| := this
        _ ≤ L * r * ‖ζ‖ * 1 := mul_le_mul_of_nonneg_left hs1 (by positivity)
        _ = _ := mul_one _
    calc ‖(M s - a) * (∫ r in (0 : ℝ)..s, M r) + a * ∫ r in (0 : ℝ)..s, (M r - a)‖
        ≤ ‖M s - a‖ * ‖∫ r in (0 : ℝ)..s, M r‖ + ‖a‖ * ‖∫ r in (0 : ℝ)..s, (M r - a)‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ (L * r * ‖ζ‖) * (‖A x‖ * ‖ζ‖ + L * r * ‖ζ‖) + (‖A x‖ * ‖ζ‖) * (L * r * ‖ζ‖) :=
          add_le_add (mul_le_mul (he s hs') hint1 (norm_nonneg _) (by positivity))
            (mul_le_mul hna hint2 (norm_nonneg _) (by positivity))
      _ = _ := by ring
  have := norm_integral_le_of_norm_le_const hbd
  rw [sub_zero, abs_one, mul_one] at this
  refine this.trans ?_
  have hζ2 : ‖ζ‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hζr 2
  have hrδ : r ≤ δ := hyz
  calc 2 * ‖A x‖ * L * r * ‖ζ‖ ^ 2 + L ^ 2 * r ^ 2 * ‖ζ‖ ^ 2
      ≤ 2 * ‖A x‖ * L * r * r ^ 2 + L ^ 2 * r ^ 2 * (δ * r) := by
        gcongr
        nlinarith [norm_nonneg ζ]
    _ = (2 * ‖A x‖ * L + L ^ 2 * δ) * r ^ 3 := by ring

end Lightlike.Gauge

namespace Lightlike.Gauge

variable {𝔄 : Type*} [NormedRing 𝔄]

/-- **Step 4a: the product of four factors `1 + pᵢ`** to second order, with the remainder of order three. -/
lemma prod_four_expand (p₁ p₂ p₃ p₄ : 𝔄) :
    (1 + p₄) * (1 + p₃) * (1 + p₂) * (1 + p₁) =
      1 + (p₁ + p₂ + p₃ + p₄) + (p₂ * p₁ + p₃ * p₁ + p₃ * p₂ + p₄ * p₁ + p₄ * p₂ + p₄ * p₃) +
        (p₃ * p₂ * p₁ + p₄ * p₂ * p₁ + p₄ * p₃ * p₁ + p₄ * p₃ * p₂ + p₄ * p₃ * p₂ * p₁) := by
  noncomm_ring

/-- The remainder of `prod_four_expand` is of order three. -/
lemma norm_prod_four_rem_le [NormOneClass 𝔄] {p₁ p₂ p₃ p₄ : 𝔄} {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (h₁ : ‖p₁‖ ≤ q) (h₂ : ‖p₂‖ ≤ q) (h₃ : ‖p₃‖ ≤ q) (h₄ : ‖p₄‖ ≤ q) :
    ‖p₃ * p₂ * p₁ + p₄ * p₂ * p₁ + p₄ * p₃ * p₁ + p₄ * p₃ * p₂ + p₄ * p₃ * p₂ * p₁‖ ≤ 5 * q ^ 3 := by
  have t : ∀ a b c : 𝔄, ‖a‖ ≤ q → ‖b‖ ≤ q → ‖c‖ ≤ q → ‖a * b * c‖ ≤ q ^ 3 := by
    intro a b c ha hb hc
    calc ‖a * b * c‖ ≤ ‖a‖ * ‖b‖ * ‖c‖ := (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ q * q * q := mul_le_mul (mul_le_mul ha hb (norm_nonneg _) hq) hc (norm_nonneg _) (by positivity)
      _ = q ^ 3 := by ring
  have t4 : ‖p₄ * p₃ * p₂ * p₁‖ ≤ q ^ 3 := by
    calc ‖p₄ * p₃ * p₂ * p₁‖ ≤ ‖p₄ * p₃ * p₂‖ * ‖p₁‖ := norm_mul_le _ _
      _ ≤ q ^ 3 * q := mul_le_mul (t _ _ _ h₄ h₃ h₂) h₁ (norm_nonneg _) (by positivity)
      _ ≤ q ^ 3 * 1 := mul_le_mul_of_nonneg_left hq1 (by positivity)
      _ = q ^ 3 := mul_one _
  calc ‖p₃ * p₂ * p₁ + p₄ * p₂ * p₁ + p₄ * p₃ * p₁ + p₄ * p₃ * p₂ + p₄ * p₃ * p₂ * p₁‖
      ≤ ‖p₃ * p₂ * p₁‖ + ‖p₄ * p₂ * p₁‖ + ‖p₄ * p₃ * p₁‖ + ‖p₄ * p₃ * p₂‖ + ‖p₄ * p₃ * p₂ * p₁‖ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        exact norm_add_le _ _
    _ ≤ q ^ 3 + q ^ 3 + q ^ 3 + q ^ 3 + q ^ 3 := by
        gcongr
        · exact t _ _ _ h₃ h₂ h₁
        · exact t _ _ _ h₄ h₂ h₁
        · exact t _ _ _ h₄ h₃ h₁
        · exact t _ _ _ h₄ h₃ h₂
    _ = 5 * q ^ 3 := by ring

end Lightlike.Gauge

/-! ### Step 4b (assembly), the computation to be formalised

Legs `i = 1..4`: base `yᵢ = x, x + εξ, x + εξ + εη, x + εη`, step `ζᵢ = εξ, εη, -εξ, -εη`; `D = fderiv A x`,
`a = A x ξ`, `b = A x η`; `cᵢ = A x ζᵢ / ε = a, b, -a, -b`.
* `Uᵢ 1 = 1 + pᵢ + O(ε³)`, `pᵢ = -D₁ⁱ + D₂ⁱ` (step 2 with `mᵢ = O(ε)`), `‖pᵢ‖ = O(ε)`.
* `U₄U₃U₂U₁ = (1+p₄)(1+p₃)(1+p₂)(1+p₁) + O(ε³)` (product perturbation).
* `= 1 + Σ pᵢ + Σ_{i>j} pᵢ pⱼ + O(ε³)` (`prod_four_expand`, `norm_prod_four_rem_le`).
* `Σ D₁ⁱ = Σ A x ζᵢ + Σ D(yᵢ - x)ζᵢ + ½ Σ D ζᵢ ζᵢ + O(ε³) = 0 + ε²(Dξη - Dξξ - Dηξ - Dηη) + ε²(Dξξ + Dηη)
  = ε²(Dξη - Dηξ) + O(ε³)` (`dyson1_expansion`).
* `Σ D₂ⁱ = ½ ε² (a² + b² + a² + b²) + O(ε³)` (`dyson2_expansion`).
* `Σ_{i>j} pᵢ pⱼ = ε² Σ_{i>j} cᵢ cⱼ + O(ε³) = ε² (ba - a² - ab - ba - b² + ba) + O(ε³)`.
* Total `ε²` coefficient: `Dηξ - Dξη + ba - ab = curvature A x η ξ` (eq. (62)). Sign checked by hand, 19 Nov.
-/

namespace Lightlike.Gauge

/-! ### The `Small` calculus: `‖f ε‖ ≤ C ε^k` for small `ε > 0` -/

variable {𝔅 : Type*} [NormedRing 𝔅]

/-- `f` is of order `ε^k` as `ε → 0⁺`. -/
def Small (k : ℕ) (f : ℝ → 𝔅) : Prop :=
  ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ‖f ε‖ ≤ C * ε ^ k

lemma Small.add {k : ℕ} {f g : ℝ → 𝔅} (hf : Small k f) (hg : Small k g) : Small k (fun ε => f ε + g ε) := by
  obtain ⟨C₁, e₁, h₁, hf⟩ := hf
  obtain ⟨C₂, e₂, h₂, hg⟩ := hg
  refine ⟨C₁ + C₂, min e₁ e₂, lt_min h₁ h₂, fun ε hε hεe => ?_⟩
  calc ‖f ε + g ε‖ ≤ ‖f ε‖ + ‖g ε‖ := norm_add_le _ _
    _ ≤ C₁ * ε ^ k + C₂ * ε ^ k := add_le_add (hf ε hε (hεe.trans (min_le_left _ _)))
        (hg ε hε (hεe.trans (min_le_right _ _)))
    _ = (C₁ + C₂) * ε ^ k := by ring

lemma Small.neg {k : ℕ} {f : ℝ → 𝔅} (hf : Small k f) : Small k (fun ε => -f ε) := by
  obtain ⟨C, e, h, hf⟩ := hf
  exact ⟨C, e, h, fun ε hε hεe => by rw [norm_neg]; exact hf ε hε hεe⟩

lemma Small.sub {k : ℕ} {f g : ℝ → 𝔅} (hf : Small k f) (hg : Small k g) : Small k (fun ε => f ε - g ε) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

lemma Small.mul {k l : ℕ} {f g : ℝ → 𝔅} (hf : Small k f) (hg : Small l g) :
    Small (k + l) (fun ε => f ε * g ε) := by
  obtain ⟨C₁, e₁, h₁, hf⟩ := hf
  obtain ⟨C₂, e₂, h₂, hg⟩ := hg
  refine ⟨C₁ * C₂, min e₁ e₂, lt_min h₁ h₂, fun ε hε hεe => ?_⟩
  have a := hf ε hε (hεe.trans (min_le_left _ _))
  have b := hg ε hε (hεe.trans (min_le_right _ _))
  have hC₁ : 0 ≤ C₁ * ε ^ k := le_trans (norm_nonneg _) a
  calc ‖f ε * g ε‖ ≤ ‖f ε‖ * ‖g ε‖ := norm_mul_le _ _
    _ ≤ (C₁ * ε ^ k) * (C₂ * ε ^ l) := mul_le_mul a b (norm_nonneg _) hC₁
    _ = C₁ * C₂ * ε ^ (k + l) := by ring

lemma Small.mono {k l : ℕ} (hkl : l ≤ k) {f : ℝ → 𝔅} (hf : Small k f) : Small l f := by
  obtain ⟨C, e, h, hf⟩ := hf
  refine ⟨max C 0, min e 1, lt_min h one_pos, fun ε hε hεe => ?_⟩
  have h1 : ε ≤ 1 := hεe.trans (min_le_right _ _)
  calc ‖f ε‖ ≤ C * ε ^ k := hf ε hε (hεe.trans (min_le_left _ _))
    _ ≤ max C 0 * ε ^ k := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C 0 * ε ^ l := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hε.le h1 hkl) (le_max_right _ _)

/-- `ε^k • c` is of order `k`. -/
lemma small_pow_smul [NormedAlgebra ℝ 𝔅] (k : ℕ) (c : 𝔅) : Small k (fun ε => ε ^ k • c) :=
  ⟨‖c‖, 1, one_pos, fun ε hε _ => by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), mul_comm]⟩

lemma small_zero (k : ℕ) : Small k (fun _ => (0 : 𝔅)) :=
  ⟨0, 1, one_pos, fun ε _ _ => by simp⟩

end Lightlike.Gauge

namespace Lightlike.Gauge

open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄]

/-- Smallness of `ε (‖yv‖ + ‖zv‖)`: for `0 < ε ≤ δ/(‖yv‖ + ‖zv‖ + 1)` it is at most `δ`. -/
lemma scaled_le {δ ε : ℝ} (hδ : 0 < δ) (yv zv : E) (hε : 0 < ε) (hεe : ε ≤ δ / (‖yv‖ + ‖zv‖ + 1)) :
    ‖ε • yv‖ + ‖ε • zv‖ ≤ δ := by
  rw [norm_smul, norm_smul, Real.norm_of_nonneg hε.le]
  have hpos : 0 < ‖yv‖ + ‖zv‖ + 1 := by positivity
  rw [le_div_iff₀ hpos] at hεe
  nlinarith [norm_nonneg yv, norm_nonneg zv]

/-- **A leg's first Dyson term in `ε`**: `D₁(x + εyv, εzv) = ε A(x)zv + ε² (DA(x) yv zv + ½ DA(x) zv zv) + O(ε³)`. -/
lemma leg_dyson1 {A : E → E →L[ℝ] 𝔄} (hA : ContDiff ℝ 2 A) (x yv zv : E) :
    Small 3 (fun ε => dyson1 A (x + ε • yv) (ε • zv) -
      (ε • A x zv + ε ^ 2 • (fderiv ℝ A x yv zv + (1 / 2 : ℝ) • fderiv ℝ A x zv zv))) := by
  obtain ⟨K, δ, hK, hδ, h⟩ := dyson1_expansion hA x
  refine ⟨K * (‖yv‖ + ‖zv‖) ^ 2 * ‖zv‖, δ / (‖yv‖ + ‖zv‖ + 1), by positivity, fun ε hε hεe => ?_⟩
  have hyx : (x + ε • yv) - x = ε • yv := by abel
  have hb := h (x + ε • yv) (ε • zv) (by rw [hyx]; exact scaled_le hδ yv zv hε hεe)
  rw [hyx] at hb
  have e : A x (ε • zv) + fderiv ℝ A x (ε • yv) (ε • zv) + (1 / 2 : ℝ) • fderiv ℝ A x (ε • zv) (ε • zv) =
      ε • A x zv + ε ^ 2 • (fderiv ℝ A x yv zv + (1 / 2 : ℝ) • fderiv ℝ A x zv zv) := by
    simp only [map_smul, ContinuousLinearMap.smul_apply]
    module
  rw [e] at hb
  refine hb.trans (le_of_eq ?_)
  simp only [norm_smul, Real.norm_of_nonneg hε.le]
  ring

/-- **A leg's second Dyson term in `ε`**: `D₂(x + εyv, εzv) = ½ ε² (A(x)zv)² + O(ε³)`. -/
lemma leg_dyson2 {A : E → E →L[ℝ] 𝔄} (hA : ContDiff ℝ 2 A) (x yv zv : E) :
    Small 3 (fun ε => dyson2 A (x + ε • yv) (ε • zv) - ε ^ 2 • ((1 / 2 : ℝ) • (A x zv * A x zv))) := by
  obtain ⟨C, δ, hC, hδ, h⟩ := dyson2_expansion hA x
  refine ⟨C * (‖yv‖ + ‖zv‖) ^ 3, δ / (‖yv‖ + ‖zv‖ + 1), by positivity, fun ε hε hεe => ?_⟩
  have hyx : (x + ε • yv) - x = ε • yv := by abel
  have hb := h (x + ε • yv) (ε • zv) (by rw [hyx]; exact scaled_le hδ yv zv hε hεe)
  rw [hyx] at hb
  have e : (1 / 2 : ℝ) • (A x (ε • zv) * A x (ε • zv)) = ε ^ 2 • ((1 / 2 : ℝ) • (A x zv * A x zv)) := by
    simp only [map_smul, smul_mul_smul_comm]
    module
  rw [e] at hb
  refine hb.trans (le_of_eq ?_)
  rw [norm_smul, norm_smul, Real.norm_of_nonneg hε.le]
  ring

end Lightlike.Gauge

namespace Lightlike.Gauge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄]

/-- The `ε²` coefficient of a leg `(yv, zv)`: `G = ½ (A zv)² - (D yv zv + ½ D zv zv)`. -/
noncomputable def legG (A : E → E →L[ℝ] 𝔄) (x yv zv : E) : 𝔄 :=
  (1 / 2 : ℝ) • (A x zv * A x zv) - (fderiv ℝ A x yv zv + (1 / 2 : ℝ) • fderiv ℝ A x zv zv)

/-- **The `ε²` coefficients add up to the curvature** (Svetlichny eq. (62)): for the legs
`(0, ξ), (ξ, η), (ξ + η, -ξ), (η, -η)` with first-order coefficients `c = a, b, -a, -b`,
`Σ Gᵢ + Σ_{i>j} cᵢ cⱼ = F(η, ξ)`. -/
lemma sum_legG_add_pairs (A : E → E →L[ℝ] 𝔄) (x ξ η : E) :
    legG A x 0 ξ + legG A x ξ η + legG A x (ξ + η) (-ξ) + legG A x η (-η) +
      (A x η * A x ξ + A x (-ξ) * A x ξ + A x (-ξ) * A x η + A x (-η) * A x ξ + A x (-η) * A x η +
        A x (-η) * A x (-ξ)) = curvature A x η ξ := by
  unfold legG curvature
  simp only [map_zero, map_neg, map_add, ContinuousLinearMap.zero_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.add_apply, neg_mul, mul_neg, neg_neg]
  module

end Lightlike.Gauge

namespace Lightlike.Gauge

variable {𝔅 : Type*} [NormedRing 𝔅]

lemma Small.congr {k : ℕ} {f g : ℝ → 𝔅} (hf : Small k f) (h : ∀ ε, f ε = g ε) : Small k g := by
  obtain ⟨C, e, he, hf⟩ := hf
  exact ⟨C, e, he, fun ε hε hεe => by rw [← h ε]; exact hf ε hε hεe⟩

end Lightlike.Gauge

namespace Lightlike.Gauge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄]

/-- The leg term `p = -D₁ + D₂` of the leg from `x + εyv` with step `εzv`. -/
noncomputable def legP (A : E → E →L[ℝ] 𝔄) (x yv zv : E) (ε : ℝ) : 𝔄 :=
  -dyson1 A (x + ε • yv) (ε • zv) + dyson2 A (x + ε • yv) (ε • zv)

lemma legP_expansion {A : E → E →L[ℝ] 𝔄} (hA : ContDiff ℝ 2 A) (x yv zv : E) :
    Small 3 (fun ε => legP A x yv zv ε - (-(ε • A x zv) + ε ^ 2 • legG A x yv zv)) := by
  refine ((leg_dyson1 hA x yv zv).neg.add (leg_dyson2 hA x yv zv)).congr fun ε => ?_
  unfold legP legG
  simp only [smul_sub, smul_add]
  abel

lemma legP_add_c {A : E → E →L[ℝ] 𝔄} (hA : ContDiff ℝ 2 A) (x yv zv : E) :
    Small 2 (fun ε => legP A x yv zv ε + ε • A x zv) := by
  refine (((legP_expansion hA x yv zv).mono (by norm_num)).add (small_pow_smul 2 (legG A x yv zv))).congr
    fun ε => ?_
  abel

lemma small_smul_one (c : 𝔄) : Small 1 (fun ε : ℝ => ε • c) :=
  (small_pow_smul 1 c).congr fun ε => by rw [pow_one]

lemma legP_small {A : E → E →L[ℝ] 𝔄} (hA : ContDiff ℝ 2 A) (x yv zv : E) :
    Small 1 (legP A x yv zv) :=
  (((legP_add_c hA x yv zv).mono (by norm_num)).sub (small_smul_one (A x zv))).congr fun ε => by
    abel

/-- `ε² (c d) = (ε c)(ε d)`. -/
lemma sq_smul_mul (ε : ℝ) (c d : 𝔄) : ε ^ 2 • (c * d) = (ε • c) * (ε • d) := by
  rw [smul_mul_smul_comm, pow_two]

/-- **The product of the four leg factors to second order** (Svetlichny eq. (62)). -/
theorem prod_legP {A : E → E →L[ℝ] 𝔄} (hA : ContDiff ℝ 2 A) (x ξ η : E) :
    Small 3 (fun ε => (1 + legP A x η (-η) ε) * (1 + legP A x (ξ + η) (-ξ) ε) * (1 + legP A x ξ η ε) *
      (1 + legP A x 0 ξ ε) - (1 + ε ^ 2 • curvature A x η ξ)) := by
  set p₁ := legP A x 0 ξ
  set p₂ := legP A x ξ η
  set p₃ := legP A x (ξ + η) (-ξ)
  set p₄ := legP A x η (-η)
  have hc : A x ξ + A x η + A x (-ξ) + A x (-η) = 0 := by simp only [map_neg]; abel
  -- the pieces
  have q₁ := legP_expansion hA x 0 ξ
  have q₂ := legP_expansion hA x ξ η
  have q₃ := legP_expansion hA x (ξ + η) (-ξ)
  have q₄ := legP_expansion hA x η (-η)
  have s₁ := legP_small hA x 0 ξ
  have s₂ := legP_small hA x ξ η
  have s₃ := legP_small hA x (ξ + η) (-ξ)
  have s₄ := legP_small hA x η (-η)
  have a₁ := legP_add_c hA x 0 ξ
  have a₂ := legP_add_c hA x ξ η
  have a₃ := legP_add_c hA x (ξ + η) (-ξ)
  have a₄ := legP_add_c hA x η (-η)
  -- the pair term `pᵢ pⱼ - (εcᵢ)(εcⱼ) = (pᵢ + εcᵢ) pⱼ - (εcᵢ)(pⱼ + εcⱼ)` is of order 3
  have pair : ∀ {pi pj : ℝ → 𝔄} {ci cj : 𝔄}, Small 2 (fun ε => pi ε + ε • ci) → Small 1 pj →
      Small 2 (fun ε => pj ε + ε • cj) →
      Small 3 (fun ε => pi ε * pj ε - (ε • ci) * (ε • cj)) := by
    intro pi pj ci cj hai hsj haj
    refine ((hai.mul hsj).sub ((small_smul_one ci).mul haj)).congr fun ε => ?_
    noncomm_ring
  have t3 : ∀ {f g h : ℝ → 𝔄}, Small 1 f → Small 1 g → Small 1 h → Small 3 (fun ε => f ε * g ε * h ε) :=
    fun hf hg hh => (hf.mul hg).mul hh
  have t4 : Small 3 (fun ε => p₄ ε * p₃ ε * p₂ ε * p₁ ε) := ((((s₄.mul s₃).mul s₂).mul s₁)).mono (by norm_num)
  have big := (((((q₁.add q₂).add q₃).add q₄).add
    ((((((pair a₂ s₁ a₁).add (pair a₃ s₁ a₁)).add (pair a₃ s₂ a₂)).add (pair a₄ s₁ a₁)).add
      (pair a₄ s₂ a₂)).add (pair a₄ s₃ a₃))).add
    (((((t3 s₃ s₂ s₁).add (t3 s₄ s₂ s₁)).add (t3 s₄ s₃ s₁)).add (t3 s₄ s₃ s₂)).add t4))
  refine big.congr fun ε => ?_
  rw [prod_four_expand, ← sum_legG_add_pairs A x ξ η]
  have hε : ε • A x ξ + ε • A x η + ε • A x (-ξ) + ε • A x (-η) = 0 := by
    rw [← smul_add, ← smul_add, ← smul_add, hc, smul_zero]
  simp only [smul_add, sq_smul_mul]
  -- now a ring identity in the atoms `pᵢ ε`, `ε • A x ·`, `ε ^ 2 • Gᵢ`
  have hε' : ε • A x (-η) = -(ε • A x ξ + ε • A x η + ε • A x (-ξ)) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact hε
  rw [hε']
  noncomm_ring

end Lightlike.Gauge

namespace Lightlike.Gauge

open Set Metric

variable {𝔅 : Type*} [NormedRing 𝔅]

/-- **Telescoping**: `‖u₄u₃u₂u₁ - v₄v₃v₂v₁‖ ≤ 4 M³ e` if all factors have norm `≤ M` and `‖uᵢ - vᵢ‖ ≤ e`. -/
lemma norm_prod4_sub_le {u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄ : 𝔅} {M e : ℝ} (hM : 0 ≤ M)
    (hu₁ : ‖u₁‖ ≤ M) (hu₂ : ‖u₂‖ ≤ M) (hu₃ : ‖u₃‖ ≤ M) (hv₂ : ‖v₂‖ ≤ M) (hv₃ : ‖v₃‖ ≤ M) (hv₄ : ‖v₄‖ ≤ M)
    (h₁ : ‖u₁ - v₁‖ ≤ e) (h₂ : ‖u₂ - v₂‖ ≤ e) (h₃ : ‖u₃ - v₃‖ ≤ e) (h₄ : ‖u₄ - v₄‖ ≤ e) :
    ‖u₄ * u₃ * u₂ * u₁ - v₄ * v₃ * v₂ * v₁‖ ≤ 4 * M ^ 3 * e := by
  have he : 0 ≤ e := le_trans (norm_nonneg _) h₁
  have id : u₄ * u₃ * u₂ * u₁ - v₄ * v₃ * v₂ * v₁ = (u₄ - v₄) * u₃ * u₂ * u₁ + v₄ * (u₃ - v₃) * u₂ * u₁ +
      v₄ * v₃ * (u₂ - v₂) * u₁ + v₄ * v₃ * v₂ * (u₁ - v₁) := by noncomm_ring
  have n4 : ∀ a b c d : 𝔅, ‖a * b * c * d‖ ≤ ‖a‖ * ‖b‖ * ‖c‖ * ‖d‖ := fun a b c d =>
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ((norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))) (norm_nonneg _))
  rw [id]
  calc _ ≤ ‖(u₄ - v₄) * u₃ * u₂ * u₁‖ + ‖v₄ * (u₃ - v₃) * u₂ * u₁‖ + ‖v₄ * v₃ * (u₂ - v₂) * u₁‖ +
        ‖v₄ * v₃ * v₂ * (u₁ - v₁)‖ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        exact norm_add_le _ _
    _ ≤ e * M * M * M + M * e * M * M + M * M * e * M + M * M * M * e := by
        gcongr
        · exact (n4 _ _ _ _).trans (by gcongr)
        · exact (n4 _ _ _ _).trans (by gcongr)
        · exact (n4 _ _ _ _).trans (by gcongr)
        · exact (n4 _ _ _ _).trans (by gcongr)
    _ = 4 * M ^ 3 * e := by ring

end Lightlike.Gauge

namespace Lightlike.Gauge

open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]

/-- A transport of the leg `(x + εyv, εzv)` is `1 + p` up to `2 (ε B)³`. -/
lemma leg_transport {A : E → E →L[ℝ] 𝔄} (hA : ContDiff ℝ 2 A) {x yv zv : E} {ε B : ℝ} (hε : 0 < ε)
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, ‖A (x + ε • yv + t • (ε • zv)) (ε • zv)‖ ≤ ε * B) (hεB : ε * B ≤ 1 / 2)
    {U : ℝ → 𝔄} (hU : IsSegmentTransport A (x + ε • yv) (ε • zv) U) :
    ‖U 1 - (1 + legP A x yv zv ε)‖ ≤ 2 * (ε * B) ^ 3 ∧ ‖U 1‖ ≤ 2 := by
  have h2 := hU.second_order hA.continuous hB hεB
  refine ⟨?_, hU.norm_le_two hA.continuous hB hεB 1 ⟨zero_le_one, le_rfl⟩⟩
  refine le_of_eq_of_le ?_ h2
  unfold legP; congr 1; abel

/-- **Holonomy of a small parallelogram is the curvature to second order** (GC1; Svetlichny eq. (62)). -/
theorem squareHolonomy_eq {A : E → E →L[ℝ] 𝔄} (hA : ContDiff ℝ 2 A) (x ξ η : E) :
    ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ U₁ U₂ U₃ U₄ : ℝ → 𝔄,
      IsSegmentTransport A x (ε • ξ) U₁ →
      IsSegmentTransport A (x + ε • ξ) (ε • η) U₂ →
      IsSegmentTransport A (x + ε • ξ + ε • η) (-(ε • ξ)) U₃ →
      IsSegmentTransport A (x + ε • η) (-(ε • η)) U₄ →
      ‖U₄ 1 * U₃ 1 * U₂ 1 * U₁ 1 - (1 + ε ^ 2 • curvature A x η ξ)‖ ≤ C * ε ^ 3 := by
  obtain ⟨L, δ, hL, hδ, hLip⟩ := lipschitz_near hA x
  obtain ⟨C₀, e₀, he₀, hP⟩ := prod_legP hA x ξ η
  set N : ℝ := 2 * (‖ξ‖ + ‖η‖) + 1 with hN
  have hN0 : 0 < N := by positivity
  set B : ℝ := (‖A x‖ + L * δ) * (‖ξ‖ + ‖η‖ + 1) with hBdef
  have hB0 : 0 ≤ B := by positivity
  refine ⟨216 * B ^ 3 + C₀, min (min e₀ (δ / N)) (1 / (2 * B + 1)), by positivity, ?_⟩
  intro ε hε hεe U₁ U₂ U₃ U₄ h₁ h₂ h₃ h₄
  have hεe₀ : ε ≤ e₀ := hεe.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεδ : ε ≤ δ / N := hεe.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hεB : ε * B ≤ 1 / 2 := by
    have h := hεe.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h
    nlinarith
  -- the integrand bound along a leg
  have bound : ∀ yv zv : E, ‖yv‖ + ‖zv‖ ≤ N → ‖zv‖ ≤ ‖ξ‖ + ‖η‖ + 1 →
      ∀ t ∈ Icc (0 : ℝ) 1, ‖A (x + ε • yv + t • (ε • zv)) (ε • zv)‖ ≤ ε * B := by
    intro yv zv hn hζ t ht
    have hz : ‖(x + ε • yv + t • (ε • zv)) - x‖ ≤ δ := by
      have e1 : (x + ε • yv + t • (ε • zv)) - x = ε • (yv + t • zv) := by
        rw [smul_add, smul_comm t ε]; abel
      rw [e1, norm_smul, Real.norm_of_nonneg hε.le]
      have : ‖yv + t • zv‖ ≤ N := by
        calc ‖yv + t • zv‖ ≤ ‖yv‖ + ‖t • zv‖ := norm_add_le _ _
          _ ≤ ‖yv‖ + ‖zv‖ := by
              rw [norm_smul, Real.norm_of_nonneg ht.1]; nlinarith [norm_nonneg zv, ht.2]
          _ ≤ N := hn
      rw [le_div_iff₀ hN0] at hεδ
      nlinarith [norm_nonneg (yv + t • zv)]
    have hA' : ‖A (x + ε • yv + t • (ε • zv))‖ ≤ ‖A x‖ + L * δ := by
      have := hLip _ hz
      calc ‖A (x + ε • yv + t • (ε • zv))‖ = ‖(A (x + ε • yv + t • (ε • zv)) - A x) + A x‖ := by
            rw [sub_add_cancel]
        _ ≤ L * ‖(x + ε • yv + t • (ε • zv)) - x‖ + ‖A x‖ := (norm_add_le _ _).trans (add_le_add this le_rfl)
        _ ≤ L * δ + ‖A x‖ := by gcongr
        _ = _ := by ring
    calc ‖A (x + ε • yv + t • (ε • zv)) (ε • zv)‖ ≤ ‖A (x + ε • yv + t • (ε • zv))‖ * ‖ε • zv‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖A x‖ + L * δ) * (ε * (‖ξ‖ + ‖η‖ + 1)) := by
          rw [norm_smul, Real.norm_of_nonneg hε.le]
          exact mul_le_mul hA' (mul_le_mul_of_nonneg_left hζ hε.le) (by positivity) (by positivity)
      _ = ε * B := by rw [hBdef]; ring
  -- the four legs, in the form `(x + εyv, εzv)`
  have e1 : x = x + ε • (0 : E) := by simp
  have e3 : x + ε • ξ + ε • η = x + ε • (ξ + η) := by rw [smul_add, add_assoc]
  have hn1 : ‖(0 : E)‖ + ‖ξ‖ ≤ N := by rw [norm_zero, hN]; nlinarith [norm_nonneg ξ, norm_nonneg η]
  have hn2 : ‖ξ‖ + ‖η‖ ≤ N := by rw [hN]; nlinarith [norm_nonneg ξ, norm_nonneg η]
  have hn3 : ‖ξ + η‖ + ‖-ξ‖ ≤ N := by
    rw [norm_neg, hN]; nlinarith [norm_add_le ξ η, norm_nonneg ξ, norm_nonneg η]
  have hn4 : ‖η‖ + ‖-η‖ ≤ N := by rw [norm_neg, hN]; nlinarith [norm_nonneg ξ, norm_nonneg η]
  rw [e1] at h₁
  rw [e3, ← smul_neg] at h₃
  rw [← smul_neg] at h₄
  obtain ⟨k₁, n₁⟩ := leg_transport hA hε (bound 0 ξ hn1 (by linarith [norm_nonneg η])) hεB h₁
  obtain ⟨k₂, n₂⟩ := leg_transport hA hε (bound ξ η hn2 (by linarith [norm_nonneg ξ])) hεB h₂
  obtain ⟨k₃, n₃⟩ := leg_transport hA hε (bound (ξ + η) (-ξ) hn3 (by rw [norm_neg]; linarith [norm_nonneg η]))
    hεB h₃
  obtain ⟨k₄, n₄⟩ := leg_transport hA hε (bound η (-η) hn4 (by rw [norm_neg]; linarith [norm_nonneg ξ])) hεB h₄
  -- the leg factors `1 + pᵢ` have norm `≤ 3`
  have hsmall : 2 * (ε * B) ^ 3 ≤ 1 := by
    have : (ε * B) ^ 3 ≤ (1 / 2) ^ 3 := pow_le_pow_left₀ (by positivity) hεB 3
    nlinarith
  have nP : ∀ {u v : 𝔄}, ‖u‖ ≤ 2 → ‖u - v‖ ≤ 2 * (ε * B) ^ 3 → ‖v‖ ≤ 3 := fun hu huv => by
    calc ‖_‖ = ‖_ - (_ - _)‖ := by rw [sub_sub_cancel]
      _ ≤ _ := norm_sub_le _ _
      _ ≤ 2 + 1 := add_le_add hu (huv.trans hsmall)
      _ = 3 := by norm_num
  have htel := norm_prod4_sub_le (M := 3) (e := 2 * (ε * B) ^ 3) (by norm_num) (n₁.trans (by norm_num))
    (n₂.trans (by norm_num)) (n₃.trans (by norm_num)) (nP n₂ k₂) (nP n₃ k₃) (nP n₄ k₄) k₁ k₂ k₃ k₄
  have hprod := hP ε hε hεe₀
  calc ‖U₄ 1 * U₃ 1 * U₂ 1 * U₁ 1 - (1 + ε ^ 2 • curvature A x η ξ)‖
      ≤ ‖U₄ 1 * U₃ 1 * U₂ 1 * U₁ 1 - (1 + legP A x η (-η) ε) * (1 + legP A x (ξ + η) (-ξ) ε) *
          (1 + legP A x ξ η ε) * (1 + legP A x 0 ξ ε)‖ +
        ‖(1 + legP A x η (-η) ε) * (1 + legP A x (ξ + η) (-ξ) ε) * (1 + legP A x ξ η ε) *
          (1 + legP A x 0 ξ ε) - (1 + ε ^ 2 • curvature A x η ξ)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 4 * 3 ^ 3 * (2 * (ε * B) ^ 3) + C₀ * ε ^ 3 := add_le_add htel hprod
    _ = (216 * B ^ 3 + C₀) * ε ^ 3 := by ring

end Lightlike.Gauge

