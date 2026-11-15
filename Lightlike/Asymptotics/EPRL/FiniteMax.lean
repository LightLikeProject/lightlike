import Lightlike.Asymptotics.EPRL.Pieces
import Lightlike.Asymptotics.EPRL.LogPhase

/-!
# Asymptotics of an `SU(2)^4` integral with finitely many nondegenerate maxima

`asymptotics_finite_max`: for a continuous `F` on `SU(2)^4` with `|F| ≤ 1`, whose modulus is one
only on a finite set `K` where `F ∘ chart_p` is smooth with vanishing differential and
nondegenerate Hessian, `∫ F^λ = Σ_p F(p)^λ (2π/λ)^6 det(-H_p/F(p))^{-1/2} ρ_H(0) + O(λ^{-7})`,
where `ρ_H(0)` is the Haar density at the centre of the chart.
-/

open MeasureTheory Set Metric Filter Asymptotics
open scoped ContDiff

namespace Lightlike.Asymptotics.EPRL

open Lightlike Lightlike.Spin4 Lightlike.Oscillatory

lemma pow_isBigO_inv_pow {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) (k : ℕ) :
    (fun lam : ℕ => ρ ^ lam) =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ k)⁻¹ := by
  have ht := (tendsto_pow_const_mul_const_pow_of_abs_lt_one k (r := ρ)
    (by rw [abs_of_nonneg h0]; exact h1)).comp tendsto_natCast_atTop_atTop
  obtain ⟨C, hC⟩ := (ht.isBigO_one ℝ).bound
  refine IsBigO.of_bound C ?_
  filter_upwards [hC, eventually_gt_atTop 0] with n hn hpos
  have hnp : (0 : ℝ) < (n : ℝ) ^ k := by positivity
  simp only [Function.comp, norm_one, mul_one, norm_mul, norm_pow, Real.norm_natCast] at hn ⊢
  rw [norm_inv, norm_pow, Real.norm_natCast, ← div_eq_mul_inv, le_div_iff₀ hnp]
  simpa [mul_comm] using hn

lemma contDiff_haarDensity4 : ContDiff ℝ ∞ fun q : Fin 12 → ℝ => haarDensity4 (reshape.symm q) := by
  unfold haarDensity4 haarDensity gsq
  refine contDiff_prod fun a _ => ?_
  refine contDiff_const.div ?_ (fun q => ?_)
  · refine contDiff_const.mul (ContDiff.pow ?_ 2)
    have hc : ∀ k : Fin 3, ContDiff ℝ ∞ fun q : Fin 12 → ℝ => q (fpf (a, k)) := fun k =>
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 12 => ℝ) (fpf (a, k))).contDiff
    exact ((contDiff_const.add ((hc 0).pow 2)).add ((hc 1).pow 2)).add ((hc 2).pow 2)
  · have : 0 < 1 + (reshape.symm q a 0) ^ 2 + (reshape.symm q a 1) ^ 2 + (reshape.symm q a 2) ^ 2 := by
      positivity
    have hpi := Real.pi_pos
    positivity

lemma rpow_neg_six_sub_one (lam : ℕ) :
    (lam : ℝ) ^ (-(((12 : ℕ) : ℝ) / 2) - 1) = ((lam : ℝ) ^ 7)⁻¹ := by
  have : (-(((12 : ℕ) : ℝ) / 2) - 1) = -((7 : ℕ) : ℝ) := by norm_num
  rw [this, Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_natCast]

/-- **Asymptotics with finitely many nondegenerate maxima.** -/
theorem asymptotics_finite_max (F : (Fin 4 → SU2) → ℂ) (hF : Continuous F)
    (hle : ∀ Y, ‖F Y‖ ≤ 1) (K : Finset (Fin 4 → SU2)) (hK : ∀ Y, ‖F Y‖ = 1 → Y ∈ K)
    (hv : ∀ p ∈ K, ‖F p‖ = 1)
    (hG : ∀ p ∈ K, ContDiff ℝ ∞ fun q => F (chartMap p q))
    (hd : ∀ p ∈ K, fderiv ℝ (fun q => F (chartMap p q)) 0 = 0)
    (hnd : ∀ p ∈ K, (-((F p)⁻¹ • hessMat (fun q => F (chartMap p q)) 0)).det ≠ 0) :
    (fun lam : ℕ => (∫ Y, F Y ^ lam ∂(haarN 4)) - ∑ p ∈ K, F p ^ lam *
        ((((2 * Real.pi / lam) ^ (((12 : ℕ) : ℝ) / 2) : ℝ) *
          invSqrtDet (-((F p)⁻¹ • hessMat (fun q => F (chartMap p q)) 0)) *
          (haarDensity4 (reshape.symm 0) : ℂ))))
      =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ 7)⁻¹ := by
  classical
  obtain ⟨r1, hr1, H⟩ := localise_pieces F hF hle K hK
  have hG0 : ∀ p ∈ K, F (chartMap p 0) = F p := fun p _ => by rw [chartMap_zero]
  have hev : ∀ᶠ q in nhds (0 : Fin 12 → ℝ), ∀ p ∈ K,
      ‖F (chartMap p q) / F p - 1‖ < 1/4 := by
    rw [Filter.eventually_all_finset]
    intro p hp
    have hc : ContinuousAt (fun q => F (chartMap p q) / F p - 1) 0 :=
      (((hF.comp (continuous_chartMap p)).div_const _).sub continuous_const).continuousAt
    have hv0 : F p ≠ 0 := by intro h; have := hv p hp; simp [h] at this
    have h0 : F (chartMap p 0) / F p - 1 = 0 := by rw [hG0 p hp, div_self hv0]; simp
    have h2 : ‖(fun q => F (chartMap p q) / F p - 1) 0‖ < 1/4 := by
      simp only []; rw [h0]; norm_num
    exact hc.norm.eventually (gt_mem_nhds h2)
  obtain ⟨δ, hδ, hδq⟩ := Metric.eventually_nhds_iff.mp hev
  set R := min r1 δ / 2 with hR
  have hRpos : 0 < R := by positivity
  let χ : ContDiffBump (0 : Fin 12 → ℝ) := ⟨R / 2, R, by positivity, by linarith⟩
  have hχr : χ.rOut = R := rfl
  have hRr1 : χ.rOut < r1 := by rw [hχr]; have := min_le_left r1 δ; linarith
  have hRδ : R < δ := by have := min_le_right r1 δ; linarith
  obtain ⟨hmax, ρ, hρ0, hρ1, hρ⟩ := H χ hRr1
  -- the amplitude
  set a : (Fin 12 → ℝ) → ℂ := fun q => ((haarDensity4 (reshape.symm q) * χ q : ℝ) : ℂ) with ha
  have hχ0 : χ 0 = 1 := χ.one_of_mem_closedBall (by simp [χ]; positivity)
  have hd0 : 0 < haarDensity4 (reshape.symm (0 : Fin 12 → ℝ)) := haarDensity4_pos _
  have haC : ContDiff ℝ ∞ a :=
    Complex.ofRealCLM.contDiff.comp (contDiff_haarDensity4.mul χ.contDiff)
  have haS : tsupport a ⊆ closedBall (0 : Fin 12 → ℝ) χ.rOut := by
    rw [← χ.tsupport_eq]
    refine closure_mono (fun q hq => ?_)
    intro h; apply hq; simp [ha, h]
  have haK : HasCompactSupport a :=
    (χ.hasCompactSupport.mul_left (f := fun q => haarDensity4 (reshape.symm q))).comp_left
      (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero
  have ha0 : a 0 = (haarDensity4 (reshape.symm 0) : ℂ) := by simp [ha, hχ0]
  have h0S : (0 : Fin 12 → ℝ) ∈ tsupport a := subset_tsupport _ (by
    simp [ha, hχ0]; exact hd0.ne')
  -- local asymptotics at each point
  have hloc : ∀ p ∈ K, (fun lam : ℕ => (∫ q, a q * F (chartMap p q) ^ lam) -
      F p ^ lam * ((((2 * Real.pi / lam) ^ (((12 : ℕ) : ℝ) / 2) : ℝ) *
        invSqrtDet (-((F p)⁻¹ • hessMat (fun q => F (chartMap p q)) 0)) *
        (haarDensity4 (reshape.symm 0) : ℂ)))) =O[atTop]
      fun lam : ℕ => (lam : ℝ) ^ (-(((12 : ℕ) : ℝ) / 2) - 1) := by
    intro p hp
    have := local_asymptotics (n := 12) (hG p hp) (hv p hp) (hG0 p hp) (hd p hp)
      (fun x => hle _) haC haK
      (fun x hx => hδq (lt_of_le_of_lt (by simpa using haS hx) hRδ) p hp)
      (fun x hx h1 => hmax p hp x (haS hx) h1) h0S (hnd p hp)
    simpa [ha0] using this
  have hsum := IsBigO.sum hloc
  rw [show (fun lam : ℕ => (lam : ℝ) ^ (-(((12 : ℕ) : ℝ) / 2) - 1)) =
      fun lam : ℕ => ((lam : ℝ) ^ 7)⁻¹ from funext rpow_neg_six_sub_one] at hsum
  have htail : (fun lam : ℕ => ((∫ Y, F Y ^ lam ∂(haarN 4)) - ∑ p ∈ K, ∫ q : Fin 12 → ℝ,
      haarDensity4 (reshape.symm q) • ((χ q : ℂ) * F (chartMap p q) ^ lam))) =O[atTop]
      fun lam : ℕ => ((lam : ℝ) ^ 7)⁻¹ :=
    (IsBigO.of_bound 1 (Eventually.of_forall fun lam => by
      rw [Real.norm_of_nonneg (pow_nonneg hρ0 lam), one_mul]; exact hρ lam)).trans
      (pow_isBigO_inv_pow hρ0 hρ1 7)
  refine (htail.add hsum).congr_left (fun lam => ?_)
  have hI : ∑ p ∈ K, ∫ q : Fin 12 → ℝ,
      haarDensity4 (reshape.symm q) • ((χ q : ℂ) * F (chartMap p q) ^ lam) =
      ∑ p ∈ K, ∫ q, a q * F (chartMap p q) ^ lam :=
    Finset.sum_congr rfl fun p _ => integral_congr_ae (ae_of_all _ fun q => by
      simp [ha, Complex.real_smul]; ring)
  simp only [Finset.sum_apply]
  rw [Finset.sum_sub_distrib, hI]
  ring

end Lightlike.Asymptotics.EPRL
