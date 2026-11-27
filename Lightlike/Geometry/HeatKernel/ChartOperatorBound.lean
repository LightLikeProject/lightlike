import Mathlib
import Lightlike.Geometry.HeatKernel.ShiftedParametrix
import Lightlike.Geometry.HeatKernel.ParamIntegralDeriv

/-!
# The parametrix operators are bounded on `C^ℓ`, uniformly in `t`

For the chart parametrix `H` (`Lightlike.IsChartParametrix`) and a smooth `F` supported near the centre, the function
`T_t F(w) = ∫ H(t, p, w) F(p) dp` is smooth and `‖D^ℓ T_t F(w)‖ ≤ C M` for `t ∈ (0, 1]`, whenever the derivatives of
`F` of order `≤ ℓ` are bounded by `M` (`Lightlike.IsChartParametrix.exists_operator_bound`). This is the chart form of
Liu Bo, *Note on Global Analysis on Manifolds*, Thm 3.2.13(1) (printed pp. 124–125, (3.2.99)–(3.2.100), read), the
input of the `C^ℓ` estimates of Levi's construction (Thm 3.2.6 there).

The proof substitutes `p = w − √t v` (`T_t F(w) = ∫ G(√t, w, v) F(w − √t v) dv`), differentiates under the integral
(`Lightlike.iteratedFDeriv_integral_eq`) and uses the Gaussian bounds of `G`
(`Lightlike.IsChartParametrix.exists_shifted`).
-/

open Set Filter Metric Real Nat MeasureTheory
open scoped ContDiff Topology

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- `(1 + u)^ℓ e^{-c u} ≤ 2^ℓ (1 + ℓ! (2/c)^ℓ) e^{-c u/2}` for `u ≥ 0`. -/
theorem one_add_pow_mul_exp_neg_le {c u : ℝ} (hc : 0 < c) (hu : 0 ≤ u) (ℓ : ℕ) :
    (1 + u) ^ ℓ * Real.exp (-(c * u)) ≤ 2 ^ ℓ * (1 + ℓ ! * (2 / c) ^ ℓ) * Real.exp (-(c * u) / 2) := by
  have h1 : (1 + u) ^ ℓ ≤ 2 ^ ℓ * (1 + u ^ ℓ) := by
    rcases le_total u 1 with hu1 | hu1
    · calc (1 + u) ^ ℓ ≤ 2 ^ ℓ := pow_le_pow_left₀ (by linarith) (by linarith) ℓ
        _ ≤ 2 ^ ℓ * (1 + u ^ ℓ) := le_mul_of_one_le_right (by positivity) (by linarith [pow_nonneg hu ℓ])
    · calc (1 + u) ^ ℓ ≤ (2 * u) ^ ℓ := pow_le_pow_left₀ (by linarith) (by linarith) ℓ
        _ = 2 ^ ℓ * u ^ ℓ := mul_pow _ _ _
        _ ≤ 2 ^ ℓ * (1 + u ^ ℓ) := by gcongr; linarith
  have h2 : u ^ ℓ * Real.exp (-(c * u) / 2) ≤ ℓ ! * (2 / c) ^ ℓ := by
    have h3 := Real.pow_div_factorial_le_exp (c * u / 2) (by positivity) ℓ
    have hfac : (0 : ℝ) < ℓ ! := by exact_mod_cast Nat.factorial_pos ℓ
    rw [div_le_iff₀ hfac] at h3
    have h4 : Real.exp (c * u / 2) * Real.exp (-(c * u) / 2) = 1 := by rw [← Real.exp_add]; ring_nf; simp
    have h5 : u ^ ℓ = (2 / c) ^ ℓ * (c * u / 2) ^ ℓ := by rw [← mul_pow]; congr 1; field_simp
    rw [h5]
    have h6 : 0 ≤ (2 / c) ^ ℓ := by positivity
    calc (2 / c) ^ ℓ * (c * u / 2) ^ ℓ * Real.exp (-(c * u) / 2)
        ≤ (2 / c) ^ ℓ * (Real.exp (c * u / 2) * ℓ !) * Real.exp (-(c * u) / 2) := by gcongr
      _ = ℓ ! * (2 / c) ^ ℓ * (Real.exp (c * u / 2) * Real.exp (-(c * u) / 2)) := by ring
      _ = ℓ ! * (2 / c) ^ ℓ := by rw [h4, mul_one]
  have he : Real.exp (-(c * u)) = Real.exp (-(c * u) / 2) * Real.exp (-(c * u) / 2) := by
    rw [← Real.exp_add]; ring_nf
  have he1 : Real.exp (-(c * u) / 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  rw [he]
  calc (1 + u) ^ ℓ * (Real.exp (-(c * u) / 2) * Real.exp (-(c * u) / 2))
      ≤ 2 ^ ℓ * (1 + u ^ ℓ) * Real.exp (-(c * u) / 2) * Real.exp (-(c * u) / 2) := by
        rw [← mul_assoc]; gcongr
    _ = 2 ^ ℓ * (Real.exp (-(c * u) / 2) + u ^ ℓ * Real.exp (-(c * u) / 2)) * Real.exp (-(c * u) / 2) := by ring
    _ ≤ 2 ^ ℓ * (1 + ℓ ! * (2 / c) ^ ℓ) * Real.exp (-(c * u) / 2) := by gcongr

/-- **Polynomial moments of a Gaussian in `ℝⁿ` are integrable and bounded.** -/
theorem exists_integral_poly_gauss_le (ℓ : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ J : ℝ, Integrable (fun v : Fin n → ℝ => (1 + ‖v‖ ^ 2) ^ ℓ * Real.exp (-(c * ‖v‖ ^ 2))) ∧
      ∫ v : Fin n → ℝ, (1 + ‖v‖ ^ 2) ^ ℓ * Real.exp (-(c * ‖v‖ ^ 2)) ≤ J := by
  set b := c / 2 / ((n : ℝ) + 1) with hb
  have hb0 : 0 < b := by positivity
  set K := 2 ^ ℓ * (1 + ℓ ! * (2 / c) ^ ℓ) with hK
  have hdom : ∀ v : Fin n → ℝ, (1 + ‖v‖ ^ 2) ^ ℓ * Real.exp (-(c * ‖v‖ ^ 2)) ≤
      K * Real.exp (-b * ∑ i, (v i - (0 : Fin n → ℝ) i) ^ 2) := by
    intro v
    refine (one_add_pow_mul_exp_neg_le hc (sq_nonneg ‖v‖) ℓ).trans ?_
    gcongr
    have hs : ∑ i, (v i - (0 : Fin n → ℝ) i) ^ 2 ≤ ((n : ℝ) + 1) * ‖v‖ ^ 2 := by
      have := sum_sq_le_card_mul_norm_sq v
      simp only [Pi.zero_apply, sub_zero]
      nlinarith [sq_nonneg ‖v‖]
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [hb]
    have : c / 2 / ((n : ℝ) + 1) * ∑ i, (v i - (0 : Fin n → ℝ) i) ^ 2 ≤ c * ‖v‖ ^ 2 / 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hn]
      nlinarith
    linarith
  have hint := (integrable_exp_neg_mul_sum_sq_sub n hb0 (0 : Fin n → ℝ)).const_mul K
  have hmeas : AEStronglyMeasurable (fun v : Fin n → ℝ => (1 + ‖v‖ ^ 2) ^ ℓ * Real.exp (-(c * ‖v‖ ^ 2))) :=
    (Continuous.aestronglyMeasurable (by fun_prop))
  have hI : Integrable (fun v : Fin n → ℝ => (1 + ‖v‖ ^ 2) ^ ℓ * Real.exp (-(c * ‖v‖ ^ 2))) :=
    hint.mono' hmeas (Eventually.of_forall fun v => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hdom v)
  refine ⟨K * (π / b) ^ ((n : ℝ) / 2), hI, ?_⟩
  calc _ ≤ ∫ v : Fin n → ℝ, K * Real.exp (-b * ∑ i, (v i - (0 : Fin n → ℝ) i) ^ 2) :=
        integral_mono hI hint hdom
    _ = K * (π / b) ^ ((n : ℝ) / 2) := by rw [integral_const_mul, integral_exp_neg_mul_sum_sq_sub n hb0]

variable {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- **The parametrix operators are bounded on `C^ℓ` uniformly in `t ∈ (0, 1]`**: for smooth `F` vanishing outside the
ball of radius `ρ` around the centre, with derivatives of order `≤ ℓ` bounded by `M`, `w ↦ ∫ H(t, p, w) F(p) dp` is
smooth and its `ℓ`-th derivative is bounded by `C M`. -/
theorem IsChartParametrix.exists_operator_bound {x : Fin n → ℝ} {N : ℕ} {r : ℝ}
    {u : ℕ → (Fin n → ℝ) × (Fin n → ℝ) → ℝ} {H : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {Ω : Set ((Fin n → ℝ) × (Fin n → ℝ))} {θ : (Fin n → ℝ) → ℝ} {σ : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    {V : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ)} (h : IsChartParametrix g U x N r u H Ω θ σ V)
    (hg : IsCoordMetric g U) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < r ∧ ∀ ℓ : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioc (0 : ℝ) 1, ∀ F : (Fin n → ℝ) → ℝ,
      ContDiff ℝ ∞ F → (∀ p, ρ ≤ ‖p - x‖ → F p = 0) → ∀ M : ℝ,
        (∀ i ≤ ℓ, ∀ p, ‖iteratedFDeriv ℝ i F p‖ ≤ M) →
        ContDiff ℝ ∞ (fun w => ∫ p, H t p w * F p) ∧
          ∀ w, ‖iteratedFDeriv ℝ ℓ (fun w => ∫ p, H t p w * F p) w‖ ≤ C * M := by
  obtain ⟨ρ, hρ0, hρr, Gx, hGs, hGsupp, hGag, c, hc, hGb⟩ := h.exists_shifted hg
  refine ⟨ρ, hρ0, hρr, fun ℓ => ?_⟩
  have hGb' := fun m => hGb m
  choose CG hCG0 hCG using hGb'
  set CG' := ∑ m ∈ Finset.range (ℓ + 1), CG m with hCG'
  have hCG'0 : 0 ≤ CG' := Finset.sum_nonneg fun m _ => hCG0 m
  obtain ⟨J, hJi, hJ⟩ := exists_integral_poly_gauss_le (n := n) ℓ hc
  have hJ0 : 0 ≤ J := le_trans (integral_nonneg fun v => by positivity) hJ
  refine ⟨2 ^ ℓ * CG' * J, by positivity, fun t ht F hF hF0 M hM => ?_⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (Nat.zero_le _) 0)
  have hr := h.r_pos
  set s := √t with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 ht.1
  have hs1 : s ≤ 1 := Real.sqrt_le_one.2 ht.2
  have hst : s ^ 2 = t := Real.sq_sqrt ht.1.le
  -- the integrand after the substitution
  set Φ : (Fin n → ℝ) → (Fin n → ℝ) → ℝ := fun v w => Gx s w v * F (w - s • v) with hΦ
  have hΦs : ContDiff ℝ ∞ (Function.uncurry Φ) := by
    have h1 : ContDiff ℝ ∞ (fun z : (Fin n → ℝ) × (Fin n → ℝ) => Gx s z.2 z.1) :=
      (hGs s hs0.ne').comp (contDiff_snd.prodMk contDiff_fst)
    have h2 : ContDiff ℝ ∞ (fun z : (Fin n → ℝ) × (Fin n → ℝ) => F (z.2 - s • z.1)) :=
      hF.comp (contDiff_snd.sub (contDiff_fst.const_smul s))
    exact h1.mul h2
  have hΦ0 : ∀ v, r / s < ‖v‖ → ∀ w, Φ v w = 0 := by
    intro v hv w
    have hsv : s • v ∉ tsupport θ := fun hmem => by
      have := h.θ_tsupport hmem
      rw [mem_ball, _root_.dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hs0] at this
      rw [div_lt_iff₀ hs0] at hv
      linarith
    simp only [hΦ, hGsupp s v w hsv, zero_mul]
  -- the representation
  have hrep : (fun w => ∫ p, H t p w * F p) = fun w => ∫ v, Φ v w := by
    funext w
    have hcv : ∫ v : Fin n → ℝ, (fun p => H t p w * F p) (w - s • v) =
        (s ^ n)⁻¹ * ∫ p, H t p w * F p := by
      have h1 := Measure.integral_comp_smul (μ := (volume : Measure (Fin n → ℝ)))
        (fun u => (fun p => H t p w * F p) (w - u)) s
      rw [Module.finrank_fin_fun, abs_of_pos (by positivity), smul_eq_mul] at h1
      rw [h1, integral_sub_left_eq_self (fun p => H t p w * F p) volume w]
    have hpt : ∀ v, s ^ n * ((fun p => H t p w * F p) (w - s • v)) = Φ v w := by
      intro v
      simp only [hΦ]
      by_cases hFv : F (w - s • v) = 0
      · simp [hFv]
      · have hvw : ‖w - s • v - x‖ ≤ ρ := by
          by_contra hc'; exact hFv (hF0 _ (le_of_lt (not_le.1 hc')))
        rw [← hGag s ⟨hs0, hs1⟩ v w hvw, hst]; ring
    rw [show (fun v => Φ v w) = fun v => s ^ n * ((fun p => H t p w * F p) (w - s • v)) from
      funext fun v => (hpt v).symm, integral_const_mul, hcv]
    field_simp
  rw [hrep]
  refine ⟨Lightlike.Lorentz.contDiff_parametric_integral_infty (μ := (volume : Measure (Fin n → ℝ)))
    hΦs aestronglyMeasurable_id measurableSet_closedBall measure_closedBall_lt_top.ne
    (Eventually.of_forall fun v hv => by rwa [mem_closedBall, _root_.dist_zero_right] at hv)
    (Eventually.of_forall fun v hv w => hΦ0 v (by
      rw [mem_closedBall, _root_.dist_zero_right, not_le] at hv; exact hv) w), fun w => ?_⟩
  rw [iteratedFDeriv_integral_eq ℓ hΦs (R := r / s) hΦ0]
  -- the pointwise bound of the integrand
  have hpt : ∀ v, ‖iteratedFDeriv ℝ ℓ (Φ v) w‖ ≤
      2 ^ ℓ * CG' * M * ((1 + ‖v‖ ^ 2) ^ ℓ * Real.exp (-(c * ‖v‖ ^ 2))) := by
    intro v
    have hGv : ContDiff ℝ ∞ (fun w' => Gx s w' v) := (hGs s hs0.ne').comp (contDiff_id.prodMk contDiff_const)
    have hFv : ContDiff ℝ ∞ (fun w' => F (w' - s • v)) := hF.comp (contDiff_id.sub contDiff_const)
    by_cases hvw : ‖w - s • v - x‖ ≤ ρ
    · have hA : ∀ m ≤ ℓ, ‖iteratedFDeriv ℝ m (fun w' => Gx s w' v) w‖ ≤
          CG' * ((1 + ‖v‖ ^ 2) ^ ℓ * Real.exp (-(c * ‖v‖ ^ 2))) := by
        intro m hm
        refine (hCG m s ⟨hs0, hs1⟩ v w hvw).trans ?_
        have h1 : CG m ≤ CG' := Finset.single_le_sum (f := CG) (fun m _ => hCG0 m)
          (Finset.mem_range.2 (Nat.lt_succ_of_le hm))
        have h2 : (1 + ‖v‖ ^ 2) ^ m ≤ (1 + ‖v‖ ^ 2) ^ ℓ :=
          pow_le_pow_right₀ (by nlinarith [sq_nonneg ‖v‖]) hm
        have h3 := Real.exp_pos (-(c * ‖v‖ ^ 2))
        calc CG m * (1 + ‖v‖ ^ 2) ^ m * Real.exp (-(c * ‖v‖ ^ 2))
            ≤ CG' * (1 + ‖v‖ ^ 2) ^ ℓ * Real.exp (-(c * ‖v‖ ^ 2)) := by gcongr
          _ = _ := by ring
      have hB : ∀ m ≤ ℓ, ‖iteratedFDeriv ℝ m (fun w' => F (w' - s • v)) w‖ ≤ M := fun m hm => by
        rw [iteratedFDeriv_comp_sub]; exact hM m hm _
      have := norm_iteratedFDeriv_mul_le_of_bounds hGv hFv w ℓ hA hB ℓ le_rfl
      calc _ ≤ _ := this
        _ = _ := by ring
    · push Not at hvw
      have hO : IsOpen {w' : Fin n → ℝ | ρ < ‖w' - s • v - x‖} :=
        isOpen_lt continuous_const ((continuous_id.sub continuous_const).sub continuous_const).norm
      have hev : Φ v =ᶠ[𝓝 w] fun _ => 0 :=
        Filter.eventually_of_mem (hO.mem_nhds hvw) fun w' hw' => by
          simp only [hΦ, hF0 _ (le_of_lt hw'), mul_zero]
      rw [(hev.iteratedFDeriv (𝕜 := ℝ) ℓ).eq_of_nhds, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
      positivity
  calc ‖∫ v, iteratedFDeriv ℝ ℓ (Φ v) w‖ ≤ ∫ v, ‖iteratedFDeriv ℝ ℓ (Φ v) w‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ v, 2 ^ ℓ * CG' * M * ((1 + ‖v‖ ^ 2) ^ ℓ * Real.exp (-(c * ‖v‖ ^ 2))) :=
        integral_mono_of_nonneg (Eventually.of_forall fun v => norm_nonneg _) (hJi.const_mul _)
          (Eventually.of_forall hpt)
    _ = 2 ^ ℓ * CG' * M * ∫ v : Fin n → ℝ, (1 + ‖v‖ ^ 2) ^ ℓ * Real.exp (-(c * ‖v‖ ^ 2)) := integral_const_mul _ _
    _ ≤ 2 ^ ℓ * CG' * M * J := by gcongr
    _ = 2 ^ ℓ * CG' * J * M := by ring

end Lightlike
