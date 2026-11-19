import Lightlike.Asymptotics.Tauberian.PolyIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Karamata's functional convergence

Let `ρ` have a regularly varying Laplace transform, `L(β) ~ β^{-α} ℓ(1/β)`. For a continuous `k` set
`Λ_t k = (t^α ℓ t)⁻¹ ∫ exp (-x/t) k (exp (-x/t)) dρ` and
`Φ k = ∫_{(0,∞)} exp (-x) k (exp (-x)) x^{α-1} / Γ(α) dx`. Then `Λ_t k → Φ k` as `t → ∞`
(`tendsto_lam`): for polynomials this is `tendsto_poly_integral` and the Gamma integral; for continuous
`k` it follows from the Weierstrass approximation theorem, since both functionals are bounded by `ε`
times their value at `1` (which tends to `1`).
-/

open MeasureTheory Set Real Filter Topology Polynomial

noncomputable section

namespace Lightlike.Tauberian

variable {ρ : Measure ℝ}

/-- The limit functional `Φ k = ∫_{(0,∞)} exp (-x) k (exp (-x)) x^{α-1} / Γ(α) dx`. -/
def Phi (α : ℝ) (k : ℝ → ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), Real.exp (-x) * k (Real.exp (-x)) * (x ^ (α - 1) / Real.Gamma α)

/-- The rescaled functional `Λ_t k`. -/
def Lam (ρ : Measure ℝ) (α : ℝ) (ℓ : ℝ → ℝ) (k : ℝ → ℝ) (t : ℝ) : ℝ :=
  (∫ x, Real.exp (-(1 / t) * x) * k (Real.exp (-(1 / t) * x)) ∂ρ) / (t ^ α * ℓ t)

/-- The Gamma integral with rate `r ≥ 1`, normalised. -/
lemma integral_gamma_rate {α : ℝ} (hα : 0 < α) {r : ℝ} (hr : 0 < r) :
    ∫ x in Ioi (0 : ℝ), Real.exp (-(r * x)) * (x ^ (α - 1) / Real.Gamma α) = r ^ (-α) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi hα hr
  have hΓ : Real.Gamma α ≠ 0 := (Real.Gamma_pos_of_pos hα).ne'
  have : ∀ x : ℝ, Real.exp (-(r * x)) * (x ^ (α - 1) / Real.Gamma α) =
      (x ^ (α - 1) * Real.exp (-(r * x))) / Real.Gamma α := fun x => by ring
  simp_rw [this]
  rw [integral_div, h, mul_div_assoc, div_self hΓ, mul_one, Real.rpow_neg hr.le, one_div,
    Real.inv_rpow hr.le]

/-- Integrability of the weight with rate `r ≥ 1`. -/
lemma integrableOn_gamma_rate {α : ℝ} (hα : 0 < α) {r : ℝ} (hr : 1 ≤ r) :
    IntegrableOn (fun x : ℝ => Real.exp (-(r * x)) * (x ^ (α - 1) / Real.Gamma α)) (Ioi 0) := by
  have h1 := (Real.GammaIntegral_convergent hα).div_const (Real.Gamma α)
  have hΓ : 0 < Real.Gamma α := Real.Gamma_pos_of_pos hα
  refine h1.mono' ?_ ?_
  · have : ContinuousOn (fun x : ℝ => Real.exp (-(r * x)) * (x ^ (α - 1) / Real.Gamma α)) (Ioi 0) := by
      refine ContinuousOn.mul (by fun_prop) ((continuousOn_id.rpow_const ?_).div_const _)
      intro x hx
      exact Or.inl (ne_of_gt hx)
    exact this.aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
    have hx0 : 0 < x := hx
    have : 0 ≤ Real.exp (-(r * x)) * (x ^ (α - 1) / Real.Gamma α) := by positivity
    rw [Real.norm_of_nonneg this]
    have hxα : 0 ≤ x ^ (α - 1) := Real.rpow_nonneg hx0.le _
    have : Real.exp (-(r * x)) ≤ Real.exp (-x) := Real.exp_le_exp.2 (by nlinarith)
    calc Real.exp (-(r * x)) * (x ^ (α - 1) / Real.Gamma α)
        = (Real.exp (-(r * x)) * x ^ (α - 1)) / Real.Gamma α := by ring
      _ ≤ (Real.exp (-x) * x ^ (α - 1)) / Real.Gamma α :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right this hxα) hΓ.le

/-- `Φ` of a polynomial. -/
lemma phi_poly {α : ℝ} (hα : 0 < α) (P : ℝ[X]) :
    Phi α (fun y => P.eval y) =
      ∑ n ∈ Finset.range (P.natDegree + 1), P.coeff n * (((n : ℝ) + 1) ^ (-α)) := by
  unfold Phi
  have h1 : ∀ x : ℝ, Real.exp (-x) * P.eval (Real.exp (-x)) * (x ^ (α - 1) / Real.Gamma α) =
      ∑ n ∈ Finset.range (P.natDegree + 1), P.coeff n *
        (Real.exp (-(((n : ℝ) + 1) * x)) * (x ^ (α - 1) / Real.Gamma α)) := by
    intro x
    rw [Polynomial.eval_eq_sum_range, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [show -(((n : ℝ) + 1) * x) = -x + (n : ℝ) * (-x) by ring, Real.exp_add, ← Real.exp_nat_mul]
    ring
  simp_rw [h1]
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_const_mul, integral_gamma_rate hα (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  · intro n _
    exact (integrableOn_gamma_rate hα (by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith)).const_mul _

/-- `Φ 1 = 1`. -/
lemma phi_one {α : ℝ} (hα : 0 < α) : Phi α (fun _ => 1) = 1 := by
  have := phi_poly hα (Polynomial.C 1)
  simpa using this

/-- Boundedness of a continuous function on `[0, 1]`. -/
lemma exists_bound_Icc {k : ℝ → ℝ} (hk : Continuous k) : ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ Icc (0 : ℝ) 1, ‖k y‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := k) hk.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun y hy => (hC y hy).trans (le_max_left _ _)⟩

/-- Integrability of the limit integrand. -/
lemma integrableOn_phi {α : ℝ} (hα : 0 < α) {k : ℝ → ℝ} (hk : Continuous k) :
    IntegrableOn (fun x : ℝ => Real.exp (-x) * k (Real.exp (-x)) * (x ^ (α - 1) / Real.Gamma α))
      (Ioi 0) := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_Icc hk
  have hg := (integrableOn_gamma_rate hα (le_refl (1 : ℝ))).const_mul C
  refine hg.mono' ?_ ?_
  · have : ContinuousOn (fun x : ℝ => Real.exp (-x) * k (Real.exp (-x)) * (x ^ (α - 1) / Real.Gamma α))
        (Ioi 0) := by
      refine ContinuousOn.mul (ContinuousOn.mul (by fun_prop) (hk.comp_continuousOn (by fun_prop)))
        ((continuousOn_id.rpow_const ?_).div_const _)
      intro x hx
      exact Or.inl (ne_of_gt hx)
    exact this.aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
    have hx0 : 0 < x := hx
    have hy : Real.exp (-x) ∈ Icc (0 : ℝ) 1 :=
      ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2 (by linarith)⟩
    have hw : 0 ≤ x ^ (α - 1) / Real.Gamma α :=
      div_nonneg (Real.rpow_nonneg hx0.le _) (Real.Gamma_pos_of_pos hα).le
    rw [norm_mul, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg hw]
    calc Real.exp (-x) * ‖k (Real.exp (-x))‖ * (x ^ (α - 1) / Real.Gamma α)
        ≤ Real.exp (-x) * C * (x ^ (α - 1) / Real.Gamma α) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hC _ hy) (Real.exp_pos _).le) hw
      _ = C * (Real.exp (-(1 * x)) * (x ^ (α - 1) / Real.Gamma α)) := by rw [one_mul]; ring

/-- `|Φ k - Φ P| ≤ ε` if `|k - P| ≤ ε` on `[0, 1]`. -/
lemma phi_sub_le {α : ℝ} (hα : 0 < α) {k : ℝ → ℝ} (hk : Continuous k) (P : ℝ[X]) {ε : ℝ}
    (hε : 0 ≤ ε) (h : ∀ y ∈ Icc (0 : ℝ) 1, |k y - P.eval y| ≤ ε) :
    |Phi α k - Phi α (fun y => P.eval y)| ≤ ε := by
  have hP : Continuous fun y => P.eval y := P.continuous
  have h1 := integrableOn_phi hα hk
  have h2 := integrableOn_phi hα hP
  unfold Phi
  rw [← integral_sub h1 h2]
  have hg := (integrableOn_gamma_rate hα (le_refl (1 : ℝ))).const_mul ε
  have hbound : ‖∫ x in Ioi (0 : ℝ), (Real.exp (-x) * k (Real.exp (-x)) * (x ^ (α - 1) / Real.Gamma α) -
      Real.exp (-x) * P.eval (Real.exp (-x)) * (x ^ (α - 1) / Real.Gamma α))‖ ≤
      ∫ x in Ioi (0 : ℝ), ε * (Real.exp (-(1 * x)) * (x ^ (α - 1) / Real.Gamma α)) := by
    refine norm_integral_le_of_norm_le hg ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
    have hx0 : 0 < x := hx
    have hy : Real.exp (-x) ∈ Icc (0 : ℝ) 1 :=
      ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2 (by linarith)⟩
    have hw : 0 ≤ x ^ (α - 1) / Real.Gamma α :=
      div_nonneg (Real.rpow_nonneg hx0.le _) (Real.Gamma_pos_of_pos hα).le
    have e : Real.exp (-x) * k (Real.exp (-x)) * (x ^ (α - 1) / Real.Gamma α) -
        Real.exp (-x) * P.eval (Real.exp (-x)) * (x ^ (α - 1) / Real.Gamma α) =
        (Real.exp (-x) * (k (Real.exp (-x)) - P.eval (Real.exp (-x)))) * (x ^ (α - 1) / Real.Gamma α) := by
      ring
    rw [e, norm_mul, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg hw,
      Real.norm_eq_abs]
    calc Real.exp (-x) * |k (Real.exp (-x)) - P.eval (Real.exp (-x))| * (x ^ (α - 1) / Real.Gamma α)
        ≤ Real.exp (-x) * ε * (x ^ (α - 1) / Real.Gamma α) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (h _ hy) (Real.exp_pos _).le) hw
      _ = ε * (Real.exp (-(1 * x)) * (x ^ (α - 1) / Real.Gamma α)) := by rw [one_mul]; ring
  rw [integral_const_mul, integral_gamma_rate hα one_pos, Real.one_rpow, mul_one] at hbound
  rw [← Real.norm_eq_abs]
  exact hbound

/-- Integrability of the rescaled integrand. -/
lemma integrable_lam (hρ : ρ (Iio 0) = 0)
    (hint : ∀ β : ℝ, 0 < β → Integrable (fun x : ℝ => Real.exp (-β * x)) ρ) {k : ℝ → ℝ}
    (hk : Continuous k) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ => Real.exp (-(1 / t) * x) * k (Real.exp (-(1 / t) * x))) ρ := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_Icc hk
  have hg := (hint (1 / t) (by positivity)).const_mul C
  refine hg.mono' ?_ ?_
  · exact (by fun_prop : Continuous fun x : ℝ => Real.exp (-(1 / t) * x) *
      k (Real.exp (-(1 / t) * x))).aestronglyMeasurable
  · have h0 : ∀ᵐ x ∂ρ, x ∉ Iio 0 := measure_eq_zero_iff_ae_notMem.1 hρ
    filter_upwards [h0] with x hx
    have hx0 : 0 ≤ x := not_lt.1 hx
    have hy : Real.exp (-(1 / t) * x) ∈ Icc (0 : ℝ) 1 :=
      ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2 (by
        have : 0 ≤ (1 / t) * x := by positivity
        linarith)⟩
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
    calc Real.exp (-(1 / t) * x) * ‖k (Real.exp (-(1 / t) * x))‖
        ≤ Real.exp (-(1 / t) * x) * C := mul_le_mul_of_nonneg_left (hC _ hy) (Real.exp_pos _).le
      _ = C * Real.exp (-(1 / t) * x) := mul_comm _ _

/-- `|Λ_t k - Λ_t P| ≤ ε Λ_t 1`. -/
lemma lam_sub_le (hρ : ρ (Iio 0) = 0)
    (hint : ∀ β : ℝ, 0 < β → Integrable (fun x : ℝ => Real.exp (-β * x)) ρ) {α : ℝ} {ℓ : ℝ → ℝ}
    {k : ℝ → ℝ} (hk : Continuous k) (P : ℝ[X]) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ y ∈ Icc (0 : ℝ) 1, |k y - P.eval y| ≤ ε) {t : ℝ} (ht : 0 < t)
    (hm : 0 < t ^ α * ℓ t) :
    |Lam ρ α ℓ k t - Lam ρ α ℓ (fun y => P.eval y) t| ≤ ε * (laplace ρ (1 / t) / (t ^ α * ℓ t)) := by
  unfold Lam
  rw [← sub_div, abs_div, abs_of_pos hm]
  rw [div_le_iff₀ hm, mul_comm, ← mul_assoc, mul_comm _ ε]
  have h1 := integrable_lam hρ hint hk ht
  have h2 := integrable_lam hρ hint P.continuous ht
  rw [← integral_sub h1 h2]
  have hg := (hint (1 / t) (by positivity)).const_mul ε
  have h0 : ∀ᵐ x ∂ρ, x ∉ Iio 0 := measure_eq_zero_iff_ae_notMem.1 hρ
  have hb : ‖∫ x, (Real.exp (-(1 / t) * x) * k (Real.exp (-(1 / t) * x)) -
      Real.exp (-(1 / t) * x) * P.eval (Real.exp (-(1 / t) * x))) ∂ρ‖ ≤
      ∫ x, ε * Real.exp (-(1 / t) * x) ∂ρ := by
    refine norm_integral_le_of_norm_le hg ?_
    filter_upwards [h0] with x hx
    have hx0 : 0 ≤ x := not_lt.1 hx
    have hy : Real.exp (-(1 / t) * x) ∈ Icc (0 : ℝ) 1 :=
      ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2 (by
        have : 0 ≤ (1 / t) * x := by positivity
        linarith)⟩
    rw [← mul_sub, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
    calc Real.exp (-(1 / t) * x) * |k (Real.exp (-(1 / t) * x)) - P.eval (Real.exp (-(1 / t) * x))|
        ≤ Real.exp (-(1 / t) * x) * ε := mul_le_mul_of_nonneg_left (h _ hy) (Real.exp_pos _).le
      _ = ε * Real.exp (-(1 / t) * x) := mul_comm _ _
  rw [integral_const_mul] at hb
  rw [Real.norm_eq_abs] at hb
  have e : ε * (t ^ α * ℓ t) * (laplace ρ (1 / t) / (t ^ α * ℓ t)) = ε * laplace ρ (1 / t) := by
    generalize t ^ α * ℓ t = m at hm ⊢
    have := hm.ne'
    field_simp
  rw [e]
  exact hb

/-- **Karamata's functional convergence**: `Λ_t k → Φ k` for continuous `k`. -/
theorem tendsto_lam (hρ : ρ (Iio 0) = 0)
    (hint : ∀ β : ℝ, 0 < β → Integrable (fun x : ℝ => Real.exp (-β * x)) ρ) {α : ℝ} (hα : 0 < α)
    {ℓ : ℝ → ℝ} (hℓ : SlowlyVarying ℓ)
    (hL : Tendsto (fun β : ℝ => laplace ρ β / (β ^ (-α) * ℓ (1 / β))) (𝓝[>] 0) (𝓝 1))
    {k : ℝ → ℝ} (hk : Continuous k) :
    Tendsto (fun t => Lam ρ α ℓ k t) atTop (𝓝 (Phi α k)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set ε₀ : ℝ := ε / 5 with hε₀
  have hε₀0 : 0 < ε₀ := by positivity
  obtain ⟨P, hP⟩ := exists_polynomial_near_of_continuousOn 0 1 k hk.continuousOn ε₀ hε₀0
  have hPk : ∀ y ∈ Icc (0 : ℝ) 1, |k y - P.eval y| ≤ ε₀ := fun y hy => by
    rw [abs_sub_comm]; exact (hP y hy).le
  have hphi := phi_sub_le hα hk P hε₀0.le hPk
  -- the three limits
  have hlamP : Tendsto (fun t => Lam ρ α ℓ (fun y => P.eval y) t) atTop (𝓝 (Phi α (fun y => P.eval y))) := by
    rw [phi_poly hα P]
    exact tendsto_poly_integral hint hℓ hL P
  have hR : Tendsto (fun t : ℝ => laplace ρ (1 / t) / (t ^ α * ℓ t)) atTop (𝓝 1) := by
    have := tendsto_scaled_laplace hℓ hL (show (0 : ℝ) < 1 from one_pos)
    simpa using this.congr' (by filter_upwards [eventually_gt_atTop 0] with t ht; simp)
  have hm : ∀ᶠ t in atTop, 0 < t ^ α * ℓ t := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hℓ.1] with t ht hℓt
    exact mul_pos (Real.rpow_pos_of_pos ht _) hℓt
  have hR2 : ∀ᶠ t in atTop, laplace ρ (1 / t) / (t ^ α * ℓ t) < 2 := hR.eventually (gt_mem_nhds (by norm_num))
  have hP2 := (Metric.tendsto_nhds.1 hlamP) ε₀ hε₀0
  filter_upwards [hm, hR2, hP2, eventually_gt_atTop (0 : ℝ)] with t htm htR htP ht
  have h1 := lam_sub_le hρ hint hk P hε₀0.le hPk ht htm
  rw [Real.dist_eq]
  have hR0 : 0 ≤ laplace ρ (1 / t) / (t ^ α * ℓ t) := div_nonneg (laplace_nonneg _ _) htm.le
  have h3 : |Lam ρ α ℓ k t - Lam ρ α ℓ (fun y => P.eval y) t| ≤ 2 * ε₀ := by
    refine h1.trans ?_
    nlinarith
  rw [Real.dist_eq] at htP
  calc |Lam ρ α ℓ k t - Phi α k|
      = |(Lam ρ α ℓ k t - Lam ρ α ℓ (fun y => P.eval y) t) +
          (Lam ρ α ℓ (fun y => P.eval y) t - Phi α (fun y => P.eval y)) +
          (Phi α (fun y => P.eval y) - Phi α k)| := by ring_nf
    _ ≤ |Lam ρ α ℓ k t - Lam ρ α ℓ (fun y => P.eval y) t| +
          |Lam ρ α ℓ (fun y => P.eval y) t - Phi α (fun y => P.eval y)| +
          |Phi α (fun y => P.eval y) - Phi α k| := by
        refine (abs_add_three _ _ _)
    _ < 2 * ε₀ + ε₀ + ε₀ := by
        rw [abs_sub_comm (Phi α (fun y => P.eval y)) (Phi α k)]
        linarith
    _ = 4 * ε₀ := by ring
    _ < ε := by rw [hε₀]; linarith

end Lightlike.Tauberian
