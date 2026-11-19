import Lightlike.Asymptotics.Tauberian.KernelFacts
import Lightlike.Asymptotics.Tauberian.Smoothing

/-!
# The smoothed step `ψ`

`ψ(y) = (1/N) ∫_{u < y} e^{β u} κ(u) du` is the weight with which `σ` is smoothed:
`∫ ψ(Δ - x) dσ(x)` replaces `σ (-∞, Δ]`.

* `psi_neg_le`: for `y < 0`, `0 ≤ ψ(y) ≤ e^{β y} 16 / (3 N |y|³)`;
* `psi_sub_one_le`: for `y > 0`, `|ψ(y) - 1| ≤ (β² e^{β y} M₂ + 8 β / y² + 16 / (3 y³)) / N`,
  with `M₂ = ∫ u² κ`; the cancellation by the evenness of `κ` (`∫ u κ = 0`) is what makes the first order
  term `β` disappear.
-/

open MeasureTheory Set Real Filter Topology

noncomputable section

namespace Lightlike.Tauberian

/-- `ψ(y) = (1/N) ∫_{u<y} e^{β u} κ(u) du`. -/
def psiS (b β y : ℝ) : ℝ := (1 / kapN b) * ∫ u in Iio y, Real.exp (β * u) * kap b u

lemma integrableOn_exp_kap {b β : ℝ} (hb : 0 < b) (hβ : 0 ≤ β) (y : ℝ) :
    IntegrableOn (fun u : ℝ => Real.exp (β * u) * kap b u) (Iio y) := by
  refine ((integrable_kap hb).integrableOn.const_mul (Real.exp (β * y))).mono'
    ((by fun_prop : Continuous fun u : ℝ => Real.exp (β * u)).mul (continuous_kap b)).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Iio).2 (Filter.Eventually.of_forall fun u hu => ?_)
  have hu' : u < y := hu
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (kap_nonneg b u))]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by nlinarith)) (kap_nonneg b u)

lemma psiS_nonneg {b β : ℝ} (hb : 0 < b) (y : ℝ) : 0 ≤ psiS b β y := by
  unfold psiS
  exact mul_nonneg (by have := kapN_pos hb; positivity)
    (integral_nonneg fun u => mul_nonneg (Real.exp_pos _).le (kap_nonneg b u))

/-- `∫_{u < y} κ = ∫_{u > -y} κ`. -/
lemma integral_Iio_kap (b y : ℝ) : ∫ u in Iio y, kap b u = ∫ u in Ioi (-y), kap b u := by
  rw [← integral_Iic_eq_integral_Iio, ← integral_comp_neg_Iic y (kap b)]
  simp_rw [kap_even]

/-- **`ψ` on the negative axis.** -/
lemma psi_neg_le {b β : ℝ} (hb : 0 < b) (hβ : 0 ≤ β) {y : ℝ} (hy : y < 0) :
    psiS b β y ≤ Real.exp (β * y) * (16 / (3 * (-y) ^ 3)) / kapN b := by
  have hN := kapN_pos hb
  unfold psiS
  have h1 : ∫ u in Iio y, Real.exp (β * u) * kap b u ≤ ∫ u in Iio y, Real.exp (β * y) * kap b u :=
    setIntegral_mono_on (integrableOn_exp_kap hb hβ y) ((integrable_kap hb).integrableOn.const_mul _)
      measurableSet_Iio fun u hu => mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.2 (by have : u < y := hu; nlinarith)) (kap_nonneg b u)
  rw [integral_const_mul, integral_Iio_kap] at h1
  have h2 := tail_kap_le hb (neg_pos.2 hy)
  calc 1 / kapN b * ∫ u in Iio y, Real.exp (β * u) * kap b u
      ≤ 1 / kapN b * (Real.exp (β * y) * (16 / (3 * (-y) ^ 3))) := by
        refine mul_le_mul_of_nonneg_left (h1.trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = _ := by ring

/-- The second moment `M₂ = ∫ u² κ`. -/
def kapM2 (b : ℝ) : ℝ := ∫ u, u ^ 2 * kap b u

lemma integrable_mul_kap {b : ℝ} (hb : 0 < b) : Integrable (fun u : ℝ => u * kap b u) := by
  refine ((integrable_kap hb).add (integrable_sq_kap hb)).mono'
    (continuous_id.mul (continuous_kap b)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (kap_nonneg b u)]
  have hk := kap_nonneg b u
  have : |u| ≤ 1 + u ^ 2 := by nlinarith [sq_abs u, abs_nonneg u, sq_nonneg (|u| - 1)]
  simp only [Pi.add_apply]
  nlinarith [mul_le_mul_of_nonneg_right this hk]

lemma integral_mul_kap_eq_zero (b : ℝ) : ∫ u, u * kap b u = 0 := by
  have h : ∫ u, (-u) * kap b (-u) = ∫ u, u * kap b u := integral_neg_eq_self (fun u => u * kap b u) volume
  have h2 : ∫ u, (-u) * kap b (-u) = -∫ u, u * kap b u := by
    simp_rw [kap_even, neg_mul]
    exact integral_neg _
  linarith

/-- The first moment tail: `∫_{u ≥ y} u κ ≤ 8 / y²`. -/
lemma tail_mul_kap_le {b : ℝ} (hb : 0 < b) {y : ℝ} (hy : 0 < y) :
    ∫ u in Ici y, u * kap b u ≤ 8 / y ^ 2 := by
  rw [integral_Ici_eq_integral_Ioi]
  have hI : IntegrableOn (fun u : ℝ => 16 * u ^ (-3 : ℝ)) (Ioi y) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hy).const_mul 16
  calc ∫ u in Ioi y, u * kap b u ≤ ∫ u in Ioi y, 16 * u ^ (-3 : ℝ) := by
        refine setIntegral_mono_on (integrable_mul_kap hb).integrableOn hI measurableSet_Ioi fun u hu => ?_
        have hu0 : 0 < u := lt_trans hy hu
        have := kap_le_inv hb hu0.ne'
        rw [Real.rpow_neg hu0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        calc u * kap b u ≤ u * (16 / u ^ 4) := mul_le_mul_of_nonneg_left this hu0.le
          _ = 16 * (u ^ 3)⁻¹ := by field_simp
    _ = 8 / y ^ 2 := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hy]
        rw [show (-3 : ℝ) + 1 = -2 by norm_num, Real.rpow_neg hy.le,
          show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        field_simp
        norm_num

/-- **`ψ` on the positive axis.** `|ψ(y) - 1| ≤ (β² e^{βy} M₂ + 8β/y² + 16/(3y³)) / N`. -/
lemma psi_sub_one_le {b β : ℝ} (hb : 0 < b) (hβ : 0 ≤ β) {y : ℝ} (hy : 0 < y) :
    |psiS b β y - 1| ≤
      (β ^ 2 * Real.exp (β * y) * kapM2 b + β * (8 / y ^ 2) + 16 / (3 * y ^ 3)) / kapN b := by
  have hN := kapN_pos hb
  set E₂ : ℝ := ∫ u in Iio y, (Real.exp (β * u) - 1 - β * u) * kap b u with hE₂
  set U : ℝ := ∫ u in Iio y, u * kap b u with hU
  set T : ℝ := ∫ u in Ici y, kap b u with hT
  set A : ℝ := ∫ u in Iio y, kap b u with hA
  have hAT : A + T = kapN b := by
    unfold kapN
    rw [hA, hT, ← Set.compl_Iio, integral_add_compl measurableSet_Iio (integrable_kap hb)]
  have iExp := integrableOn_exp_kap hb hβ y
  have iκ : IntegrableOn (kap b) (Iio y) := (integrable_kap hb).integrableOn
  have iU : IntegrableOn (fun u : ℝ => u * kap b u) (Iio y) := (integrable_mul_kap hb).integrableOn
  have iE₂ : IntegrableOn (fun u : ℝ => (Real.exp (β * u) - 1 - β * u) * kap b u) (Iio y) :=
    ((iExp.sub iκ).sub (iU.const_mul β)).congr (Filter.Eventually.of_forall fun u => by
      simp only [Pi.sub_apply]; ring)
  have hsplit : ∫ u in Iio y, Real.exp (β * u) * kap b u = E₂ + A + β * U := by
    have : ∀ u : ℝ, Real.exp (β * u) * kap b u =
        ((Real.exp (β * u) - 1 - β * u) * kap b u + kap b u) + β * (u * kap b u) := fun u => by ring
    simp_rw [this]
    have h2 := integral_add (iE₂.add iκ) (iU.const_mul β)
    have h1 := integral_add iE₂ iκ
    simp only [Pi.add_apply] at h2 h1
    rw [h2, h1, integral_const_mul]
  -- `U = - ∫_{u ≥ y} u κ`
  have hU' : U = -∫ u in Ici y, u * kap b u := by
    have h0 := integral_mul_kap_eq_zero b
    have : ∫ u, u * kap b u = U + ∫ u in Ici y, u * kap b u := by
      rw [hU, ← Set.compl_Iio]
      exact (integral_add_compl measurableSet_Iio (integrable_mul_kap hb)).symm
    linarith
  have hUb : |U| ≤ 8 / y ^ 2 := by
    rw [hU', abs_neg]
    have h0 : 0 ≤ ∫ u in Ici y, u * kap b u := by
      refine setIntegral_nonneg measurableSet_Ici fun u hu => ?_
      exact mul_nonneg (le_trans hy.le hu) (kap_nonneg b u)
    rw [abs_of_nonneg h0]
    exact tail_mul_kap_le hb hy
  have hE₂b : |E₂| ≤ β ^ 2 * Real.exp (β * y) * kapM2 b := by
    have hb2 : ∀ u ∈ Iio y, |(Real.exp (β * u) - 1 - β * u) * kap b u| ≤
        β ^ 2 * Real.exp (β * y) * (u ^ 2 * kap b u) := by
      intro u hu
      have hu' : u < y := hu
      rw [abs_mul, abs_of_nonneg (kap_nonneg b u)]
      have h1 := abs_exp_sub_one_sub_le (β * u)
      have h2 : Real.exp (max (β * u) 0) ≤ Real.exp (β * y) :=
        Real.exp_le_exp.2 (max_le (by nlinarith) (by nlinarith))
      calc |Real.exp (β * u) - 1 - β * u| * kap b u ≤ (β * u) ^ 2 * Real.exp (max (β * u) 0) * kap b u :=
            mul_le_mul_of_nonneg_right h1 (kap_nonneg b u)
        _ ≤ (β * u) ^ 2 * Real.exp (β * y) * kap b u :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (sq_nonneg _)) (kap_nonneg b u)
        _ = β ^ 2 * Real.exp (β * y) * (u ^ 2 * kap b u) := by ring
    calc |E₂| ≤ ∫ u in Iio y, |(Real.exp (β * u) - 1 - β * u) * kap b u| := abs_integral_le_integral_abs
      _ ≤ ∫ u in Iio y, β ^ 2 * Real.exp (β * y) * (u ^ 2 * kap b u) :=
          setIntegral_mono_on iE₂.abs ((integrable_sq_kap hb).integrableOn.const_mul _)
            measurableSet_Iio hb2
      _ ≤ β ^ 2 * Real.exp (β * y) * kapM2 b := by
          rw [integral_const_mul]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact setIntegral_le_integral (integrable_sq_kap hb)
            (Filter.Eventually.of_forall fun u => mul_nonneg (sq_nonneg u) (kap_nonneg b u))
  have hT0 : 0 ≤ T := setIntegral_nonneg measurableSet_Ici fun u _ => kap_nonneg b u
  have hTb : T ≤ 16 / (3 * y ^ 3) := by
    rw [hT, integral_Ici_eq_integral_Ioi]; exact tail_kap_le hb hy
  have hψ : kapN b * (psiS b β y - 1) = E₂ + β * U - T := by
    unfold psiS
    rw [hsplit]
    have : kapN b * (1 / kapN b * (E₂ + A + β * U) - 1) = E₂ + A + β * U - kapN b := by
      field_simp
    rw [this]; linarith
  have habs : |kapN b * (psiS b β y - 1)| = kapN b * |psiS b β y - 1| := by
    rw [abs_mul, abs_of_pos hN]
  rw [le_div_iff₀ hN, mul_comm, ← habs, hψ]
  calc |E₂ + β * U - T| ≤ |E₂| + |β * U| + |T| := by
        refine (abs_sub _ _).trans ?_
        have := abs_add_le E₂ (β * U)
        linarith [abs_nonneg T]
    _ ≤ β ^ 2 * Real.exp (β * y) * kapM2 b + β * (8 / y ^ 2) + 16 / (3 * y ^ 3) := by
        rw [abs_mul, abs_of_nonneg hβ, abs_of_nonneg hT0]
        have := mul_le_mul_of_nonneg_left hUb hβ
        linarith

/-- `∫_{s > 0} h (y - s) ds = ∫_{u < y} h u du`. -/
lemma integral_Ioi_sub (h : ℝ → ℝ) (y : ℝ) :
    ∫ s in Ioi (0 : ℝ), h (y - s) = ∫ u in Iio y, h u := by
  have e1 : ∀ s : ℝ, h (y - s) = (fun t => h (y + t)) (-s) := fun s => by simp [sub_eq_add_neg]
  simp_rw [e1]
  rw [integral_comp_neg_Ioi 0 (fun t => h (y + t))]
  rw [neg_zero]
  have hmp := (measurePreserving_add_left (volume : Measure ℝ) y)
  have := hmp.setIntegral_preimage_emb (measurableEmbedding_addLeft y) h (Iic y)
  have hpre : (fun t : ℝ => y + t) ⁻¹' Iic y = Iic 0 := by
    ext t; simp
  rw [hpre] at this
  rw [this, integral_Iic_eq_integral_Iio]

/-- **The identity between the two smoothings**: `N ψ(y) = e^{β y} Ψ(-y)`. -/
lemma kapN_mul_psiS {b β : ℝ} (hb : 0 < b) (y : ℝ) :
    kapN b * psiS b β y = Real.exp (β * y) * smoothΨ b β (-y) := by
  have hN := (kapN_pos hb).ne'
  unfold psiS smoothΨ
  have : kapN b * (1 / kapN b * ∫ u in Iio y, Real.exp (β * u) * kap b u) =
      ∫ u in Iio y, Real.exp (β * u) * kap b u := by field_simp
  rw [this, ← integral_Ioi_sub (fun u => Real.exp (β * u) * kap b u) y, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only
  have e1 : kap b (y - s) = (2 * b * Real.sinc (b * (-y + s))) ^ 4 := by
    have : kap b (y - s) = kap b (-y + s) := by
      rw [← kap_even b (y - s)]; congr 1; ring
    rw [this]; rfl
  rw [e1, ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

end Lightlike.Tauberian
