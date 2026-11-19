import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# An effective Laplace method for `∫₀^π e^{-s (1 - cos θ)} dθ`

`laplace_cos_eff`: for `s > 0`, `|(1/π) ∫₀^π e^{-s(1-cos θ)} dθ - 1/√(2π s)| ≤ C s^{-3/2}`, with an explicit `C`.
The comparison function is the Gaussian `e^{-s θ²/2}`; the error is controlled by `1 - cos θ ≥ 2θ²/π²` and
`θ²/2 - (1 - cos θ) ≤ θ⁴/2` on `[0, π]`.
-/

open MeasureTheory Set Real

noncomputable section

namespace Lightlike.Tauberian

/-- `1 - cos θ ≥ 2 θ² / π²` on `[0, π]`. -/
lemma one_sub_cos_ge {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ π) : 2 * θ ^ 2 / π ^ 2 ≤ 1 - Real.cos θ := by
  have hs : 2 / π * (θ / 2) ≤ Real.sin (θ / 2) :=
    Real.mul_le_sin (by positivity) (by linarith)
  have hc : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have h2 := Real.sin_sq_add_cos_sq (θ / 2)
    have h3 : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
      rw [← Real.cos_two_mul]; congr 1; ring
    nlinarith
  rw [hc]
  have hpi : 0 < π := Real.pi_pos
  have : θ / π ≤ Real.sin (θ / 2) := by
    have e : 2 / π * (θ / 2) = θ / π := by field_simp
    linarith
  have h4 : (θ / π) ^ 2 ≤ Real.sin (θ / 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) this 2
  have : 2 * θ ^ 2 / π ^ 2 = 2 * (θ / π) ^ 2 := by field_simp
  linarith

/-- `θ²/2 - (1 - cos θ) ≤ θ⁴/2` on `[0, π]`. -/
lemma quartic_le {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ π) :
    θ ^ 2 / 2 - (1 - Real.cos θ) ≤ θ ^ 4 / 2 := by
  by_cases hθ : θ ≤ 1
  · have := Real.cos_bound (x := θ) (by rw [abs_of_nonneg h0]; exact hθ)
    rw [abs_of_nonneg h0] at this
    have := (abs_le.1 this).2
    nlinarith [pow_nonneg h0 4]
  · push Not at hθ
    have hc : 0 ≤ 1 - Real.cos θ := by linarith [Real.cos_le_one θ]
    have : θ ^ 2 ≤ θ ^ 4 := by
      have h2 : 1 ≤ θ ^ 2 := by nlinarith
      nlinarith [sq_nonneg θ]
    nlinarith

/-- The pointwise comparison of `e^{-s(1-cos θ)}` with the Gaussian. -/
lemma exp_cos_sub_gauss {s θ : ℝ} (hs : 0 < s) (h0 : 0 ≤ θ) (h1 : θ ≤ π) :
    0 ≤ Real.exp (-(s * (1 - Real.cos θ))) - Real.exp (-(s * θ ^ 2 / 2)) ∧
    Real.exp (-(s * (1 - Real.cos θ))) - Real.exp (-(s * θ ^ 2 / 2)) ≤
      s / 2 * θ ^ 4 * Real.exp (-(2 * s / π ^ 2 * θ ^ 2)) := by
  set r : ℝ := θ ^ 2 / 2 - (1 - Real.cos θ) with hr
  have hr0 : 0 ≤ r := by
    have := Real.one_sub_sq_div_two_le_cos (x := θ)
    rw [hr]; linarith
  have hr1 : r ≤ θ ^ 4 / 2 := quartic_le h0 h1
  have hg : Real.exp (-(s * θ ^ 2 / 2)) =
      Real.exp (-(s * (1 - Real.cos θ))) * Real.exp (-(s * r)) := by
    rw [← Real.exp_add]; congr 1; rw [hr]; ring
  have hf0 := Real.exp_pos (-(s * (1 - Real.cos θ)))
  have he : Real.exp (-(s * r)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  rw [hg]
  constructor
  · nlinarith [Real.exp_pos (-(s * r))]
  · have h2 : 1 - Real.exp (-(s * r)) ≤ s * r := by
      have := Real.add_one_le_exp (-(s * r)); linarith
    have h3 : Real.exp (-(s * (1 - Real.cos θ))) ≤ Real.exp (-(2 * s / π ^ 2 * θ ^ 2)) := by
      apply Real.exp_le_exp.2
      have := one_sub_cos_ge h0 h1
      have h4 : 2 * s / π ^ 2 * θ ^ 2 = s * (2 * θ ^ 2 / π ^ 2) := by ring
      rw [h4]; nlinarith
    calc Real.exp (-(s * (1 - Real.cos θ))) - Real.exp (-(s * (1 - Real.cos θ))) * Real.exp (-(s * r))
        = Real.exp (-(s * (1 - Real.cos θ))) * (1 - Real.exp (-(s * r))) := by ring
      _ ≤ Real.exp (-(2 * s / π ^ 2 * θ ^ 2)) * (s * (θ ^ 4 / 2)) := by
          refine mul_le_mul h3 ?_ (by linarith) (Real.exp_pos _).le
          nlinarith
      _ = s / 2 * θ ^ 4 * Real.exp (-(2 * s / π ^ 2 * θ ^ 2)) := by ring

/-- Integrability of `θ⁴ e^{-bθ²}` on the half-line. -/
lemma integrableOn_quartic {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun θ : ℝ => θ ^ 4 * Real.exp (-(b * θ ^ 2))) (Ioi (0 : ℝ)) := by
  have := integrableOn_rpow_mul_exp_neg_mul_sq hb (s := 4) (by norm_num)
  refine this.congr_fun (fun θ _ => ?_) measurableSet_Ioi
  simp only
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, neg_mul]

/-- `∫_{θ>0} θ⁴ e^{-κθ²} ≤ (8/κ²) ∫_{θ>0} e^{-κθ²/2} = (8/κ²) √(2π/κ) / 2`. -/
lemma quartic_gauss {κ : ℝ} (hκ : 0 < κ) :
    ∫ θ in Ioi (0 : ℝ), θ ^ 4 * Real.exp (-(κ * θ ^ 2)) ≤ 8 / κ ^ 2 * (√(π / (κ / 2)) / 2) := by
  have hpt : ∀ θ : ℝ, θ ^ 4 * Real.exp (-(κ * θ ^ 2)) ≤ 8 / κ ^ 2 * Real.exp (-(κ / 2 * θ ^ 2)) := by
    intro θ
    set y : ℝ := κ * θ ^ 2 / 2 with hy
    have hy0 : 0 ≤ y := by positivity
    have h1 := Real.quadratic_le_exp_of_nonneg hy0
    have h2 : y ^ 2 / 2 ≤ Real.exp y := by nlinarith
    have hθ : θ ^ 4 = 4 * y ^ 2 / κ ^ 2 := by rw [hy]; field_simp; ring
    have e1 : Real.exp (-(κ * θ ^ 2)) = Real.exp (-(κ / 2 * θ ^ 2)) * Real.exp (-y) := by
      rw [← Real.exp_add]; congr 1; rw [hy]; ring
    have hey : Real.exp (-y) * (y ^ 2 / 2) ≤ 1 := by
      have := mul_le_mul_of_nonneg_left h2 (Real.exp_pos (-y)).le
      rw [← Real.exp_add] at this; simp at this; linarith
    rw [e1, hθ]
    have hE := Real.exp_pos (-(κ / 2 * θ ^ 2))
    have : 4 * y ^ 2 / κ ^ 2 * (Real.exp (-(κ / 2 * θ ^ 2)) * Real.exp (-y)) =
        (8 / κ ^ 2) * Real.exp (-(κ / 2 * θ ^ 2)) * (Real.exp (-y) * (y ^ 2 / 2)) := by ring
    rw [this]
    have : 0 ≤ 8 / κ ^ 2 * Real.exp (-(κ / 2 * θ ^ 2)) := by positivity
    nlinarith
  have hg : Integrable (fun θ : ℝ => Real.exp (-(κ / 2 * θ ^ 2))) := by
    have := integrable_exp_neg_mul_sq (b := κ / 2) (by positivity)
    simpa using this
  calc ∫ θ in Ioi (0 : ℝ), θ ^ 4 * Real.exp (-(κ * θ ^ 2))
      ≤ ∫ θ in Ioi (0 : ℝ), 8 / κ ^ 2 * Real.exp (-(κ / 2 * θ ^ 2)) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun θ => by positivity)
          (hg.integrableOn.const_mul _) (Filter.Eventually.of_forall hpt)
    _ = 8 / κ ^ 2 * (√(π / (κ / 2)) / 2) := by
        rw [integral_const_mul]
        congr 1
        have := integral_gaussian_Ioi (κ / 2)
        simpa [neg_mul] using this

/-- **The effective Laplace method** with explicit error terms. -/
theorem laplace_cos_eff {s : ℝ} (hs : 0 < s) :
    |(1 / π) * (∫ θ in (0 : ℝ)..π, Real.exp (-(s * (1 - Real.cos θ)))) - 1 / √(2 * π * s)| ≤
      (1 / π) * (s / 2 * (8 / (2 * s / π ^ 2) ^ 2 * (√(π / (2 * s / π ^ 2 / 2)) / 2)) +
        1 / π ^ 4 * (8 / (s / 2) ^ 2 * (√(π / (s / 2 / 2)) / 2))) := by
  have hpi : 0 < π := Real.pi_pos
  set f : ℝ → ℝ := fun θ => Real.exp (-(s * (1 - Real.cos θ))) with hf
  set g : ℝ → ℝ := fun θ => Real.exp (-(s * θ ^ 2 / 2)) with hg
  have hgg : ∀ θ : ℝ, g θ = Real.exp (-(s / 2 * θ ^ 2)) := fun θ => by simp only [hg]; congr 1; ring
  have hfc : Continuous f := by simp only [hf]; fun_prop
  have hgc : Continuous g := by simp only [hg]; fun_prop
  have hgi : Integrable g := by
    have := integrable_exp_neg_mul_sq (b := s / 2) (by positivity)
    refine this.congr (Filter.Eventually.of_forall fun θ => ?_)
    simp only [hg]; congr 1; ring
  set κ : ℝ := 2 * s / π ^ 2 with hκ
  have hκ0 : 0 < κ := by positivity
  set A : ℝ := √(π / (s / 2)) / 2 with hA
  have hAint : ∫ θ in Ioi (0 : ℝ), g θ = A := by
    have := integral_gaussian_Ioi (s / 2)
    simp_rw [hgg]
    simpa [neg_mul] using this
  -- the two pieces
  set J : ℝ := ∫ θ in (0 : ℝ)..π, f θ with hJ
  set G : ℝ := ∫ θ in (0 : ℝ)..π, g θ with hG
  have hJG : 0 ≤ J - G ∧ J - G ≤ s / 2 * (8 / κ ^ 2 * (√(π / (κ / 2)) / 2)) := by
    have hd : J - G = ∫ θ in (0 : ℝ)..π, (f θ - g θ) := by
      rw [intervalIntegral.integral_sub (hfc.intervalIntegrable _ _) (hgc.intervalIntegrable _ _)]
    rw [hd, intervalIntegral.integral_of_le hpi.le]
    constructor
    · exact setIntegral_nonneg measurableSet_Ioc fun θ hθ => (exp_cos_sub_gauss hs hθ.1.le hθ.2).1
    · have h1 : ∫ θ in Ioc (0 : ℝ) π, (f θ - g θ) ≤ ∫ θ in Ioc (0 : ℝ) π, s / 2 * (θ ^ 4 * Real.exp (-(κ * θ ^ 2))) := by
        refine setIntegral_mono_on ?_ ?_ measurableSet_Ioc fun θ hθ => ?_
        · exact ((hfc.sub hgc).integrableOn_Icc (a := 0) (b := π)).mono_set Ioc_subset_Icc_self
        · exact (((by fun_prop : Continuous fun θ : ℝ => s / 2 * (θ ^ 4 * Real.exp (-(κ * θ ^ 2))))).integrableOn_Icc
            (a := 0) (b := π)).mono_set Ioc_subset_Icc_self
        · have := (exp_cos_sub_gauss hs hθ.1.le hθ.2).2
          simp only [hf, hg]
          calc _ ≤ s / 2 * θ ^ 4 * Real.exp (-(2 * s / π ^ 2 * θ ^ 2)) := this
            _ = _ := by rw [hκ]; ring
      refine h1.trans ?_
      have h2 : ∫ θ in Ioc (0 : ℝ) π, s / 2 * (θ ^ 4 * Real.exp (-(κ * θ ^ 2))) ≤
          ∫ θ in Ioi (0 : ℝ), s / 2 * (θ ^ 4 * Real.exp (-(κ * θ ^ 2))) := by
        refine setIntegral_mono_set ?_ ?_ (Filter.Eventually.of_forall Ioc_subset_Ioi_self)
        · exact (integrableOn_quartic hκ0).const_mul (s / 2)
        · exact Filter.Eventually.of_forall fun θ => by positivity
      refine h2.trans ?_
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (quartic_gauss hκ0) (by positivity)
  -- the Gaussian tail
  have hGA : ∃ T : ℝ, 0 ≤ T ∧ T ≤ 1 / π ^ 4 * (8 / (s / 2) ^ 2 * (√(π / (s / 2 / 2)) / 2)) ∧ G = A - T := by
    refine ⟨∫ θ in Ioi π, g θ, setIntegral_nonneg measurableSet_Ioi fun θ _ => (Real.exp_pos _).le, ?_, ?_⟩
    · have h1 : ∫ θ in Ioi π, g θ ≤ ∫ θ in Ioi π, 1 / π ^ 4 * (θ ^ 4 * Real.exp (-(s / 2 * θ ^ 2))) := by
        refine setIntegral_mono_on hgi.integrableOn ?_ measurableSet_Ioi fun θ hθ => ?_
        · exact (((integrableOn_quartic (b := s / 2) (by positivity)).mono_set
            (Ioi_subset_Ioi hpi.le))).const_mul (1 / π ^ 4)
        · have hθ' : π ≤ θ := le_of_lt hθ
          have : 1 ≤ θ ^ 4 / π ^ 4 := by
            rw [le_div_iff₀ (by positivity)]; nlinarith [pow_le_pow_left₀ hpi.le hθ' 4]
          rw [hgg]
          have he := Real.exp_pos (-(s / 2 * θ ^ 2))
          calc Real.exp (-(s / 2 * θ ^ 2)) ≤ θ ^ 4 / π ^ 4 * Real.exp (-(s / 2 * θ ^ 2)) :=
                le_mul_of_one_le_left he.le this
            _ = _ := by ring
      refine h1.trans ?_
      have h2 : ∫ θ in Ioi π, 1 / π ^ 4 * (θ ^ 4 * Real.exp (-(s / 2 * θ ^ 2))) ≤
          ∫ θ in Ioi (0 : ℝ), 1 / π ^ 4 * (θ ^ 4 * Real.exp (-(s / 2 * θ ^ 2))) := by
        refine setIntegral_mono_set ?_ ?_ (Filter.Eventually.of_forall (Ioi_subset_Ioi hpi.le))
        · exact (integrableOn_quartic (b := s / 2) (by positivity)).const_mul (1 / π ^ 4)
        · exact Filter.Eventually.of_forall fun θ => by positivity
      refine h2.trans ?_
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (quartic_gauss (κ := s / 2) (by positivity)) (by positivity)
    · have hsplit : Ioi (0 : ℝ) = Ioc 0 π ∪ Ioi π := (Ioc_union_Ioi_eq_Ioi hpi.le).symm
      have hint1 : IntegrableOn g (Ioc (0 : ℝ) π) := (hgc.integrableOn_Icc (a := 0) (b := π)).mono_set Ioc_subset_Icc_self
      have := setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hint1 hgi.integrableOn
      rw [← hsplit, hAint] at this
      rw [hG, intervalIntegral.integral_of_le hpi.le]
      linarith
  obtain ⟨T, hT0, hT1, hGT⟩ := hGA
  have hmain : (1 / π) * A = 1 / √(2 * π * s) := by
    rw [hA]
    have h2 : √(π / (s / 2)) = √(2 * π * s) / s := by
      rw [show π / (s / 2) = (2 * π * s) / s ^ 2 by field_simp, Real.sqrt_div (by positivity), Real.sqrt_sq hs.le]
    rw [h2]
    have : 0 < √(2 * π * s) := Real.sqrt_pos.2 (by positivity)
    have h3 : √(2 * π * s) ^ 2 = 2 * π * s := Real.sq_sqrt (by positivity)
    field_simp
    have h4 : √(π * 2 * s) = √(2 * π * s) := by congr 1; ring
    rw [h4]; nlinarith
  have e : (1 / π) * J - 1 / √(2 * π * s) = (1 / π) * (J - G) - (1 / π) * T := by
    rw [← hmain, hGT]; ring
  rw [e]
  have hpi' : 0 < 1 / π := by positivity
  rw [abs_le]
  constructor
  · nlinarith [mul_nonneg hpi'.le hJG.1, mul_le_mul_of_nonneg_left hT1 hpi'.le,
      mul_nonneg hpi'.le (show 0 ≤ s / 2 * (8 / κ ^ 2 * (√(π / (κ / 2)) / 2)) by positivity)]
  · nlinarith [mul_le_mul_of_nonneg_left hJG.2 hpi'.le, mul_nonneg hpi'.le hT0]

/-- **`I₀` asymptotics with a relative error `O(1/s)`**:
`|√(2π s) e^{-s} I₀(s) - 1| ≤ C / s` for `s ≥ 1`, where `I₀(s) = (1/π) ∫₀^π e^{s cos θ} dθ`. -/
theorem besselI0_eff :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 1 ≤ s →
      |√(2 * π * s) * (Real.exp (-s) * ((1 / π) * ∫ θ in (0 : ℝ)..π, Real.exp (s * Real.cos θ))) - 1| ≤ C / s := by
  have hpi : 0 < π := Real.pi_pos
  set c1 : ℝ := π ^ 4 * √(π ^ 3) / 2 with hc1
  set c2 : ℝ := 32 * √π / π ^ 4 with hc2
  refine ⟨√(2 * π) / π * (c1 + c2), by positivity, fun s hs => ?_⟩
  have hs0 : 0 < s := by linarith
  have ht : 0 < √s := Real.sqrt_pos.2 hs0
  have hts : √s ^ 2 = s := Real.sq_sqrt hs0.le
  have h := laplace_cos_eff hs0
  have hrel : (1 / π) * (∫ θ in (0 : ℝ)..π, Real.exp (-(s * (1 - Real.cos θ)))) =
      Real.exp (-s) * ((1 / π) * ∫ θ in (0 : ℝ)..π, Real.exp (s * Real.cos θ)) := by
    have : ∀ θ : ℝ, Real.exp (-(s * (1 - Real.cos θ))) = Real.exp (-s) * Real.exp (s * Real.cos θ) := fun θ => by
      rw [← Real.exp_add]; congr 1; ring
    simp_rw [this]
    rw [intervalIntegral.integral_const_mul]; ring
  rw [hrel] at h
  have e1 : √(π / (2 * s / π ^ 2 / 2)) = √(π ^ 3) / √s := by
    rw [show π / (2 * s / π ^ 2 / 2) = π ^ 3 / s by field_simp, Real.sqrt_div (by positivity)]
  have e2 : √(π / (s / 2 / 2)) = 2 * √π / √s := by
    rw [show π / (s / 2 / 2) = 4 * π / s by field_simp; ring, Real.sqrt_div (by positivity),
      Real.sqrt_mul (by norm_num)]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [e1, e2] at h
  have hE : (1 / π) * (s / 2 * (8 / (2 * s / π ^ 2) ^ 2 * (√(π ^ 3) / √s / 2)) +
        1 / π ^ 4 * (8 / (s / 2) ^ 2 * (2 * √π / √s / 2))) =
      (1 / π) * (c1 / (s * √s) + c2 / (s ^ 2 * √s)) := by
    rw [hc1, hc2]; field_simp; ring
  rw [hE] at h
  have hq : √(2 * π * s) = √(2 * π) * √s := Real.sqrt_mul (by positivity) _
  have hrw : √(2 * π * s) * (Real.exp (-s) * ((1 / π) * ∫ θ in (0 : ℝ)..π, Real.exp (s * Real.cos θ))) - 1 =
      √(2 * π * s) * ((Real.exp (-s) * ((1 / π) * ∫ θ in (0 : ℝ)..π, Real.exp (s * Real.cos θ))) -
        1 / √(2 * π * s)) := by
    have : 0 < √(2 * π * s) := Real.sqrt_pos.2 (by positivity)
    field_simp
  rw [hrw, abs_mul, abs_of_pos (Real.sqrt_pos.2 (by positivity : 0 < 2 * π * s))]
  calc √(2 * π * s) * |Real.exp (-s) * ((1 / π) * ∫ θ in (0 : ℝ)..π, Real.exp (s * Real.cos θ)) - 1 / √(2 * π * s)|
      ≤ √(2 * π * s) * ((1 / π) * (c1 / (s * √s) + c2 / (s ^ 2 * √s))) :=
        mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg _)
    _ = √(2 * π) / π * (c1 / s + c2 / s ^ 2) := by
        rw [hq]; field_simp
    _ ≤ √(2 * π) / π * (c1 + c2) / s := by
        have hc1' : 0 ≤ c1 := by positivity
        have hc2' : 0 ≤ c2 := by positivity
        have : c2 / s ^ 2 ≤ c2 / s := by
          refine div_le_div_of_nonneg_left hc2' hs0 (by nlinarith)
        have h2 : √(2 * π) / π * (c1 / s + c2 / s ^ 2) ≤ √(2 * π) / π * (c1 / s + c2 / s) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        refine h2.trans (le_of_eq ?_)
        field_simp

end Lightlike.Tauberian
