import Lightlike.Asymptotics.Tauberian.BesselAsymp
import Lightlike.Asymptotics.Tauberian.CrossingBound

/-!
# The series of the crossing density as an integral

`∑_{k ≥ 0} (z/2)^{2k+1} / (k! (k+1)!) = (1/π) ∫₀^π e^{z cos θ} cos θ dθ` (the modified Bessel function
`I₁`), from the Wallis integrals `∫₀^π cos^m θ dθ` and termwise integration of the exponential series.
-/

open MeasureTheory Set Real Filter Topology

noncomputable section

namespace Lightlike.Tauberian

/-- The Wallis product `∏_{i<m} (2i+1)/(2i+2)`. -/
def wallis (m : ℕ) : ℝ := ∏ i ∈ Finset.range m, (2 * (i : ℝ) + 1) / (2 * i + 2)

lemma wallis_eq (m : ℕ) : wallis m = ((2 * m).factorial : ℝ) / (4 ^ m * ((m.factorial : ℝ)) ^ 2) := by
  induction m with
  | zero => simp [wallis]
  | succ m ih =>
    unfold wallis at ih ⊢
    rw [Finset.prod_range_succ, ih]
    have h1 : (2 * (m + 1)).factorial = (2 * m + 2) * (2 * m + 1) * (2 * m).factorial := by
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]; ring
    rw [h1, Nat.factorial_succ]
    push_cast
    have hm : (m.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring

/-- `∫₀^π cos^{m+2} = (m+1)/(m+2) ∫₀^π cos^m`. -/
lemma integral_cos_pow_two (m : ℕ) :
    ∫ x in (0 : ℝ)..π, Real.cos x ^ (m + 2) =
      ((m : ℝ) + 1) / ((m : ℝ) + 2) * ∫ x in (0 : ℝ)..π, Real.cos x ^ m := by
  rw [integral_cos_pow]
  simp

lemma integral_cos_pow_even (m : ℕ) :
    ∫ x in (0 : ℝ)..π, Real.cos x ^ (2 * m) = π * wallis m := by
  induction m with
  | zero => simp [wallis]
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 2 by ring, integral_cos_pow_two, ih]
    unfold wallis
    rw [Finset.prod_range_succ]
    push_cast
    ring

lemma integral_cos_pow_odd (m : ℕ) : ∫ x in (0 : ℝ)..π, Real.cos x ^ (2 * m + 1) = 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by ring, integral_cos_pow_two, ih, mul_zero]

/-- The integral of the `n`-th term. -/
lemma integral_term (z : ℝ) (n : ℕ) :
    ∫ θ in (0 : ℝ)..π, z ^ n / (n.factorial : ℝ) * Real.cos θ ^ (n + 1) =
      if Even n then 0 else z ^ n / (n.factorial : ℝ) * (π * wallis ((n + 1) / 2)) := by
  rw [intervalIntegral.integral_const_mul]
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have : Even (2 * k) := ⟨k, by ring⟩
    simp only [this, ↓reduceIte]
    rw [integral_cos_pow_odd, mul_zero]
  · have : ¬ Even (2 * k + 1) := by simp
    simp only [this, ↓reduceIte]
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, integral_cos_pow_even]
    congr 3
    omega

/-- **The series of `I₁` as an integral.** -/
theorem hasSum_besselI1 (z : ℝ) :
    HasSum (fun k : ℕ => (z / 2) ^ (2 * k + 1) / ((k.factorial : ℝ) * ((k + 1).factorial : ℝ)))
      ((1 / π) * ∫ θ in (0 : ℝ)..π, Real.exp (z * Real.cos θ) * Real.cos θ) := by
  set F : ℕ → ℝ → ℝ := fun n θ => z ^ n / (n.factorial : ℝ) * Real.cos θ ^ (n + 1) with hF
  have hFc : ∀ n, Continuous (F n) := fun n => by simp only [hF]; fun_prop
  have hint : ∀ n, Integrable (F n) (volume.restrict (Ioc (0 : ℝ) π)) := fun n =>
    ((hFc n).integrableOn_Icc (a := 0) (b := π)).mono_set Set.Ioc_subset_Icc_self
  have hbound : ∀ n, ∫ θ in Ioc (0 : ℝ) π, ‖F n θ‖ ≤ π * (|z| ^ n / (n.factorial : ℝ)) := by
    intro n
    have h1 : ∀ θ, ‖F n θ‖ ≤ |z| ^ n / (n.factorial : ℝ) := by
      intro θ
      simp only [hF, norm_mul, Real.norm_eq_abs, abs_div, abs_pow, Nat.abs_cast]
      have : |Real.cos θ| ^ (n + 1) ≤ 1 := pow_le_one₀ (abs_nonneg _) (Real.abs_cos_le_one _)
      calc |z| ^ n / (n.factorial : ℝ) * |Real.cos θ| ^ (n + 1) ≤ |z| ^ n / (n.factorial : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := mul_one _
    calc ∫ θ in Ioc (0 : ℝ) π, ‖F n θ‖ ≤ ∫ θ in Ioc (0 : ℝ) π, |z| ^ n / (n.factorial : ℝ) :=
          setIntegral_mono_on (hint n).norm (integrableOn_const (by simp)) measurableSet_Ioc
            fun θ _ => h1 θ
      _ = π * (|z| ^ n / (n.factorial : ℝ)) := by
          simp [Real.volume_real_Ioc_of_le Real.pi_pos.le]
  have hsum : Summable fun n => ∫ θ in Ioc (0 : ℝ) π, ‖F n θ‖ :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun θ => norm_nonneg _) hbound
      ((hasSum_exp_div (z := |z|)).summable.mul_left π)
  have hA := hasSum_integral_of_summable_integral_norm hint hsum
  have hTsum : ∀ θ, ∑' n, F n θ = Real.exp (z * Real.cos θ) * Real.cos θ := by
    intro θ
    have := (hasSum_exp_div (z := z * Real.cos θ)).mul_right (Real.cos θ)
    rw [← this.tsum_eq]
    refine tsum_congr fun n => ?_
    simp only [hF]; rw [mul_pow, pow_succ]; ring
  simp_rw [hTsum] at hA
  rw [← intervalIntegral.integral_of_le Real.pi_pos.le] at hA
  have hB : HasSum (fun n : ℕ => ∫ θ in (0 : ℝ)..π, F n θ)
      (∫ θ in (0 : ℝ)..π, Real.exp (z * Real.cos θ) * Real.cos θ) := by
    simpa [intervalIntegral.integral_of_le Real.pi_pos.le] using hA
  have hg : ∀ n, ∫ θ in (0 : ℝ)..π, F n θ =
      if Even n then 0 else z ^ n / (n.factorial : ℝ) * (π * wallis ((n + 1) / 2)) :=
    fun n => integral_term z n
  have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := fun p q h => by simpa using h
  have hsupp : ∀ n ∉ Set.range (fun k : ℕ => 2 * k + 1), (∫ θ in (0 : ℝ)..π, F n θ) = 0 := by
    intro n hn
    rw [hg]
    have : Even n := by
      by_contra hne
      obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.1 hne
      exact hn ⟨k, hk.symm⟩
    simp [this]
  have hC := (hinj.hasSum_iff hsupp).2 hB
  have hD := hC.mul_left (1 / π)
  refine hD.congr_fun ?_
  intro k
  simp only [Function.comp]
  rw [hg]
  simp only [show ¬ Even (2 * k + 1) from by simp, ↓reduceIte]
  rw [show (2 * k + 1 + 1) / 2 = k + 1 by omega, wallis_eq]
  have h1 : (2 * (k + 1)).factorial = (2 * k + 2) * (2 * k + 1).factorial := by
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Nat.factorial_succ]
  rw [h1]
  have hf1 : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  push_cast
  rw [hf1]
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  have hk2 : ((2 * k + 1).factorial : ℝ) ≠ 0 := by positivity
  have hpi : π ≠ 0 := Real.pi_pos.ne'
  rw [div_pow, show (2 : ℝ) ^ (2 * k + 1) = 2 * 4 ^ k by rw [pow_succ, pow_mul]; norm_num; ring]
  field_simp
  ring

/-- `cosLaplace` in terms of the series: `∫₀^π e^{z cos θ} cos θ dθ = e^z cosLaplace z`. -/
lemma exp_mul_cosLaplace (z : ℝ) :
    ∫ θ in (0 : ℝ)..π, Real.exp (z * Real.cos θ) * Real.cos θ = Real.exp z * cosLaplace z := by
  unfold cosLaplace
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  show Real.exp (z * Real.cos θ) * Real.cos θ = Real.exp z * (Real.exp (-z * (1 - Real.cos θ)) * Real.cos θ)
  rw [← mul_assoc, ← Real.exp_add]
  congr 2; ring

/-- **The crossing density as a Bessel integral**: for `a, x > 0` and `z = 2 √(a x)`,
`crossingDensity a x = 2 a e^z cosLaplace(z) / (π z)`. -/
theorem crossingDensity_eq {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    crossingDensity a x = 2 * a / (π * (2 * Real.sqrt (a * x))) *
      (Real.exp (2 * Real.sqrt (a * x)) * cosLaplace (2 * Real.sqrt (a * x))) := by
  set z := 2 * Real.sqrt (a * x) with hz
  have hzpos : 0 < z := by positivity
  have hz2 : z ^ 2 = 4 * (a * x) := by
    rw [hz, mul_pow, Real.sq_sqrt (by positivity)]; ring
  have h := (hasSum_besselI1 z).mul_left (2 * a / z)
  rw [exp_mul_cosLaplace] at h
  have h2 : crossingDensity a x = 2 * a / z * ((1 / π) * (Real.exp z * cosLaplace z)) := by
    unfold crossingDensity
    rw [← h.tsum_eq]
    refine tsum_congr fun k => ?_
    unfold crossingTerm
    have hfac : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hpow : (z / 2) ^ (2 * k + 1) = (z / 2) * (a * x) ^ k := by
      rw [pow_succ, pow_mul, div_pow, hz2]
      rw [show (4 * (a * x) / 2 ^ 2) = a * x by ring]; ring
    rw [hpow]
    have hk : (k.factorial : ℝ) ≠ 0 := by positivity
    have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    rw [hfac, mul_pow, pow_succ]
    field_simp
  rw [h2]; ring

/-- **D2 (sharp asymptotics).** With `z = 2 √(a x)`, `crossingDensity a x ~ 2 a e^z / (π z √z) · √(π/2)`,
that is `√(a/x) I₁(2 √(a x)) ~ …`: the leading behaviour of the crossing kernel of MZ (2.6). -/
theorem tendsto_crossingDensity {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => crossingDensity a x *
        (π * (2 * Real.sqrt (a * x)) * Real.sqrt (2 * Real.sqrt (a * x)) / (2 * a)) *
        Real.exp (-(2 * Real.sqrt (a * x)))) atTop (𝓝 (Real.sqrt (π / 2))) := by
  have hz : Tendsto (fun x : ℝ => 2 * Real.sqrt (a * x)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop two_pos
      (Real.tendsto_sqrt_atTop.comp (Filter.Tendsto.const_mul_atTop ha tendsto_id))
  refine (tendsto_sqrt_mul_cosLaplace.comp hz).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp only [Function.comp]
  rw [crossingDensity_eq ha hx]
  set z := 2 * Real.sqrt (a * x)
  have hzpos : 0 < z := by positivity
  have hs : 0 < Real.sqrt z := Real.sqrt_pos.2 hzpos
  have hexp : Real.exp z * Real.exp (-z) = 1 := by rw [← Real.exp_add]; simp
  have hpi : π ≠ 0 := Real.pi_pos.ne'
  have hz0 : z ≠ 0 := hzpos.ne'
  have ha0 : a ≠ 0 := ha.ne'
  have key : 2 * a / (π * z) * (Real.exp z * cosLaplace z) * (π * z * Real.sqrt z / (2 * a)) *
      Real.exp (-z) = Real.sqrt z * cosLaplace z * (Real.exp z * Real.exp (-z)) := by
    field_simp
  rw [key, hexp, mul_one]

end Lightlike.Tauberian
