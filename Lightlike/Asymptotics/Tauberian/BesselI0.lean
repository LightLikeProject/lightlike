import Lightlike.Asymptotics.Tauberian.BesselSeries

/-!
# The series `∑ (z/2)^{2k} / (k!)²` (the modified Bessel function `I₀`) as an integral

`hasSum_besselI0`: `∑_k (z/2)^{2k}/(k!)² = (1/π) ∫₀^π e^{z cos θ} dθ`, by termwise integration with the
Wallis integrals of `BesselSeries`.
-/

open MeasureTheory Set Filter Topology Real

noncomputable section

namespace Lightlike.Tauberian

/-- The integral of the `n`-th term of the exponential series of `z cos θ`. -/
lemma integral_term0 (z : ℝ) (n : ℕ) :
    ∫ θ in (0 : ℝ)..π, z ^ n / (n.factorial : ℝ) * Real.cos θ ^ n =
      if Even n then z ^ n / (n.factorial : ℝ) * (π * wallis (n / 2)) else 0 := by
  rw [intervalIntegral.integral_const_mul]
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have : Even (2 * k) := ⟨k, by ring⟩
    simp only [this, ↓reduceIte]
    rw [integral_cos_pow_even]
    congr 3
    omega
  · have : ¬ Even (2 * k + 1) := by simp
    simp only [this, ↓reduceIte]
    rw [integral_cos_pow_odd, mul_zero]

/-- **The series of `I₀` as an integral.** -/
theorem hasSum_besselI0 (z : ℝ) :
    HasSum (fun k : ℕ => (z / 2) ^ (2 * k) / ((k.factorial : ℝ) * (k.factorial : ℝ)))
      ((1 / π) * ∫ θ in (0 : ℝ)..π, Real.exp (z * Real.cos θ)) := by
  set F : ℕ → ℝ → ℝ := fun n θ => z ^ n / (n.factorial : ℝ) * Real.cos θ ^ n with hF
  have hFc : ∀ n, Continuous (F n) := fun n => by simp only [hF]; fun_prop
  have hint : ∀ n, Integrable (F n) (volume.restrict (Ioc (0 : ℝ) π)) := fun n =>
    ((hFc n).integrableOn_Icc (a := 0) (b := π)).mono_set Set.Ioc_subset_Icc_self
  have hbound : ∀ n, ∫ θ in Ioc (0 : ℝ) π, ‖F n θ‖ ≤ π * (|z| ^ n / (n.factorial : ℝ)) := by
    intro n
    have h1 : ∀ θ, ‖F n θ‖ ≤ |z| ^ n / (n.factorial : ℝ) := by
      intro θ
      simp only [hF, norm_mul, Real.norm_eq_abs, abs_div, abs_pow, Nat.abs_cast]
      have : |Real.cos θ| ^ n ≤ 1 := pow_le_one₀ (abs_nonneg _) (Real.abs_cos_le_one _)
      calc |z| ^ n / (n.factorial : ℝ) * |Real.cos θ| ^ n ≤ |z| ^ n / (n.factorial : ℝ) * 1 :=
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
  have hTsum : ∀ θ, ∑' n, F n θ = Real.exp (z * Real.cos θ) := by
    intro θ
    have := (hasSum_exp_div (z := z * Real.cos θ))
    rw [← this.tsum_eq]
    refine tsum_congr fun n => ?_
    simp only [hF]; rw [mul_pow]; ring
  simp_rw [hTsum] at hA
  rw [← intervalIntegral.integral_of_le Real.pi_pos.le] at hA
  have hB : HasSum (fun n : ℕ => ∫ θ in (0 : ℝ)..π, F n θ)
      (∫ θ in (0 : ℝ)..π, Real.exp (z * Real.cos θ)) := by
    simpa [intervalIntegral.integral_of_le Real.pi_pos.le] using hA
  have hg : ∀ n, ∫ θ in (0 : ℝ)..π, F n θ =
      if Even n then z ^ n / (n.factorial : ℝ) * (π * wallis (n / 2)) else 0 :=
    fun n => integral_term0 z n
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := fun p q h => by simpa using h
  have hsupp : ∀ n ∉ Set.range (fun k : ℕ => 2 * k), (∫ θ in (0 : ℝ)..π, F n θ) = 0 := by
    intro n hn
    rw [hg]
    have : ¬ Even n := by
      intro hne
      obtain ⟨k, hk⟩ := hne
      exact hn ⟨k, by show 2 * k = n; omega⟩
    simp [this]
  have hC := (hinj.hasSum_iff hsupp).2 hB
  have hD := hC.mul_left (1 / π)
  refine hD.congr_fun ?_
  intro k
  simp only [Function.comp]
  rw [hg]
  simp only [show Even (2 * k) from ⟨k, by ring⟩, ↓reduceIte]
  rw [show 2 * k / 2 = k by omega, wallis_eq]
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  have hk2 : ((2 * k).factorial : ℝ) ≠ 0 := by positivity
  have hpi : π ≠ 0 := Real.pi_pos.ne'
  rw [div_pow, show (2 : ℝ) ^ (2 * k) = 4 ^ k by rw [pow_mul]; norm_num]
  field_simp

end Lightlike.Tauberian
