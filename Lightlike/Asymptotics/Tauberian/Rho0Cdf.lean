import Lightlike.Asymptotics.Tauberian.CrossingMeasure
import Lightlike.Asymptotics.Tauberian.BesselI0

/-!
# The distribution function of the crossing measure

`rho0_real_Iic`: `ρ₀(-∞, x] = ∑_m (a x)^m / (m!)² = (1/π) ∫₀^π e^{2√(a x) cos θ} dθ` for `x ≥ 0`
(so `ρ₀(-∞, x] = I₀(2√(a x))`).
-/

open MeasureTheory Set Filter Topology Real

noncomputable section

namespace Lightlike.Tauberian

/-- The integral of the `k`-th term of the crossing density over `(0, x]`. -/
lemma integral_crossingTerm {a x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    ∫ t in Ioc (0 : ℝ) x, crossingTerm a k t = (a * x) ^ (k + 1) / (((k + 1).factorial : ℝ) ^ 2) := by
  rw [← intervalIntegral.integral_of_le hx]
  unfold crossingTerm
  have : ∀ t : ℝ, a ^ (k + 1) * t ^ k / (((k + 1).factorial : ℝ) * (k.factorial : ℝ)) =
      a ^ (k + 1) / (((k + 1).factorial : ℝ) * (k.factorial : ℝ)) * t ^ k := fun t => by ring
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul, integral_pow]
  have hf : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  rw [hf, mul_pow, zero_pow (by omega), sub_zero]
  field_simp

/-- `∫_{(0,x]} ρ₀(t) dt = ∑_{m ≥ 1} (a x)^m / (m!)²`. -/
lemma hasSum_integral_crossingDensity {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    HasSum (fun k : ℕ => (a * x) ^ (k + 1) / (((k + 1).factorial : ℝ) ^ 2))
      (∫ t in Ioc (0 : ℝ) x, crossingDensity a t) := by
  have hint : ∀ k, Integrable (crossingTerm a k) (volume.restrict (Ioc (0 : ℝ) x)) := fun k =>
    ((continuousOn_crossingTerm a k).integrableOn_Icc (a := 0) (b := x)).mono_set Set.Ioc_subset_Icc_self
  have hnorm : ∀ k, ∫ t in Ioc (0 : ℝ) x, ‖crossingTerm a k t‖ =
      (a * x) ^ (k + 1) / (((k + 1).factorial : ℝ) ^ 2) := by
    intro k
    rw [← integral_crossingTerm hx k]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [Real.norm_of_nonneg (crossingTerm_nonneg ha k ht.1.le)]
  have hsum : Summable fun k => ∫ t in Ioc (0 : ℝ) x, ‖crossingTerm a k t‖ := by
    have h := (summable_nat_add_iff 1).2 (hasSum_exp_div (z := a * x)).summable
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun t => norm_nonneg _) (fun k => ?_) h
    rw [hnorm]
    have hf : (1 : ℝ) ≤ ((k + 1).factorial : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
    have hax : 0 ≤ (a * x) ^ (k + 1) := pow_nonneg (by positivity) _
    calc (a * x) ^ (k + 1) / (((k + 1).factorial : ℝ) ^ 2) ≤ (a * x) ^ (k + 1) / ((k + 1).factorial : ℝ) := by
          refine div_le_div_of_nonneg_left hax (by positivity) ?_
          nlinarith
      _ = _ := rfl
  have h2 := hasSum_integral_of_summable_integral_norm hint hsum
  have e : (fun k : ℕ => ∫ t in Ioc (0 : ℝ) x, crossingTerm a k t) =
      fun k : ℕ => (a * x) ^ (k + 1) / (((k + 1).factorial : ℝ) ^ 2) :=
    funext fun k => integral_crossingTerm hx k
  rw [e] at h2
  exact h2

/-- **The distribution function of the crossing measure.** -/
theorem rho0_real_Iic {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    (rho0 a).real (Iic x) = (1 / π) * ∫ θ in (0 : ℝ)..π, Real.exp (2 * Real.sqrt (a * x) * Real.cos θ) := by
  have hS := hasSum_besselI0 (2 * Real.sqrt (a * x))
  have e1 : ∀ k : ℕ, (2 * Real.sqrt (a * x) / 2) ^ (2 * k) / ((k.factorial : ℝ) * (k.factorial : ℝ)) =
      (a * x) ^ k / ((k.factorial : ℝ) ^ 2) := by
    intro k
    rw [show 2 * Real.sqrt (a * x) / 2 = Real.sqrt (a * x) by ring, pow_mul, Real.sq_sqrt (by positivity)]
    ring
  simp_rw [e1] at hS
  -- split off the `k = 0` term
  have hT := hasSum_integral_crossingDensity ha hx
  have hS' : HasSum (fun k : ℕ => (a * x) ^ (k + 1) / (((k + 1).factorial : ℝ) ^ 2))
      ((1 / π) * (∫ θ in (0 : ℝ)..π, Real.exp (2 * Real.sqrt (a * x) * Real.cos θ)) - 1) := by
    have := (hasSum_nat_add_iff' 1).2 hS
    simpa using this
  have hI : ∫ t in Ioc (0 : ℝ) x, crossingDensity a t =
      (1 / π) * (∫ θ in (0 : ℝ)..π, Real.exp (2 * Real.sqrt (a * x) * Real.cos θ)) - 1 :=
    hT.unique hS'
  have hm : (rho0 a) (Iic x) = 1 + ∫⁻ t in Ioc (0 : ℝ) x, ENNReal.ofReal (crossingDensity a t) := by
    unfold rho0
    rw [Measure.add_apply, Measure.dirac_apply' _ measurableSet_Iic, withDensity_apply _ measurableSet_Iic,
      Measure.restrict_restrict measurableSet_Iic]
    have : Iic x ∩ Ioi 0 = Ioc 0 x := by ext t; simp [and_comm]
    rw [this]
    simp [hx]
  have hint : IntegrableOn (crossingDensity a) (Ioc (0 : ℝ) x) :=
    (((continuousOn_crossingDensity ha).mono Set.Icc_subset_Ici_self).integrableOn_Icc (a := 0) (b := x)).mono_set
      (fun t ht => ⟨ht.1.le, ht.2⟩)
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) x)] crossingDensity a :=
    (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun t ht =>
      crossingDensity_nonneg ha ht.1.le)
  have hI0 : 0 ≤ ∫ t in Ioc (0 : ℝ) x, crossingDensity a t :=
    setIntegral_nonneg measurableSet_Ioc fun t ht => crossingDensity_nonneg ha ht.1.le
  rw [Measure.real, hm, ← ofReal_integral_eq_lintegral_ofReal hint hnn,
    ENNReal.toReal_add (by simp) ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hI0, hI]
  simp

end Lightlike.Tauberian
