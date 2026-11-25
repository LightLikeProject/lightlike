module

public import Lightlike.Lorentz.SL2RPlancherel.Cayley
public import Lightlike.Lorentz.SL2RPlancherel.DiscMeanValue

/-!
# The reproducing property of `(z + i)⁻ⁿ` in the weighted Bergman space

For `n ≥ 2` and `φ` holomorphic on the upper half-plane with `φ · conj((z+i)⁻ⁿ) · yⁿ⁻²` integrable,
`∫_{Im z>0} φ(z) conj((z+i)⁻ⁿ) yⁿ⁻² dA = (4π/(n-1)) (-2i)⁻ⁿ φ(i)`.
The Cayley transform turns the integral into `4(-2i)⁻ⁿ ∫_𝔻 h(w) (1-|w|²)ⁿ⁻² dA(w)` with
`h(w) = φ(z(w)) (1-w)⁻ⁿ` holomorphic, and the weighted mean-value property gives `h(0) π/(n-1)`.
-/

@[expose] public section

open MeasureTheory Set Complex Metric Real

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The integrand of the Bergman pairing with `(z + i)⁻ⁿ` at the Cayley point, with the Jacobian, as `h(w) ρ(|w|)`. -/
lemma pairing_cayley {n : ℕ} (hn : 2 ≤ n) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) (φ : ℂ → ℂ) :
    (4 / ‖1 - w‖ ^ 4 : ℝ) • (φ (cayleyInv w) * (starRingEnd ℂ) (((cayleyInv w + Complex.I) ^ n)⁻¹) *
        (((cayleyInv w).im ^ (n - 2) : ℝ) : ℂ)) =
      (4 * ((-2 * Complex.I) ^ n)⁻¹ * (φ (cayleyInv w) * ((1 - w) ^ n)⁻¹)) *
        (((1 - ‖w‖ ^ 2) ^ (n - 2) : ℝ) : ℂ) := by
  have hu := one_sub_ne_zero hw
  have hū : (starRingEnd ℂ) (1 - w) ≠ 0 := (map_ne_zero (starRingEnd ℂ)).2 hu
  have hy := im_cayleyInv hw
  have hzI : cayleyInv w + Complex.I = 2 * Complex.I / (1 - w) := by
    unfold cayleyInv; field_simp; ring
  have hcz : (starRingEnd ℂ) (cayleyInv w + Complex.I) = -2 * Complex.I / (starRingEnd ℂ) (1 - w) := by
    rw [hzI]; simp [map_div₀, map_ofNat]
  have hnormsq : ((‖1 - w‖ : ℝ) : ℂ) ^ 2 = (1 - w) * (starRingEnd ℂ) (1 - w) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hw2 : ((Complex.normSq w : ℝ) : ℂ) = ((‖w‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]; push_cast; ring
  have hn2 : (Complex.normSq (1 - w) : ℝ) = ‖1 - w‖ ^ 2 := Complex.normSq_eq_norm_sq _
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [Complex.real_smul, map_inv₀, map_pow, hcz, hy, hn2]
  have h4 : (‖1 - w‖ ^ 4 : ℝ) = (‖1 - w‖ ^ 2) ^ 2 := by ring
  rw [h4]
  push_cast
  rw [hnormsq]
  have h2I : (-2 * Complex.I : ℂ) ≠ 0 := by simp [Complex.I_ne_zero]
  rw [hw2]
  generalize (φ (cayleyInv w)) = P
  generalize (starRingEnd ℂ) (1 - w) = v at *
  generalize (1 - w) = u at *
  generalize ((‖w‖ : ℝ) : ℂ) = c
  generalize (-2 * Complex.I : ℂ) = a at *
  simp only [div_pow, mul_pow]
  field_simp
  ring

/-- `∫_0^1 s (1-s²)^m ds = 1/(2(m+1))`. -/
lemma integral_radial_weight (m : ℕ) :
    ∫ s in Ioo (0 : ℝ) 1, s * (1 - s ^ 2) ^ m = 1 / (2 * ((m : ℝ) + 1)) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  have hd : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => -(1 - s ^ 2) ^ (m + 1) / (2 * ((m : ℝ) + 1)))
      (x * (1 - x ^ 2) ^ m) x := by
    intro x _
    have h1 : HasDerivAt (fun s : ℝ => 1 - s ^ 2) (-(2 * x)) x := by
      simpa using ((hasDerivAt_id x).pow 2).const_sub 1
    have h2 := (h1.pow (m + 1)).neg.div_const (2 * ((m : ℝ) + 1))
    convert h2 using 1
    have : (m : ℝ) + 1 ≠ 0 := by positivity
    simp only [Nat.add_sub_cancel]
    field_simp
    push_cast
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · simp
    have : (m : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  · exact (continuous_id.mul ((continuous_const.sub (continuous_id.pow 2)).pow m)).intervalIntegrable _ _

/-- **The reproducing property of `(z + i)⁻ⁿ`**: for `n ≥ 2` and `φ` holomorphic on the upper half-plane with the
pairing integrable,
`∫_{Im z>0} φ(z) conj((z+i)⁻ⁿ) yⁿ⁻² dA = (4π/(n-1)) (-2i)⁻ⁿ φ(i)`. -/
theorem bergman_reproducing {n : ℕ} (hn : 2 ≤ n) {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ {z : ℂ | 0 < z.im})
    (hint : IntegrableOn (fun z : ℂ => φ z * (starRingEnd ℂ) (((z + Complex.I) ^ n)⁻¹) *
      (((z.im ^ (n - 2) : ℝ)) : ℂ)) {z : ℂ | 0 < z.im}) :
    ∫ z in {z : ℂ | 0 < z.im}, φ z * (starRingEnd ℂ) (((z + Complex.I) ^ n)⁻¹) *
        (((z.im ^ (n - 2) : ℝ)) : ℂ) =
      ((4 * π / (n - 1) : ℝ) : ℂ) * ((-2 * Complex.I) ^ n)⁻¹ * φ Complex.I := by
  set g : ℂ → ℂ := fun z => φ z * (starRingEnd ℂ) (((z + Complex.I) ^ n)⁻¹) * (((z.im ^ (n - 2) : ℝ)) : ℂ)
    with hg
  set k : ℂ → ℂ := fun w => 4 * ((-2 * Complex.I) ^ n)⁻¹ * (φ (cayleyInv w) * ((1 - w) ^ n)⁻¹) with hk
  set ρ : ℝ → ℝ := fun s => (1 - s ^ 2) ^ (n - 2) with hρ
  have hρc : Continuous ρ := by simp only [hρ]; fun_prop
  have hkd : DifferentiableOn ℂ k (ball (0 : ℂ) 1) := by
    intro w hw
    have h1 := one_sub_ne_zero hw
    have hz : cayleyInv w ∈ {z : ℂ | 0 < z.im} := cayleyInv_mem hw
    have hφd : DifferentiableAt ℂ φ (cayleyInv w) :=
      (hφ (cayleyInv w) hz).differentiableAt (isOpen_lt continuous_const Complex.continuous_im |>.mem_nhds hz)
    have hc : DifferentiableAt ℂ cayleyInv w := (hasDerivAt_cayleyInv hw).differentiableAt
    have : DifferentiableAt ℂ k w := by
      simp only [hk]
      refine (differentiableAt_const _).mul ((hφd.comp w hc).mul ?_)
      exact ((differentiableAt_const _).sub differentiableAt_id |>.pow n).inv (pow_ne_zero _ h1)
    exact this.differentiableWithinAt
  -- integrability on the disc
  have hf' : ∀ w ∈ ball (0 : ℂ) 1, HasFDerivWithinAt cayleyInv
      (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (2 * Complex.I / (1 - w) ^ 2)).restrictScalars ℝ))
      (ball (0 : ℂ) 1) w :=
    fun w hw => ((hasDerivAt_cayleyInv hw).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hintD : IntegrableOn (fun w => (4 / ‖1 - w‖ ^ 4 : ℝ) • g (cayleyInv w)) (ball (0 : ℂ) 1) := by
    have := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume measurableSet_ball hf'
      cayleyInv_injOn g).1 (by rw [image_cayleyInv]; exact hint)
    refine this.congr_fun (fun w hw => ?_) measurableSet_ball
    simp only [abs_det_cayleyInv hw]
  have hint2 : IntegrableOn (fun w => k w * (ρ ‖w‖ : ℂ)) (ball (0 : ℂ) 1) := by
    refine hintD.congr_fun (fun w hw => ?_) measurableSet_ball
    simp only [hg, hk, hρ]
    exact pairing_cayley hn hw φ
  have hint1 : IntegrableOn (fun w : ℂ => (ρ ‖w‖ : ℂ)) (ball (0 : ℂ) 1) := by
    have hc : Continuous fun w : ℂ => (ρ ‖w‖ : ℂ) := by simp only [hρ]; fun_prop
    exact (hc.continuousOn.integrableOn_compact (isCompact_closedBall 0 1)).mono_set ball_subset_closedBall
  have hmv := integral_ball_radial_mul hkd hρc hint2 hint1
  have hrad : ∫ w in ball (0 : ℂ) 1, (ρ ‖w‖ : ℂ) = ((π / (n - 1) : ℝ) : ℂ) := by
    have h := integral_ball_radial (k := fun _ => (1 : ℂ)) (differentiableOn_const _) hρc (by simpa using hint1)
    simp only [one_mul] at h
    rw [h]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    simp only [hρ, Nat.add_sub_cancel]
    rw [integral_radial_weight m]
    push_cast
    simp only [Complex.real_smul, mul_one]
    have h1 : (1 : ℂ) + m ≠ 0 := by exact_mod_cast (by omega : 1 + m ≠ 0)
    have h2 : (m : ℂ) + 1 ≠ 0 := by exact_mod_cast (by omega : m + 1 ≠ 0)
    push_cast
    field_simp
    rw [show (m : ℂ) + 2 - 1 = m + 1 by ring, div_self h2]
  rw [integral_upperHalf_eq_disc g]
  rw [setIntegral_congr_fun measurableSet_ball (fun w hw => pairing_cayley hn hw φ)]
  rw [show (fun w => (4 * ((-2 * Complex.I) ^ n)⁻¹ * (φ (cayleyInv w) * ((1 - w) ^ n)⁻¹)) *
      (((1 - ‖w‖ ^ 2) ^ (n - 2) : ℝ) : ℂ)) = fun w => k w * (ρ ‖w‖ : ℂ) from rfl]
  rw [hmv, hrad]
  have h0 : cayleyInv 0 = Complex.I := by simp [cayleyInv]
  simp only [hk, h0, sub_zero, one_pow, inv_one, mul_one]
  push_cast
  ring

end Lightlike.Lorentz.SL2RPlancherel
