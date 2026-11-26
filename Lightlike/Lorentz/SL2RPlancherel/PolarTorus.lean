module

public import Mathlib
public import Lightlike.Lorentz.SL2RPlancherel.PolarIntegral

/-!
# The polar integration formula over the full torus of angles

`lintegral_haarR_torus`: for measurable `F : SL(2,ℝ) → [0,∞]`,
`∫ F d haarR = ∫_{ξ>0} sinh ξ ∫_0^{2π} ∫_0^{2π} F(k_α a(ξ) k_θ) dθ dα dξ`.
It follows from `lintegral_haarR_polar` (angle `α ∈ (-π/2, π/2)`), since
`(α, θ) ↦ k_α a(ξ) k_θ` is invariant under `(α, θ) ↦ (α + π, θ + π)`, so the integral over the
full torus is twice that over the half.  Layer 2b of the Plancherel formula on `SL(2,ℝ)`.
-/

@[expose] public section

open MeasureTheory Set Real

noncomputable section

namespace Lightlike.Lorentz.SL2R

lemma rot_pi_mul_comm_aR (ξ : ℝ) : rot π * aR ξ = aR ξ * rot π := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [aR, diagSL, Matrix.mul_apply, Fin.sum_univ_two]

lemma rot_pi_mul_rot_pi : rot π * rot π = 1 := by
  rw [← rot_add, ← two_mul]
  have := rot_periodic 0
  simpa using this

lemma continuous_aR : Continuous aR := by
  refine Continuous.subtype_mk ?_ _
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [← Real.exp_neg] <;> fun_prop

/-- Shifting the first angle by `π` does not change the circle integral. -/
lemma lintegral_theta_add_pi (F : SL2R → ENNReal) (ξ α : ℝ) :
    ∫⁻ θ in Ioc 0 (2 * π), F (rot (α + π) * aR ξ * rot θ) =
      ∫⁻ θ in Ioc 0 (2 * π), F (rot α * aR ξ * rot θ) := by
  have e : ∀ θ : ℝ, rot (α + π) * aR ξ * rot θ = rot α * aR ξ * rot (π + θ) := fun θ => by
    rw [rot_add, rot_add, mul_assoc (rot α), rot_pi_mul_comm_aR, mul_assoc, mul_assoc, mul_assoc]
  simp_rw [e]
  exact lintegral_rot_add (fun h => F (rot α * aR ξ * h)) π

/-- A `π`-periodic function has the same integral over every interval of length `π`. -/
lemma lintegral_Ioc_periodic (K : ℝ → ENNReal) (hK : ∀ α, K (α + π) = K α) (a : ℝ) :
    ∫⁻ α in Ioc a (a + π), K α = ∫⁻ α in Ioc 0 (0 + π), K α := by
  have : Fact (0 < π) := ⟨Real.pi_pos⟩
  have hper : Function.Periodic K π := hK
  let f : AddCircle π → ENNReal := fun x => hper.lift x
  have h1 := AddCircle.lintegral_preimage π a f
  have h2 := AddCircle.lintegral_preimage π 0 f
  have e : ∀ x : ℝ, f x = K x := fun x => rfl
  simp only [e] at h1 h2
  rw [h1, h2]

lemma lintegral_Ioc_two_pi (K : ℝ → ENNReal) (hK : ∀ α, K (α + π) = K α) :
    ∫⁻ α in Ioc 0 (2 * π), K α = 2 * ∫⁻ α in Ioc (-(π / 2)) (-(π / 2) + π), K α := by
  have hsplit : Ioc 0 (2 * π) = Ioc 0 π ∪ Ioc π (2 * π) := by
    rw [Ioc_union_Ioc_eq_Ioc Real.pi_pos.le (by linarith [Real.pi_pos])]
  rw [hsplit, lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl)]
  have h2 := lintegral_Ioc_periodic K hK π
  have h3 := lintegral_Ioc_periodic K hK (-(π / 2))
  rw [show 2 * π = π + π by ring, h2, zero_add, h3.trans (by rw [zero_add])]
  rw [two_mul]


/-- **Polar integration formula over the full torus of angles.** -/
theorem lintegral_haarR_torus {F : SL2R → ENNReal} (hF : Measurable F) :
    ∫⁻ g, F g ∂haarR =
      ∫⁻ ξ in Ioi (0 : ℝ), ENNReal.ofReal (Real.sinh ξ) *
        ∫⁻ α in Ioc 0 (2 * π), ∫⁻ θ in Ioc 0 (2 * π), F (rot α * aR ξ * rot θ) := by
  set Θ : ℝ → ℝ → ENNReal := fun ξ α => ∫⁻ θ in Ioc 0 (2 * π), F (rot α * aR ξ * rot θ) with hΘ
  have hcont : Continuous fun p : (ℝ × ℝ) × ℝ => rot p.1.2 * aR p.1.1 * rot p.2 :=
    ((continuous_rot.comp (continuous_snd.comp continuous_fst)).mul
      (continuous_aR.comp (continuous_fst.comp continuous_fst))).mul
      (continuous_rot.comp continuous_snd)
  have hΘm : Measurable (Function.uncurry Θ) := by
    have : Measurable fun p : (ℝ × ℝ) × ℝ => F (rot p.1.2 * aR p.1.1 * rot p.2) :=
      hF.comp hcont.measurable
    exact this.lintegral_prod_right'
  have hsinh : Measurable fun ξ : ℝ => ENNReal.ofReal (Real.sinh ξ) := by fun_prop
  rw [lintegral_haarR_polar hF]
  have hper : ∀ ξ α, Θ ξ (α + π) = Θ ξ α := fun ξ α => lintegral_theta_add_pi F ξ α
  have step : ∀ ξ, 2 * ∫⁻ α in Ioo (-(π / 2)) (π / 2), Θ ξ α =
      ∫⁻ α in Ioc 0 (2 * π), Θ ξ α := by
    intro ξ
    rw [lintegral_Ioc_two_pi (Θ ξ) (hper ξ)]
    congr 1
    rw [setLIntegral_congr Ioo_ae_eq_Ioc]
    congr 2 <;> ring
  have h1 : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (Real.sinh p.2) :=
    hsinh.comp measurable_snd
  have h2 : Measurable fun p : ℝ × ℝ => Θ p.2 p.1 := by
    have := hΘm.comp (measurable_swap (α := ℝ) (β := ℝ))
    exact this
  have hswap : Measurable (Function.uncurry fun (α ξ : ℝ) =>
      ENNReal.ofReal (Real.sinh ξ) * Θ ξ α) := h1.mul h2
  have hs := lintegral_lintegral_swap (μ := volume.restrict (Ioo (-(π / 2)) (π / 2)))
    (ν := volume.restrict (Ioi (0 : ℝ))) hswap.aemeasurable
  rw [hs]
  have key : ∀ ξ : ℝ, 2 * ∫⁻ x in Ioo (-(π / 2)) (π / 2), ENNReal.ofReal (Real.sinh ξ) * Θ ξ x =
      ENNReal.ofReal (Real.sinh ξ) * ∫⁻ α in Ioc 0 (2 * π), Θ ξ α := by
    intro ξ
    have hm : Measurable (fun α => Θ ξ α) := hΘm.of_uncurry_left
    rw [lintegral_const_mul _ hm, ← step ξ, mul_left_comm]
  rw [← lintegral_const_mul' (2 : ENNReal) _ ENNReal.ofNat_ne_top]
  exact lintegral_congr key

end Lightlike.Lorentz.SL2R
