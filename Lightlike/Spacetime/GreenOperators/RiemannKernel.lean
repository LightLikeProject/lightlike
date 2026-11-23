import Mathlib
import Lightlike.Spacetime.GreenOperators.Primitive
import Lightlike.Spacetime.GreenOperators.Bessel

/-!
# The Riemann kernel of the Klein–Gordon operator on `1+1` Minkowski space

Supporting file for G1-021 (SC6; Bär–Ginoux–Pfäffle 2007, source key `bgp-2007`).
In null coordinates `(a, b) = (t - x, t + x)` the operator `-∂ₜ² + ∂ₓ² - m²` is `-4 ∂ₐ ∂_b - m²`.
With `c = -m²/4` the *Riemann kernel* is `riemannKernel c (s, r) = 1_{s, r ≥ 0} · φ(s r)`,
`φ = besselPhi c`.  The identity
`φ(σ ρ) = 1 + c ∫₀^σ ∫₀^ρ φ(s r) dr ds` (`besselPhi_eq_one_add`; two applications of the fundamental
theorem of calculus and the ODE `z φ'' + φ' = c φ`) says `K = 1_Q + c · (1_Q ⋆ K)`
(`riemannKernel_eq`), which is the integral form of `K_{ab} = δ + c K`.

This is a supporting result; no catalogue entry.
-/

open Set MeasureTheory
open scoped Convolution

namespace Lightlike.GreenOperators

/-- The Riemann kernel `1_{s, r ≥ 0} · φ(s r)` with `φ = besselPhi c`. -/
noncomputable def riemannKernel (c : ℝ) : ℝ × ℝ → ℝ :=
  (Ici (0 : ℝ × ℝ)).indicator fun q => besselPhi c (q.1 * q.2)

lemma riemannKernel_locallyIntegrable (c : ℝ) :
    LocallyIntegrable (riemannKernel c) (volume : Measure (ℝ × ℝ)) := by
  have hc : Continuous fun q : ℝ × ℝ => besselPhi c (q.1 * q.2) :=
    (contDiff_besselPhi c).continuous.comp (continuous_fst.mul continuous_snd)
  exact hc.locallyIntegrable.indicator measurableSet_Ici

/-- The inner integral: `∫₀^ρ c φ(s r) dr = ρ φ'(s ρ)`. -/
lemma integral_besselPhi_inner (c s ρ : ℝ) :
    ∫ r in (0 : ℝ)..ρ, c * besselPhi c (s * r) = ρ * besselPhi1 c (s * ρ) := by
  have hc : Continuous (besselPhi c) := (contDiff_besselPhi c).continuous
  have hd : ∀ r ∈ uIcc (0 : ℝ) ρ,
      HasDerivAt (fun r => r * besselPhi1 c (s * r)) (c * besselPhi c (s * r)) r := by
    intro r _
    have h1 : HasDerivAt (fun r => besselPhi1 c (s * r)) (besselPhi2 c (s * r) * s) r := by
      have := (hasDerivAt_besselPhi1 c (s * r)).comp r ((hasDerivAt_id r).const_mul s)
      simp only [mul_one] at this
      exact this
    have h := (hasDerivAt_id r).mul h1
    have := besselPhi_ode c (s * r)
    refine h.congr_deriv ?_
    simp only [id]
    linarith
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuous_const.mul (hc.comp (by fun_prop))).intervalIntegrable _ _)]
  simp

/-- `φ(σ ρ) = 1 + c ∫₀^σ ∫₀^ρ φ(s r) dr ds`. -/
theorem besselPhi_eq_one_add (c σ ρ : ℝ) :
    besselPhi c (σ * ρ) = 1 + c * ∫ s in (0 : ℝ)..σ, ∫ r in (0 : ℝ)..ρ, besselPhi c (s * r) := by
  have hc : Continuous (besselPhi c) := (contDiff_besselPhi c).continuous
  have h1 : c * ∫ s in (0 : ℝ)..σ, ∫ r in (0 : ℝ)..ρ, besselPhi c (s * r)
      = ∫ s in (0 : ℝ)..σ, ρ * besselPhi1 c (s * ρ) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [← integral_besselPhi_inner, intervalIntegral.integral_const_mul]
  have hd : ∀ s ∈ uIcc (0 : ℝ) σ,
      HasDerivAt (fun s => besselPhi c (s * ρ)) (ρ * besselPhi1 c (s * ρ)) s := by
    intro s _
    have h1 : HasDerivAt (fun s : ℝ => s * ρ) ρ s := by
      simpa using (hasDerivAt_id s).mul_const ρ
    have h := (hasDerivAt_besselPhi c (s * ρ)).comp s h1
    refine h.congr_deriv ?_
    ring
  have hcont : Continuous fun s : ℝ => ρ * besselPhi1 c (s * ρ) := by
    have h1' : Continuous (besselPhi1 c) := by
      have : deriv (besselPhi c) = besselPhi1 c :=
        funext fun z => (hasDerivAt_besselPhi c z).deriv
      rw [← this]
      exact (contDiff_besselPhi c).continuous_deriv (by norm_num)
    exact continuous_const.mul (h1'.comp (by fun_prop))
  rw [h1, intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable _ _)]
  simp [besselPhi_zero]

/-- `(1_Q ⋆ K)(p) = ∫₀^{p₁} ∫₀^{p₂} φ(s r)` for `p ≥ 0`, and `0` otherwise. -/
lemma quadKernel_convolution_riemannKernel (c : ℝ) (p : ℝ × ℝ) :
    (quadKernel ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] riemannKernel c) p
      = if (0 : ℝ × ℝ) ≤ p then ∫ s in (0 : ℝ)..p.1, ∫ r in (0 : ℝ)..p.2, besselPhi c (s * r) else 0 := by
  have hΨ : Continuous fun q : ℝ × ℝ => besselPhi c (q.1 * q.2) :=
    (contDiff_besselPhi c).continuous.comp (continuous_fst.mul continuous_snd)
  rw [convolution_def]
  have h1 : ∀ t : ℝ × ℝ, (ContinuousLinearMap.lsmul ℝ ℝ) (quadKernel t) (riemannKernel c (p - t))
      = (Icc (0 : ℝ × ℝ) p).indicator (fun q : ℝ × ℝ => besselPhi c (q.1 * q.2)) (p - t) := by
    intro t
    by_cases ht : (0 : ℝ × ℝ) ≤ t
    · by_cases ht2 : t ≤ p
      · have e1 : (0 : ℝ × ℝ) ≤ p - t := sub_nonneg.mpr ht2
        have e2 : p - t ≤ p := sub_le_self _ ht
        simp [quadKernel, riemannKernel, ht, e1, e2, indicator_of_mem, mem_Icc]
      · have e1 : ¬ (0 : ℝ × ℝ) ≤ p - t := fun h => ht2 (sub_nonneg.mp h)
        simp [quadKernel, riemannKernel, ht, e1, mem_Icc]
    · have e2 : ¬ p - t ≤ p := fun h => ht (by simpa using h)
      simp [quadKernel, riemannKernel, ht, e2, mem_Icc]
  simp_rw [h1]
  rw [integral_sub_left_eq_self (fun q => (Icc (0 : ℝ × ℝ) p).indicator
    (fun q : ℝ × ℝ => besselPhi c (q.1 * q.2)) q) volume p,
    integral_indicator measurableSet_Icc]
  by_cases hp : (0 : ℝ × ℝ) ≤ p
  · simp only [hp, ↓reduceIte]
    have hset : Icc (0 : ℝ × ℝ) p = Icc (0 : ℝ) p.1 ×ˢ Icc (0 : ℝ) p.2 := by
      ext q; simp [Prod.le_def, and_assoc, and_left_comm]
    have hint : IntegrableOn (fun q : ℝ × ℝ => besselPhi c (q.1 * q.2))
        (Icc (0 : ℝ) p.1 ×ˢ Icc (0 : ℝ) p.2) (volume : Measure (ℝ × ℝ)) :=
      hΨ.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    rw [Measure.volume_eq_prod] at hint
    rw [hset, Measure.volume_eq_prod, setIntegral_prod _ hint]
    have hp1 : (0 : ℝ) ≤ p.1 := hp.1
    have hp2 : (0 : ℝ) ≤ p.2 := hp.2
    simp only [intervalIntegral.integral_of_le hp1, intervalIntegral.integral_of_le hp2,
      integral_Icc_eq_integral_Ioc]
  · simp only [hp, ↓reduceIte]
    have : Icc (0 : ℝ × ℝ) p = ∅ := Icc_eq_empty hp
    rw [this]
    simp

/-- `K = 1_Q + c · (1_Q ⋆ K)`: the integral form of `K_{ab} = δ + c K`. -/
theorem riemannKernel_eq (c : ℝ) (p : ℝ × ℝ) :
    riemannKernel c p = quadKernel p
      + c * (quadKernel ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] riemannKernel c) p := by
  rw [quadKernel_convolution_riemannKernel]
  by_cases hp : (0 : ℝ × ℝ) ≤ p
  · have hq : quadKernel p = 1 := by simp [quadKernel, hp]
    simp only [hp, ↓reduceIte]
    rw [hq, ← besselPhi_eq_one_add]
    simp [riemannKernel, hp]
  · simp [riemannKernel, quadKernel, hp]

end Lightlike.GreenOperators
