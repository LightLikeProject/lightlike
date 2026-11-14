module

public import Mathlib

/-!
# Hadamard's lemma and smooth parametric integrals

* `contDiff_intervalIntegral_param`: if `h : E × ℝ → F` is smooth, then so is
  `x ↦ ∫₀¹ h(x, t) dt` (`E` finite-dimensional). Mathlib differentiates under the integral sign
  once (`intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`); smoothness follows
  by induction on the order, since the derivative is again a parametric integral
  (`hasFDerivAt_intervalIntegral_param`).
* `hadamard`: a smooth `f : ℝⁿ → ℂ` satisfies `f(x) = f(0) + ∑ᵢ xᵢ fᵢ(x)` with smooth
  `fᵢ(x) = ∫₀¹ ∂ᵢf(t x) dt` (`hadamardCoeff`), and `fᵢ(0) = ∂ᵢf(0)` (`hadamardCoeff_zero`).
  This is the form of Taylor's formula used in the proof of Hörmander, *The Analysis of Linear
  Partial Differential Operators I*, Theorem 7.7.5, to write a phase as its quadratic part plus
  a sum of cubic terms.
-/

@[expose] public section

namespace Lightlike.Oscillatory


open MeasureTheory Set Filter
open scoped ContDiff Topology

/-! ### Smoothness of parametric integrals over `[0, 1]` -/

section Param

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The partial derivative in the first variable of `h : E → ℝ → F`. -/
noncomputable def paramDeriv (h : E → ℝ → F) (x : E) (t : ℝ) : E →L[ℝ] F :=
  (fderiv ℝ (fun p : E × ℝ => h p.1 p.2) (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)

/-- `paramDeriv h x t` is the derivative of `y ↦ h y t` at `x`. -/
theorem hasFDerivAt_paramDeriv {h : E → ℝ → F} {k : ℕ}
    (hh : ContDiff ℝ (k + 1) (fun p : E × ℝ => h p.1 p.2)) (x : E) (t : ℝ) :
    HasFDerivAt (fun y => h y t) (paramDeriv h x t) x := by
  have hd : DifferentiableAt ℝ (fun p : E × ℝ => h p.1 p.2) (x, t) :=
    (hh.differentiable (by simp)).differentiableAt
  have hl : HasFDerivAt (fun y : E => (y, t)) (ContinuousLinearMap.inl ℝ E ℝ) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const t x)
  exact hd.hasFDerivAt.comp x hl

/-- The partial derivative of a `C^{k+1}` function is `C^k` in both variables. -/
theorem contDiff_paramDeriv {h : E → ℝ → F} {k : ℕ}
    (hh : ContDiff ℝ (k + 1) (fun p : E × ℝ => h p.1 p.2)) :
    ContDiff ℝ k (fun p : E × ℝ => paramDeriv h p.1 p.2) := by
  unfold paramDeriv
  have h1 : ContDiff ℝ k (fderiv ℝ (fun p : E × ℝ => h p.1 p.2)) :=
    hh.fderiv_right (by exact_mod_cast le_rfl)
  exact h1.clm_comp contDiff_const

/-- Differentiation under the integral sign over `[0, 1]`. -/
theorem hasFDerivAt_intervalIntegral_param [FiniteDimensional ℝ E] [CompleteSpace F]
    {h : E → ℝ → F} {k : ℕ}
    (hh : ContDiff ℝ (k + 1) (fun p : E × ℝ => h p.1 p.2)) (x₀ : E) :
    HasFDerivAt (fun x => ∫ t in (0 : ℝ)..1, h x t)
      (∫ t in (0 : ℝ)..1, paramDeriv h x₀ t) x₀ := by
  have hc : Continuous (fun p : E × ℝ => h p.1 p.2) := hh.continuous
  have hD : Continuous (fun p : E × ℝ => paramDeriv h p.1 p.2) :=
    (contDiff_paramDeriv hh).continuous
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x₀ 1).prod isCompact_Icc).exists_bound_of_continuousOn
    (hD.continuousOn (s := Metric.closedBall x₀ 1 ×ˢ Icc (0 : ℝ) 1))
  have hct : ∀ x, Continuous (fun t => h x t) := fun x =>
    hc.comp (continuous_const.prodMk continuous_id)
  have hDt : ∀ x, Continuous (fun t => paramDeriv h x t) := fun x =>
    hD.comp (continuous_const.prodMk continuous_id)
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume)
    (bound := fun _ => C) (Metric.ball_mem_nhds x₀ one_pos)
    (Eventually.of_forall fun x => (hct x).aestronglyMeasurable)
    ((hct x₀).intervalIntegrable 0 1) (hDt x₀).aestronglyMeasurable ?_
    intervalIntegrable_const ?_
  · refine Eventually.of_forall fun t ht x hx => hC (x, t) ⟨Metric.ball_subset_closedBall hx, ?_⟩
    rw [uIoc_of_le zero_le_one] at ht
    exact Ioc_subset_Icc_self ht
  · exact Eventually.of_forall fun t _ x _ => hasFDerivAt_paramDeriv hh x t

/-- A parametric integral over `[0, 1]` of a `C^k` function is `C^k`. -/
theorem contDiff_intervalIntegral_param_nat [FiniteDimensional ℝ E] (k : ℕ) :
    ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {h : E → ℝ → F},
      ContDiff ℝ k (fun p : E × ℝ => h p.1 p.2) →
        ContDiff ℝ k (fun x => ∫ t in (0 : ℝ)..1, h x t) := by
  induction k with
  | zero =>
    intro F _ _ _ h hh
    rw [Nat.cast_zero, contDiff_zero] at hh ⊢
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hh 0 1
  | succ k ih =>
    intro F _ _ _ h hh
    have hh' : ContDiff ℝ ((k : WithTop ℕ∞) + 1) (fun p : E × ℝ => h p.1 p.2) := by
      exact_mod_cast hh
    have hf : ∀ x₀, HasFDerivAt (fun x => ∫ t in (0 : ℝ)..1, h x t)
        (∫ t in (0 : ℝ)..1, paramDeriv h x₀ t) x₀ :=
      hasFDerivAt_intervalIntegral_param hh'
    have hfd : fderiv ℝ (fun x => ∫ t in (0 : ℝ)..1, h x t) =
        fun x₀ => ∫ t in (0 : ℝ)..1, paramDeriv h x₀ t := funext fun x₀ => (hf x₀).fderiv
    rw [show ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiff_succ_iff_fderiv]
    refine ⟨fun x₀ => (hf x₀).differentiableAt, by simp, ?_⟩
    rw [hfd]
    exact ih (contDiff_paramDeriv hh')

/-- A parametric integral over `[0, 1]` of a smooth function is smooth. -/
theorem contDiff_intervalIntegral_param [FiniteDimensional ℝ E] [CompleteSpace F]
    {h : E → ℝ → F}
    (hh : ContDiff ℝ ∞ (fun p : E × ℝ => h p.1 p.2)) :
    ContDiff ℝ ∞ (fun x => ∫ t in (0 : ℝ)..1, h x t) :=
  contDiff_infty.mpr fun k => contDiff_intervalIntegral_param_nat k
    (hh.of_le (by exact_mod_cast le_top))

end Param

/-! ### Hadamard's lemma -/

variable {n : ℕ}

/-- The `i`-th coefficient in Hadamard's lemma, `∫₀¹ ∂ᵢf(t x) dt`. -/
noncomputable def hadamardCoeff (f : (Fin n → ℝ) → ℂ) (i : Fin n) (x : Fin n → ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1, fderiv ℝ f (t • x) (Pi.single i 1)

/-- The Hadamard coefficients of a smooth function are smooth. -/
theorem contDiff_hadamardCoeff {f : (Fin n → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f) (i : Fin n) :
    ContDiff ℝ ∞ (hadamardCoeff f i) := by
  unfold hadamardCoeff
  apply contDiff_intervalIntegral_param
  have h1 : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have h2 : ContDiff ℝ ∞ (fun p : (Fin n → ℝ) × ℝ => p.2 • p.1) := contDiff_snd.smul contDiff_fst
  exact (h1.comp h2).clm_apply contDiff_const

/-- At the origin the Hadamard coefficient is the partial derivative: `fᵢ(0) = ∂ᵢf(0)`. -/
theorem hadamardCoeff_zero (f : (Fin n → ℝ) → ℂ) (i : Fin n) :
    hadamardCoeff f i 0 = fderiv ℝ f 0 (Pi.single i 1) := by
  simp [hadamardCoeff]

/-- **Hadamard's lemma**: `f(x) = f(0) + ∑ᵢ xᵢ fᵢ(x)` with `fᵢ(x) = ∫₀¹ ∂ᵢf(t x) dt`. -/
theorem hadamard {f : (Fin n → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f) (x : Fin n → ℝ) :
    f x = f 0 + ∑ i, (x i : ℂ) * hadamardCoeff f i x := by
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => f (t • x)) (fderiv ℝ f (t • x) x) t := by
    intro t _
    have hl : HasDerivAt (fun t : ℝ => t • x) x t := by
      simpa using (hasDerivAt_id t).smul_const x
    exact (hd (t • x)).hasFDerivAt.comp_hasDerivAt t hl
  have hcont : Continuous (fun t : ℝ => fderiv ℝ f (t • x) x) :=
    ((hf.continuous_fderiv (by simp)).comp (continuous_id.smul continuous_const)).clm_apply
      continuous_const
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 1)
  simp only [one_smul, zero_smul] at hftc
  have hsum : ∀ t : ℝ, fderiv ℝ f (t • x) x =
      ∑ i, (x i : ℂ) * fderiv ℝ f (t • x) (Pi.single i 1) := by
    intro t
    have hx : x = ∑ i, x i • (Pi.single i 1 : Fin n → ℝ) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    calc fderiv ℝ f (t • x) x = fderiv ℝ f (t • x) (∑ i, x i • (Pi.single i 1 : Fin n → ℝ)) := by
          rw [← hx]
      _ = _ := ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Complex.real_smul]
  simp_rw [hsum] at hftc
  rw [intervalIntegral.integral_finsetSum] at hftc
  · simp_rw [intervalIntegral.integral_const_mul] at hftc
    unfold hadamardCoeff
    rw [hftc]
    ring
  · intro i _
    refine Continuous.intervalIntegrable ?_ 0 1
    exact continuous_const.mul (((hf.continuous_fderiv (by simp)).comp
      (continuous_id.smul continuous_const)).clm_apply continuous_const)

end Lightlike.Oscillatory
