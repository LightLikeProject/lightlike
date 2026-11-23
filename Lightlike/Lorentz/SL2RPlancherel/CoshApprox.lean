import Mathlib

/-!
# Approximation of even smooth functions by polynomials in `cosh t`

For a smooth even `h : ℝ → ℝ`, the odd function `h'` is `k · sinh` with `k` continuous and even
(`exists_quotient_sinh`).  Together with Weierstrass' theorem this gives polynomials `q` such that
`q (cosh t)` approximates `h` together with its derivative, uniformly on a compact interval
(`exists_poly_cosh_approx`).  This is a step in the surjectivity of the spherical Plancherel
isometry for `SL(2,ℝ)` (milestone HA3): it avoids Whitney's theorem on even smooth functions.
-/

open Set Real Polynomial
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- Every real polynomial has a polynomial antiderivative. -/
theorem exists_polynomial_derivative_eq (p : ℝ[X]) : ∃ q : ℝ[X], derivative q = p := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hr
    exact ⟨a + b, by rw [derivative_add, ha, hb]⟩
  | monomial n c =>
    refine ⟨C (c / (n + 1)) * X ^ (n + 1), ?_⟩
    rw [derivative_C_mul_X_pow, ← C_mul_X_pow_eq_monomial]
    congr 2
    push_cast
    field_simp

/-- Hadamard's lemma for `C¹` functions: `f t - f 0 = t ∫₀¹ f'(s t) ds`. -/
theorem sub_eq_mul_integral (f : ℝ → ℝ) (t : ℝ) (hf : ContDiff ℝ 1 f) :
    f t - f 0 = t * ∫ s in (0 : ℝ)..1, deriv f (t * s) := by
  by_cases ht : t = 0
  · simp [ht]
  · rw [intervalIntegral.integral_comp_mul_left (fun x => deriv f x) ht]
    have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
    have := intervalIntegral.integral_deriv_eq_sub (f := f) (a := t * 0) (b := t * 1)
      (fun x _ => hd x) ((hf.continuous_deriv (by norm_num)).intervalIntegrable _ _)
    simp only [mul_zero, mul_one] at this ⊢
    rw [this, smul_eq_mul]
    field_simp

/-- For `h` smooth and even, `h' = k · sinh` with `k` continuous and even. -/
theorem exists_quotient_sinh (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h) (he : ∀ t, h (-t) = h t) :
    ∃ k : ℝ → ℝ, Continuous k ∧ (∀ t, k (-t) = k t) ∧ ∀ t, deriv h t = k t * Real.sinh t := by
  have hd : ContDiff ℝ ∞ (deriv h) := (contDiff_infty_iff_deriv.1 hh).2
  have hdd : Continuous (deriv h) := hd.continuous
  have hodd : ∀ t, deriv h (-t) = - deriv h t := by
    intro t
    have h1 : h = fun x => h (-x) := funext fun x => (he x).symm
    have h2 : deriv h t = - deriv h (-t) := by
      conv_lhs => rw [h1]
      rw [deriv_comp_neg]
    linarith
  have h0 : deriv h 0 = 0 := by
    have := hodd 0
    simp only [neg_zero] at this
    linarith
  set m : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..1, deriv (deriv h) (t * s) with hm
  set c : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..1, Real.cosh (t * s) with hc
  have hdd' : Continuous (deriv (deriv h)) :=
    (contDiff_infty_iff_deriv.1 hd).2.continuous
  have hmc : Continuous m := by
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun t s => deriv (deriv h) (t * s)) ?_ 0 1
    exact hdd'.comp (by fun_prop)
  have hcc : Continuous c := by
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun t s => Real.cosh (t * s)) ?_ 0 1
    exact Real.continuous_cosh.comp (by fun_prop)
  have hc1 : ∀ t, 1 ≤ c t := by
    intro t
    have : ∫ s in (0 : ℝ)..1, (1 : ℝ) ≤ ∫ s in (0 : ℝ)..1, Real.cosh (t * s) := by
      have hcont : Continuous fun s : ℝ => Real.cosh (t * s) :=
        Real.continuous_cosh.comp (continuous_const.mul continuous_id)
      refine intervalIntegral.integral_mono_on (by norm_num) (by simp)
        (hcont.intervalIntegrable 0 1) (fun s _ => ?_)
      exact Real.one_le_cosh _
    simpa using this
  have hm_eq : ∀ t, deriv h t = t * m t := by
    intro t
    have := sub_eq_mul_integral (deriv h) t (hd.of_le (by norm_num))
    rw [h0, sub_zero] at this
    exact this
  have hs_eq : ∀ t, Real.sinh t = t * c t := by
    intro t
    have := sub_eq_mul_integral Real.sinh t Real.contDiff_sinh
    rw [Real.deriv_sinh, Real.sinh_zero, sub_zero] at this
    exact this
  have hcpos : ∀ t, 0 < c t := fun t => lt_of_lt_of_le one_pos (hc1 t)
  refine ⟨fun t => m t / c t, hmc.div hcc (fun t => (hcpos t).ne'), ?_, ?_⟩
  · intro t
    by_cases ht : t = 0
    · simp [ht]
    · have h1 : deriv h t = m t / c t * Real.sinh t := by
        rw [hm_eq, hs_eq]
        field_simp [(hcpos t).ne']
      have h2 : deriv h (-t) = m (-t) / c (-t) * Real.sinh (-t) := by
        rw [hm_eq, hs_eq]
        field_simp [(hcpos (-t)).ne']
      have hsinh : Real.sinh t ≠ 0 := by
        rw [Ne, Real.sinh_eq_zero]; exact ht
      rw [hodd, h1, Real.sinh_neg] at h2
      have : m (-t) / c (-t) * Real.sinh t = m t / c t * Real.sinh t := by linarith
      exact mul_right_cancel₀ hsinh this
  · intro t
    show deriv h t = m t / c t * Real.sinh t
    rw [hm_eq, hs_eq]
    field_simp [(hcpos t).ne']

/-- **Weierstrass approximation in the variable `cosh t`**: a smooth even `h` is approximated,
together with its derivative, uniformly on `[-T, T]` by `q (cosh t)`, `q` a real polynomial. -/
theorem exists_poly_cosh_approx (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h) (he : ∀ t, h (-t) = h t)
    (T ε : ℝ) (hT : 0 ≤ T) (hε : 0 < ε) :
    ∃ q : ℝ[X], ∀ t ∈ Icc (-T) T, |q.eval (Real.cosh t) - h t| ≤ ε ∧
      |deriv (fun s => q.eval (Real.cosh s)) t - deriv h t| ≤ ε := by
  obtain ⟨k, hk, hke, hkd⟩ := exists_quotient_sinh h hh he
  set V : ℝ := Real.cosh T with hV
  set S : ℝ := Real.sinh T with hS
  have hS0 : 0 ≤ S := Real.sinh_nonneg_iff.2 hT
  set δ : ℝ := ε / ((1 + T) * (1 + S)) with hδ
  have hδpos : 0 < δ := by positivity
  have hδS : δ * S ≤ ε := by
    rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hT hS0, mul_pos hε hε]
  have hTδS : T * (δ * S) ≤ ε := by
    rw [hδ, show T * (ε / ((1 + T) * (1 + S)) * S) = ε * (T * S) / ((1 + T) * (1 + S)) by ring,
      div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hT hS0, mul_pos hε hε]
  have hKc : ContinuousOn (fun v => k (Real.arcosh v)) (Icc 1 V) :=
    hk.comp_continuousOn (Real.continuousOn_arcosh.mono Icc_subset_Ici_self)
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 1 V _ hKc δ hδpos
  obtain ⟨q0, hq0⟩ := exists_polynomial_derivative_eq p
  set q : ℝ[X] := q0 + C (h 0 - q0.eval 1) with hq
  have hqd : derivative q = p := by rw [hq, derivative_add, derivative_C, add_zero, hq0]
  refine ⟨q, fun t ht => ?_⟩
  have hg : ∀ x, HasDerivAt (fun s => q.eval (Real.cosh s)) (p.eval (Real.cosh x) * Real.sinh x) x := by
    intro x
    have := (q.hasDerivAt (Real.cosh x)).comp x (Real.hasDerivAt_cosh x)
    rw [hqd] at this
    exact this
  have hht : ∀ x, DifferentiableAt ℝ h x := fun x => hh.differentiable (by simp) x
  have habs : ∀ x ∈ Icc (-T) T, |x| ≤ T := fun x hx => abs_le.2 ⟨hx.1, hx.2⟩
  have hcosh : ∀ x ∈ Icc (-T) T, Real.cosh x ∈ Icc 1 V := fun x hx =>
    ⟨Real.one_le_cosh x, Real.cosh_le_cosh.2 (by rw [abs_of_nonneg hT]; exact habs x hx)⟩
  have hkx : ∀ x, k (Real.arcosh (Real.cosh x)) = k x := by
    intro x
    rw [← Real.cosh_abs, Real.arcosh_cosh (abs_nonneg x)]
    rcases abs_cases x with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1]
    · rw [h1, hke]
  have hderiv : ∀ x ∈ Icc (-T) T,
      |deriv (fun s => q.eval (Real.cosh s)) x - deriv h x| ≤ δ * S := by
    intro x hx
    rw [(hg x).deriv, hkd x, ← sub_mul, abs_mul]
    have h1 := hp _ (hcosh x hx)
    rw [hkx] at h1
    have h2 : |Real.sinh x| ≤ S := by
      rw [Real.abs_sinh, hS]
      exact Real.sinh_le_sinh.2 (habs x hx)
    exact mul_le_mul h1.le h2 (abs_nonneg _) hδpos.le
  have hD0 : q.eval (Real.cosh 0) - h 0 = 0 := by
    simp [hq]
  have hmvt : |q.eval (Real.cosh t) - h t| ≤ δ * S * |t| := by
    have hconv : Convex ℝ (Icc (-T) T) := convex_Icc _ _
    have h0m : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, hT⟩
    have := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := fun s => q.eval (Real.cosh s) - h s) (C := δ * S)
      (fun x _ => (hg x).differentiableAt.sub (hht x))
      (fun x hx => by
        have h1 := hderiv x hx
        rw [(hg x).deriv] at h1
        have hs : HasDerivAt (fun s => q.eval (Real.cosh s) - h s)
            (p.eval (Real.cosh x) * Real.sinh x - deriv h x) x := (hg x).sub (hht x).hasDerivAt
        rw [hs.deriv, Real.norm_eq_abs]
        exact h1) hconv h0m ht
    simp only [Real.norm_eq_abs, hD0, sub_zero] at this
    exact this
  have hfin : |q.eval (Real.cosh t) - h t| ≤ ε := by
    have h3 : δ * S * |t| ≤ δ * S * T :=
      mul_le_mul_of_nonneg_left (habs t ht) (by positivity)
    nlinarith
  exact ⟨hfin, (hderiv t ht).trans hδS⟩

end Lightlike.Lorentz.SL2RPlancherel
