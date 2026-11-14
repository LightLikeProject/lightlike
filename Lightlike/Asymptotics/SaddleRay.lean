import Lightlike.Asymptotics.KernelLead
import Lightlike.Asymptotics.UniformValley

/-!
# The rays through the saddle of Racah's kernel

Racah's sum is `−(1/π) Im (Φ(x₂) − Φ(x₁))` for a primitive `Φ` of Racah's kernel `K`
(`racahSum_eq_im_primitive`). After the rescaling `z = N w − 3/2` the primitive
`F(w) = Φ(N w − 3/2)` has `F' = N K(N w − 3/2)`, and on the upper half-plane
`(2π)² N² K(N w − 3/2) = e^{N ψ(w)} P(w) (1 + O(1/N))` (`norm_racahKernel_sub_lead_le`). This file
evaluates the increment of `F` along the two valley rays `t ↦ s + t v` through the saddle `s`:

* `norm_sub_le_of_path`: the mean value bound `‖F(γ b) − F(γ a)‖ ≤ M L (b − a)` along a path of
  speed at most `L` on which `‖F'‖ ≤ M`, with `F` only continuous at the end point.
* `laplace_amp_uniform`: Laplace's method along a tilted valley ray with a Lipschitz amplitude,
  with one constant for all phases, saddles, directions and amplitudes obeying the same bounds.
* `ray_estimate`: along a valley ray of direction `v = ε u₀ (1 + iτ)`,
  `(2π)² N^{3/2} e^{−N ψ(s)} (F(s + r v) − F(s)) = ε P(s) u₀ √(π/‖b‖)/2 + O(N^{−1/2})`, with one
  constant for all data obeying the same bounds.
* `IsEuclid.leadP_mul_saddleDir`, `IsEuclid.norm_saddleCoeff_mul_prod`, `IsEuclid.im_lead_main`:
  the leading term in closed form. For a Euclidean tetrahedron, `P(s) u₀ = e^{−iπ/4}/√Π` with
  `Π = ∏ᵢ |s − Aᵢ|`, and `‖b‖ Π = 12 √V`; hence
  `−(V^{1/4}/(π (2π)²)) Im (e^{iX} P(s) u₀ √(π/‖b‖)) = cos(X + π/4)/(√(12π) (2π)²)`.
-/

open Complex Set Filter Topology MeasureTheory
open scoped Real Interval

namespace Lightlike.Asymptotics

/-! ## A mean value bound along a path -/

/-- **Mean value bound along a path.** Let `γ` be continuous on `[a, b]` with right derivative
`γ'`, `‖γ'‖ ≤ L` on `[a, b)`, and let `F' = f` at the points `γ t`, `t ∈ [a, b)`, with
`‖f (γ t)‖ ≤ M`. If `F` is continuous at the end point `γ b`, then
`‖F (γ b) − F (γ a)‖ ≤ M L (b − a)`. -/
theorem norm_sub_le_of_path {F f : ℂ → ℂ} {γ γ' : ℝ → ℂ} {a b M L : ℝ} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b))
    (hγ' : ∀ t ∈ Ico a b, HasDerivWithinAt γ (γ' t) (Ici t) t)
    (hL : ∀ t ∈ Ico a b, ‖γ' t‖ ≤ L)
    (hF : ∀ t ∈ Ico a b, HasDerivAt F (f (γ t)) (γ t))
    (hM : ∀ t ∈ Ico a b, ‖f (γ t)‖ ≤ M)
    (hFb : ContinuousAt F (γ b)) :
    ‖F (γ b) - F (γ a)‖ ≤ M * L * (b - a) := by
  have hc : ContinuousOn (fun t => F (γ t)) (Icc a b) := by
    intro t ht
    obtain rfl | h := eq_or_lt_of_le ht.2
    · exact hFb.comp_continuousWithinAt (hγ _ ht)
    · exact (hF t ⟨ht.1, h⟩).continuousAt.comp_continuousWithinAt (hγ t ht)
  refine norm_image_sub_le_of_norm_deriv_right_le_segment (f := fun t => F (γ t))
    (f' := fun t => f (γ t) * γ' t) hc
    (fun t ht => (hF t ht).comp_hasDerivWithinAt t (hγ' t ht)) (fun t ht => ?_) b ⟨hab, le_rfl⟩
  rw [norm_mul]
  exact mul_le_mul (hM t ht) (hL t ht) (norm_nonneg _) ((norm_nonneg _).trans (hM t ht))

/-! ## Laplace's method with an amplitude -/

/-- **Laplace's method along a valley ray with an amplitude**, uniform in all data. Fix `r > 0`,
`β > 0`, `K`, `L`, `G`. There is one `C` such that for every phase `ψ = phaseC A B`, saddle `s`,
coefficient `b` with `‖b‖ ≥ β` and unit `u₀` with `b u₀² = −‖b‖`, valley direction
`v = valleyDir u₀ ε τ` (`ε = ±1`, `|τ| ≤ 1/2`) along which the valley bounds hold on `[0, r]`, and
every amplitude `g` continuous on `[0, r]` with `‖g t − g 0‖ ≤ L t` and `‖g 0‖ ≤ G`,
`‖∫₀ʳ g(t) v e^{N(ψ(s + t v) − ψ(s))} dt − g(0) ε u₀ √(π/(N‖b‖))/2‖ ≤ C/N` for all `N > 0`. -/
theorem laplace_amp_uniform {r β K L G : ℝ} (hr : 0 < r) (hβ : 0 < β) :
    ∃ C : ℝ, ∀ (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) (s b u₀ : ℂ) (ε τ : ℝ) (g : ℝ → ℂ),
      ‖u₀‖ = 1 → b * u₀ ^ 2 = -‖b‖ → β ≤ ‖b‖ → ε ^ 2 = 1 → |τ| ≤ 1 / 2 →
      (∀ t ∈ Icc (0 : ℝ) r, 0 < (s + t * valleyDir u₀ ε τ).im ∧
        ‖phaseC A B (s + t * valleyDir u₀ ε τ) - phaseC A B s -
            b * valleyDir u₀ ε τ ^ 2 * t ^ 2‖ ≤ K * t ^ 3 ∧
        (phaseC A B (s + t * valleyDir u₀ ε τ)).re ≤ (phaseC A B s).re - ‖b‖ / 4 * t ^ 2) →
      ContinuousOn g (Icc 0 r) → (∀ t ∈ Icc (0 : ℝ) r, ‖g t - g 0‖ ≤ L * t) → ‖g 0‖ ≤ G →
      ∀ N : ℝ, 0 < N →
        ‖(∫ t in (0 : ℝ)..r, g t * valleyDir u₀ ε τ *
            cexp (N * (phaseC A B (s + t * valleyDir u₀ ε τ) - phaseC A B s))) -
          g 0 * (ε * u₀ * (Real.sqrt (π / (N * ‖b‖)) : ℂ) / 2)‖ ≤ C / N := by
  obtain ⟨C, hC⟩ := Lightlike.Oscillatory.laplace_ray_uniform r β K (β / 4) (L * (3 / 2)) (G * (3 / 2))
    hr hβ (by positivity)
  refine ⟨C, fun A B s b u₀ ε τ g hu hbu hβb hε hτ hray hg hgL hgG N hN => ?_⟩
  have hbn : 0 < ‖b‖ := hβ.trans_le hβb
  have hv := norm_valleyDir_le hu hε hτ
  have hv2 := mul_valleyDir_sq hbu hε τ
  set v := valleyDir u₀ ε τ with hvdef
  have hτ2 : τ ^ 2 ≤ 1 / 4 := by
    have := sq_abs τ
    nlinarith [abs_nonneg τ]
  have ha : -2 * b * v ^ 2 =
      ((2 * ‖b‖ * (1 - τ ^ 2) : ℝ) : ℂ) + ((4 * ‖b‖ * τ : ℝ) : ℂ) * I := by
    push_cast; linear_combination (-2 : ℂ) * hv2
  have key := hC (-2 * b * v ^ 2)
    (fun t => phaseC A B (s + t * v) - phaseC A B s) (fun t => g t * v)
    (by
      rw [ha, add_re, ofReal_re, re_ofReal_mul, I_re, mul_zero, add_zero]
      nlinarith [mul_le_mul_of_nonneg_left hτ2 hbn.le])
    (((continuousOn_phaseC A B).comp (by fun_prop : Continuous fun t : ℝ =>
      s + t * v).continuousOn
        (fun t ht => (hray t ht).1.le)).sub continuousOn_const)
    (hg.mul continuousOn_const)
    (fun t ht => by
      have := (hray t ht).2.1
      convert this using 2; ring)
    (fun t ht => by
      have h1 := (hray t ht).2.2
      have h2 := mul_le_mul_of_nonneg_right hβb (sq_nonneg t)
      rw [sub_re]; nlinarith)
    (fun t ht => by
      show ‖g t * v - g 0 * v‖ ≤ L * (3 / 2) * t
      rw [← sub_mul, norm_mul]
      have h1 := hgL t ht
      calc ‖g t - g 0‖ * ‖v‖ ≤ (L * t) * (3 / 2) :=
            mul_le_mul h1 hv (norm_nonneg _) ((norm_nonneg _).trans h1)
        _ = L * (3 / 2) * t := by ring)
    (by
      show ‖g 0 * v‖ ≤ G * (3 / 2)
      rw [norm_mul]
      exact mul_le_mul hgG hv (norm_nonneg _) ((norm_nonneg _).trans hgG))
    N hN
  -- the leading term
  have hx : 0 < π / (N * ‖b‖) := by positivity
  set q : ℝ := Real.sqrt (π / (N * ‖b‖)) with hqdef
  have hq2 : (q : ℂ) ^ 2 = (π : ℂ) / (N * ‖b‖) := by
    rw [← ofReal_pow, hqdef, Real.sq_sqrt hx.le]; push_cast; ring
  have h1τ : (1 + (τ : ℂ) * I) ≠ 0 := by
    intro h0
    have := congrArg re h0
    simp at this
  set w : ℂ := (q : ℂ) / (1 + τ * I) with hwdef
  have hw : w = ((q / (1 + τ ^ 2) : ℝ) : ℂ) * (1 - τ * I) := by
    have e : (1 - (τ : ℂ) * I) * (1 + τ * I) = 1 + (τ : ℂ) ^ 2 := by
      linear_combination (-(τ : ℂ) ^ 2) * I_sq
    have h2 : (1 + (τ : ℂ) ^ 2) ≠ 0 := by exact_mod_cast (by positivity : (1 + τ ^ 2 : ℝ) ≠ 0)
    rw [hwdef, div_eq_iff h1τ, mul_assoc, e]
    push_cast
    field_simp
  have hwre : 0 < w.re := by
    rw [hw, re_ofReal_mul]
    simp only [sub_re, one_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, sub_zero]
    positivity
  have harg := abs_lt.1 (abs_arg_lt_pi_div_two_iff.2 (Or.inl hwre))
  have e1 : (N : ℂ) * (-2 * b * v ^ 2) / 2 = N * ‖b‖ * (1 + τ * I) ^ 2 := by
    linear_combination (-(N : ℂ)) * hv2 - ((N : ℂ) * ‖b‖ * τ ^ 2) * I_sq
  have hsq : (π : ℂ) / (N * (-2 * b * v ^ 2) / 2) = w ^ 2 := by
    rw [e1, hwdef, div_pow, hq2, div_div]
  have hhalf : (1 / 2 : ℂ) = ((2 : ℕ) : ℂ)⁻¹ := by norm_num
  have hroot : ((π : ℂ) / (N * (-2 * b * v ^ 2) / 2)) ^ (1 / 2 : ℂ) = w := by
    rw [hsq, hhalf]
    exact pow_cpow_nat_inv two_ne_zero (by push_cast; linarith) (by push_cast; linarith)
  have hlead : v * (w / 2) = ε * u₀ * (q : ℂ) / 2 := by
    rw [hwdef, hvdef, valleyDir]
    field_simp
  simp only [hroot] at key
  rw [mul_assoc (g 0), hlead] at key
  exact key

/-! ## Racah's kernel on the upper half-plane -/

/-- Points of the open upper half-plane are not integers. -/
lemma ne_intCast_of_im_pos {z : ℂ} (hz : 0 < z.im) : ∀ n : ℤ, z ≠ n := by
  intro n h
  rw [h, intCast_im] at hz
  exact lt_irrefl _ hz

/-- Racah's kernel is complex differentiable off the integers. -/
lemma differentiableAt_racahKernel (a : Fin 4 → ℕ) (b : Fin 3 → ℕ) {z : ℂ}
    (hz : ∀ n : ℤ, z ≠ n) : DifferentiableAt ℂ (racahKernel a b) z :=
  ((differentiable_racahT a b z).const_mul _).div (by fun_prop) (sin_pi_mul_ne_zero hz)

/-- The rescaling `w ↦ N w − 3/2` multiplies imaginary parts by `N`. -/
lemma im_rescale (N : ℝ) (w : ℂ) : ((N : ℂ) * w - 3 / 2).im = N * w.im := by
  rw [sub_im, im_ofReal_mul]
  norm_num

/-- **The rescaled primitive.** If `Φ' = f` on the closed upper half-plane off the integers, then
`F(w) = Φ(N w − 3/2)` has `F'(w) = N f(N w − 3/2)` on the open upper half-plane (`N > 0`). -/
lemma hasDerivAt_rescale {Φ f : ℂ → ℂ} {N : ℝ} (hN : 0 < N)
    (hΦ : ∀ z : ℂ, 0 ≤ z.im → (∀ n : ℤ, z ≠ n) → HasDerivAt Φ (f z) z) {w : ℂ}
    (hw : 0 < w.im) :
    HasDerivAt (fun w => Φ (N * w - 3 / 2)) (N * f (N * w - 3 / 2)) w := by
  have him : 0 < ((N : ℂ) * w - 3 / 2).im := by rw [im_rescale]; positivity
  have h1 : HasDerivAt (fun w : ℂ => (N : ℂ) * w - 3 / 2) N w := by
    simpa using ((hasDerivAt_id w).const_mul (N : ℂ)).sub_const (3 / 2 : ℂ)
  have := (hΦ _ him.le (ne_intCast_of_im_pos him)).comp w h1
  rwa [mul_comm (f _)] at this

/-! ## The increment of the primitive along a valley ray -/

/-- **The increment of the primitive along a valley ray**, uniform in all data. Fix `r, β, y > 0`
and `K`, `R`. There is one `C` such that the following holds. Let `ψ = phaseC A B` with
`N Aᵢ = aᵢ + 3/2`, `N Bₖ = b'ₖ + 2` for natural `a, b'`, `Σ A = Σ B` and `N ≥ 1` large compared
with `R` and `1/y` (the hypotheses of `norm_racahKernel_sub_lead_le`). Let `v = valleyDir u₀ ε τ`
be a valley direction at `s` along which the valley bounds hold on `[0, r]`, with
`Im (s + t v) ≥ y` and `|s + t v|, |s + t v − Aᵢ|, |s + t v − Bₖ| ≤ R`. If
`F' = N K(N w − 3/2)` on the upper half-plane, with `K` Racah's kernel of `a, b'`, then
`‖(2π)² N^{3/2} e^{−N ψ(s)} (F(s + r v) − F(s)) − ε P(s) u₀ √(π/‖b‖)/2‖ ≤ C/√N`. -/
theorem ray_estimate {r β K y R : ℝ} (hr : 0 < r) (hβ : 0 < β) (hy : 0 < y) :
    ∃ C : ℝ, ∀ (a : Fin 4 → ℕ) (b' : Fin 3 → ℕ) (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) (s b u₀ : ℂ)
      (ε τ N : ℝ) (F : ℂ → ℂ),
      ‖u₀‖ = 1 → b * u₀ ^ 2 = -‖b‖ → β ≤ ‖b‖ → ε ^ 2 = 1 → |τ| ≤ 1 / 2 →
      (∀ t ∈ Icc (0 : ℝ) r, 0 < (s + t * valleyDir u₀ ε τ).im ∧
        ‖phaseC A B (s + t * valleyDir u₀ ε τ) - phaseC A B s -
            b * valleyDir u₀ ε τ ^ 2 * t ^ 2‖ ≤ K * t ^ 3 ∧
        (phaseC A B (s + t * valleyDir u₀ ε τ)).re ≤ (phaseC A B s).re - ‖b‖ / 4 * t ^ 2) →
      (∀ t ∈ Icc (0 : ℝ) r, y ≤ (s + t * valleyDir u₀ ε τ).im ∧
        ‖s + t * valleyDir u₀ ε τ‖ ≤ R ∧ (∀ i, ‖s + t * valleyDir u₀ ε τ - A i‖ ≤ R) ∧
        ∀ k, ‖s + t * valleyDir u₀ ε τ - B k‖ ≤ R) →
      (∀ i, N * A i = a i + 3 / 2) → (∀ k, N * B k = b' k + 2) → ∑ i, A i = ∑ k, B k →
      1 ≤ N → 2 * (R + 1) ≤ N * y ^ 2 → 12 * ((R + 1) / y) ^ 2 + 4 ≤ N * y →
      (∀ w : ℂ, 0 < w.im → HasDerivAt F (N * racahKernel a b' (N * w - 3 / 2)) w) →
      ‖(((2 * π) ^ 2 * N * √N : ℝ) : ℂ) * cexp (-(N * phaseC A B s)) *
          (F (s + r * valleyDir u₀ ε τ) - F s) -
        ε * (leadP A s * u₀ * (√(π / ‖b‖) : ℂ)) / 2‖ ≤ C / √N := by
  obtain ⟨Cl, hCl⟩ := laplace_amp_uniform (K := K) (L := 3 / y ^ 3) (G := 1 / y ^ 2) hr hβ
  refine ⟨Cl + r * (3 / 2) * kernelLeadC y R / y ^ 2, ?_⟩
  intro a b' A B s b u₀ ε τ N F hu hbu hβb hε hτ hray hbd hA hB hAB hN1 hN hNE hF
  have hv := norm_valleyDir_le hu hε hτ
  set v := valleyDir u₀ ε τ with hvdef
  have hbn : 0 < ‖b‖ := hβ.trans_le hβb
  have hN0 : 0 < N := one_pos.trans_le hN1
  have hsN : 0 < √N := Real.sqrt_pos.2 hN0
  have hk : 0 ≤ kernelLeadC y R / N := by unfold kernelLeadC; positivity
  have hmem : ∀ t ∈ Icc (0 : ℝ) r, 0 < (s + t * v).im := fun t ht => hy.trans_le (hbd t ht).1
  have h0 : s + ((0 : ℝ) : ℂ) * v = s := by simp
  have hs : y ≤ s.im := by simpa using (hbd 0 ⟨le_rfl, hr.le⟩).1
  -- continuity along the ray
  have hKc : ContinuousOn (fun t : ℝ => racahKernel a b' (N * (s + t * v) - 3 / 2))
      (Icc 0 r) := by
    intro t ht
    have him : 0 < ((N : ℂ) * (s + t * v) - 3 / 2).im := by
      rw [im_rescale]; exact mul_pos hN0 (hmem t ht)
    exact ((differentiableAt_racahKernel a b' (ne_intCast_of_im_pos him)).continuousAt.comp
      (f := fun t : ℝ => (N : ℂ) * (s + t * v) - 3 / 2) (by fun_prop)).continuousWithinAt
  have hPc : ContinuousOn (fun t : ℝ => leadP A (s + t * v)) (Icc 0 r) := by
    intro t ht
    exact ((hasDerivAt_leadP A (hmem t ht)).continuousAt.comp
      (f := fun t : ℝ => s + t * v) (by fun_prop)).continuousWithinAt
  have hψc : ContinuousOn (fun t : ℝ => phaseC A B (s + t * v)) (Icc 0 r) :=
    (continuousOn_phaseC A B).comp (by fun_prop : Continuous fun t : ℝ => s + t * v).continuousOn
      (fun t ht => (hmem t ht).le)
  -- the ray as an integral
  have hray_eq := primitive_sub_eq_integral (U := {w : ℂ | 0 < w.im})
    (f := fun w => (N : ℂ) * racahKernel a b' (N * w - 3 / 2)) (fun w hw => hF w hw) hr.le hmem
    (continuousOn_const.mul hKc)
  beta_reduce at hray_eq
  set E := cexp (-(N * phaseC A B s)) with hE
  have hfun : (fun t : ℝ => (2 * (π : ℂ)) ^ 2 * (N : ℂ) ^ 2 *
        racahKernel a b' (N * (s + t * v) - 3 / 2) * E * v) =
      fun t : ℝ => ((2 * π) ^ 2 * N * E) * (N * racahKernel a b' (N * (s + t * v) - 3 / 2) * v) := by
    funext t; ring
  have hIk : (((2 * π) ^ 2 * N * √N : ℝ) : ℂ) * E * (F (s + r * v) - F s) =
      (√N : ℂ) * ∫ t in (0 : ℝ)..r,
        (2 * π) ^ 2 * N ^ 2 * racahKernel a b' (N * (s + t * v) - 3 / 2) * E * v := by
    rw [hfun, intervalIntegral.integral_const_mul, hray_eq]
    push_cast; ring
  -- the Laplace part
  have hgL : ∀ t ∈ Icc (0 : ℝ) r,
      ‖leadP A (s + t * v) - leadP A (s + ((0 : ℝ) : ℂ) * v)‖ ≤ 3 / y ^ 3 * t := by
    intro t ht
    rw [h0]
    refine (norm_leadP_sub_le A hy hs (hbd t ht).1).trans ?_
    rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
    have h1 := mul_le_mul_of_nonneg_left hv ht.1
    have hy3 : 0 < 2 / y ^ 3 := by positivity
    calc 2 / y ^ 3 * (t * ‖v‖) ≤ 2 / y ^ 3 * (t * (3 / 2)) := mul_le_mul_of_nonneg_left h1 hy3.le
      _ = 3 / y ^ 3 * t := by ring
  have hgG : ‖leadP A (s + ((0 : ℝ) : ℂ) * v)‖ ≤ 1 / y ^ 2 := by
    rw [h0]; exact norm_leadP_le A hy hs
  have hlap := hCl A B s b u₀ ε τ (fun t => leadP A (s + t * v)) hu hbu hβb hε hτ hray hPc hgL
    hgG N hN0
  simp only [h0] at hlap
  -- the kernel against its leading form
  have hpt : ∀ t ∈ Ι (0 : ℝ) r,
      ‖(2 * π) ^ 2 * N ^ 2 * racahKernel a b' (N * (s + t * v) - 3 / 2) * E * v -
        leadP A (s + t * v) * v * cexp (N * (phaseC A B (s + t * v) - phaseC A B s))‖ ≤
      kernelLeadC y R / N * (1 / y ^ 2) * (3 / 2) := by
    intro t ht
    rw [uIoc_of_le hr.le] at ht
    have ht' : t ∈ Icc 0 r := Ioc_subset_Icc_self ht
    obtain ⟨hyt, hRt, hAt, hBt⟩ := hbd t ht'
    have hD := norm_racahKernel_sub_lead_le a b' hA hB hAB hy hyt hRt hAt hBt hN1 hN hNE
    have hP := norm_leadP_le A hy hyt
    have hre := (hray t ht').2.2
    have hEE : ‖cexp (N * phaseC A B (s + t * v))‖ * ‖E‖ ≤ 1 := by
      rw [hE, norm_exp, norm_exp, ← Real.exp_add, Real.exp_le_one_iff]
      simp only [neg_re, re_ofReal_mul]
      have h1 : (phaseC A B (s + t * v)).re ≤ (phaseC A B s).re := by
        have : 0 ≤ ‖b‖ / 4 * t ^ 2 := by positivity
        linarith
      nlinarith [mul_le_mul_of_nonneg_left h1 hN0.le]
    have hexp : cexp (N * (phaseC A B (s + t * v) - phaseC A B s)) =
        cexp (N * phaseC A B (s + t * v)) * E := by
      rw [hE, ← Complex.exp_add]; congr 1; ring
    rw [hexp, show ∀ X Y P : ℂ, X * E * v - P * v * (Y * E) = (X - Y * P) * E * v from
      fun X Y P => by ring, norm_mul, norm_mul]
    calc _ ≤ kernelLeadC y R / N * ‖cexp (N * phaseC A B (s + t * v)) * leadP A (s + t * v)‖ *
          ‖E‖ * (3 / 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hD (norm_nonneg _)) hv (norm_nonneg _)
            (mul_nonneg (mul_nonneg hk (norm_nonneg _)) (norm_nonneg _))
      _ = kernelLeadC y R / N * ‖leadP A (s + t * v)‖ *
          (‖cexp (N * phaseC A B (s + t * v))‖ * ‖E‖) * (3 / 2) := by
          rw [norm_mul]; ring
      _ ≤ kernelLeadC y R / N * (1 / y ^ 2) * 1 * (3 / 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left hP hk) hEE
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (mul_nonneg hk (by positivity)))
            (by norm_num)
      _ = _ := by ring
  have hint1 : IntervalIntegrable (fun t : ℝ => (2 * π) ^ 2 * N ^ 2 *
      racahKernel a b' (N * (s + t * v) - 3 / 2) * E * v) volume 0 r :=
    (((continuousOn_const.mul hKc).mul continuousOn_const).mul
      continuousOn_const).intervalIntegrable_of_Icc hr.le
  have hint2 : IntervalIntegrable (fun t : ℝ => leadP A (s + t * v) * v *
      cexp (N * (phaseC A B (s + t * v) - phaseC A B s))) volume 0 r :=
    ((hPc.mul continuousOn_const).mul
      ((continuousOn_const.mul (hψc.sub continuousOn_const)).cexp)).intervalIntegrable_of_Icc hr.le
  have hdiffI := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [intervalIntegral.integral_sub hint1 hint2, sub_zero, abs_of_pos hr] at hdiffI
  -- assembling
  rw [hIk]
  set Ik := ∫ t in (0 : ℝ)..r,
    (2 * π) ^ 2 * N ^ 2 * racahKernel a b' (N * (s + t * v) - 3 / 2) * E * v with hIkdef
  set Ip := ∫ t in (0 : ℝ)..r,
    leadP A (s + t * v) * v * cexp (N * (phaseC A B (s + t * v) - phaseC A B s)) with hIpdef
  have hmain : (√N : ℂ) * (leadP A s * (ε * u₀ * (√(π / (N * ‖b‖)) : ℂ) / 2)) =
      ε * (leadP A s * u₀ * (√(π / ‖b‖) : ℂ)) / 2 := by
    have h1 : √N * √(π / (N * ‖b‖)) = √(π / ‖b‖) := by
      rw [← Real.sqrt_mul hN0.le]; congr 1; field_simp
    have hc : (√N : ℂ) * (√(π / (N * ‖b‖)) : ℂ) = (√(π / ‖b‖) : ℂ) := by exact_mod_cast h1
    linear_combination (ε * leadP A s * u₀ / 2) * hc
  have e : ∀ X : ℝ, √N * (X / N) = X / √N := fun X => by
    rw [eq_div_iff hsN.ne']
    have hsq : √N * √N = N := Real.mul_self_sqrt hN0.le
    calc √N * (X / N) * √N = X * (√N * √N) / N := by ring
      _ = X := by rw [hsq]; field_simp
  calc ‖(√N : ℂ) * Ik - ε * (leadP A s * u₀ * (√(π / ‖b‖) : ℂ)) / 2‖
      = ‖(√N : ℂ) * (Ik - Ip) +
          (√N : ℂ) * (Ip - leadP A s * (ε * u₀ * (√(π / (N * ‖b‖)) : ℂ) / 2))‖ := by
        rw [← hmain]; congr 1; ring
    _ ≤ ‖(√N : ℂ) * (Ik - Ip)‖ +
          ‖(√N : ℂ) * (Ip - leadP A s * (ε * u₀ * (√(π / (N * ‖b‖)) : ℂ) / 2))‖ :=
        norm_add_le _ _
    _ ≤ √N * (kernelLeadC y R / N * (1 / y ^ 2) * (3 / 2) * r) + √N * (Cl / N) := by
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hsN.le]
        exact add_le_add (mul_le_mul_of_nonneg_left hdiffI hsN.le)
          (mul_le_mul_of_nonneg_left hlap hsN.le)
    _ = √N * ((Cl + r * (3 / 2) * kernelLeadC y R / y ^ 2) / N) := by ring
    _ = _ := e _

/-! ## The leading term in closed form -/

/-- **The amplitude along the descent direction.** For a Euclidean tetrahedron,
`P(s) u₀ = e^{−(Σᵢ log |s − Aᵢ|)/2} e^{−iπ/4}`: the phases `−Σ arg(s − Aᵢ)/2` of the amplitude and
`Σ arg(s − Aᵢ)/2 − π/4` of the descent direction cancel up to `−π/4`. -/
theorem leadP_mul_saddleDir (l : Fin 6 → ℝ) :
    leadP (faceSum l) (saddle l) * saddleDir l =
      ((Real.exp (-(∑ i, Real.log ‖saddle l - faceSum l i‖) / 2) : ℝ) : ℂ) *
        cexp (-(π / 4 : ℂ) * I) := by
  rw [leadP, saddleDir, ← Complex.exp_add, ofReal_exp, ← Complex.exp_add]
  congr 1
  apply Complex.ext
  · simp [Complex.re_sum, Complex.log_re]
  · simp [Complex.im_sum, Complex.log_im]
    ring

/-- `e^{−(Σᵢ log fᵢ)/2}` squared is `1/∏ᵢ fᵢ` for positive `fᵢ`. -/
lemma exp_neg_half_sum_log_sq {f : Fin 4 → ℝ} (hf : ∀ i, 0 < f i) :
    Real.exp (-(∑ i, Real.log (f i)) / 2) ^ 2 * ∏ i, f i = 1 := by
  have hP : ∏ i, f i = Real.exp (∑ i, Real.log (f i)) := by
    rw [Real.exp_sum]; exact Finset.prod_congr rfl fun i _ => (Real.exp_log (hf i)).symm
  rw [hP, ← Real.exp_nat_mul, ← Real.exp_add,
    show ((2 : ℕ) : ℝ) * (-(∑ i, Real.log (f i)) / 2) + ∑ i, Real.log (f i) = 0 by push_cast; ring,
    Real.exp_zero]

/-- **The Hessian against the volume.** For a Euclidean tetrahedron,
`‖b‖ ∏ᵢ |s − Aᵢ| = 12 √V`, with `b = ψ''(s)/2` and `V = vol2l l`. -/
theorem IsEuclid.norm_saddleCoeff_mul_prod {l : Fin 6 → ℝ} (h : IsEuclid l) :
    ‖saddleCoeff l‖ * ∏ i, ‖saddle l - faceSum l i‖ = 12 * √(vol2l l) := by
  have hP : d2phaseC (faceSum l) (quadSum l) (saddle l) * ∏ i, (saddle l - faceSum l i) =
      -(24 * I * (√(vol2l l) : ℂ)) := by
    rw [Fin.prod_univ_four, d2phaseC_eq_d2phase]; exact h.d2phase_saddle
  have hV : 0 < √(vol2l l) := Real.sqrt_pos.2 h.2
  have hnorm : ‖d2phaseC (faceSum l) (quadSum l) (saddle l) * ∏ i, (saddle l - faceSum l i)‖ =
      24 * √(vol2l l) := by
    rw [hP, norm_neg, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hV.le]
    norm_num
  rw [← norm_prod, saddleCoeff, norm_div, Complex.norm_two, div_mul_eq_mul_div, ← norm_mul,
    hnorm]
  ring

/-- **The leading term.** For a Euclidean tetrahedron and every real `X`,
`−(V^{1/4}/(π (2π)²)) Im (e^{iX} P(s) u₀ √(π/‖b‖)) = cos(X + π/4)/(√(12π) (2π)²)`, with
`P` the amplitude at the saddle, `u₀ = saddleDir l`, `b = saddleCoeff l` and `V = vol2l l`. -/
theorem IsEuclid.im_lead_main {l : Fin 6 → ℝ} (h : IsEuclid l) (X : ℝ) :
    -(√(√(vol2l l)) / (π * (2 * π) ^ 2)) *
        (cexp (X * I) * (leadP (faceSum l) (saddle l) * saddleDir l *
          (√(π / ‖saddleCoeff l‖) : ℂ))).im =
      Real.cos (X + π / 4) / (√(12 * π) * (2 * π) ^ 2) := by
  set ρ := Real.exp (-(∑ i, Real.log ‖saddle l - faceSum l i‖) / 2) with hρdef
  set q := √(π / ‖saddleCoeff l‖) with hqdef
  set Pr := ∏ i, ‖saddle l - faceSum l i‖ with hPrdef
  have hpos : ∀ i, 0 < ‖saddle l - faceSum l i‖ := fun i =>
    norm_pos_iff.2 (h.saddle_sub_ne_zero _)
  have hPr : 0 < Pr := Finset.prod_pos fun i _ => hpos i
  have hρPr : ρ ^ 2 * Pr = 1 := exp_neg_half_sum_log_sq hpos
  have hbPr := h.norm_saddleCoeff_mul_prod
  rw [← hPrdef] at hbPr
  have hV : 0 < √(vol2l l) := Real.sqrt_pos.2 h.2
  have hb : 0 < ‖saddleCoeff l‖ := norm_pos_iff.2 h.saddleCoeff_ne_zero
  have hρ : 0 < ρ := Real.exp_pos _
  -- the real prefactor
  have key : √(√(vol2l l)) * ρ * q / π = 1 / √(12 * π) := by
    have ha : 0 ≤ √(√(vol2l l)) * ρ * q / π := by positivity
    have hc : 0 ≤ 1 / √(12 * π) := by positivity
    have hsq : (√(√(vol2l l)) * ρ * q / π) ^ 2 = (1 / √(12 * π)) ^ 2 := by
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hV.le, hqdef, Real.sq_sqrt (by positivity),
        div_pow, one_pow, Real.sq_sqrt (by positivity)]
      have hb' : ‖saddleCoeff l‖ = 12 * √(vol2l l) / Pr := by
        rw [eq_div_iff hPr.ne']; exact hbPr
      have hρ' : ρ ^ 2 = 1 / Pr := by
        rw [eq_div_iff hPr.ne']; exact hρPr
      rw [hρ', hb']
      field_simp
    have := congrArg Real.sqrt hsq
    rwa [Real.sqrt_sq ha, Real.sqrt_sq hc] at this
  rw [leadP_mul_saddleDir]
  have hphase : cexp (X * I) * (ρ * cexp (-(π / 4 : ℂ) * I) * q) =
      ((ρ * q : ℝ) : ℂ) * cexp (((X - π / 4 : ℝ) : ℂ) * I) := by
    calc cexp (X * I) * (ρ * cexp (-(π / 4 : ℂ) * I) * q)
        = (ρ : ℂ) * q * (cexp (X * I) * cexp (-(π / 4 : ℂ) * I)) := by ring
      _ = ((ρ * q : ℝ) : ℂ) * cexp (((X - π / 4 : ℝ) : ℂ) * I) := by
        rw [← Complex.exp_add]; push_cast; congr 2; ring
  rw [hphase, im_ofReal_mul, exp_ofReal_mul_I_im, Real.sin_sub, Real.cos_pi_div_four,
    Real.sin_pi_div_four, Real.cos_add, Real.cos_pi_div_four, Real.sin_pi_div_four]
  calc -(√(√(vol2l l)) / (π * (2 * π) ^ 2)) *
        (ρ * q * (Real.sin X * (√2 / 2) - Real.cos X * (√2 / 2)))
      = (√(√(vol2l l)) * ρ * q / π) *
          (Real.cos X * (√2 / 2) - Real.sin X * (√2 / 2)) / (2 * π) ^ 2 := by
        field_simp
        ring
    _ = _ := by rw [key]; field_simp

end Lightlike.Asymptotics
