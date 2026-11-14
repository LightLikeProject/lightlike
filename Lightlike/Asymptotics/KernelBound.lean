import Lightlike.Asymptotics.GammaBounds
import Lightlike.Asymptotics.ContourIdentity
import Lightlike.Asymptotics.Contour

/-!
# Racah's kernel is dominated by the exponential of the continued phase

Racah's kernel `f(z) = π T(z)/sin(π z)` (`racahKernel`) is, on the open upper half-plane, a
product of Gamma functions (`racahT_eq_Gamma`):

  `f(z) = π Γ(z + 2) / (∏ᵢ Γ(z − aᵢ + 1) ∏ₖ Γ(bₖ − z + 1) sin(π z))`.

In the variable `σ = z + 3/2`, with `Aᵢ = aᵢ + 3/2` and `Bₖ = bₖ + 2` (for integer spins `J` and
lengths `ℓ = J + ½` these are the face sums and quadrilateral sums of `ℓ`), every Gamma factor
has the form `Γ(w + ½)`, with `w = σ`, `w = σ − Aᵢ + ½` (the *half-shift* of the face factors) and
`w = Bₖ − σ`. The uniform bounds of `GammaBounds.lean` then dominate the kernel by
`exp(kernelExp A B σ)`, with

  `kernelExp A B σ = Re f(σ) − Σᵢ Re f(σ − Aᵢ + ½) − Σₖ Re f(Bₖ − σ) − π Im σ`

and `f(w) = w log w − w`. This needs, besides the Gamma bounds, a lower bound on `|sin(π z)|`:

* where `Im z ≥ c > 0`, `|sin(π z)| ≥ (1 − e^{−2πc}) e^{π Im z}/2`;
* near the real axis, where `sin(π z)` vanishes at the integers, the *reflection pairing*
  `π/(sin(π z) Γ(z − a + 1)) = ±Γ(a − z)` (left of a face sum `a`) or
  `π/(sin(π z) Γ(b − z + 1)) = ±Γ(z − b)` (right of a quadrilateral sum `b`) removes the
  division; the reflection of the Stirling exponent gives the same `kernelExp`.

Finally the half-shift inequality `Re(u log u) ≤ Re((u + ½) log(u + ½)) + log 2` on the whole
complex plane (sharp at `u = −¼`), and `Σᵢ Aᵢ = Σₖ Bₖ`, give
`kernelExp ≤ Re phaseC(A, B, σ) + 2 + 4 log 2`.

## Main results

* `re_xlog_le_re_xlog_add_half`: the half-shift inequality.
* `exists_norm_racahKernel_le_kernelExp`: `|f(z)| ≤ C exp(kernelExp A B σ)` for `Im z > 0`
  where `Im z ≥ c`, or `−3/2 ≤ Re z ≤ aᵢ − ½` for some `i`, or `Re z ≥ bₖ + ½` for some `k`, with
  `C` depending only on `c`.
* `exists_norm_racahKernel_le`: for integer spins `J` and `ℓ = J + ½`,
  `|f(z)| ≤ C exp(Re phaseC(Aℓ, Bℓ, z + 3/2))` on the same region.

## References

* G. Ponzano, T. Regge, *Semiclassical limit of Racah coefficients*, in *Spectroscopic and
  group theoretical methods in physics*, North-Holland (1968), 1–58.
* J. Roberts, *Classical 6j-symbols and the tetrahedron*, Geom. Topol. 3 (1999) 21–66.
-/

open Complex Set Filter Topology Finset PhyslibAlpha.Sl2
open scoped Real

namespace Lightlike.Asymptotics

/-! ## The half-shift inequality -/

/-- The real part of `w log w`. -/
lemma re_xlog (w : ℂ) : (xlog w).re = w.re * Real.log ‖w‖ - w.im * arg w := by
  simp only [xlog, mul_re, log_re, log_im]

/-- `p log p + q log q ≥ −log 2` for `p, q > 0` with `p + q = ½`, from `log x ≥ 1 − 1/x`. -/
lemma mul_log_add_mul_log_ge {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hpq : p + q = 1 / 2) :
    -Real.log 2 ≤ p * Real.log p + q * Real.log q := by
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have key : ∀ t : ℝ, 0 < t → t - 1 / 4 ≤ t * Real.log 4 + t * Real.log t := fun t ht => by
    have h := Real.one_sub_inv_le_log_of_pos (show 0 < 4 * t by positivity)
    rw [Real.log_mul (by norm_num) ht.ne'] at h
    have h' := mul_le_mul_of_nonneg_left h ht.le
    have hinv : t * (1 - (4 * t)⁻¹) = t - 1 / 4 := by
      field_simp
    nlinarith [hinv]
  have hp' := key p hp
  have hq' := key q hq
  have hs : p * Real.log 4 + q * Real.log 4 = 1 / 2 * Real.log 4 := by rw [← add_mul, hpq]
  linarith

/-- The modulus part of the half-shift inequality: `x log |u| ≤ (x + ½) log |u + ½| + log 2`
for `x = Re u`. -/
lemma re_mul_log_norm_le (u : ℂ) :
    u.re * Real.log ‖u‖ ≤ (u.re + 1 / 2) * Real.log ‖u + 1 / 2‖ + Real.log 2 := by
  set x := u.re with hx
  have hr : |x| ≤ ‖u‖ := abs_re_le_norm u
  have hr' : |x + 1 / 2| ≤ ‖u + 1 / 2‖ := by
    have := abs_re_le_norm (u + 1 / 2)
    simpa [hx] using this
  have hsq : ‖u + 1 / 2‖ ^ 2 = ‖u‖ ^ 2 + x + 1 / 4 := by
    rw [Complex.sq_norm, Complex.sq_norm, normSq_apply, normSq_apply]
    simp only [add_re, add_im, hx]
    norm_num
    ring
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hloghalf : Real.log (1 / 2) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  rcases le_or_gt 0 x with h0 | h0
  · -- `x ≥ 0`: `|u| ≤ |u + ½|` and `|u + ½| ≥ ½`.
    have hr'2 : 1 / 2 ≤ ‖u + 1 / 2‖ := by
      rw [abs_of_nonneg (by linarith)] at hr'
      linarith
    have hl' : -Real.log 2 ≤ Real.log ‖u + 1 / 2‖ := by
      rw [← hloghalf]
      exact Real.log_le_log (by norm_num) hr'2
    have hle : x * Real.log ‖u‖ ≤ x * Real.log ‖u + 1 / 2‖ := by
      rcases h0.eq_or_lt with h | h
      · rw [← h]
        simp
      · apply mul_le_mul_of_nonneg_left _ h.le
        have hpos : 0 < ‖u‖ := lt_of_lt_of_le (abs_pos.2 h.ne') hr
        apply Real.log_le_log hpos
        have : ‖u‖ ^ 2 ≤ ‖u + 1 / 2‖ ^ 2 := by rw [hsq]; linarith
        exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this
    nlinarith
  rcases le_or_gt x (-1 / 2) with h1 | h1
  · -- `x ≤ −½`: `|u + ½| ≤ |u|` and `|u| ≥ ½`.
    have hr2 : 1 / 2 ≤ ‖u‖ := by
      rw [abs_of_neg h0] at hr
      linarith
    have hl : -Real.log 2 ≤ Real.log ‖u‖ := by
      rw [← hloghalf]
      exact Real.log_le_log (by norm_num) hr2
    have hle : (x + 1 / 2) * Real.log ‖u‖ ≤ (x + 1 / 2) * Real.log ‖u + 1 / 2‖ := by
      rcases h1.eq_or_lt with h | h
      · have h' : x + 1 / 2 = 0 := by linarith
        rw [h', zero_mul, zero_mul]
      · apply mul_le_mul_of_nonpos_left _ (by linarith)
        have hpos : 0 < ‖u + 1 / 2‖ :=
          lt_of_lt_of_le (abs_pos.2 (by linarith : x + 1 / 2 ≠ 0)) hr'
        apply Real.log_le_log hpos
        have : ‖u + 1 / 2‖ ^ 2 ≤ ‖u‖ ^ 2 := by rw [hsq]; linarith
        exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this
    nlinarith
  · -- `−½ < x < 0`: `|u| ≥ −x`, `|u + ½| ≥ x + ½`, and `p log p + q log q ≥ −log 2`.
    have hp : 0 < -x := by linarith
    have hq : 0 < x + 1 / 2 := by linarith
    have hpr : -x ≤ ‖u‖ := by rw [abs_of_neg h0] at hr; exact hr
    have hqr : x + 1 / 2 ≤ ‖u + 1 / 2‖ := by rw [abs_of_pos hq] at hr'; exact hr'
    have h1' : -x * Real.log (-x) ≤ -x * Real.log ‖u‖ :=
      mul_le_mul_of_nonneg_left (Real.log_le_log hp hpr) hp.le
    have h2' : (x + 1 / 2) * Real.log (x + 1 / 2) ≤ (x + 1 / 2) * Real.log ‖u + 1 / 2‖ :=
      mul_le_mul_of_nonneg_left (Real.log_le_log hq hqr) hq.le
    have h3 := mul_log_add_mul_log_ge hp hq (by ring)
    nlinarith

/-- `x/r ≤ (x + ½)/r'` in cleared form, for `r = √(x² + y²)` and `r' = √((x + ½)² + y²)`: the
cosine of the argument increases when `½` is added. -/
lemma mul_sqrt_le_mul_sqrt {x y r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') (h2 : r ^ 2 = x ^ 2 + y ^ 2)
    (h2' : r' ^ 2 = (x + 1 / 2) ^ 2 + y ^ 2) : x * r' ≤ (x + 1 / 2) * r := by
  rcases le_or_gt x 0 with h0 | h0
  · rcases le_or_gt (-1 / 2) x with h1 | h1
    · nlinarith
    · have hx : (x + 1 / 2) ^ 2 ≤ x ^ 2 := by nlinarith
      have hsq : (-(x + 1 / 2) * r) ^ 2 ≤ (-x * r') ^ 2 := by
        calc (-(x + 1 / 2) * r) ^ 2 = (x + 1 / 2) ^ 2 * (x ^ 2 + y ^ 2) := by rw [← h2]; ring
          _ ≤ x ^ 2 * ((x + 1 / 2) ^ 2 + y ^ 2) := by
            nlinarith [mul_le_mul_of_nonneg_right hx (sq_nonneg y)]
          _ = (-x * r') ^ 2 := by rw [mul_pow, h2']; ring
      have := (sq_le_sq₀ (by nlinarith) (by nlinarith)).1 hsq
      linarith
  · have hx : x ^ 2 ≤ (x + 1 / 2) ^ 2 := by nlinarith
    have hsq : (x * r') ^ 2 ≤ ((x + 1 / 2) * r) ^ 2 := by
      calc (x * r') ^ 2 = x ^ 2 * ((x + 1 / 2) ^ 2 + y ^ 2) := by rw [mul_pow, h2']
        _ ≤ (x + 1 / 2) ^ 2 * (x ^ 2 + y ^ 2) := by
            nlinarith [mul_le_mul_of_nonneg_right hx (sq_nonneg y)]
        _ = ((x + 1 / 2) * r) ^ 2 := by rw [mul_pow, h2]
    exact (sq_le_sq₀ (by positivity) (by nlinarith)).1 hsq

/-- Adding `½` moves the argument towards `0`: `Im u · arg(u + ½) ≤ Im u · arg u`. -/
lemma im_mul_arg_add_half_le (u : ℂ) : u.im * arg (u + 1 / 2) ≤ u.im * arg u := by
  have hu2 : ‖u‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := by
    rw [Complex.sq_norm, normSq_apply]
    ring
  have hu2' : ‖u + 1 / 2‖ ^ 2 = (u.re + 1 / 2) ^ 2 + u.im ^ 2 := by
    rw [Complex.sq_norm, normSq_apply]
    simp only [add_re, add_im]
    norm_num
    ring
  have hre : (u + 1 / 2).re = u.re + 1 / 2 := by simp
  rcases lt_trichotomy u.im 0 with h | h | h
  · have h' : (u + 1 / 2).im < 0 := by simpa using h
    have hn : 0 < ‖u‖ := norm_pos_iff.2 fun h0 => by rw [h0] at h; simp at h
    have hn' : 0 < ‖u + 1 / 2‖ := norm_pos_iff.2 fun h0 => by rw [h0] at h'; simp at h'
    apply mul_le_mul_of_nonpos_left _ h.le
    rw [arg_of_im_neg h, arg_of_im_neg h', neg_le_neg_iff]
    apply Real.arccos_le_arccos
    rw [div_le_div_iff₀ hn hn', hre]
    exact mul_sqrt_le_mul_sqrt hn hn' hu2 hu2'
  · rw [h]
    simp
  · have h' : 0 < (u + 1 / 2).im := by simpa using h
    have hn : 0 < ‖u‖ := norm_pos_iff.2 fun h0 => by rw [h0] at h; simp at h
    have hn' : 0 < ‖u + 1 / 2‖ := norm_pos_iff.2 fun h0 => by rw [h0] at h'; simp at h'
    apply mul_le_mul_of_nonneg_left _ h.le
    rw [arg_of_im_pos h, arg_of_im_pos h']
    apply Real.arccos_le_arccos
    rw [div_le_div_iff₀ hn hn', hre]
    exact mul_sqrt_le_mul_sqrt hn hn' hu2 hu2'

/-- **The half-shift inequality.** For every `u ∈ ℂ`,
`Re(u log u) ≤ Re((u + ½) log(u + ½)) + log 2`. Equality holds at `u = −¼`. -/
theorem re_xlog_le_re_xlog_add_half (u : ℂ) :
    (xlog u).re ≤ (xlog (u + 1 / 2)).re + Real.log 2 := by
  rw [re_xlog, re_xlog]
  have h1 := re_mul_log_norm_le u
  have h2 := im_mul_arg_add_half_le u
  have hre : (u + 1 / 2).re = u.re + 1 / 2 := by simp
  have him : (u + 1 / 2).im = u.im := by simp
  rw [hre, him]
  linarith

/-! ## Lower bounds for `|sin|` and `|cos|` away from the real axis -/

/-- `e^{Im x} − e^{−Im x} ≤ 2 |sin x|`. -/
lemma exp_im_sub_le_two_norm_sin (x : ℂ) :
    Real.exp x.im - Real.exp (-x.im) ≤ 2 * ‖Complex.sin x‖ := by
  have h := congrArg norm (Complex.two_sin x)
  rw [norm_mul, norm_mul, norm_I, mul_one, Complex.norm_two] at h
  rw [h]
  have := norm_sub_norm_le (Complex.exp (-x * I)) (Complex.exp (x * I))
  rw [Complex.norm_exp, Complex.norm_exp] at this
  simpa using this

/-- `e^{Im x} − e^{−Im x} ≤ 2 |cos x|`. -/
lemma exp_im_sub_le_two_norm_cos (x : ℂ) :
    Real.exp x.im - Real.exp (-x.im) ≤ 2 * ‖Complex.cos x‖ := by
  have h := congrArg norm (Complex.two_cos x)
  rw [norm_mul, Complex.norm_two] at h
  rw [h]
  have := norm_sub_norm_le (Complex.exp (-x * I)) (-Complex.exp (x * I))
  rw [sub_neg_eq_add, norm_neg, Complex.norm_exp, Complex.norm_exp] at this
  rw [add_comm]
  simpa using this

/-- For `t ≥ c > 0`, `(1 − e^{−2c}) e^t ≤ e^t − e^{−t}`. -/
lemma one_sub_exp_mul_exp_le {c t : ℝ} (hct : c ≤ t) :
    (1 - Real.exp (-2 * c)) * Real.exp t ≤ Real.exp t - Real.exp (-t) := by
  have : Real.exp (-t) ≤ Real.exp (-2 * c) * Real.exp t := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  linarith

/-- `1/|sin x| ≤ 2 e^{−Im x}/(1 − e^{−2c})` for `Im x ≥ c > 0`. -/
lemma inv_norm_sin_le {c : ℝ} (hc : 0 < c) {x : ℂ} (hx : c ≤ x.im) :
    ‖Complex.sin x‖⁻¹ ≤ 2 / (1 - Real.exp (-2 * c)) * Real.exp (-x.im) := by
  have hd : 0 < 1 - Real.exp (-2 * c) := by
    have : Real.exp (-2 * c) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    linarith
  have h1 := exp_im_sub_le_two_norm_sin x
  have h2 := one_sub_exp_mul_exp_le hx
  have hpos : 0 < (1 - Real.exp (-2 * c)) / 2 * Real.exp x.im :=
    mul_pos (half_pos hd) (Real.exp_pos _)
  calc ‖Complex.sin x‖⁻¹ ≤ ((1 - Real.exp (-2 * c)) / 2 * Real.exp x.im)⁻¹ :=
        inv_anti₀ hpos (by linarith)
    _ = 2 / (1 - Real.exp (-2 * c)) * Real.exp (-x.im) := by
        rw [mul_inv, inv_div, Real.exp_neg]

/-- `1/|cos x| ≤ 2 e^{−Im x}/(1 − e^{−2c})` for `Im x ≥ c > 0`. -/
lemma inv_norm_cos_le {c : ℝ} (hc : 0 < c) {x : ℂ} (hx : c ≤ x.im) :
    ‖Complex.cos x‖⁻¹ ≤ 2 / (1 - Real.exp (-2 * c)) * Real.exp (-x.im) := by
  have hd : 0 < 1 - Real.exp (-2 * c) := by
    have : Real.exp (-2 * c) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    linarith
  have h1 := exp_im_sub_le_two_norm_cos x
  have h2 := one_sub_exp_mul_exp_le hx
  have hpos : 0 < (1 - Real.exp (-2 * c)) / 2 * Real.exp x.im :=
    mul_pos (half_pos hd) (Real.exp_pos _)
  calc ‖Complex.cos x‖⁻¹ ≤ ((1 - Real.exp (-2 * c)) / 2 * Real.exp x.im)⁻¹ :=
        inv_anti₀ hpos (by linarith)
    _ = 2 / (1 - Real.exp (-2 * c)) * Real.exp (-x.im) := by
        rw [mul_inv, inv_div, Real.exp_neg]

/-- `1/|sin(π z)|` and `1/|cos(π z)|` are at most `K e^{−π Im z}` where `Im z ≥ c > 0`, with `K`
depending only on `c`. -/
lemma exists_inv_norm_sin_pi_mul_le {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ z : ℂ, c ≤ z.im →
      ‖Complex.sin (π * z)‖⁻¹ ≤ K * Real.exp (-(π * z.im)) ∧
        ‖Complex.cos (π * z)‖⁻¹ ≤ K * Real.exp (-(π * z.im)) := by
  have hc' : 0 < π * c := mul_pos Real.pi_pos hc
  have hd : 0 < 1 - Real.exp (-2 * (π * c)) := by
    have : Real.exp (-2 * (π * c)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    linarith
  refine ⟨2 / (1 - Real.exp (-2 * (π * c))), div_pos two_pos hd, fun z hz => ?_⟩
  have hpi : ((π : ℂ) * z).im = π * z.im := by simp
  have hx : π * c ≤ ((π : ℂ) * z).im := by
    rw [hpi]
    exact mul_le_mul_of_nonneg_left hz Real.pi_pos.le
  have h1 := inv_norm_sin_le hc' hx
  have h2 := inv_norm_cos_le hc' hx
  rw [hpi] at h1 h2
  exact ⟨h1, h2⟩

/-! ## The Gamma factor `Γ(σ + ½)` away from the left real axis -/

/-- **`Γ(w + ½)` off the left real axis.** For `c > 0` there is `C` with
`|Γ(w + ½)| ≤ C exp(Re f(w))` wherever `Re w ≥ 0` or `Im w ≥ c`. On the left half-plane the
reflection formula gives `Γ(w + ½) = π/(cos(π w) Γ(½ − w))`; the bound on `1/Γ(½ − w)` and
`Re f(−w) = −Re f(w) − π |Im w|` leave `exp(Re f(w) + π Im w)/|cos(π w)|`, and
`|cos(π w)| ≥ (1 − e^{−2πc}) e^{π Im w}/2` cancels the growth. -/
theorem exists_norm_Gamma_half_add_le_of_im {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, (0 ≤ w.re ∨ c ≤ w.im) →
      ‖Gamma (w + 1 / 2)‖ ≤ C * Real.exp (stirF w).re := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_inv_Gamma_half_add_le
  obtain ⟨C₂, hC₂, h₂⟩ := exists_norm_Gamma_half_add_le
  obtain ⟨K, hK, hKw⟩ := exists_inv_norm_sin_pi_mul_le hc
  refine ⟨C₂ + π * K * C₁, by positivity, fun w hw => ?_⟩
  rcases le_or_gt 0 w.re with hre | hre
  · calc ‖Gamma (w + 1 / 2)‖ ≤ C₂ * Real.exp (stirF w).re := h₂ w hre
      _ ≤ (C₂ + π * K * C₁) * Real.exp (stirF w).re :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (Real.exp_pos _).le
  have him : c ≤ w.im := hw.resolve_left (not_le.2 hre)
  have hpos : 0 < w.im := hc.trans_le him
  have hG : Gamma (-w + 1 / 2) ≠ 0 := Complex.Gamma_ne_zero fun m hm => by
    have := congrArg Complex.im hm
    simp at this
    linarith
  have heq : Gamma (w + 1 / 2) = π / Complex.cos (π * w) * (Gamma (-w + 1 / 2))⁻¹ := by
    rw [← Gamma_half_add_mul_Gamma_half_sub w, mul_assoc, mul_inv_cancel₀ hG, mul_one]
  have hinv : ‖(Gamma (-w + 1 / 2))⁻¹‖ ≤ C₁ * Real.exp ((stirF w).re + π * w.im) := by
    have h := h₁ (-w)
    have e : -(-(stirF w).re - π * w.im) = (stirF w).re + π * w.im := by ring
    rw [re_stirF_neg, abs_of_pos hpos, e] at h
    exact h
  have hcos := (hKw w him).2
  calc ‖Gamma (w + 1 / 2)‖ = π * ‖Complex.cos (π * w)‖⁻¹ * ‖(Gamma (-w + 1 / 2))⁻¹‖ := by
        rw [heq, norm_mul, norm_div, Complex.norm_of_nonneg Real.pi_pos.le, div_eq_mul_inv]
    _ ≤ π * (K * Real.exp (-(π * w.im))) * (C₁ * Real.exp ((stirF w).re + π * w.im)) := by
        gcongr
    _ = π * K * C₁ * Real.exp (stirF w).re * (Real.exp (π * w.im))⁻¹ * Real.exp (π * w.im) := by
        rw [Real.exp_add, Real.exp_neg]
        ring
    _ = π * K * C₁ * Real.exp (stirF w).re := by
        rw [mul_assoc (π * K * C₁ * Real.exp (stirF w).re), inv_mul_cancel₀ (Real.exp_pos _).ne',
          mul_one]
    _ ≤ (C₂ + π * K * C₁) * Real.exp (stirF w).re :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₂.le) (Real.exp_pos _).le

/-! ## The reflection pairing near the real axis -/

/-- `|sin(π(n − z))| = |sin(π z)|` for a natural number `n`. -/
lemma norm_sin_pi_mul_natCast_sub (n : ℕ) (z : ℂ) :
    ‖Complex.sin (π * (n - z))‖ = ‖Complex.sin (π * z)‖ := by
  have h : Complex.sin (π * z - n * π) = (-1) ^ n * Complex.sin (π * z) :=
    Complex.sin_antiperiodic.sub_nat_mul_eq n
  rw [show (π : ℂ) * (n - z) = -(π * z - n * π) by ring, Complex.sin_neg, norm_neg, h, norm_mul,
    norm_pow, norm_neg, norm_one, one_pow, one_mul]

/-- `|sin(π(z − n))| = |sin(π z)|` for a natural number `n`. -/
lemma norm_sin_pi_mul_sub_natCast (n : ℕ) (z : ℂ) :
    ‖Complex.sin (π * (z - n))‖ = ‖Complex.sin (π * z)‖ := by
  have h : Complex.sin (π * z - n * π) = (-1) ^ n * Complex.sin (π * z) :=
    Complex.sin_antiperiodic.sub_nat_mul_eq n
  rw [show (π : ℂ) * (z - n) = π * z - n * π by ring, h, norm_mul, norm_pow, norm_neg, norm_one,
    one_pow, one_mul]

/-- **Reflection pairing left of a face sum.** For `Im z > 0` and `n ∈ ℕ`,
`π |1/Γ(z − n + 1)| / |sin(π z)| = |Γ(n − z)|`. The zeros of `1/Γ(z − n + 1)` at the integers
`z < n` cancel the zeros of `sin(π z)` there, so the right side stays bounded near them. -/
lemma pi_div_norm_sin_mul_norm_inv_Gamma_sub (n : ℕ) {z : ℂ} (hz : 0 < z.im) :
    π / ‖Complex.sin (π * z)‖ * ‖(Gamma (z - n + 1))⁻¹‖ = ‖Gamma (n - z)‖ := by
  have hG : Gamma (z - n + 1) ≠ 0 := Complex.Gamma_ne_zero fun m hm => by
    have := congrArg Complex.im hm
    simp at this
    linarith
  have h := Complex.Gamma_mul_Gamma_one_sub ((n : ℂ) - z)
  rw [show 1 - ((n : ℂ) - z) = z - n + 1 by ring] at h
  have h' : Gamma (n - z) = π / Complex.sin (π * (n - z)) * (Gamma (z - n + 1))⁻¹ := by
    rw [← h, mul_assoc, mul_inv_cancel₀ hG, mul_one]
  rw [h', norm_mul, norm_div, Complex.norm_of_nonneg Real.pi_pos.le, norm_sin_pi_mul_natCast_sub]

/-- **Reflection pairing right of a quadrilateral sum.** For `Im z > 0` and `n ∈ ℕ`,
`π |1/Γ(n − z + 1)| / |sin(π z)| = |Γ(z − n)|`. The zeros of `1/Γ(n − z + 1)` at the integers
`z > n` cancel the zeros of `sin(π z)` there. -/
lemma pi_div_norm_sin_mul_norm_inv_Gamma_natCast_sub (n : ℕ) {z : ℂ} (hz : 0 < z.im) :
    π / ‖Complex.sin (π * z)‖ * ‖(Gamma (n - z + 1))⁻¹‖ = ‖Gamma (z - n)‖ := by
  have hG : Gamma (n - z + 1) ≠ 0 := Complex.Gamma_ne_zero fun m hm => by
    have := congrArg Complex.im hm
    simp at this
    linarith
  have h := Complex.Gamma_mul_Gamma_one_sub (z - n)
  rw [show 1 - (z - (n : ℂ)) = n - z + 1 by ring] at h
  have h' : Gamma (z - n) = π / Complex.sin (π * (z - n)) * (Gamma (n - z + 1))⁻¹ := by
    rw [← h, mul_assoc, mul_inv_cancel₀ hG, mul_one]
  rw [h', norm_mul, norm_div, Complex.norm_of_nonneg Real.pi_pos.le, norm_sin_pi_mul_sub_natCast]

/-! ## The kernel bound -/

/-- The Stirling exponent of Racah's kernel in the variable `σ = z + 3/2`, for face sums `A` and
quadrilateral sums `B`: `Re f(σ) − Σᵢ Re f(σ − Aᵢ + ½) − Σₖ Re f(Bₖ − σ) − π Im σ`, with
`f(w) = w log w − w`. -/
noncomputable def kernelExp (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) (σ : ℂ) : ℝ :=
  (stirF σ).re - ∑ i, (stirF (σ - A i + 1 / 2)).re - ∑ k, (stirF (B k - σ)).re - π * σ.im

/-- A product of nonnegative factors `fᵢ ≤ C e^{−uᵢ}` is at most `C^{|s|} e^{−Σ uᵢ}`. -/
lemma prod_le_pow_mul_exp {ι : Type*} (s : Finset ι) {f u : ι → ℝ} {C : ℝ}
    (hf : ∀ i, f i ≤ C * Real.exp (-u i)) (hf0 : ∀ i, 0 ≤ f i) :
    ∏ i ∈ s, f i ≤ C ^ s.card * Real.exp (-∑ i ∈ s, u i) := by
  calc ∏ i ∈ s, f i ≤ ∏ i ∈ s, C * Real.exp (-u i) :=
        Finset.prod_le_prod₀ (fun i _ => hf0 i) (fun i _ => hf i)
    _ = C ^ s.card * Real.exp (-∑ i ∈ s, u i) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, ← Finset.sum_neg_distrib, Real.exp_sum]

/-- **Racah's kernel is dominated by the exponential of its Stirling exponent.** For every
`c > 0` there is `C`, independent of the face sums `aᵢ` and the quadrilateral sums `bₖ`, with
`|f(z)| ≤ C exp(kernelExp(a + 3/2, b + 2, z + 3/2))` for `Im z > 0` in each of three regions:
`Im z ≥ c`; `−3/2 ≤ Re z ≤ aᵢ − ½` for some `i` (left of a face sum, where the zeros of
`1/Γ(z − aᵢ + 1)` cancel those of `sin(π z)`); and `Re z ≥ bₖ + ½` for some `k` (right of a
quadrilateral sum, where the zeros of `1/Γ(bₖ − z + 1)` do). -/
theorem exists_norm_racahKernel_le_kernelExp {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Fin 4 → ℕ) (b : Fin 3 → ℕ) (z : ℂ), 0 < z.im →
      (c ≤ z.im ∨ (-3 / 2 ≤ z.re ∧ ∃ i, z.re ≤ (a i : ℝ) - 1 / 2) ∨
        ∃ k, (b k : ℝ) + 1 / 2 ≤ z.re) →
      ‖racahKernel a b z‖ ≤ C * Real.exp
        (kernelExp (fun i => (a i : ℝ) + 3 / 2) (fun k => (b k : ℝ) + 2) (z + 3 / 2)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_inv_Gamma_half_add_le
  obtain ⟨C₂, hC₂, h₂⟩ := exists_norm_Gamma_half_add_le
  obtain ⟨G, hG, hG'⟩ := exists_norm_Gamma_half_add_le_of_im hc
  obtain ⟨K, hK0, hKz⟩ := exists_inv_norm_sin_pi_mul_le hc
  refine ⟨G * C₁ ^ 6 * (π * K * C₁ + C₂), by positivity, ?_⟩
  intro a b z hz hreg
  -- the arguments of the Gamma factors, in the form `w + ½`
  obtain ⟨u, hu⟩ : ∃ u : Fin 4 → ℂ,
      u = fun i => z + 3 / 2 - (((a i : ℝ) + 3 / 2 : ℝ) : ℂ) + 1 / 2 := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : Fin 3 → ℂ, v = fun k => (((b k : ℝ) + 2 : ℝ) : ℂ) - (z + 3 / 2) :=
    ⟨_, rfl⟩
  have hE : kernelExp (fun i => (a i : ℝ) + 3 / 2) (fun k => (b k : ℝ) + 2) (z + 3 / 2) =
      (stirF (z + 3 / 2)).re - ∑ i, (stirF (u i)).re - ∑ k, (stirF (v k)).re - π * z.im := by
    have him : (z + 3 / 2).im = z.im := by simp
    subst hu hv
    rw [kernelExp, him]
  have eF : ∀ i, z - (a i : ℂ) + 1 = u i + 1 / 2 := fun i => by
    rw [hu]
    push_cast
    ring
  have eQ : ∀ k, (b k : ℂ) - z + 1 = v k + 1 / 2 := fun k => by
    rw [hv]
    push_cast
    ring
  have hF : ∀ i, ‖(Gamma (z - a i + 1))⁻¹‖ ≤ C₁ * Real.exp (-(stirF (u i)).re) := fun i => by
    rw [eF i]
    exact h₁ (u i)
  have hQ : ∀ k, ‖(Gamma (b k - z + 1))⁻¹‖ ≤ C₁ * Real.exp (-(stirF (v k)).re) := fun k => by
    rw [eQ k]
    exact h₁ (v k)
  have h0 : (c ≤ z.im ∨ -3 / 2 ≤ z.re) →
      ‖Gamma (z + 2)‖ ≤ G * Real.exp (stirF (z + 3 / 2)).re := fun h => by
    rw [show z + 2 = z + 3 / 2 + 1 / 2 by ring]
    apply hG'
    have hre : (z + 3 / 2).re = z.re + 3 / 2 := by simp
    have him : (z + 3 / 2).im = z.im := by simp
    rw [hre, him]
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl (by linarith)
  have hK : ‖racahKernel a b z‖ = π * (‖Gamma (z + 2)‖ * (∏ i, ‖(Gamma (z - a i + 1))⁻¹‖) *
      ∏ k, ‖(Gamma (b k - z + 1))⁻¹‖) / ‖Complex.sin (π * z)‖ := by
    rw [racahKernel, racahT_eq_Gamma a b hz]
    simp only [norm_div, norm_mul, norm_prod, Complex.norm_of_nonneg Real.pi_pos.le]
  have hP := prod_le_pow_mul_exp Finset.univ hF (fun i => norm_nonneg _)
  have hQ' := prod_le_pow_mul_exp Finset.univ hQ (fun k => norm_nonneg _)
  rw [Finset.card_fin] at hP hQ'
  rcases hreg with h | ⟨hre, i₀, hi₀⟩ | ⟨k₀, hk₀⟩
  · -- away from the real axis: the lower bound on `|sin(π z)|`
    have hs := (hKz z h).1
    have hg := h0 (Or.inl h)
    calc ‖racahKernel a b z‖
        = π * (‖Gamma (z + 2)‖ * (∏ i, ‖(Gamma (z - a i + 1))⁻¹‖) *
            ∏ k, ‖(Gamma (b k - z + 1))⁻¹‖) * ‖Complex.sin (π * z)‖⁻¹ := by
          rw [hK, div_eq_mul_inv]
      _ ≤ π * ((G * Real.exp (stirF (z + 3 / 2)).re) *
            (C₁ ^ 4 * Real.exp (-∑ i, (stirF (u i)).re)) *
            (C₁ ^ 3 * Real.exp (-∑ k, (stirF (v k)).re))) * (K * Real.exp (-(π * z.im))) := by
          gcongr
      _ = G * C₁ ^ 6 * (π * K * C₁) * (Real.exp (stirF (z + 3 / 2)).re *
            Real.exp (-∑ i, (stirF (u i)).re) * Real.exp (-∑ k, (stirF (v k)).re) *
            Real.exp (-(π * z.im))) := by
          ring
      _ = G * C₁ ^ 6 * (π * K * C₁) * Real.exp
            (kernelExp (fun i => (a i : ℝ) + 3 / 2) (fun k => (b k : ℝ) + 2) (z + 3 / 2)) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, hE]
          congr 2
      _ ≤ _ := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hC₂.le) (by positivity))
            (Real.exp_pos _).le
  · -- left of the face sum `a i₀`: pair `sin(π z)` with `1/Γ(z − a i₀ + 1)`
    have hg := h0 (Or.inr hre)
    have hsplit : ∏ i, ‖(Gamma (z - a i + 1))⁻¹‖ =
        ‖(Gamma (z - a i₀ + 1))⁻¹‖ * ∏ i ∈ Finset.univ.erase i₀, ‖(Gamma (z - a i + 1))⁻¹‖ :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ i₀)).symm
    have hsum : ∑ i, (stirF (u i)).re =
        (stirF (u i₀)).re + ∑ i ∈ Finset.univ.erase i₀, (stirF (u i)).re :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ i₀)).symm
    have hc3 : (Finset.univ.erase i₀).card = 3 := by simp
    have hP' := prod_le_pow_mul_exp (Finset.univ.erase i₀) hF (fun i => norm_nonneg _)
    rw [hc3] at hP'
    have hpair := pi_div_norm_sin_mul_norm_inv_Gamma_sub (a i₀) hz
    have hΓ : ‖Gamma (a i₀ - z)‖ ≤ C₂ * Real.exp (-(stirF (u i₀)).re - π * z.im) := by
      have hre' : 0 ≤ (-u i₀).re := by
        rw [hu]
        simp
        linarith
      have h := h₂ (-u i₀) hre'
      have him : (u i₀).im = z.im := by
        rw [hu]
        simp
      rw [re_stirF_neg, him, abs_of_pos hz] at h
      rwa [show ((a i₀ : ℕ) : ℂ) - z = -u i₀ + 1 / 2 by rw [hu]; push_cast; ring]
    calc ‖racahKernel a b z‖
        = ‖Gamma (a i₀ - z)‖ * ‖Gamma (z + 2)‖ *
            (∏ i ∈ Finset.univ.erase i₀, ‖(Gamma (z - a i + 1))⁻¹‖) *
            ∏ k, ‖(Gamma (b k - z + 1))⁻¹‖ := by
          rw [hK, hsplit, ← hpair]
          ring
      _ ≤ (C₂ * Real.exp (-(stirF (u i₀)).re - π * z.im)) *
            (G * Real.exp (stirF (z + 3 / 2)).re) *
            (C₁ ^ 3 * Real.exp (-∑ i ∈ Finset.univ.erase i₀, (stirF (u i)).re)) *
            (C₁ ^ 3 * Real.exp (-∑ k, (stirF (v k)).re)) := by
          gcongr
      _ = G * C₁ ^ 6 * C₂ * (Real.exp (-(stirF (u i₀)).re - π * z.im) *
            Real.exp (stirF (z + 3 / 2)).re *
            Real.exp (-∑ i ∈ Finset.univ.erase i₀, (stirF (u i)).re) *
            Real.exp (-∑ k, (stirF (v k)).re)) := by
          ring
      _ = G * C₁ ^ 6 * C₂ * Real.exp
            (kernelExp (fun i => (a i : ℝ) + 3 / 2) (fun k => (b k : ℝ) + 2) (z + 3 / 2)) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, hE, hsum]
          congr 2
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (by positivity))
            (Real.exp_pos _).le
  · -- right of the quadrilateral sum `b k₀`: pair `sin(π z)` with `1/Γ(b k₀ − z + 1)`
    have hb : (0 : ℝ) ≤ b k₀ := Nat.cast_nonneg _
    have hg := h0 (Or.inr (by linarith))
    have hsplit : ∏ k, ‖(Gamma (b k - z + 1))⁻¹‖ =
        ‖(Gamma (b k₀ - z + 1))⁻¹‖ * ∏ k ∈ Finset.univ.erase k₀, ‖(Gamma (b k - z + 1))⁻¹‖ :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ k₀)).symm
    have hsum : ∑ k, (stirF (v k)).re =
        (stirF (v k₀)).re + ∑ k ∈ Finset.univ.erase k₀, (stirF (v k)).re :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ k₀)).symm
    have hc2 : (Finset.univ.erase k₀).card = 2 := by simp
    have hQ'' := prod_le_pow_mul_exp (Finset.univ.erase k₀) hQ (fun k => norm_nonneg _)
    rw [hc2] at hQ''
    have hpair := pi_div_norm_sin_mul_norm_inv_Gamma_natCast_sub (b k₀) hz
    have hΓ : ‖Gamma (z - b k₀)‖ ≤ C₂ * Real.exp (-(stirF (v k₀)).re - π * z.im) := by
      have hre' : 0 ≤ (-v k₀).re := by
        rw [hv]
        simp
        linarith
      have h := h₂ (-v k₀) hre'
      have him : |(v k₀).im| = z.im := by
        rw [hv]
        simp [abs_of_pos hz]
      rw [re_stirF_neg, him] at h
      rwa [show z - ((b k₀ : ℕ) : ℂ) = -v k₀ + 1 / 2 by rw [hv]; push_cast; ring]
    calc ‖racahKernel a b z‖
        = ‖Gamma (z - b k₀)‖ * ‖Gamma (z + 2)‖ * (∏ i, ‖(Gamma (z - a i + 1))⁻¹‖) *
            ∏ k ∈ Finset.univ.erase k₀, ‖(Gamma (b k - z + 1))⁻¹‖ := by
          rw [hK, hsplit, ← hpair]
          ring
      _ ≤ (C₂ * Real.exp (-(stirF (v k₀)).re - π * z.im)) *
            (G * Real.exp (stirF (z + 3 / 2)).re) *
            (C₁ ^ 4 * Real.exp (-∑ i, (stirF (u i)).re)) *
            (C₁ ^ 2 * Real.exp (-∑ k ∈ Finset.univ.erase k₀, (stirF (v k)).re)) := by
          gcongr
      _ = G * C₁ ^ 6 * C₂ * (Real.exp (-(stirF (v k₀)).re - π * z.im) *
            Real.exp (stirF (z + 3 / 2)).re * Real.exp (-∑ i, (stirF (u i)).re) *
            Real.exp (-∑ k ∈ Finset.univ.erase k₀, (stirF (v k)).re)) := by
          ring
      _ = G * C₁ ^ 6 * C₂ * Real.exp
            (kernelExp (fun i => (a i : ℝ) + 3 / 2) (fun k => (b k : ℝ) + 2) (z + 3 / 2)) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, hE, hsum]
          congr 2
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (by positivity))
            (Real.exp_pos _).le

/-! ## Comparison with the continued phase -/

/-- **Comparison with the phase.** For the face sums and quadrilateral sums of lengths `ℓ`,
`kernelExp ≤ Re ψ(σ) + 2 + 4 log 2` on the whole plane, where `ψ` is the phase `phase ℓ`. Each
of the four half-shifts costs at most `log 2` (`re_xlog_le_re_xlog_add_half`), and the linear
terms of `f(w) = w log w − w` add up to `2` because `Σᵢ Aᵢ = Σₖ Bₖ`. -/
theorem kernelExp_le_re_phase (l : Fin 6 → ℝ) (σ : ℂ) :
    kernelExp (faceSum l) (quadSum l) σ ≤ (phase l σ).re + 2 + 4 * Real.log 2 := by
  have hS : ∀ w : ℂ, (stirF w).re = (xlog w).re - w.re := fun w => by
    simp only [stirF, xlog, sub_re]
  have hπ : ((π : ℂ) * I * σ).re = -(π * σ.im) := by simp
  have hP : (phase l σ).re = (xlog σ).re - ∑ i, (xlog (σ - faceSum l i)).re -
      ∑ k, (xlog ((quadSum l k : ℂ) - σ)).re - π * σ.im := by
    simp only [phase, xlog, sub_re, add_re, Complex.re_sum, hπ]
    ring
  have hre : ∀ x : ℝ, (σ - x + 1 / 2).re = σ.re - x + 1 / 2 := fun x => by simp
  have hre' : ∀ x : ℝ, ((x : ℂ) - σ).re = x - σ.re := fun x => by simp
  have hF : ∀ i, (xlog (σ - faceSum l i)).re ≤ (xlog (σ - faceSum l i + 1 / 2)).re +
      Real.log 2 := fun i => re_xlog_le_re_xlog_add_half _
  have hsum := sum_faceSum_eq_sum_quadSum l
  simp only [Fin.sum_univ_four, Fin.sum_univ_three] at hsum
  have h0 := hF 0
  have h1 := hF 1
  have h2 := hF 2
  have h3 := hF 3
  rw [hP]
  simp only [kernelExp, hS, hre, hre', Fin.sum_univ_four, Fin.sum_univ_three]
  linarith

/-- For integer spins `J` and lengths `ℓ = J + ½`, the face sums of `ℓ` are those of `J` plus
`3/2`. -/
lemma faceSum_add_half (J : Fin 6 → ℕ) (i : Fin 4) :
    faceSum (fun e => (J e : ℝ) + 1 / 2) i = faceN J i + 3 / 2 := by
  fin_cases i <;> simp [faceSum, faceN] <;> ring

/-- For integer spins `J` and lengths `ℓ = J + ½`, the quadrilateral sums of `ℓ` are those of
`J` plus `2`. -/
lemma quadSum_add_half (J : Fin 6 → ℕ) (k : Fin 3) :
    quadSum (fun e => (J e : ℝ) + 1 / 2) k = quadN J k + 2 := by
  fin_cases k <;> simp [quadSum, quadN] <;> ring

/-- **The kernel bound along the contour.** For every `c > 0` there is `C` such that, for all
integer spins `J` and lengths `ℓ = J + ½`,
`|f(z)| ≤ C exp(Re phaseC(Aℓ, Bℓ, z + 3/2))` for `Im z > 0` where `Im z ≥ c`, or
`−3/2 ≤ Re z ≤ aᵢ − ½` for a face sum `aᵢ` of `J`, or `Re z ≥ bₖ + ½` for a quadrilateral
sum `bₖ` of `J`. The constant does not depend on `J`, so the bound is uniform under rescaling of
the spins. -/
theorem exists_norm_racahKernel_le {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : Fin 6 → ℕ) (z : ℂ), 0 < z.im →
      (c ≤ z.im ∨ (-3 / 2 ≤ z.re ∧ ∃ i, z.re ≤ (faceN J i : ℝ) - 1 / 2) ∨
        ∃ k, (quadN J k : ℝ) + 1 / 2 ≤ z.re) →
      ‖racahKernel (faceN J) (quadN J) z‖ ≤
        C * Real.exp (phaseC (faceSum fun e => (J e : ℝ) + 1 / 2)
          (quadSum fun e => (J e : ℝ) + 1 / 2) (z + 3 / 2)).re := by
  obtain ⟨C, hC, hK⟩ := exists_norm_racahKernel_le_kernelExp hc
  refine ⟨C * Real.exp (2 + 4 * Real.log 2), by positivity, fun J z hz hreg => ?_⟩
  have hA : faceSum (fun e => (J e : ℝ) + 1 / 2) = fun i => (faceN J i : ℝ) + 3 / 2 :=
    funext (faceSum_add_half J)
  have hB : quadSum (fun e => (J e : ℝ) + 1 / 2) = fun k => (quadN J k : ℝ) + 2 :=
    funext (quadSum_add_half J)
  have him : 0 < (z + 3 / 2).im := by simpa using hz
  have hle := kernelExp_le_re_phase (fun e => (J e : ℝ) + 1 / 2) (z + 3 / 2)
  rw [phase_eq_phaseC _ him, hA, hB] at hle
  rw [hA, hB]
  calc ‖racahKernel (faceN J) (quadN J) z‖
      ≤ C * Real.exp (kernelExp (fun i => (faceN J i : ℝ) + 3 / 2)
          (fun k => (quadN J k : ℝ) + 2) (z + 3 / 2)) := hK (faceN J) (quadN J) z hz hreg
    _ ≤ C * Real.exp (2 + 4 * Real.log 2 + (phaseC (fun i => (faceN J i : ℝ) + 3 / 2)
          (fun k => (quadN J k : ℝ) + 2) (z + 3 / 2)).re) := by
        gcongr
        linarith
    _ = C * Real.exp (2 + 4 * Real.log 2) * Real.exp (phaseC (fun i => (faceN J i : ℝ) + 3 / 2)
          (fun k => (quadN J k : ℝ) + 2) (z + 3 / 2)).re := by
        rw [Real.exp_add]
        ring

end Lightlike.Asymptotics
