import Lightlike.Asymptotics.Ridge
import Lightlike.Asymptotics.UniformContour

/-!
# Orientation of the steepest-descent contour

At the saddle `s` of a Euclidean tetrahedron the phase is `ψ(s + t v) ≈ ψ(s) + b v² t²` with
`b = ψ''(s)/2`, so the two descent directions are `± u₀` with `b u₀² = −‖b‖`. This file picks the
root

  `saddleDir l = exp(i (Σᵢ arg(s − Aᵢ)/2 − π/4))`,

shows that it is one (`IsEuclid.mul_saddleDir_sq`), and proves that the descent path leaving `s`
along `+saddleDir` lands to the right of every `Bₖ`, while the one along `−saddleDir` lands in
`(0, Aᵢ)` (`IsEuclid.exists_contour`). This fixes the sign of the saddle contribution.

The argument:

* `Re saddleDir > 0` (`IsEuclid.re_saddleDir_pos`). Since `Im ψ'(s) = 0`, `arg s ≤ arg(s − Aᵢ)` and
  `arg(s − Bₖ) < π`, the sum `Σᵢ arg(s − Aᵢ)` is below `4π/3` (`IsEuclid.sum_arg_lt`).
* On the vertical line through `s`, `Re ψ > Re ψ(s)` away from `s` (`Ridge`). The valley rays have
  `Re ψ < Re ψ(s)`, so they never cross that line, and neither does a descent path, along which
  `Re ψ` decreases. So the path started to the right of `s` lands at `x ≥ Re s`
  (`IsEuclid.re_saddle_le_of_lift`), and the one started to the left at `x ≤ Re s`.
* Of the two landing patterns allowed by `IsEuclid.landing_sides_strict`, one would put the
  right-hand path in `(0, Aᵢ)` and the left-hand one beyond `Bₖ > Aᵢ`, which the previous point
  excludes.
-/

open Complex Set Filter Topology
open scoped Real

namespace Lightlike.Asymptotics

/-- Half the second derivative of the phase at the saddle, `b = ψ''(s)/2`. -/
noncomputable def saddleCoeff (l : Fin 6 → ℝ) : ℂ :=
  d2phaseC (faceSum l) (quadSum l) (saddle l) / 2

/-- The descent direction at the saddle, `exp(i (Σᵢ arg(s − Aᵢ)/2 − π/4))`. -/
noncomputable def saddleDir (l : Fin 6 → ℝ) : ℂ :=
  exp ((((∑ i, arg (saddle l - faceSum l i)) / 2 - π / 4 : ℝ) : ℂ) * I)

/-- `saddleDir l` is a unit vector. -/
lemma norm_saddleDir (l : Fin 6 → ℝ) : ‖saddleDir l‖ = 1 := norm_exp_ofReal_mul_I _

/-- `ψ''(s) = 2 b` for `b = saddleCoeff l`. -/
lemma d2phaseC_saddle_eq (l : Fin 6 → ℝ) :
    d2phaseC (faceSum l) (quadSum l) (saddle l) = 2 * saddleCoeff l := by
  unfold saddleCoeff; ring

/-- `b = ψ''(s)/2` is not zero at the saddle of a Euclidean tetrahedron. -/
lemma IsEuclid.saddleCoeff_ne_zero {l : Fin 6 → ℝ} (h : IsEuclid l) : saddleCoeff l ≠ 0 :=
  div_ne_zero h.d2phaseC_saddle_ne_zero two_ne_zero

/-- Polar form of `∏ᵢ (s − Aᵢ)`. -/
lemma prod_saddle_sub_faceSum (l : Fin 6 → ℝ) :
    ∏ i, (saddle l - faceSum l i) =
      ((∏ i, ‖saddle l - faceSum l i‖ : ℝ) : ℂ) *
        exp (((∑ i, arg (saddle l - faceSum l i) : ℝ) : ℂ) * I) := by
  calc ∏ i, (saddle l - faceSum l i)
      = ∏ i, ((‖saddle l - faceSum l i‖ : ℂ) * exp (arg (saddle l - faceSum l i) * I)) := by
        simp only [norm_mul_exp_arg_mul_I]
    _ = _ := by
        rw [Finset.prod_mul_distrib, ofReal_prod, ofReal_sum, Finset.sum_mul, Complex.exp_sum]

/-- `saddleDir² = −i exp(i Σᵢ arg(s − Aᵢ))`. -/
lemma saddleDir_sq (l : Fin 6 → ℝ) :
    saddleDir l ^ 2 = -I * exp (((∑ i, arg (saddle l - faceSum l i) : ℝ) : ℂ) * I) := by
  unfold saddleDir
  rw [← Complex.exp_nat_mul]
  have he : ((2 : ℕ) : ℂ) * ((((∑ i, arg (saddle l - faceSum l i)) / 2 - π / 4 : ℝ) : ℂ) * I) =
      ((∑ i, arg (saddle l - faceSum l i) : ℝ) : ℂ) * I + ((-(π / 2) : ℝ) : ℂ) * I := by
    push_cast; ring
  have hpi : exp (((-(π / 2) : ℝ) : ℂ) * I) = -I := by
    rw [Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_neg, Real.sin_neg,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    push_cast; ring
  rw [he, Complex.exp_add, hpi]; ring

/-- `saddleDir² ‖P‖ = −i P` for `P = ∏ᵢ (s − Aᵢ)`. -/
lemma saddleDir_sq_mul_norm (l : Fin 6 → ℝ) :
    saddleDir l ^ 2 * (‖∏ i, (saddle l - faceSum l i)‖ : ℂ) = -I * ∏ i, (saddle l - faceSum l i) := by
  rw [Complex.norm_prod, saddleDir_sq]
  conv_rhs => rw [prod_saddle_sub_faceSum]
  ring

/-- **`saddleDir` is a descent direction**: `b saddleDir² = −‖b‖` for `b = ψ''(s)/2`. -/
theorem IsEuclid.mul_saddleDir_sq {l : Fin 6 → ℝ} (h : IsEuclid l) :
    saddleCoeff l * saddleDir l ^ 2 = -‖saddleCoeff l‖ := by
  set P : ℂ := ∏ i, (saddle l - faceSum l i) with hPdef
  set d2 := d2phaseC (faceSum l) (quadSum l) (saddle l) with hd2
  have hP : d2 * P = -(24 * I * (√(vol2l l) : ℂ)) := by
    rw [hPdef, Fin.prod_univ_four, hd2, d2phaseC_eq_d2phase]; exact h.d2phase_saddle
  have hV : 0 < √(vol2l l) := Real.sqrt_pos.2 h.2
  have hP0 : P ≠ 0 := by
    rintro h0
    rw [h0, mul_zero] at hP
    have : (24 * I * (√(vol2l l) : ℂ)) = 0 := by linear_combination hP
    simp [hV.ne'] at this
  have hPn : (‖P‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 hP0).ne'
  have hnorm : ‖d2 * P‖ = 24 * √(vol2l l) := by
    rw [hP, norm_neg, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hV.le]
    norm_num
  have e2 : (‖saddleCoeff l‖ : ℂ) * (‖P‖ : ℂ) = 12 * (√(vol2l l) : ℂ) := by
    have : ‖saddleCoeff l‖ * ‖P‖ = 12 * √(vol2l l) := by
      rw [saddleCoeff, ← hd2, norm_div, Complex.norm_two, div_mul_eq_mul_div, ← norm_mul, hnorm]
      ring
    exact_mod_cast this
  have e1 := saddleDir_sq_mul_norm l
  try rw [← hPdef] at e1
  have hb : saddleCoeff l = d2 / 2 := rfl
  have key : (saddleCoeff l * saddleDir l ^ 2 + ‖saddleCoeff l‖) * (‖P‖ : ℂ) = 0 := by
    linear_combination saddleCoeff l * e1 + (-I / 2) * hP + e2 + (12 * (√(vol2l l) : ℂ)) * I_sq -
      (I * P) * hb
  have := (mul_eq_zero.1 key).resolve_right hPn
  linear_combination this

/-- `arg z ≤ arg (z − a)` for `Im z > 0` and `a ≥ 0`: moving `z` to the left turns it
anticlockwise. -/
lemma arg_le_arg_sub_ofReal {z : ℂ} (hz : 0 < z.im) {a : ℝ} (ha : 0 ≤ a) :
    arg z ≤ arg (z - a) := by
  have hz0 : z ≠ 0 := fun h0 => by simp [h0] at hz
  have him : (z - a).im = z.im := by simp
  have hre : (z - a).re = z.re - a := by simp
  have hza : z - a ≠ 0 := fun h0 => by rw [h0] at him; simp at him; linarith
  by_contra hlt
  rw [not_le] at hlt
  have h1 : arg z < π := arg_lt_pi_iff.2 (Or.inr hz.ne')
  have h2 : 0 ≤ arg (z - a) := arg_nonneg_iff.2 (by rw [him]; exact hz.le)
  have hs : Real.sin (arg (z - a) - arg z) < 0 :=
    Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
  have hsin : Real.sin (arg (z - a) - arg z) = a * z.im / (‖z - a‖ * ‖z‖) := by
    rw [Real.sin_sub, sin_arg, cos_arg hz0, sin_arg, cos_arg hza, him, hre]
    have : ‖z - a‖ ≠ 0 := norm_ne_zero_iff.2 hza
    have : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz0
    field_simp
    ring
  have : 0 ≤ a * z.im / (‖z - a‖ * ‖z‖) := by positivity
  linarith

/-- `Σᵢ arg(s − Aᵢ) < 4π/3` at the saddle of a Euclidean tetrahedron. From `Im ψ'(s) = 0`,
`Σᵢ arg(s − Aᵢ) = arg s + Σₖ arg(s − Bₖ) − 2π < arg s + π`, and each `arg(s − Aᵢ) ≥ arg s`. -/
theorem IsEuclid.sum_arg_lt {l : Fin 6 → ℝ} (h : IsEuclid l) :
    ∑ i, arg (saddle l - faceSum l i) < 4 * π / 3 := by
  have hs := h.saddle_im_pos
  have hi := congrArg Complex.im h.dphaseC_saddle
  rw [im_dphaseC, zero_im] at hi
  have hφ : ∑ k, arg (saddle l - quadSum l k) < ∑ _k : Fin 3, π :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun k _ =>
      arg_lt_pi_iff.2 (Or.inr (by rw [sub_im, ofReal_im, sub_zero]; exact hs.ne'))
  have hθ : ∑ _i : Fin 4, arg (saddle l) ≤ ∑ i, arg (saddle l - faceSum l i) :=
    Finset.sum_le_sum fun i _ => arg_le_arg_sub_ofReal hs (h.faceSum_pos i).le
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hφ hθ
  push_cast at hφ hθ
  linarith

/-- **`Re saddleDir > 0`**: `Σᵢ arg(s − Aᵢ)/2 − π/4` lies in `(−π/4, 5π/12)`. -/
theorem IsEuclid.re_saddleDir_pos {l : Fin 6 → ℝ} (h : IsEuclid l) : 0 < (saddleDir l).re := by
  have hs := h.saddle_im_pos
  have h0 : 0 ≤ ∑ i, arg (saddle l - faceSum l i) :=
    Finset.sum_nonneg fun i _ => arg_nonneg_iff.2 (by rw [sub_im, ofReal_im, sub_zero]; exact hs.le)
  have h1 := h.sum_arg_lt
  unfold saddleDir
  rw [exp_ofReal_mul_I_re]
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

/-- `Re (valleyDir u₀ ε τ) = ε (Re u₀ − τ Im u₀)`. -/
lemma valleyDir_re (u₀ : ℂ) (ε τ : ℝ) :
    (valleyDir u₀ ε τ).re = ε * (u₀.re - τ * u₀.im) := by
  simp only [valleyDir, mul_re, mul_im, ofReal_re, ofReal_im, add_re, add_im, one_re, one_im,
    I_re, I_im]
  ring

/-- A real function that is continuous on `[0, T)` and never takes the value `c` stays on the
side of `c` where it starts. -/
lemma lt_of_ne_of_continuousOn {f : ℝ → ℝ} {T c : ℝ} (hf : ContinuousOn f (Ico 0 T))
    (hne : ∀ t ∈ Ico 0 T, f t ≠ c) (h0 : c < f 0) : ∀ t ∈ Ico 0 T, c < f t := by
  intro t ht
  by_contra hle
  rw [not_lt] at hle
  have hsub : Icc 0 t ⊆ Ico 0 T := fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 ht.2⟩
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc' ht.1 (hf.mono hsub) ⟨hle, h0.le⟩
  exact hne x (hsub hx) hfx

/-- The real part along a lift is continuous on `[0, T)`. -/
lemma IsLift.continuousOn_re {v : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ} {T : ℝ} {α : ℝ → ℂ}
    (hα : IsLift v U z₀ T α) : ContinuousOn (fun t => (α t).re) (Ico 0 T) :=
  continuous_re.comp_continuousOn fun t ht => (hα.deriv t ht).continuousWithinAt

variable {l : Fin 6 → ℝ}

/-- **A descent path does not cross the vertical line through the saddle**: along a lift from a
point with `Re ψ < Re ψ(s)`, `Re α(t) ≠ Re s`. -/
theorem IsEuclid.re_lift_ne (h : IsEuclid l) {z₀ : ℂ} {T : ℝ} {α : ℝ → ℂ}
    (hα : IsLift (descentField (faceSum l) (quadSum l)) (descentDomain l) z₀ T α)
    (hz₀ : (phaseC (faceSum l) (quadSum l) z₀).re < (phaseC (faceSum l) (quadSum l) (saddle l)).re) :
    ∀ t ∈ Ico 0 T, (α t).re ≠ (saddle l).re := by
  intro t ht he
  have hm := hα.mem t ht
  have hl := congrArg Complex.re (h.phaseC_lift hα t ht)
  rw [sub_re, ofReal_re] at hl
  have := h.re_phaseC_saddle_lt_of_re_eq hm.1 he hm.2
  linarith [ht.1]

/-- A descent path started to the right of the saddle, with `Re ψ < Re ψ(s)`, lands at
`x ≥ Re s`. -/
theorem IsEuclid.re_saddle_le_of_lift (h : IsEuclid l) {z₀ : ℂ} {T : ℝ} {α : ℝ → ℂ}
    (hα : IsLift (descentField (faceSum l) (quadSum l)) (descentDomain l) z₀ T α)
    (hz₀ : (phaseC (faceSum l) (quadSum l) z₀).re < (phaseC (faceSum l) (quadSum l) (saddle l)).re)
    (hre : (saddle l).re < z₀.re) {x : ℝ} (hx : Tendsto α (𝓝[<] T) (𝓝 (x : ℂ))) :
    (saddle l).re ≤ x := by
  have hlt := lt_of_ne_of_continuousOn hα.continuousOn_re (h.re_lift_ne hα hz₀)
    (by simpa only [hα.start] using hre)
  have hlim : Tendsto (fun t => (α t).re) (𝓝[<] T) (𝓝 x) := by
    have := (continuous_re.tendsto (x : ℂ)).comp hx
    rw [ofReal_re] at this
    exact this
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT hα.pos] with t ht
  exact (hlt t ⟨ht.1.le, ht.2⟩).le

/-- A descent path started to the left of the saddle, with `Re ψ < Re ψ(s)`, lands at
`x ≤ Re s`. -/
theorem IsEuclid.le_re_saddle_of_lift (h : IsEuclid l) {z₀ : ℂ} {T : ℝ} {α : ℝ → ℂ}
    (hα : IsLift (descentField (faceSum l) (quadSum l)) (descentDomain l) z₀ T α)
    (hz₀ : (phaseC (faceSum l) (quadSum l) z₀).re < (phaseC (faceSum l) (quadSum l) (saddle l)).re)
    (hre : z₀.re < (saddle l).re) {x : ℝ} (hx : Tendsto α (𝓝[<] T) (𝓝 (x : ℂ))) :
    x ≤ (saddle l).re := by
  have hne := h.re_lift_ne hα hz₀
  have hlt := lt_of_ne_of_continuousOn (f := fun t => -(α t).re) (c := -(saddle l).re)
    hα.continuousOn_re.neg (fun t ht he => hne t ht (neg_inj.1 he))
    (by simp only [hα.start]; linarith)
  have hlim : Tendsto (fun t => (α t).re) (𝓝[<] T) (𝓝 x) := by
    have := (continuous_re.tendsto (x : ℂ)).comp hx
    rw [ofReal_re] at this
    exact this
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT hα.pos] with t ht
  have : -(saddle l).re < -(α t).re := hlt t ⟨ht.1.le, ht.2⟩
  show (α t).re ≤ (saddle l).re
  linarith

/-- The valley rays along `± saddleDir` do not cross the vertical line through the saddle:
`Re saddleDir − τ Im saddleDir > 0` for `|τ| ≤ 1/2`. -/
theorem IsEuclid.re_saddleDir_sub_pos (h : IsEuclid l) {K r : ℝ} (hr : 0 < r)
    (hray : ∀ ε : ℝ, ε ^ 2 = 1 → ∀ τ : ℝ, |τ| ≤ 1 / 2 → ∀ t ∈ Icc (0 : ℝ) r,
      0 < (saddle l + t * valleyDir (saddleDir l) ε τ).im ∧
      ‖phaseC (faceSum l) (quadSum l) (saddle l + t * valleyDir (saddleDir l) ε τ) -
          phaseC (faceSum l) (quadSum l) (saddle l) -
          saddleCoeff l * valleyDir (saddleDir l) ε τ ^ 2 * t ^ 2‖ ≤ K * t ^ 3 ∧
      (phaseC (faceSum l) (quadSum l) (saddle l + t * valleyDir (saddleDir l) ε τ)).re ≤
        (phaseC (faceSum l) (quadSum l) (saddle l)).re - ‖saddleCoeff l‖ / 4 * t ^ 2)
    {τ : ℝ} (hτ : |τ| ≤ 1 / 2) : 0 < (saddleDir l).re - τ * (saddleDir l).im := by
  set u := saddleDir l
  have hb : 0 < ‖saddleCoeff l‖ := norm_pos_iff.2 h.saddleCoeff_ne_zero
  have hne : ∀ σ : ℝ, |σ| ≤ 1 / 2 → u.re - σ * u.im ≠ 0 := by
    intro σ hσ h0
    obtain ⟨him, -, hle⟩ := hray 1 (by norm_num) σ hσ r ⟨hr.le, le_rfl⟩
    have hlt : (phaseC (faceSum l) (quadSum l) (saddle l + r * valleyDir u 1 σ)).re <
        (phaseC (faceSum l) (quadSum l) (saddle l)).re := by
      have : 0 < ‖saddleCoeff l‖ / 4 * r ^ 2 := by positivity
      linarith
    have hre : (saddle l + r * valleyDir u 1 σ).re = (saddle l).re := by
      rw [add_re, re_ofReal_mul, valleyDir_re, h0]; ring
    have hzs : saddle l + r * valleyDir u 1 σ ≠ saddle l := fun he => by
      rw [he] at hlt; exact lt_irrefl _ hlt
    have := h.re_phaseC_saddle_lt_of_re_eq him hre hzs
    linarith
  have h0 : 0 < u.re := h.re_saddleDir_pos
  by_contra hle
  rw [not_lt] at hle
  have hd : 0 < u.re - (u.re - τ * u.im) := by
    rcases hle.lt_or_eq with hl | he
    · linarith
    · exact absurd he (hne τ hτ)
  set θ := u.re / (u.re - (u.re - τ * u.im))
  have hθ0 : 0 < θ := div_pos h0 hd
  have hθ1 : θ ≤ 1 := (div_le_one hd).2 (by linarith)
  have hθτ : |θ * τ| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos hθ0]
    calc θ * |τ| ≤ 1 * |τ| := by gcongr
      _ ≤ 1 / 2 := by linarith
  apply hne (θ * τ) hθτ
  have : θ * (u.re - (u.re - τ * u.im)) = u.re := div_mul_cancel₀ _ hd.ne'
  linear_combination -this

/-- **The oriented steepest-descent contour of a Euclidean tetrahedron.** With `b = ψ''(s)/2`
and `u₀ = saddleDir l` there are a valley radius `r`, offsets `τ₁`, `τ₂` and two descent paths:
the one from `s + r v(1, τ₁)` lands at `x₁` beyond some `Bₖ`, the one from `s + r v(−1, τ₂)` lands
at `x₂ ∈ (0, Aᵢ)` for some `i`. Both start and land on the level `Im ψ = Im ψ(s)`. -/
theorem IsEuclid.exists_contour (h : IsEuclid l) :
    ∃ (K r τ₁ τ₂ T₁ T₂ : ℝ) (α₁ α₂ : ℝ → ℂ) (x₁ x₂ : ℝ),
      0 < r ∧ 0 ≤ K ∧ |τ₁| ≤ 1 / 2 ∧ |τ₂| ≤ 1 / 2 ∧
      (∀ ε : ℝ, ε ^ 2 = 1 → ∀ τ : ℝ, |τ| ≤ 1 / 2 → ∀ t ∈ Icc (0 : ℝ) r,
        0 < (saddle l + t * valleyDir (saddleDir l) ε τ).im ∧
        ‖phaseC (faceSum l) (quadSum l) (saddle l + t * valleyDir (saddleDir l) ε τ) -
            phaseC (faceSum l) (quadSum l) (saddle l) -
            saddleCoeff l * valleyDir (saddleDir l) ε τ ^ 2 * t ^ 2‖ ≤ K * t ^ 3 ∧
        (phaseC (faceSum l) (quadSum l) (saddle l + t * valleyDir (saddleDir l) ε τ)).re ≤
          (phaseC (faceSum l) (quadSum l) (saddle l)).re - ‖saddleCoeff l‖ / 4 * t ^ 2) ∧
      (phaseC (faceSum l) (quadSum l) (saddle l + r * valleyDir (saddleDir l) 1 τ₁)).im =
        (phaseC (faceSum l) (quadSum l) (saddle l)).im ∧
      (phaseC (faceSum l) (quadSum l) (saddle l + r * valleyDir (saddleDir l) (-1) τ₂)).im =
        (phaseC (faceSum l) (quadSum l) (saddle l)).im ∧
      IsLift (descentField (faceSum l) (quadSum l)) (descentDomain l)
        (saddle l + r * valleyDir (saddleDir l) 1 τ₁) T₁ α₁ ∧
      Tendsto α₁ (𝓝[<] T₁) (𝓝 (x₁ : ℂ)) ∧
      IsLift (descentField (faceSum l) (quadSum l)) (descentDomain l)
        (saddle l + r * valleyDir (saddleDir l) (-1) τ₂) T₂ α₂ ∧
      Tendsto α₂ (𝓝[<] T₂) (𝓝 (x₂ : ℂ)) ∧
      bdry (faceSum l) (quadSum l) x₁ = (phaseC (faceSum l) (quadSum l) (saddle l)).im ∧
      bdry (faceSum l) (quadSum l) x₂ = (phaseC (faceSum l) (quadSum l) (saddle l)).im ∧
      (∃ k, quadSum l k < x₁) ∧ 0 < x₂ ∧ ∃ i, x₂ < faceSum l i := by
  have hs := h.saddle_im_pos
  have hb0 := h.saddleCoeff_ne_zero
  have hb : 0 < ‖saddleCoeff l‖ := norm_pos_iff.2 hb0
  obtain ⟨K, r, hr, hK, hray, hlev⟩ := Lightlike.Asymptotics.exists_valley (faceSum l) (quadSum l) hs h.dphaseC_saddle
    (d2phaseC_saddle_eq l) hb0 (norm_saddleDir l) h.mul_saddleDir_sq
  obtain ⟨τ₁, hτ₁, hl₁⟩ := hlev 1 (by norm_num) 0 (by rw [abs_zero]; positivity)
  obtain ⟨τ₂, hτ₂, hl₂⟩ := hlev (-1) (by norm_num) 0 (by rw [abs_zero]; positivity)
  rw [add_zero] at hl₁ hl₂
  obtain ⟨hlo, hhi⟩ := h.pi_faceSum_lt_level
  obtain ⟨T₁, T₂, α₁, α₂, x₁, x₂, hα₁, hx₁, hα₂, hx₂, hb₁, hb₂, hside⟩ :=
    h.landing_sides_strict hb0 (norm_saddleDir l) h.mul_saddleDir_sq hr hray hτ₁ hτ₂ hl₁ hl₂
      hlo hhi
  have hdrop : ∀ ε : ℝ, ε ^ 2 = 1 → ∀ τ : ℝ, |τ| ≤ 1 / 2 →
      (phaseC (faceSum l) (quadSum l) (saddle l + r * valleyDir (saddleDir l) ε τ)).re <
        (phaseC (faceSum l) (quadSum l) (saddle l)).re := by
    intro ε hε τ hτ
    have := (hray ε hε τ hτ r ⟨hr.le, le_rfl⟩).2.2
    have : 0 < ‖saddleCoeff l‖ / 4 * r ^ 2 := by positivity
    linarith
  have hR : (saddle l).re ≤ x₁ := by
    refine h.re_saddle_le_of_lift hα₁ (hdrop 1 (by norm_num) τ₁ hτ₁) ?_ hx₁
    rw [add_re, re_ofReal_mul, valleyDir_re]
    have := h.re_saddleDir_sub_pos hr hray hτ₁
    nlinarith
  have hL : x₂ ≤ (saddle l).re := by
    refine h.le_re_saddle_of_lift hα₂ (hdrop (-1) (by norm_num) τ₂ hτ₂) ?_ hx₂
    rw [add_re, re_ofReal_mul, valleyDir_re]
    have := h.re_saddleDir_sub_pos hr hray hτ₂
    nlinarith
  refine ⟨K, r, τ₁, τ₂, T₁, T₂, α₁, α₂, x₁, x₂, hr, hK, hτ₁, hτ₂, hray, hl₁, hl₂, hα₁, hx₁, hα₂,
    hx₂, hb₁, hb₂, ?_⟩
  rcases hside with ⟨⟨-, i, hi⟩, k, hk⟩ | ⟨⟨h0, i, hi⟩, k, hk⟩
  · exfalso
    have := h.lt i k
    linarith
  · exact ⟨⟨k, hk⟩, h0, i, hi⟩

end Lightlike.Asymptotics
