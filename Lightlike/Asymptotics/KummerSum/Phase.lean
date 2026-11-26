import Lightlike.Asymptotics.Contour

/-!
# The phase of Kummer's kernel and its saddle

In the variable `α = (z + ½)/N`, `N = m + 1`, Stirling's formula turns Kummer's kernel
`π (m!)² / (sin(π z) Γ(z+1)² Γ(m−z+1)²)` on the upper half-plane into `exp(N ψ(α))` times slowly
varying factors (`KummerSum/Kernel.lean`), with the phase

  `ψ(α) = iπ α − 2 (α log α + (1 − α) log(1 − α))`   (`kummerPhase`).

This file finds the saddle and the bounds that Laplace's method needs along the horizontal line
through it:

* `ψ'(α) = iπ − 2 (log α − log(1 − α))` and `ψ''(α) = −2 (1/α + 1/(1 − α))`
  (`hasDerivAt_kummerPhase`, `hasDerivAt_dkummerPhase`);
* the saddle is `α₀ = (1 + i)/2`: `ψ'(α₀) = 0`, `ψ''(α₀) = −4`, `ψ(α₀) = log 2 + iπ/2`
  (`dkummerPhase_saddle`, `d2kummerPhase_saddle`, `kummerPhase_saddle`);
* along `α₀ + s`, `s ∈ [−½, ½]`, with `φ(s) = ψ(α₀ + s) − ψ(α₀)`:
  `‖φ(s) + 2 s²‖ ≤ 16 |s|³` (`norm_kummerPhase_taylor_le`) and `Re φ(s) ≤ −s²/2`
  (`re_kummerPhase_sub_le`), the second from `Re ψ'' ≤ −1` on that segment
  (`re_d2kummerPhase_le`).

The saddle and the second derivative come out of the phase; nothing here uses the closed form of
the sum.
-/

open Complex Set
open scoped Real

namespace Lightlike.Asymptotics

/-- The phase of Kummer's kernel, `ψ(α) = iπ α − 2 (α log α + (1 − α) log(1 − α))`. -/
noncomputable def kummerPhase (α : ℂ) : ℂ := π * I * α - 2 * (xlog α + xlog (1 - α))

/-- `ψ'(α) = iπ − 2 (log α − log(1 − α))`. -/
noncomputable def dkummerPhase (α : ℂ) : ℂ := π * I - 2 * (log α - log (1 - α))

/-- `ψ''(α) = −2 (1/α + 1/(1 − α))`. -/
noncomputable def d2kummerPhase (α : ℂ) : ℂ := -2 * (1 / α + 1 / (1 - α))

/-- The saddle `α₀ = (1 + i)/2`. -/
noncomputable def kummerSaddle : ℂ := (1 + I) / 2

/-- The strip where the bounds hold: `Im α = ½`. -/
lemma mem_slitPlane_of_im_eq {α : ℂ} (h : α.im = 1 / 2) : α ∈ slitPlane :=
  mem_slitPlane_of_im_pos (by rw [h]; norm_num)

lemma one_sub_mem_slitPlane_of_im_eq {α : ℂ} (h : α.im = 1 / 2) : 1 - α ∈ slitPlane := by
  rw [mem_slitPlane_iff]; right; simp [h]

theorem hasDerivAt_kummerPhase {α : ℂ} (h1 : α ∈ slitPlane) (h2 : 1 - α ∈ slitPlane) :
    HasDerivAt kummerPhase (dkummerPhase α) α := by
  have ha := hasDerivAt_xlog h1
  have hb : HasDerivAt (fun α : ℂ => xlog (1 - α)) ((log (1 - α) + 1) * (-1)) α := by
    have := (hasDerivAt_xlog h2).comp α ((hasDerivAt_id' α).const_sub 1)
    simpa [Function.comp_def] using this
  have := ((hasDerivAt_id' α).const_mul (π * I)).sub ((ha.add hb).const_mul 2)
  unfold kummerPhase dkummerPhase
  convert this using 1
  ring

theorem hasDerivAt_dkummerPhase {α : ℂ} (h1 : α ∈ slitPlane) (h2 : 1 - α ∈ slitPlane) :
    HasDerivAt dkummerPhase (d2kummerPhase α) α := by
  have hα : α ≠ 0 := slitPlane_ne_zero h1
  have hβ : 1 - α ≠ 0 := slitPlane_ne_zero h2
  have ha := hasDerivAt_log h1
  have hb : HasDerivAt (fun α : ℂ => log (1 - α)) ((1 - α)⁻¹ * (-1)) α := by
    have := (hasDerivAt_log h2).comp α ((hasDerivAt_id' α).const_sub 1)
    simpa [Function.comp_def] using this
  have := (ha.sub hb).const_mul (2 : ℂ)
  have := this.const_sub (π * I)
  unfold dkummerPhase d2kummerPhase
  convert this using 1
  simp only [one_div]
  ring

/-! ## The saddle -/

lemma kummerSaddle_eq : kummerSaddle =
    ((√2 / 2 : ℝ) : ℂ) * (Complex.cos ((π / 4 : ℝ) : ℂ) + Complex.sin ((π / 4 : ℝ) : ℂ) * I) := by
  rw [← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_four, Real.sin_pi_div_four, kummerSaddle]
  apply Complex.ext <;> simp <;> ring_nf <;> norm_num [Real.sq_sqrt]

lemma arg_kummerSaddle : arg kummerSaddle = π / 4 := by
  rw [kummerSaddle_eq]
  exact arg_mul_cos_add_sin_mul_I (by positivity) ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

lemma norm_kummerSaddle : ‖kummerSaddle‖ = √2 / 2 := by
  rw [kummerSaddle_eq, norm_mul, norm_cos_add_sin_mul_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

lemma one_sub_kummerSaddle : 1 - kummerSaddle = (starRingEnd ℂ) kummerSaddle := by
  rw [kummerSaddle, map_div₀, map_add, map_one, conj_I, map_ofNat]; ring

lemma log_kummerSaddle : log kummerSaddle = (-(Real.log 2 / 2) : ℝ) + (π / 4 : ℝ) * I := by
  rw [log, norm_kummerSaddle, arg_kummerSaddle]
  congr 2
  rw [show √2 / 2 = (√2)⁻¹ by
    rw [inv_eq_one_div, eq_div_iff (by positivity), div_mul_eq_mul_div,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num, Real.log_inv, Real.log_sqrt (by norm_num)]

lemma log_one_sub_kummerSaddle :
    log (1 - kummerSaddle) = (-(Real.log 2 / 2) : ℝ) - (π / 4 : ℝ) * I := by
  rw [one_sub_kummerSaddle, log_conj _ (by rw [arg_kummerSaddle]; linarith [Real.pi_pos]),
    log_kummerSaddle]
  rw [map_add, map_mul, conj_ofReal, conj_ofReal, conj_I]
  ring

/-- **The saddle point**: `ψ'(α₀) = 0`. -/
theorem dkummerPhase_saddle : dkummerPhase kummerSaddle = 0 := by
  rw [dkummerPhase, log_kummerSaddle, log_one_sub_kummerSaddle]
  push_cast
  ring

/-- `ψ''(α₀) = −4`. -/
theorem d2kummerPhase_saddle : d2kummerPhase kummerSaddle = -4 := by
  have h1 : kummerSaddle ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [kummerSaddle] at this
  have h2 : 1 - kummerSaddle ≠ 0 := by
    rw [one_sub_kummerSaddle]; exact (map_ne_zero _).2 h1
  have e1 : 1 / kummerSaddle = 1 - I := by
    rw [div_eq_iff h1, kummerSaddle]; ring_nf; rw [I_sq]; ring
  have e2 : 1 / (1 - kummerSaddle) = 1 + I := by
    rw [div_eq_iff h2, kummerSaddle]; ring_nf; rw [I_sq]; ring
  rw [d2kummerPhase, e1, e2]
  ring

/-- **The value at the saddle**: `ψ(α₀) = log 2 + iπ/2`, so `exp(N ψ(α₀)) = 2^N i^N`. -/
theorem kummerPhase_saddle : kummerPhase kummerSaddle = Real.log 2 + π / 2 * I := by
  rw [kummerPhase, xlog, xlog, log_kummerSaddle, log_one_sub_kummerSaddle, kummerSaddle]
  push_cast
  ring_nf

/-! ## Bounds along the horizontal line through the saddle -/

lemma norm_ge_half_of_im_eq {α : ℂ} (h : α.im = 1 / 2) : 1 / 2 ≤ ‖α‖ := by
  have := abs_im_le_norm α; rw [h] at this; simpa using this

lemma norm_one_sub_ge_half_of_im_eq {α : ℂ} (h : α.im = 1 / 2) : 1 / 2 ≤ ‖1 - α‖ := by
  have := abs_im_le_norm (1 - α); simp [h] at this; linarith

/-- `‖1/u − 1/c‖ ≤ 4 ‖u − c‖` when `‖u‖, ‖c‖ ≥ ½`. -/
lemma norm_one_div_sub_one_div_le {u c : ℂ} (hu : 1 / 2 ≤ ‖u‖) (hc : 1 / 2 ≤ ‖c‖) :
    ‖1 / u - 1 / c‖ ≤ 4 * ‖u - c‖ := by
  have hu0 : u ≠ 0 := by rintro rfl; norm_num at hu
  have hc0 : c ≠ 0 := by rintro rfl; norm_num at hc
  rw [div_sub_div _ _ hu0 hc0, norm_div, norm_mul, one_mul, mul_one, norm_sub_rev c u]
  rw [div_le_iff₀ (by positivity)]
  have : 1 / 4 ≤ ‖u‖ * ‖c‖ := by nlinarith
  nlinarith [norm_nonneg (u - c)]

/-- `‖ψ''(u) − ψ''(c)‖ ≤ 16 ‖u − c‖` on the line `Im = ½`. -/
lemma norm_d2kummerPhase_sub_le {u c : ℂ} (hu : u.im = 1 / 2) (hc : c.im = 1 / 2) :
    ‖d2kummerPhase u - d2kummerPhase c‖ ≤ 16 * ‖u - c‖ := by
  have h1 := norm_one_div_sub_one_div_le (norm_ge_half_of_im_eq hu) (norm_ge_half_of_im_eq hc)
  have h2 := norm_one_div_sub_one_div_le (norm_one_sub_ge_half_of_im_eq hu)
    (norm_one_sub_ge_half_of_im_eq hc)
  have e : d2kummerPhase u - d2kummerPhase c =
      -2 * ((1 / u - 1 / c) + (1 / (1 - u) - 1 / (1 - c))) := by
    unfold d2kummerPhase; ring
  rw [e, norm_mul, show ‖(-2 : ℂ)‖ = 2 by norm_num, show (1 - u) - (1 - c) = -(u - c) by ring]
    at *
  rw [norm_neg] at h2
  calc 2 * ‖1 / u - 1 / c + (1 / (1 - u) - 1 / (1 - c))‖
      ≤ 2 * (‖1 / u - 1 / c‖ + ‖1 / (1 - u) - 1 / (1 - c)‖) := by gcongr; exact norm_add_le _ _
    _ ≤ 16 * ‖u - c‖ := by linarith

/-- A point of the segment `[c, w]` is no farther from `c` than `w` is. -/
lemma norm_sub_le_of_mem_segment {c w u : ℂ} (hu : u ∈ segment ℝ c w) : ‖u - c‖ ≤ ‖w - c‖ := by
  rw [segment_eq_image'] at hu
  obtain ⟨t, ht, rfl⟩ := hu
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  exact mul_le_of_le_one_left (norm_nonneg _) ht.2

/-- The horizontal segment through the saddle, as a convex set. -/
def kummerLine : Set ℂ := {u : ℂ | u.im = 1 / 2}

lemma convex_kummerLine : Convex ℝ kummerLine := by
  intro x hx y hy a b ha hb hab
  simp only [kummerLine, mem_ofPred_eq] at *
  simp [hx, hy]
  linear_combination (1 / 2 : ℝ) * hab

lemma im_kummerSaddle : kummerSaddle.im = 1 / 2 := by simp [kummerSaddle]

/-- First-order Taylor bound for `ψ'` on the line `Im = ½`. -/
theorem norm_dkummerPhase_taylor_le {w : ℂ} (hw : w.im = 1 / 2) :
    ‖dkummerPhase w - dkummerPhase kummerSaddle - d2kummerPhase kummerSaddle * (w - kummerSaddle)‖
      ≤ 16 * ‖w - kummerSaddle‖ ^ 2 := by
  set c := kummerSaddle
  have hc : c.im = 1 / 2 := im_kummerSaddle
  have hS : segment ℝ c w ⊆ kummerLine :=
    convex_kummerLine.segment_subset (by exact hc) (by exact hw)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun u => dkummerPhase u - d2kummerPhase c * u)
    (f' := fun u => d2kummerPhase u - d2kummerPhase c)
    (C := 16 * ‖w - c‖)
    (fun u hu => by
      have hu' : u.im = 1 / 2 := hS hu
      have := ((hasDerivAt_dkummerPhase (mem_slitPlane_of_im_eq hu')
        (one_sub_mem_slitPlane_of_im_eq hu')).sub
        ((hasDerivAt_id' u).const_mul (d2kummerPhase c))).hasDerivWithinAt
        (s := segment ℝ c w)
      convert this using 1
      ring)
    (fun u hu => by
      calc _ ≤ 16 * ‖u - c‖ := norm_d2kummerPhase_sub_le (hS hu) hc
        _ ≤ 16 * ‖w - c‖ := by
          gcongr
          exact norm_sub_le_of_mem_segment hu)
    (convex_segment c w) (left_mem_segment ℝ c w) (right_mem_segment ℝ c w)
  have e : dkummerPhase w - dkummerPhase c - d2kummerPhase c * (w - c) =
      (dkummerPhase w - d2kummerPhase c * w) - (dkummerPhase c - d2kummerPhase c * c) := by ring
  rw [e]
  calc _ ≤ 16 * ‖w - c‖ * ‖w - c‖ := h
    _ = 16 * ‖w - c‖ ^ 2 := by ring

/-- **Taylor bound for the phase**: on the line `Im = ½`,
`‖ψ(z) − ψ(α₀) + 2 (z − α₀)²‖ ≤ 16 ‖z − α₀‖³`. -/
theorem norm_kummerPhase_taylor_le {z : ℂ} (hz : z.im = 1 / 2) :
    ‖kummerPhase z - kummerPhase kummerSaddle + 2 * (z - kummerSaddle) ^ 2‖ ≤
      16 * ‖z - kummerSaddle‖ ^ 3 := by
  set c := kummerSaddle
  have hc : c.im = 1 / 2 := im_kummerSaddle
  have hS : segment ℝ c z ⊆ kummerLine :=
    convex_kummerLine.segment_subset (by exact hc) (by exact hz)
  have hd : ∀ u ∈ segment ℝ c z, ‖u - c‖ ≤ ‖z - c‖ := fun u hu => by
    exact norm_sub_le_of_mem_segment hu
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun u => kummerPhase u - dkummerPhase c * (u - c) -
      d2kummerPhase c / 2 * ((u - c) * (u - c)))
    (f' := fun u => dkummerPhase u - dkummerPhase c - d2kummerPhase c * (u - c))
    (C := 16 * ‖z - c‖ ^ 2)
    (fun u hu => by
      have hu' : u.im = 1 / 2 := hS hu
      have h1 : HasDerivAt (fun y : ℂ => y - c) 1 u := (hasDerivAt_id' u).sub_const c
      have := (((hasDerivAt_kummerPhase (mem_slitPlane_of_im_eq hu')
        (one_sub_mem_slitPlane_of_im_eq hu')).sub (h1.const_mul (dkummerPhase c))).sub
        ((h1.mul h1).const_mul (d2kummerPhase c / 2))).hasDerivWithinAt (s := segment ℝ c z)
      convert this using 1
      ring)
    (fun u hu => by
      calc _ ≤ 16 * ‖u - c‖ ^ 2 := norm_dkummerPhase_taylor_le (hS hu)
        _ ≤ 16 * ‖z - c‖ ^ 2 := by gcongr; exact hd u hu)
    (convex_segment c z) (left_mem_segment ℝ c z) (right_mem_segment ℝ c z)
  have e : kummerPhase z - kummerPhase c + 2 * (z - c) ^ 2 =
      (kummerPhase z - dkummerPhase c * (z - c) - d2kummerPhase c / 2 * ((z - c) * (z - c))) -
      (kummerPhase c - dkummerPhase c * (c - c) - d2kummerPhase c / 2 * ((c - c) * (c - c))) := by
    rw [dkummerPhase_saddle, d2kummerPhase_saddle]; ring
  rw [e]
  calc _ ≤ 16 * ‖z - c‖ ^ 2 * ‖z - c‖ := h
    _ = 16 * ‖z - c‖ ^ 3 := by ring

/-! ## Decay of the real part -/

/-- `a/(a² + ¼) ≥ ½` for `½ ≤ a ≤ 1`. -/
lemma half_le_div_sq_add {a : ℝ} (h1 : 1 / 2 ≤ a) (h2 : a ≤ 1) : 1 / 2 ≤ a / (a ^ 2 + 1 / 4) := by
  rw [le_div_iff₀ (by positivity)]; nlinarith

lemma div_sq_add_nonneg {a : ℝ} (h : 0 ≤ a) : 0 ≤ a / (a ^ 2 + 1 / 4) := by positivity

/-- **`Re ψ'' ≤ −1` on the segment**: for `α = α₀ + s`, `|s| ≤ ½`. -/
theorem re_d2kummerPhase_le {s : ℝ} (hs : |s| ≤ 1 / 2) :
    (d2kummerPhase (kummerSaddle + s)).re ≤ -1 := by
  have hs1 := neg_abs_le s
  have hs2 := le_abs_self s
  set a := 1 / 2 + s with ha
  have e1 : (1 / (kummerSaddle + s)).re = a / (a ^ 2 + 1 / 4) := by
    rw [one_div, inv_re, normSq_apply]; simp [kummerSaddle, ha]; ring
  have e2 : (1 / (1 - (kummerSaddle + s))).re = (1 - a) / ((1 - a) ^ 2 + 1 / 4) := by
    rw [one_div, inv_re, normSq_apply]; simp [kummerSaddle, ha]; ring_nf
  have hre : (d2kummerPhase (kummerSaddle + s)).re =
      -2 * (a / (a ^ 2 + 1 / 4) + (1 - a) / ((1 - a) ^ 2 + 1 / 4)) := by
    rw [d2kummerPhase, ← e1, ← e2]; simp
  rw [hre]
  rcases le_total (1 / 2) a with h | h
  · have := half_le_div_sq_add h (by linarith)
    have := div_sq_add_nonneg (show 0 ≤ 1 - a by linarith)
    linarith
  · have := half_le_div_sq_add (show 1 / 2 ≤ 1 - a by linarith) (by linarith)
    have := div_sq_add_nonneg (show 0 ≤ a by linarith)
    linarith

lemma im_kummerSaddle_add (s : ℝ) : (kummerSaddle + s).im = 1 / 2 := by simp [kummerSaddle]

/-- The real part `g(s) = Re (ψ(α₀ + s) − ψ(α₀)) + s²/2`, and its derivatives. -/
lemma hasDerivAt_re_phase (s : ℝ) :
    HasDerivAt (fun s : ℝ => (kummerPhase (kummerSaddle + s)).re)
      (dkummerPhase (kummerSaddle + s)).re s := by
  have h := im_kummerSaddle_add s
  have := (hasDerivAt_kummerPhase (mem_slitPlane_of_im_eq h)
    (one_sub_mem_slitPlane_of_im_eq h)).comp (s : ℂ) ((hasDerivAt_id' (s : ℂ)).const_add kummerSaddle)
  simpa using this.real_of_complex

lemma hasDerivAt_re_dphase (s : ℝ) :
    HasDerivAt (fun s : ℝ => (dkummerPhase (kummerSaddle + s)).re)
      (d2kummerPhase (kummerSaddle + s)).re s := by
  have h := im_kummerSaddle_add s
  have := (hasDerivAt_dkummerPhase (mem_slitPlane_of_im_eq h)
    (one_sub_mem_slitPlane_of_im_eq h)).comp (s : ℂ) ((hasDerivAt_id' (s : ℂ)).const_add kummerSaddle)
  simpa using this.real_of_complex

/-- **Gaussian decay along the line**: `Re (ψ(α₀ + s) − ψ(α₀)) ≤ −s²/2` for `|s| ≤ ½`. -/
theorem re_kummerPhase_sub_le {s : ℝ} (hs : |s| ≤ 1 / 2) :
    (kummerPhase (kummerSaddle + s) - kummerPhase kummerSaddle).re ≤ -(s ^ 2 / 2) := by
  set D : Set ℝ := Icc (-(1 / 2)) (1 / 2)
  have hD : Convex ℝ D := convex_Icc _ _
  -- `g' = Re ψ'(α₀ + s) + s` is antitone on `D`, since its derivative is `Re ψ'' + 1 ≤ 0`
  set g' : ℝ → ℝ := fun s => (dkummerPhase (kummerSaddle + s)).re + s
  have hg'd : ∀ s : ℝ, HasDerivAt g' ((d2kummerPhase (kummerSaddle + s)).re + 1) s :=
    fun s => (hasDerivAt_re_dphase s).add (hasDerivAt_id s)
  have hanti : AntitoneOn g' D := by
    apply antitoneOn_of_deriv_nonpos hD
    · exact fun s _ => (hg'd s).continuousAt.continuousWithinAt
    · exact fun s _ => (hg'd s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hg'd s).deriv]
      have : |s| ≤ 1 / 2 := abs_le.2 ⟨hs.1.le, hs.2.le⟩
      linarith [re_d2kummerPhase_le this]
  have hg'0 : g' 0 = 0 := by simp [g', dkummerPhase_saddle]
  have h0D : (0 : ℝ) ∈ D := ⟨by norm_num, by norm_num⟩
  set g : ℝ → ℝ := fun s => (kummerPhase (kummerSaddle + s)).re + s ^ 2 / 2
  have hgd : ∀ s : ℝ, HasDerivAt g (g' s) s := fun s => by
    have := (hasDerivAt_re_phase s).add ((hasDerivAt_pow 2 s).div_const 2)
    convert this using 1
    simp [g']
  have hsD : s ∈ D := abs_le.1 hs
  have key : g s ≤ g 0 := by
    rcases le_total 0 s with h | h
    · -- `g` is antitone on `[0, ½]`
      have : AntitoneOn g (Icc 0 (1 / 2)) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
        · exact fun s _ => (hgd s).continuousAt.continuousWithinAt
        · exact fun s _ => (hgd s).differentiableAt.differentiableWithinAt
        · intro u hu
          rw [interior_Icc] at hu
          rw [(hgd u).deriv, ← hg'0]
          exact hanti h0D ⟨by linarith [hu.1], hu.2.le⟩ hu.1.le
      exact this ⟨le_rfl, by norm_num⟩ ⟨h, hsD.2⟩ h
    · have : MonotoneOn g (Icc (-(1 / 2)) 0) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
        · exact fun s _ => (hgd s).continuousAt.continuousWithinAt
        · exact fun s _ => (hgd s).differentiableAt.differentiableWithinAt
        · intro u hu
          rw [interior_Icc] at hu
          rw [(hgd u).deriv, ← hg'0]
          exact hanti ⟨hu.1.le, by linarith [hu.2]⟩ h0D hu.2.le
      exact this ⟨hsD.1, h⟩ ⟨by norm_num, le_rfl⟩ h
  simp only [g, ofReal_zero, add_zero] at key
  rw [sub_re]
  nlinarith [key]

end Lightlike.Asymptotics
