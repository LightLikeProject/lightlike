import Lightlike.Asymptotics.Orientation

/-!
# Valleys with explicit constants

The valley bounds of `exists_valley` hold with constants that depend only on a lower bound `y`
for `Im s` and a lower bound `β` for `‖b‖`, `ψ''(s) = 2b`: along the rays `t ↦ s + t v`,
`v = valleyDir u₀ ε τ`, for `0 ≤ t ≤ valleyRadius y β = min (y/3) (β y²/256)` the cubic error is
at most `128/y² · t³` (`valley_bounds`).

The saddle `s_m`, the coefficient `b_m = ψ_m''(s_m)/2` and the oriented direction `saddleDir m` are
continuous on the open set of Euclidean tetrahedra (`continuousOn_saddleCoeff`,
`continuousOn_saddleDir`). So near a Euclidean tetrahedron `l` the valley rays along `saddleDir m`
have one radius and one cubic constant for all `m` (`IsEuclid.eventually_valley_bounds`). Applied
to the rescaled lengths `lengthsDir j λ → j`, this gives the rays of Laplace's method with
constants that do not depend on `λ`.
-/

open Complex Set Filter Topology
open scoped Real

namespace Lightlike.Asymptotics

/-- The radius `min (y/3) (β y²/256)` of the valley rays at a saddle with `Im s ≥ y` and
`‖b‖ ≥ β`. -/
noncomputable def valleyRadius (y β : ℝ) : ℝ := min (y / 3) (β * y ^ 2 / 256)

/-- The valley radius is positive when `y` and `β` are. -/
lemma valleyRadius_pos {y β : ℝ} (hy : 0 < y) (hβ : 0 < β) : 0 < valleyRadius y β :=
  lt_min (by linarith) (by positivity)

/-- **Valley bounds with explicit constants.** Let `ψ'(s) = 0`, `ψ''(s) = 2b`, `b u₀² = −‖b‖`,
`‖u₀‖ = 1`, and let `0 < y ≤ Im s` and `β ≤ ‖b‖`. Along every valley ray `t ↦ s + t v`,
`v = valleyDir u₀ ε τ` with `ε² = 1` and `|τ| ≤ 1/2`, for `0 ≤ t ≤ valleyRadius y β`: the ray
stays in the open upper half-plane, `‖ψ(s + t v) − ψ s − b v² t²‖ ≤ 128/y² · t³`, and
`Re ψ(s + t v) ≤ Re ψ s − ‖b‖ t²/4`. -/
theorem valley_bounds (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) {s : ℂ} {y : ℝ} (hy : 0 < y)
    (hys : y ≤ s.im) (hd : dphaseC A B s = 0) {b : ℂ} (hb : d2phaseC A B s = 2 * b) {β : ℝ}
    (hβb : β ≤ ‖b‖) {u₀ : ℂ} (hu : ‖u₀‖ = 1) (hbu : b * u₀ ^ 2 = -‖b‖) :
    ∀ ε : ℝ, ε ^ 2 = 1 → ∀ τ : ℝ, |τ| ≤ 1 / 2 → ∀ t ∈ Icc (0 : ℝ) (valleyRadius y β),
      0 < (s + t * valleyDir u₀ ε τ).im ∧
      ‖phaseC A B (s + t * valleyDir u₀ ε τ) - phaseC A B s -
          b * valleyDir u₀ ε τ ^ 2 * t ^ 2‖ ≤ 128 / y ^ 2 * t ^ 3 ∧
      (phaseC A B (s + t * valleyDir u₀ ε τ)).re ≤ (phaseC A B s).re - ‖b‖ / 4 * t ^ 2 := by
  have hs : 0 < s.im := hy.trans_le hys
  intro ε hε τ hτ t ht
  have hr1 : t ≤ y / 3 := ht.2.trans (min_le_left _ _)
  have hr2 : t ≤ β * y ^ 2 / 256 := ht.2.trans (min_le_right _ _)
  have hv := norm_valleyDir_le hu hε hτ
  have hzs : s + t * valleyDir u₀ ε τ - s = t * valleyDir u₀ ε τ := by ring
  have hn : ‖(t : ℂ) * valleyDir u₀ ε τ‖ ≤ 3 / 2 * t := by
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    nlinarith [ht.1]
  have hball : ‖s + t * valleyDir u₀ ε τ - s‖ ≤ s.im / 2 := by
    rw [hzs]; linarith
  have hpos : 0 < (s + t * valleyDir u₀ ε τ).im :=
    (by linarith : (0 : ℝ) < s.im / 2).trans_le (half_im_le_im hball)
  -- the cubic error
  have hE : ‖phaseC A B (s + t * valleyDir u₀ ε τ) - phaseC A B s -
      b * valleyDir u₀ ε τ ^ 2 * t ^ 2‖ ≤ 128 / y ^ 2 * t ^ 3 := by
    have hT := norm_phaseC_taylor_le A B hs hball
    rw [hd, zero_mul, sub_zero, hb, hzs] at hT
    have e : phaseC A B (s + t * valleyDir u₀ ε τ) - phaseC A B s -
        b * valleyDir u₀ ε τ ^ 2 * t ^ 2 = phaseC A B (s + t * valleyDir u₀ ε τ) -
        phaseC A B s - 2 * b / 2 * (t * valleyDir u₀ ε τ) ^ 2 := by ring
    rw [e]
    have hn3 : ‖(t : ℂ) * valleyDir u₀ ε τ‖ ^ 3 ≤ (3 / 2 * t) ^ 3 :=
      pow_le_pow_left₀ (norm_nonneg _) hn 3
    have ht3 : (3 / 2 * t) ^ 3 ≤ 4 * t ^ 3 := by nlinarith [pow_nonneg ht.1 3]
    have hK : 32 / s.im ^ 2 ≤ 32 / y ^ 2 := by gcongr
    calc _ ≤ 32 / s.im ^ 2 * ‖(t : ℂ) * valleyDir u₀ ε τ‖ ^ 3 := hT
      _ ≤ 32 / y ^ 2 * (4 * t ^ 3) := by gcongr; exact hn3.trans ht3
      _ = 128 / y ^ 2 * t ^ 3 := by ring
  refine ⟨hpos, hE, ?_⟩
  -- the real part
  have hq : (b * valleyDir u₀ ε τ ^ 2 * t ^ 2).re = -‖b‖ * (1 - τ ^ 2) * t ^ 2 := by
    rw [mul_valleyDir_sq hbu hε τ, show -(‖b‖ : ℂ) * (1 - τ ^ 2 + 2 * τ * I) * (t : ℂ) ^ 2 =
      ((-‖b‖ * (1 - τ ^ 2) * t ^ 2 : ℝ) : ℂ) + ((-2 * ‖b‖ * τ * t ^ 2 : ℝ) : ℂ) * I by
        push_cast; ring]
    simp only [add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im]
    ring
  have hKt : 128 / y ^ 2 * t ^ 3 ≤ ‖b‖ / 2 * t ^ 2 := by
    have h1 : 128 / y ^ 2 * t ≤ ‖b‖ / 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hβb (sq_nonneg y)]
    have := mul_le_mul_of_nonneg_right h1 (sq_nonneg t)
    nlinarith
  have hre := re_le_norm (phaseC A B (s + t * valleyDir u₀ ε τ) - phaseC A B s -
    b * valleyDir u₀ ε τ ^ 2 * t ^ 2)
  rw [sub_re, sub_re, hq] at hre
  have hτ2 : τ ^ 2 ≤ 1 / 4 := by
    have := sq_abs τ
    nlinarith [abs_nonneg τ]
  have h2 := mul_le_mul_of_nonneg_left hτ2 (by positivity : 0 ≤ ‖b‖ * t ^ 2)
  nlinarith

/-! ## Continuity of the saddle data in the edge lengths -/

/-- For a Euclidean tetrahedron, `s − x` lies in the slit plane for every real `x`. -/
lemma IsEuclid.saddle_sub_mem_slitPlane {l : Fin 6 → ℝ} (h : IsEuclid l) (x : ℝ) :
    saddle l - x ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  right
  simp only [sub_im, ofReal_im, sub_zero]
  exact h.saddle_im_pos.ne'

/-- `b_m = ψ_m''(s_m)/2` is continuous on the open set of Euclidean tetrahedra. -/
theorem continuousOn_saddleCoeff : ContinuousOn saddleCoeff {l : Fin 6 → ℝ | IsEuclid l} := by
  have hinv : ∀ g : (Fin 6 → ℝ) → ℝ, Continuous g →
      ContinuousOn (fun l => 1 / (saddle l - (g l : ℂ))) {l : Fin 6 → ℝ | IsEuclid l} := by
    intro g hg
    refine continuousOn_const.div
      (continuousOn_saddle.sub (continuous_ofReal.comp hg).continuousOn) ?_
    intro l hl h0
    have := congrArg Complex.im h0
    simp only [sub_im, ofReal_im, sub_zero, zero_im] at this
    exact (show IsEuclid l from hl).saddle_im_pos.ne' this
  have h0 : ContinuousOn (fun l => 1 / saddle l) {l : Fin 6 → ℝ | IsEuclid l} := by
    simpa only [ofReal_zero, sub_zero] using hinv (fun _ => 0) continuous_const
  unfold saddleCoeff d2phaseC
  exact ((h0.sub (continuousOn_finsetSum _ fun i _ => hinv _ (continuous_faceSum i))).add
    (continuousOn_finsetSum _ fun k _ => hinv _ (continuous_quadSum k))).div_const 2

/-- The oriented valley direction `saddleDir m` is continuous on the open set of Euclidean
tetrahedra: the arguments `arg (s_m − Aᵢ(m))` are taken in the open upper half-plane, away from
the cut of `arg`. -/
theorem continuousOn_saddleDir : ContinuousOn saddleDir {l : Fin 6 → ℝ | IsEuclid l} := by
  have harg : ∀ i, ContinuousOn (fun l => arg (saddle l - faceSum l i))
      {l : Fin 6 → ℝ | IsEuclid l} := by
    intro i l hl
    have hs : ContinuousWithinAt (fun l => saddle l - (faceSum l i : ℂ))
        {l : Fin 6 → ℝ | IsEuclid l} l :=
      (continuousOn_saddle l hl).sub
        ((continuous_ofReal.comp (continuous_faceSum i)).continuousWithinAt)
    exact ContinuousAt.comp_continuousWithinAt (g := arg)
      (f := fun l => saddle l - (faceSum l i : ℂ))
      (continuousAt_arg ((show IsEuclid l from hl).saddle_sub_mem_slitPlane _)) hs
  have hsum : ContinuousOn (fun l => ((∑ i, arg (saddle l - faceSum l i)) / 2 - π / 4 : ℝ))
      {l : Fin 6 → ℝ | IsEuclid l} :=
    ((continuousOn_finsetSum _ fun i _ => harg i).div_const 2).sub continuousOn_const
  have hc : ContinuousOn (fun l => (((∑ i, arg (saddle l - faceSum l i)) / 2 - π / 4 : ℝ) : ℂ) * I)
      {l : Fin 6 → ℝ | IsEuclid l} :=
    (continuous_ofReal.comp_continuousOn hsum).mul continuousOn_const
  exact Complex.continuous_exp.comp_continuousOn hc

/-- `b_m → b_j` along the rescaled lengths `lengthsDir j λ`. -/
theorem tendsto_saddleCoeff_lengthsDir {j : Fin 6 → ℕ} (h : IsEuclid fun e => (j e : ℝ)) :
    Tendsto (fun lam => saddleCoeff (lengthsDir j lam)) atTop
      (𝓝 (saddleCoeff fun e => (j e : ℝ))) :=
  ((continuousOn_saddleCoeff.continuousAt (isOpen_isEuclid.mem_nhds h)).tendsto).comp
    (tendsto_lengthsDir j)

/-- `saddleDir m → saddleDir j` along the rescaled lengths `lengthsDir j λ`. -/
theorem tendsto_saddleDir_lengthsDir {j : Fin 6 → ℕ} (h : IsEuclid fun e => (j e : ℝ)) :
    Tendsto (fun lam => saddleDir (lengthsDir j lam)) atTop
      (𝓝 (saddleDir fun e => (j e : ℝ))) :=
  ((continuousOn_saddleDir.continuousAt (isOpen_isEuclid.mem_nhds h)).tendsto).comp
    (tendsto_lengthsDir j)

/-- **Uniform valleys near a Euclidean tetrahedron.** For a Euclidean `l` there are a radius
`r > 0`, a constant `K` and `β > 0` such that every `m` close to `l` is Euclidean, has
`‖b_m‖ ≥ β`, and along all valley rays `t ↦ s_m + t v`, `v = valleyDir (saddleDir m) ε τ`
(`ε² = 1`, `|τ| ≤ 1/2`, `0 ≤ t ≤ r`) the ray stays in the open upper half-plane,
`‖ψ_m(s_m + t v) − ψ_m(s_m) − b_m v² t²‖ ≤ K t³` and
`Re ψ_m(s_m + t v) ≤ Re ψ_m(s_m) − ‖b_m‖ t²/4`. -/
theorem IsEuclid.eventually_valley_bounds {l : Fin 6 → ℝ} (h : IsEuclid l) :
    ∃ r K β : ℝ, 0 < r ∧ 0 < β ∧ ∀ᶠ m in 𝓝 l, IsEuclid m ∧ β ≤ ‖saddleCoeff m‖ ∧
      ∀ ε : ℝ, ε ^ 2 = 1 → ∀ τ : ℝ, |τ| ≤ 1 / 2 → ∀ t ∈ Icc (0 : ℝ) r,
        0 < (saddle m + t * valleyDir (saddleDir m) ε τ).im ∧
        ‖phaseC (faceSum m) (quadSum m) (saddle m + t * valleyDir (saddleDir m) ε τ) -
            phaseC (faceSum m) (quadSum m) (saddle m) -
            saddleCoeff m * valleyDir (saddleDir m) ε τ ^ 2 * t ^ 2‖ ≤ K * t ^ 3 ∧
        (phaseC (faceSum m) (quadSum m) (saddle m + t * valleyDir (saddleDir m) ε τ)).re ≤
          (phaseC (faceSum m) (quadSum m) (saddle m)).re - ‖saddleCoeff m‖ / 4 * t ^ 2 := by
  have hb0 : 0 < ‖saddleCoeff l‖ := norm_pos_iff.2 h.saddleCoeff_ne_zero
  have hy : 0 < (saddle l).im / 2 := half_pos h.saddle_im_pos
  have hβ : 0 < ‖saddleCoeff l‖ / 2 := half_pos hb0
  have hE : ∀ᶠ m in 𝓝 l, IsEuclid m := isOpen_isEuclid.mem_nhds h
  have hS : ∀ᶠ m in 𝓝 l, (saddle l).im / 2 ≤ (saddle m).im := by
    have ht : Tendsto (fun m => (saddle m).im) (𝓝 l) (𝓝 (saddle l).im) :=
      (continuous_im.tendsto _).comp (continuousOn_saddle.continuousAt hE).tendsto
    exact (ht.eventually (lt_mem_nhds (half_lt_self h.saddle_im_pos))).mono fun _ h => h.le
  have hB : ∀ᶠ m in 𝓝 l, ‖saddleCoeff l‖ / 2 ≤ ‖saddleCoeff m‖ := by
    have ht : Tendsto (fun m => ‖saddleCoeff m‖) (𝓝 l) (𝓝 ‖saddleCoeff l‖) :=
      (continuous_norm.tendsto _).comp (continuousOn_saddleCoeff.continuousAt hE).tendsto
    exact (ht.eventually (lt_mem_nhds (half_lt_self hb0))).mono fun _ h => h.le
  refine ⟨valleyRadius ((saddle l).im / 2) (‖saddleCoeff l‖ / 2), 128 / ((saddle l).im / 2) ^ 2,
    ‖saddleCoeff l‖ / 2, valleyRadius_pos hy hβ, hβ, ?_⟩
  filter_upwards [hE, hS, hB] with m hm hms hmb
  exact ⟨hm, hmb, valley_bounds _ _ hy hms hm.dphaseC_saddle (d2phaseC_saddle_eq m) hmb
    (norm_saddleDir m) hm.mul_saddleDir_sq⟩

end Lightlike.Asymptotics
