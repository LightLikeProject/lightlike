import Lightlike.Asymptotics.Descent

/-!
# The valleys of the continued phase at the saddle point

This is the valley step of the steepest-descent proof of `RacahSumAsymptotics`.
Write `ψ = phaseC A B`
for the continued phase (`Contour.lean`) and `s` for a nondegenerate critical point of `ψ` in the
open upper half-plane: `ψ'(s) = 0` and `ψ''(s) ≠ 0`. For a Euclidean tetrahedron, `s = saddle l`
is such a point (`IsEuclid.dphaseC_saddle`, `IsEuclid.d2phaseC_saddle_ne_zero`).

**Taylor bound** (`norm_phaseC_taylor_le`). For `c` in the open upper half-plane and
`‖z − c‖ ≤ Im c / 2`,

  `‖ψ z − ψ c − ψ'(c)(z − c) − ψ''(c)/2 · (z − c)²‖ ≤ 32 / (Im c)² · ‖z − c‖³`.

The constant comes from the Lipschitz bound `‖ψ''(w) − ψ''(z)‖ ≤ 8 ‖w − z‖ / m²` when
`Im w, Im z ≥ m > 0` (`norm_d2phaseC_sub_le`), since `ψ''` is a sum of eight terms
`± 1/(z − c)` with `c` real.

**Valleys** (`exists_valley`, `IsEuclid.exists_valley`). Write `ψ''(s) = 2b` and choose `u₀` with
`b u₀² = −‖b‖` and `‖u₀‖ = 1`: `±u₀` are the two directions of steepest descent. The *valley
rays* are `t ↦ s + t v` with `v = valleyDir u₀ ε τ = ε u₀ (1 + iτ)`, `ε = ±1`, `|τ| ≤ 1/2`.
There are `r > 0` and `K ≥ 0` such that for `0 ≤ t ≤ r`, uniformly in `ε` and `τ`:

* `s + t v` lies in the open upper half-plane;
* `‖ψ(s + t v) − ψ s − b v² t²‖ ≤ K t³`;
* `Re ψ(s + t v) ≤ Re ψ s − ‖b‖ t² / 4`, so the rays run below the saddle level except at `s`;

and in each valley (`ε = ±1`) every level `Im ψ s + η` with `|η| ≤ ‖b‖ r² / 2` is taken by
`Im ψ` at the end point `s + r v` of some valley ray (intermediate value theorem in `τ`). Here
`b v² = −‖b‖ (1 − τ² + 2iτ)` (`mul_valleyDir_sq`), so `Re (b v²) ≤ −3‖b‖/4` and
`Im (b v²) = −2‖b‖τ` runs from `‖b‖` to `−‖b‖`.

These are the data that the Laplace method needs: along each ray, `φ(t) = ψ(s + t v) − ψ s`
satisfies `φ(t) + a t²/2 = O(t³)` and `Re φ(t) ≤ −‖b‖ t²/4` with `a = −2 b v²`,
`Re a ≥ 3‖b‖/2`, and all constants are uniform in `ε` and `τ`. The two valleys use the same
`u₀`, so their half-Gaussian contributions add.
-/

open Complex Set Filter Topology Metric
open scoped Real

namespace Lightlike.Asymptotics

/-! ## The second derivative of the continued phase -/

/-- `ψ''(z) = 1/z − Σᵢ 1/(z − Aᵢ) + Σₖ 1/(z − Bₖ)`, the derivative of `dphaseC A B` on the open
upper half-plane (`hasDerivAt_dphaseC`). -/
noncomputable def d2phaseC (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) (z : ℂ) : ℂ :=
  1 / z - ∑ i, 1 / (z - A i) + ∑ k, 1 / (z - B k)

/-- For a tetrahedron, `d2phaseC` is the second derivative `d2phase` of Racah's phase. -/
lemma d2phaseC_eq_d2phase (l : Fin 6 → ℝ) : d2phaseC (faceSum l) (quadSum l) = d2phase l := rfl

/-- `d2phaseC` is the derivative of `dphaseC` on the open upper half-plane. -/
theorem hasDerivAt_dphaseC (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (dphaseC A B) (d2phaseC A B z) z := by
  have hl : ∀ c : ℝ, HasDerivAt (fun w : ℂ => log (w - c)) (1 / (z - c)) z := fun c => by
    have := (hasDerivAt_log (mem_slitPlane_sub hz c)).comp_sub_const z (c : ℂ)
    rwa [one_div]
  have h0 : HasDerivAt (fun w : ℂ => log w) (1 / z) z := by
    rw [one_div]; exact hasDerivAt_log (mem_slitPlane_of_im_pos hz)
  exact ((h0.sub (HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hl (A i))).add
    (HasDerivAt.fun_sum (u := Finset.univ) fun k _ => hl (B k))).sub_const (2 * π * I)

/-! ## A Lipschitz bound for `ψ''` and the Taylor bound for `ψ` -/

/-- `‖1/(w − c) − 1/(z − c)‖ ≤ ‖w − z‖ / m²` for real `c` when `Im w, Im z ≥ m > 0`. -/
lemma norm_one_div_sub_sub_le {w z : ℂ} (c : ℝ) {m : ℝ} (hm : 0 < m) (hw : m ≤ w.im)
    (hz : m ≤ z.im) : ‖1 / (w - c) - 1 / (z - c)‖ ≤ ‖w - z‖ / m ^ 2 := by
  have key : ∀ u : ℂ, m ≤ u.im → m ≤ ‖u - c‖ := fun u hu => by
    have := abs_im_le_norm (u - c)
    rw [sub_im, ofReal_im, sub_zero] at this
    exact hu.trans ((le_abs_self _).trans this)
  have hw' := key w hw
  have hz' := key z hz
  have hw0 : w - c ≠ 0 := norm_pos_iff.1 (hm.trans_le hw')
  have hz0 : z - c ≠ 0 := norm_pos_iff.1 (hm.trans_le hz')
  rw [div_sub_div _ _ hw0 hz0, norm_div, norm_mul,
    show (1 : ℂ) * (z - c) - (w - c) * 1 = -(w - z) by ring, norm_neg]
  apply div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hm 2)
  rw [sq]
  exact mul_le_mul hw' hz' hm.le (norm_nonneg _)

/-- `‖Σᵢ (1/(w − cᵢ) − 1/(z − cᵢ))‖ ≤ n ‖w − z‖ / m²` for `n` real points `cᵢ`. -/
lemma norm_sum_one_div_sub_le {n : ℕ} (c : Fin n → ℝ) {w z : ℂ} {m : ℝ} (hm : 0 < m)
    (hw : m ≤ w.im) (hz : m ≤ z.im) :
    ‖∑ i, (1 / (w - c i) - 1 / (z - c i))‖ ≤ n * (‖w - z‖ / m ^ 2) := by
  calc _ ≤ ∑ i, ‖1 / (w - c i) - 1 / (z - c i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, ‖w - z‖ / m ^ 2 :=
        Finset.sum_le_sum fun i _ => norm_one_div_sub_sub_le (c i) hm hw hz
    _ = n * (‖w - z‖ / m ^ 2) := by simp

/-- **Lipschitz bound for `ψ''`**: `‖ψ''(w) − ψ''(z)‖ ≤ 8 ‖w − z‖ / m²` when
`Im w, Im z ≥ m > 0`. -/
theorem norm_d2phaseC_sub_le (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) {w z : ℂ} {m : ℝ} (hm : 0 < m)
    (hw : m ≤ w.im) (hz : m ≤ z.im) :
    ‖d2phaseC A B w - d2phaseC A B z‖ ≤ 8 * ‖w - z‖ / m ^ 2 := by
  have e : d2phaseC A B w - d2phaseC A B z = (1 / (w - (0 : ℝ)) - 1 / (z - (0 : ℝ))) -
      ∑ i, (1 / (w - A i) - 1 / (z - A i)) + ∑ k, (1 / (w - B k) - 1 / (z - B k)) := by
    simp only [d2phaseC, Finset.sum_sub_distrib, ofReal_zero, sub_zero]; ring
  rw [e]
  have h0 := norm_one_div_sub_sub_le 0 hm hw hz
  have hA := norm_sum_one_div_sub_le A hm hw hz
  have hB := norm_sum_one_div_sub_le B hm hw hz
  push_cast at hA hB
  have h1 := norm_add_le ((1 / (w - (0 : ℝ)) - 1 / (z - (0 : ℝ))) -
      ∑ i, (1 / (w - A i) - 1 / (z - A i))) (∑ k, (1 / (w - B k) - 1 / (z - B k)))
  have h2 := norm_sub_le (1 / (w - (0 : ℝ)) - 1 / (z - (0 : ℝ)))
      (∑ i, (1 / (w - A i) - 1 / (z - A i)))
  have e8 : 8 * ‖w - z‖ / m ^ 2 =
      ‖w - z‖ / m ^ 2 + 4 * (‖w - z‖ / m ^ 2) + 3 * (‖w - z‖ / m ^ 2) := by ring
  linarith

/-- Points within `Im c / 2` of `c` have imaginary part at least `Im c / 2`. -/
lemma half_im_le_im {c u : ℂ} (h : ‖u - c‖ ≤ c.im / 2) : c.im / 2 ≤ u.im := by
  have h1 := abs_im_le_norm (u - c)
  rw [sub_im] at h1
  have h2 := neg_abs_le (u.im - c.im)
  linarith

/-- First-order Taylor bound for `ψ'`: for `‖w − c‖ ≤ Im c / 2`,
`‖ψ'(w) − ψ'(c) − ψ''(c)(w − c)‖ ≤ 32 / (Im c)² · ‖w − c‖²`. -/
theorem norm_dphaseC_taylor_le (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) {c w : ℂ} (hc : 0 < c.im)
    (hw : ‖w - c‖ ≤ c.im / 2) :
    ‖dphaseC A B w - dphaseC A B c - d2phaseC A B c * (w - c)‖ ≤
      32 / c.im ^ 2 * ‖w - c‖ ^ 2 := by
  have hm : 0 < c.im / 2 := by linarith
  have hS : ∀ u ∈ closedBall c ‖w - c‖, c.im / 2 ≤ u.im := fun u hu => by
    have : ‖u - c‖ ≤ ‖w - c‖ := by rw [← dist_eq_norm]; exact mem_closedBall.1 hu
    exact half_im_le_im (this.trans hw)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun u => dphaseC A B u - d2phaseC A B c * u)
    (f' := fun u => d2phaseC A B u - d2phaseC A B c)
    (C := 8 * ‖w - c‖ / (c.im / 2) ^ 2)
    (fun u hu => by
      have := ((hasDerivAt_dphaseC A B (hm.trans_le (hS u hu))).sub
        ((hasDerivAt_id' u).const_mul (d2phaseC A B c))).hasDerivWithinAt
        (s := closedBall c ‖w - c‖)
      convert this using 1
      ring)
    (fun u hu => by
      have hu' : ‖u - c‖ ≤ ‖w - c‖ := by rw [← dist_eq_norm]; exact mem_closedBall.1 hu
      calc _ ≤ 8 * ‖u - c‖ / (c.im / 2) ^ 2 :=
            norm_d2phaseC_sub_le A B hm (hS u hu) (by linarith)
        _ ≤ 8 * ‖w - c‖ / (c.im / 2) ^ 2 := by gcongr)
    (convex_closedBall c ‖w - c‖) (mem_closedBall_self (norm_nonneg _))
    (by rw [mem_closedBall, dist_eq_norm])
  have e : dphaseC A B w - dphaseC A B c - d2phaseC A B c * (w - c) =
      (dphaseC A B w - d2phaseC A B c * w) - (dphaseC A B c - d2phaseC A B c * c) := by ring
  rw [e]
  calc _ ≤ 8 * ‖w - c‖ / (c.im / 2) ^ 2 * ‖w - c‖ := h
    _ = 32 / c.im ^ 2 * ‖w - c‖ ^ 2 := by field_simp; ring

/-- **Taylor bound for the continued phase**: for `c` in the open upper half-plane and
`‖z − c‖ ≤ Im c / 2`,
`‖ψ z − ψ c − ψ'(c)(z − c) − ψ''(c)/2 · (z − c)²‖ ≤ 32 / (Im c)² · ‖z − c‖³`. -/
theorem norm_phaseC_taylor_le (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) {c z : ℂ} (hc : 0 < c.im)
    (hz : ‖z - c‖ ≤ c.im / 2) :
    ‖phaseC A B z - phaseC A B c - dphaseC A B c * (z - c) - d2phaseC A B c / 2 * (z - c) ^ 2‖ ≤
      32 / c.im ^ 2 * ‖z - c‖ ^ 3 := by
  have hm : 0 < c.im / 2 := by linarith
  have hball : ∀ u ∈ closedBall c ‖z - c‖, ‖u - c‖ ≤ ‖z - c‖ := fun u hu => by
    rw [← dist_eq_norm]; exact mem_closedBall.1 hu
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun u => phaseC A B u - dphaseC A B c * (u - c) -
      d2phaseC A B c / 2 * ((u - c) * (u - c)))
    (f' := fun u => dphaseC A B u - dphaseC A B c - d2phaseC A B c * (u - c))
    (C := 32 / c.im ^ 2 * ‖z - c‖ ^ 2)
    (fun u hu => by
      have hu' : 0 < u.im := hm.trans_le (half_im_le_im ((hball u hu).trans hz))
      have h1 : HasDerivAt (fun y : ℂ => y - c) 1 u := (hasDerivAt_id' u).sub_const c
      have := (((hasDerivAt_phaseC A B hu').sub (h1.const_mul (dphaseC A B c))).sub
        ((h1.mul h1).const_mul (d2phaseC A B c / 2))).hasDerivWithinAt
        (s := closedBall c ‖z - c‖)
      convert this using 1
      ring)
    (fun u hu => by
      calc _ ≤ 32 / c.im ^ 2 * ‖u - c‖ ^ 2 :=
            norm_dphaseC_taylor_le A B hc ((hball u hu).trans hz)
        _ ≤ 32 / c.im ^ 2 * ‖z - c‖ ^ 2 := by gcongr; exact hball u hu)
    (convex_closedBall c ‖z - c‖) (mem_closedBall_self (norm_nonneg _))
    (by rw [mem_closedBall, dist_eq_norm])
  have e : phaseC A B z - phaseC A B c - dphaseC A B c * (z - c) -
      d2phaseC A B c / 2 * (z - c) ^ 2 =
      (phaseC A B z - dphaseC A B c * (z - c) - d2phaseC A B c / 2 * ((z - c) * (z - c))) -
      (phaseC A B c - dphaseC A B c * (c - c) - d2phaseC A B c / 2 * ((c - c) * (c - c))) := by
    ring
  rw [e]
  calc _ ≤ 32 / c.im ^ 2 * ‖z - c‖ ^ 2 * ‖z - c‖ := h
    _ = 32 / c.im ^ 2 * ‖z - c‖ ^ 3 := by ring

/-! ## The saddle is nondegenerate -/

/-- **The saddle is nondegenerate**: `ψ''(s) ≠ 0`, since `ψ''(s) ∏ᵢ (s − Aᵢ) = −24 i √vol2` and
`vol2 > 0` (`IsEuclid.d2phase_saddle`). -/
theorem IsEuclid.d2phaseC_saddle_ne_zero {l : Fin 6 → ℝ} (h : IsEuclid l) :
    d2phaseC (faceSum l) (quadSum l) (saddle l) ≠ 0 := by
  intro h0
  have h1 : d2phase l (saddle l) = 0 := h0
  have h2 := h.d2phase_saddle
  rw [h1, zero_mul] at h2
  have h3 := congrArg Complex.im h2
  have hv := Real.sqrt_pos.2 h.vol2_pos
  simp only [zero_im, neg_im, mul_im, I_re, I_im, ofReal_re, ofReal_im, re_ofNat, im_ofNat]
    at h3
  linarith

/-! ## The valley rays -/

/-- The direction `ε u₀ (1 + iτ)` of a valley ray. For `b u₀² = −‖b‖`, `ε = ±1` picks the valley
and `τ` tilts the ray inside it (`mul_valleyDir_sq`). -/
noncomputable def valleyDir (u₀ : ℂ) (ε τ : ℝ) : ℂ := ε * u₀ * (1 + τ * I)

/-- `b v² = −‖b‖ (1 − τ² + 2iτ)` for `v = valleyDir u₀ ε τ`, when `b u₀² = −‖b‖` and `ε² = 1`. -/
lemma mul_valleyDir_sq {b u₀ : ℂ} (hb : b * u₀ ^ 2 = -‖b‖) {ε : ℝ} (hε : ε ^ 2 = 1) (τ : ℝ) :
    b * valleyDir u₀ ε τ ^ 2 = -‖b‖ * (1 - τ ^ 2 + 2 * τ * I) := by
  have hε' : (ε : ℂ) ^ 2 = 1 := by exact_mod_cast hε
  unfold valleyDir
  linear_combination ((ε : ℂ) ^ 2 * (1 + τ * I) ^ 2) * hb -
    (‖b‖ : ℂ) * (1 + τ * I) ^ 2 * hε' - (‖b‖ : ℂ) * (τ : ℂ) ^ 2 * I_sq

/-- `‖valleyDir u₀ ε τ‖ ≤ 3/2` for `‖u₀‖ = 1`, `ε² = 1` and `|τ| ≤ 1/2`. -/
lemma norm_valleyDir_le {u₀ : ℂ} (hu : ‖u₀‖ = 1) {ε : ℝ} (hε : ε ^ 2 = 1) {τ : ℝ}
    (hτ : |τ| ≤ 1 / 2) : ‖valleyDir u₀ ε τ‖ ≤ 3 / 2 := by
  have hε1 : |ε| = 1 := by
    have := sq_abs ε
    nlinarith [abs_nonneg ε]
  have h1 : ‖1 + (τ : ℂ) * I‖ ≤ 1 + |τ| := by
    calc _ ≤ ‖(1 : ℂ)‖ + ‖(τ : ℂ) * I‖ := norm_add_le _ _
      _ = 1 + |τ| := by rw [norm_one, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
  rw [valleyDir, norm_mul, norm_mul, norm_real, Real.norm_eq_abs, hε1, hu, one_mul, one_mul]
  linarith

/-- **Valleys at a nondegenerate critical point.** Let `s` be in the open upper half-plane with
`ψ'(s) = 0` and `ψ''(s) = 2b ≠ 0`, and let `b u₀² = −‖b‖`, `‖u₀‖ = 1`. Then there are `r > 0`
and `K ≥ 0` such that along every valley ray `t ↦ s + t v`, `v = valleyDir u₀ ε τ` with
`ε² = 1` and `|τ| ≤ 1/2`, for `0 ≤ t ≤ r`: the ray stays in the open upper half-plane,
`‖ψ(s + t v) − ψ s − b v² t²‖ ≤ K t³`, and `Re ψ(s + t v) ≤ Re ψ s − ‖b‖ t²/4`. Moreover in
each valley every level `Im ψ s + η` with `|η| ≤ ‖b‖ r²/2` is the value of `Im ψ` at the end
point `s + r v` of some valley ray. -/
theorem exists_valley (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) {s : ℂ} (hs : 0 < s.im)
    (hd : dphaseC A B s = 0) {b : ℂ} (hb : d2phaseC A B s = 2 * b) (hb0 : b ≠ 0) {u₀ : ℂ}
    (hu : ‖u₀‖ = 1) (hbu : b * u₀ ^ 2 = -‖b‖) :
    ∃ K r : ℝ, 0 < r ∧ 0 ≤ K ∧
      (∀ ε : ℝ, ε ^ 2 = 1 → ∀ τ : ℝ, |τ| ≤ 1 / 2 → ∀ t ∈ Icc (0 : ℝ) r,
        0 < (s + t * valleyDir u₀ ε τ).im ∧
        ‖phaseC A B (s + t * valleyDir u₀ ε τ) - phaseC A B s -
            b * valleyDir u₀ ε τ ^ 2 * t ^ 2‖ ≤ K * t ^ 3 ∧
        (phaseC A B (s + t * valleyDir u₀ ε τ)).re ≤ (phaseC A B s).re - ‖b‖ / 4 * t ^ 2) ∧
      (∀ ε : ℝ, ε ^ 2 = 1 → ∀ η : ℝ, |η| ≤ ‖b‖ * r ^ 2 / 2 → ∃ τ : ℝ, |τ| ≤ 1 / 2 ∧
        (phaseC A B (s + r * valleyDir u₀ ε τ)).im = (phaseC A B s).im + η) := by
  have hbn : 0 < ‖b‖ := norm_pos_iff.2 hb0
  set K₀ : ℝ := 32 / s.im ^ 2 with hK₀
  have hK₀p : 0 < K₀ := by positivity
  set r : ℝ := min (s.im / 3) (‖b‖ / (2 * (4 * K₀))) with hr
  have hr0 : 0 < r := lt_min (by linarith) (by positivity)
  have hr1 : r ≤ s.im / 3 := min_le_left _ _
  have hr2 : r ≤ ‖b‖ / (2 * (4 * K₀)) := min_le_right _ _
  -- the cubic error along every valley ray
  have key : ∀ ε : ℝ, ε ^ 2 = 1 → ∀ τ : ℝ, |τ| ≤ 1 / 2 → ∀ t ∈ Icc (0 : ℝ) r,
      0 < (s + t * valleyDir u₀ ε τ).im ∧
      ‖phaseC A B (s + t * valleyDir u₀ ε τ) - phaseC A B s -
          b * valleyDir u₀ ε τ ^ 2 * t ^ 2‖ ≤ 4 * K₀ * t ^ 3 := by
    intro ε hε τ hτ t ht
    have hv := norm_valleyDir_le hu hε hτ
    have hzs : s + t * valleyDir u₀ ε τ - s = t * valleyDir u₀ ε τ := by ring
    have hn : ‖(t : ℂ) * valleyDir u₀ ε τ‖ ≤ 3 / 2 * t := by
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
      nlinarith [ht.1]
    have hball : ‖s + t * valleyDir u₀ ε τ - s‖ ≤ s.im / 2 := by
      rw [hzs]; linarith [ht.2]
    refine ⟨(by linarith : (0 : ℝ) < s.im / 2).trans_le (half_im_le_im hball), ?_⟩
    · have hT := norm_phaseC_taylor_le A B hs hball
      rw [hd, zero_mul, sub_zero, hb, hzs] at hT
      have e : phaseC A B (s + t * valleyDir u₀ ε τ) - phaseC A B s -
          b * valleyDir u₀ ε τ ^ 2 * t ^ 2 = phaseC A B (s + t * valleyDir u₀ ε τ) -
          phaseC A B s - 2 * b / 2 * (t * valleyDir u₀ ε τ) ^ 2 := by ring
      rw [e]
      have hn3 : ‖(t : ℂ) * valleyDir u₀ ε τ‖ ^ 3 ≤ (3 / 2 * t) ^ 3 :=
        pow_le_pow_left₀ (norm_nonneg _) hn 3
      have ht3 : (3 / 2 * t) ^ 3 ≤ 4 * t ^ 3 := by nlinarith [pow_nonneg ht.1 3]
      calc _ ≤ K₀ * ‖(t : ℂ) * valleyDir u₀ ε τ‖ ^ 3 := hT
        _ ≤ K₀ * (4 * t ^ 3) := by gcongr; exact hn3.trans ht3
        _ = 4 * K₀ * t ^ 3 := by ring
  -- the quadratic term
  have hq : ∀ ε : ℝ, ε ^ 2 = 1 → ∀ τ t : ℝ,
      (b * valleyDir u₀ ε τ ^ 2 * t ^ 2).re = -‖b‖ * (1 - τ ^ 2) * t ^ 2 ∧
      (b * valleyDir u₀ ε τ ^ 2 * t ^ 2).im = -2 * ‖b‖ * τ * t ^ 2 := by
    intro ε hε τ t
    rw [mul_valleyDir_sq hbu hε τ, show -(‖b‖ : ℂ) * (1 - τ ^ 2 + 2 * τ * I) * (t : ℂ) ^ 2 =
      ((-‖b‖ * (1 - τ ^ 2) * t ^ 2 : ℝ) : ℂ) + ((-2 * ‖b‖ * τ * t ^ 2 : ℝ) : ℂ) * I by
        push_cast; ring]
    constructor <;> simp only [add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im] <;>
      ring
  -- the cubic term is at most half the quadratic one
  have hKt : ∀ t ∈ Icc (0 : ℝ) r, 4 * K₀ * t ^ 3 ≤ ‖b‖ / 2 * t ^ 2 := fun t ht => by
    have h1 : 4 * K₀ * t ≤ ‖b‖ / 2 := by
      have := ht.2.trans hr2
      rw [le_div_iff₀ (by positivity)] at this
      linarith
    have := mul_le_mul_of_nonneg_right h1 (sq_nonneg t)
    nlinarith
  refine ⟨4 * K₀, r, hr0, by positivity, fun ε hε τ hτ t ht => ?_, fun ε hε η hη => ?_⟩
  · obtain ⟨hpos, hE⟩ := key ε hε τ hτ t ht
    refine ⟨hpos, hE, ?_⟩
    have hre := re_le_norm (phaseC A B (s + t * valleyDir u₀ ε τ) - phaseC A B s -
      b * valleyDir u₀ ε τ ^ 2 * t ^ 2)
    rw [sub_re, sub_re, (hq ε hε τ t).1] at hre
    have hτ2 : τ ^ 2 ≤ 1 / 4 := by
      have := sq_abs τ
      nlinarith [abs_nonneg τ]
    have h1 := hKt t ht
    have h2 := mul_le_mul_of_nonneg_left hτ2 (by positivity : 0 ≤ ‖b‖ * t ^ 2)
    nlinarith
  · -- the intermediate value theorem in `τ`
    have hr' : r ∈ Icc (0 : ℝ) r := ⟨hr0.le, le_rfl⟩
    have him : ∀ τ : ℝ, |τ| ≤ 1 / 2 →
        |(phaseC A B (s + r * valleyDir u₀ ε τ)).im - ((phaseC A B s).im +
          -2 * ‖b‖ * τ * r ^ 2)| ≤ ‖b‖ / 2 * r ^ 2 := fun τ hτ => by
      have h1 := abs_im_le_norm (phaseC A B (s + r * valleyDir u₀ ε τ) - phaseC A B s -
        b * valleyDir u₀ ε τ ^ 2 * r ^ 2)
      rw [sub_im, sub_im, (hq ε hε τ r).2] at h1
      have h2 := (key ε hε τ hτ r hr').2
      have h3 := hKt r hr'
      rw [show (phaseC A B (s + r * valleyDir u₀ ε τ)).im - ((phaseC A B s).im +
        -2 * ‖b‖ * τ * r ^ 2) = (phaseC A B (s + r * valleyDir u₀ ε τ)).im -
          (phaseC A B s).im - -2 * ‖b‖ * τ * r ^ 2 by ring]
      linarith
    set f : ℝ → ℝ := fun τ => (phaseC A B (s + r * valleyDir u₀ ε τ)).im with hf
    have hcont : ContinuousOn f (Icc (-(1 / 2)) (1 / 2)) := fun τ hτ => by
      have hτ' : |τ| ≤ 1 / 2 := abs_le.2 hτ
      have hpos := (key ε hε τ hτ' r hr').1
      have hc : Continuous fun τ : ℝ => s + (r : ℂ) * valleyDir u₀ ε τ := by
        unfold valleyDir; fun_prop
      have h3 : ContinuousAt (fun τ : ℝ => phaseC A B (s + r * valleyDir u₀ ε τ)) τ :=
        ContinuousAt.comp (f := fun τ : ℝ => s + (r : ℂ) * valleyDir u₀ ε τ)
          (hasDerivAt_phaseC A B hpos).continuousAt hc.continuousAt
      exact (continuous_im.continuousAt.comp h3).continuousWithinAt
    have hlo := him (1 / 2) (by norm_num [abs_of_pos])
    have hhi := him (-(1 / 2)) (by norm_num [abs_of_pos])
    have hmem : (phaseC A B s).im + η ∈ Icc (f (1 / 2)) (f (-(1 / 2))) := by
      have hη' := abs_le.1 hη
      constructor
      · have := (abs_le.1 hlo).2
        simp only [hf]; nlinarith
      · have := (abs_le.1 hhi).1
        simp only [hf]; nlinarith
    obtain ⟨τ, hτ, hfτ⟩ := intermediate_value_Icc' (by norm_num) hcont hmem
    exact ⟨τ, abs_le.2 hτ, hfτ⟩

/-- **Valleys at the saddle of a Euclidean tetrahedron.** With `ψ''(s) = 2b`, there
are `u₀` with `b u₀² = −‖b‖`, `‖u₀‖ = 1`, and `r > 0`, `K ≥ 0` with the properties of
`exists_valley`: the valley rays `s + t valleyDir u₀ ε τ` (`ε = ±1`, `|τ| ≤ 1/2`, `0 ≤ t ≤ r`)
stay in the open upper half-plane, follow the quadratic approximation `ψ s + b v² t²` up to
`K t³`, run below the saddle level by at least `‖b‖ t²/4`, and their end points take in each
valley every level `Im ψ s + η` with `|η| ≤ ‖b‖ r²/2`. -/
theorem IsEuclid.exists_valley {l : Fin 6 → ℝ} (h : IsEuclid l) :
    ∃ (b u₀ : ℂ) (K r : ℝ), d2phaseC (faceSum l) (quadSum l) (saddle l) = 2 * b ∧ b ≠ 0 ∧
      ‖u₀‖ = 1 ∧ b * u₀ ^ 2 = -‖b‖ ∧ 0 < r ∧ 0 ≤ K ∧
      (∀ ε : ℝ, ε ^ 2 = 1 → ∀ τ : ℝ, |τ| ≤ 1 / 2 → ∀ t ∈ Icc (0 : ℝ) r,
        0 < (saddle l + t * valleyDir u₀ ε τ).im ∧
        ‖phaseC (faceSum l) (quadSum l) (saddle l + t * valleyDir u₀ ε τ) -
            phaseC (faceSum l) (quadSum l) (saddle l) - b * valleyDir u₀ ε τ ^ 2 * t ^ 2‖ ≤
          K * t ^ 3 ∧
        (phaseC (faceSum l) (quadSum l) (saddle l + t * valleyDir u₀ ε τ)).re ≤
          (phaseC (faceSum l) (quadSum l) (saddle l)).re - ‖b‖ / 4 * t ^ 2) ∧
      (∀ ε : ℝ, ε ^ 2 = 1 → ∀ η : ℝ, |η| ≤ ‖b‖ * r ^ 2 / 2 → ∃ τ : ℝ, |τ| ≤ 1 / 2 ∧
        (phaseC (faceSum l) (quadSum l) (saddle l + r * valleyDir u₀ ε τ)).im =
          (phaseC (faceSum l) (quadSum l) (saddle l)).im + η) := by
  set b := d2phaseC (faceSum l) (quadSum l) (saddle l) / 2
  have hb : d2phaseC (faceSum l) (quadSum l) (saddle l) = 2 * b := by ring
  have hb0 : b ≠ 0 := div_ne_zero h.d2phaseC_saddle_ne_zero two_ne_zero
  set u₀ : ℂ := (-(‖b‖ : ℂ) / b) ^ ((2 : ℕ) : ℂ)⁻¹
  have hu2 : u₀ ^ 2 = -(‖b‖ : ℂ) / b := cpow_nat_inv_pow _ two_ne_zero
  have hbu : b * u₀ ^ 2 = -‖b‖ := by rw [hu2]; field_simp
  have hu : ‖u₀‖ = 1 := by
    have : ‖u₀‖ ^ 2 = 1 := by
      rw [← norm_pow, hu2, norm_div, norm_neg, norm_real, norm_norm,
        div_self (norm_ne_zero_iff.2 hb0)]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 this
  obtain ⟨K, r, hr, hK, h1, h2⟩ :=
    Lightlike.Asymptotics.exists_valley (faceSum l) (quadSum l) h.saddle_im_pos h.dphaseC_saddle hb hb0 hu hbu
  exact ⟨b, u₀, K, r, hb, hb0, hu, hbu, hr, hK, h1, h2⟩

end Lightlike.Asymptotics
