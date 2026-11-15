import Mathlib

/-!
# Second-order Taylor bound for `arccos` (RC6b, step 4b)

The angle of a triangle is `arccos` of a ratio of squared lengths. The comparison of the angle
computed from geodesic lengths with the frozen-metric angle needs `arccos` to second order, with a
remainder that is uniform on `[-s, s]`, `s < 1`.

With `q(y) = √(1 - y²)`: `arccos' = -1/q`, `arccos'' = -y/q³`, `arccos''' = -(1 + 2y²)/q⁵`.

## Main results

* `abs_arccos_taylor_le`: for `x, y ∈ [-s, s]`, `0 ≤ s < 1`, with `c = 1/√(1 - s²)`,
  `|arccos y - arccos x + (y - x)/q(x) + x (y - x)²/(2 q(x)³)| ≤ 3 c⁵ |y - x|³`.
-/

open Real

namespace Lightlike.CMS

/-- `q y = √(1 - y²)`. -/
noncomputable def qq (y : ℝ) : ℝ := √(1 - y ^ 2)

theorem hasDerivAt_qq {y : ℝ} (h : |y| < 1) : HasDerivAt qq (-y / qq y) y := by
  have h1 : 0 < 1 - y ^ 2 := by nlinarith [abs_nonneg y, sq_abs y]
  have := ((hasDerivAt_pow 2 y).const_sub 1).sqrt h1.ne'
  refine HasDerivAt.congr_deriv (f := fun y => √(1 - y ^ 2)) this ?_
  have h3 : √(1 - y ^ 2) ≠ 0 := (Real.sqrt_pos.mpr h1).ne'
  simp only [qq, Nat.cast_ofNat]
  field_simp
  ring

theorem qq_pos {y : ℝ} (h : |y| < 1) : 0 < qq y :=
  Real.sqrt_pos.mpr (by nlinarith [abs_nonneg y, sq_abs y])

theorem qq_sq {y : ℝ} (h : |y| < 1) : qq y ^ 2 = 1 - y ^ 2 :=
  Real.sq_sqrt (by nlinarith [abs_nonneg y, sq_abs y])

/-- `κ y = -y / q³`, the second derivative of `arccos`. -/
noncomputable def kap (y : ℝ) : ℝ := -y / qq y ^ 3

/-- `ψ y = -1 / q`, the derivative of `arccos`. -/
noncomputable def psi (y : ℝ) : ℝ := -1 / qq y

theorem hasDerivAt_psi {y : ℝ} (h : |y| < 1) : HasDerivAt psi (kap y) y := by
  have hq := hasDerivAt_qq h
  have hp := qq_pos h
  have := (hasDerivAt_const y (-1 : ℝ)).div hq hp.ne'
  refine HasDerivAt.congr_deriv (f := fun y => (-1 : ℝ) / qq y) this ?_
  have : qq y ≠ 0 := hp.ne'
  simp only [kap]
  field_simp
  ring

theorem hasDerivAt_kap {y : ℝ} (h : |y| < 1) : HasDerivAt kap (-(1 + 2 * y ^ 2) / qq y ^ 5) y := by
  have hq := hasDerivAt_qq h
  have hp := qq_pos h
  have h3 := hq.pow 3
  have := ((hasDerivAt_id y).neg).div h3 (pow_pos hp 3).ne'
  refine HasDerivAt.congr_deriv (f := fun y => -y / qq y ^ 3) this ?_
  have h5 := qq_sq h
  have : qq y ≠ 0 := hp.ne'
  simp only [Pi.pow_apply, Pi.neg_apply, id, Nat.cast_ofNat]
  field_simp
  generalize qq y = q at *
  have h6 : y ^ 2 = 1 - q ^ 2 := by linarith
  rw [h6]
  ring

theorem qq_ge {s w : ℝ} (hs : s < 1) (hw : w ∈ Set.Icc (-s) s) : √(1 - s ^ 2) ≤ qq w := by
  have hw2 : w ^ 2 ≤ s ^ 2 := by nlinarith [hw.1, hw.2]
  exact Real.sqrt_le_sqrt (by linarith)

theorem abs_w_lt {s w : ℝ} (hs : s < 1) (hw : w ∈ Set.Icc (-s) s) : |w| < 1 :=
  abs_lt.mpr ⟨by linarith [hw.1], by linarith [hw.2]⟩

/-- Bound on the third derivative of `arccos` on `[-s, s]`. -/
theorem abs_dkap_le {s w : ℝ} (hs0 : 0 ≤ s) (hs : s < 1) (hw : w ∈ Set.Icc (-s) s) :
    |-(1 + 2 * w ^ 2) / qq w ^ 5| ≤ 3 / √(1 - s ^ 2) ^ 5 := by
  have hm : 0 < √(1 - s ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hq := qq_ge hs hw
  have hw2 : w ^ 2 ≤ 1 := by nlinarith [hw.1, hw.2]
  have hqp : 0 < qq w := lt_of_lt_of_le hm hq
  rw [abs_div, abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 + 2 * w ^ 2),
    abs_of_pos (pow_pos hqp 5)]
  calc (1 + 2 * w ^ 2) / qq w ^ 5 ≤ 3 / qq w ^ 5 := by gcongr; linarith
    _ ≤ 3 / √(1 - s ^ 2) ^ 5 := by gcongr

/-- **Second-order Taylor bound for `arccos`.** For `x, y ∈ [-s, s]`, `0 ≤ s < 1`, with
`m = √(1 - s²)`: `|arccos y - arccos x + (y - x)/q(x) + x (y - x)²/(2 q(x)³)| ≤ 3 |y - x|³ / m⁵`,
where `q(x) = √(1 - x²)`. -/
theorem abs_arccos_taylor_le {s x y : ℝ} (hs0 : 0 ≤ s) (hs : s < 1) (hx : x ∈ Set.Icc (-s) s)
    (hy : y ∈ Set.Icc (-s) s) :
    |arccos y - arccos x + (y - x) / qq x + x * (y - x) ^ 2 / (2 * qq x ^ 3)| ≤
      3 * |y - x| ^ 3 / √(1 - s ^ 2) ^ 5 := by
  have hm : 0 < √(1 - s ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  set M := 3 / √(1 - s ^ 2) ^ 5 with hM
  have hM0 : 0 ≤ M := by positivity
  set S := Set.uIcc x y with hS
  have hSsub : S ⊆ Set.Icc (-s) s := Set.uIcc_subset_Icc hx hy
  have hSconv : Convex ℝ S := convex_uIcc x y
  have hxS : x ∈ S := Set.left_mem_uIcc
  have hyS : y ∈ S := Set.right_mem_uIcc
  have hdist : ∀ z ∈ S, |z - x| ≤ |y - x| := by
    intro z hz
    rcases le_total x y with h | h
    · rw [hS, Set.uIcc_of_le h] at hz
      rw [abs_of_nonneg (by linarith [hz.1]), abs_of_nonneg (by linarith)]; linarith [hz.2]
    · rw [hS, Set.uIcc_of_ge h] at hz
      rw [abs_of_nonpos (by linarith [hz.2]), abs_of_nonpos (by linarith)]; linarith [hz.1]
  -- first-order remainder of psi
  have hpsi : ∀ z ∈ S, |psi z - psi x - kap x * (z - x)| ≤ M * |y - x| * |z - x| := by
    intro z hz
    have hSz : Set.uIcc x z ⊆ S := Set.uIcc_subset_uIcc hxS hz
    have hconv : Convex ℝ (Set.uIcc x z) := convex_uIcc x z
    have hder : ∀ w ∈ Set.uIcc x z,
        HasDerivWithinAt (fun w => psi w - psi x - kap x * (w - x)) (kap w - kap x)
          (Set.uIcc x z) w := by
      intro w hw
      have hw' := hSsub (hSz hw)
      have h1 := hasDerivAt_psi (abs_w_lt hs hw')
      have h2 : HasDerivAt (fun w : ℝ => kap x * (w - x)) (kap x) w := by
        simpa using ((hasDerivAt_id w).sub_const x).const_mul (kap x)
      exact ((h1.sub_const (psi x)).sub h2).hasDerivWithinAt
    have hbd : ∀ w ∈ Set.uIcc x z, ‖kap w - kap x‖ ≤ M * |y - x| := by
      intro w hw
      have hw' := hSsub (hSz hw)
      have hlip : ‖kap w - kap x‖ ≤ M * |w - x| := by
        have := (convex_Icc (-s) s).norm_image_sub_le_of_norm_hasDerivWithin_le
          (f := kap) (f' := fun w => -(1 + 2 * w ^ 2) / qq w ^ 5) (C := M)
          (fun w hw => (hasDerivAt_kap (abs_w_lt hs hw)).hasDerivWithinAt)
          (fun w hw => by rw [Real.norm_eq_abs]; exact abs_dkap_le hs0 hs hw) hx hw'
        simpa [Real.norm_eq_abs, abs_sub_comm] using this
      have hwz : |w - x| ≤ |y - x| := hdist w (hSz hw)
      calc _ ≤ M * |w - x| := hlip
        _ ≤ M * |y - x| := by gcongr
    have := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd
      Set.left_mem_uIcc Set.right_mem_uIcc
    simp only [sub_self, mul_zero, sub_zero, Real.norm_eq_abs] at this
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  -- integrate once more
  have hder2 : ∀ z ∈ S, HasDerivWithinAt
      (fun z => arccos z - arccos x - psi x * (z - x) - kap x * (z - x) ^ 2 / 2)
      (psi z - psi x - kap x * (z - x)) S z := by
    intro z hz
    have hz' := hSsub hz
    have hlt := abs_w_lt hs hz'
    have h1 : HasDerivAt arccos (psi z) z := by
      have := hasDerivAt_arccos (x := z) (by linarith [hz'.1]) (by linarith [hz'.2])
      convert this using 1
      simp only [psi, qq]; rw [neg_div, one_div]
    have h2 : HasDerivAt (fun z : ℝ => psi x * (z - x)) (psi x) z := by
      simpa using ((hasDerivAt_id z).sub_const x).const_mul (psi x)
    have h3 : HasDerivAt (fun z : ℝ => kap x * (z - x) ^ 2 / 2) (kap x * (z - x)) z := by
      have := (((hasDerivAt_id z).sub_const x).pow 2).const_mul (kap x) |>.div_const 2
      refine HasDerivAt.congr_deriv (f := fun z : ℝ => kap x * (z - x) ^ 2 / 2) this ?_
      simp; ring
    exact (((h1.sub_const (arccos x)).sub h2).sub h3).hasDerivWithinAt
  have hbd2 : ∀ z ∈ S, ‖psi z - psi x - kap x * (z - x)‖ ≤ M * |y - x| ^ 2 := by
    intro z hz
    rw [Real.norm_eq_abs]
    calc _ ≤ M * |y - x| * |z - x| := hpsi z hz
      _ ≤ M * |y - x| * |y - x| :=
          mul_le_mul_of_nonneg_left (hdist z hz) (mul_nonneg hM0 (abs_nonneg _))
      _ = _ := by ring
  have := hSconv.norm_image_sub_le_of_norm_hasDerivWithin_le hder2 hbd2 hxS hyS
  simp only [sub_self, mul_zero, zero_sub, sub_zero, Real.norm_eq_abs, zero_div] at this
  have hqx : qq x ≠ 0 := (qq_pos (abs_w_lt hs hx)).ne'
  have this' : |arccos y - arccos x - psi x * (y - x) - kap x * (y - x) ^ 2 / 2| ≤
      M * |y - x| ^ 2 * |y - x| := by simpa using this
  have e : arccos y - arccos x + (y - x) / qq x + x * (y - x) ^ 2 / (2 * qq x ^ 3) =
      arccos y - arccos x - psi x * (y - x) - kap x * (y - x) ^ 2 / 2 := by
    simp only [psi, kap]; field_simp; ring
  rw [e]
  calc _ ≤ M * |y - x| ^ 2 * |y - x| := this'
    _ = _ := by rw [hM]; ring

/-- **Non-vacuity.** The bound holds, with all hypotheses met, at `x = 0`, `y = 1/10`, `s = 3/5`
(`m = 4/5`). -/
example : |arccos (1 / 10) - arccos 0 + (1 / 10 - 0) / qq 0 + 0 * (1 / 10 - 0) ^ 2 / (2 * qq 0 ^ 3)| ≤
    3 * |(1 / 10 : ℝ) - 0| ^ 3 / √(1 - (3 / 5 : ℝ) ^ 2) ^ 5 :=
  abs_arccos_taylor_le (s := 3 / 5) (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num⟩

end Lightlike.CMS
