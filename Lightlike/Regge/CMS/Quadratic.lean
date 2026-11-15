import Mathlib
import Lightlike.Regge.CMS.Taylor
import Lightlike.Regge.CMS.Angle

/-!
# Second-order expansion of a triangle angle (RC6b, step 4b)

The squared lengths of a triangle are `a₀ (1 + x)`, `b₀ (1 + y)`, `c₀ (1 + z)` with small relative
errors. The cosine of the angle between the first two edges is then a smooth function of
`(x, y, z)`; this file expands it, and the angle, to second order with an explicit cubic remainder.

## Main results

* `abs_invSqrt_sub_le`: `|1/√(1+x) - (1 - x/2 + 3x²/8)| ≤ 2|x|³` for `|x| ≤ 1/2`.
-/

open Real

namespace Lightlike.CMS

/-- The second-order Taylor polynomial of `(1 + x)^(-1/2)`. -/
noncomputable def invSqrtPoly (x : ℝ) : ℝ := 1 - x / 2 + 3 * x ^ 2 / 8

/-- **`1/√(1+x)` to second order.** -/
theorem abs_invSqrt_sub_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |1 / √(1 + x) - invSqrtPoly x| ≤ 2 * |x| ^ 3 := by
  have hx1 := abs_le.mp hx
  have hpos : 0 < 1 + x := by linarith [hx1.1]
  set t := 1 / √(1 + x) with ht
  have hs : 0 < √(1 + x) := Real.sqrt_pos.mpr hpos
  have ht0 : 0 < t := by positivity
  have ht2 : t ^ 2 * (1 + x) = 1 := by
    rw [ht, div_pow, Real.sq_sqrt hpos.le]; field_simp
  set p := invSqrtPoly x with hp
  have hp0 : 21 / 25 ≤ p := by
    rw [hp, invSqrtPoly]; nlinarith [sq_nonneg (x - 2 / 3)]
  have hx3 : |x| ^ 3 = |x ^ 3| := by rw [abs_pow]
  have he : p ^ 2 * (1 + x) - 1 = x ^ 3 * (5 / 8 - 15 / 64 * x + 9 / 64 * x ^ 2) := by
    rw [hp, invSqrtPoly]; ring
  have hfac : |5 / 8 - 15 / 64 * x + 9 / 64 * x ^ 2| ≤ 4 / 5 := by
    rw [abs_le]; constructor <;> nlinarith [hx1.1, hx1.2]
  have hkey : (p - t) * (p + t) * (1 + x) = x ^ 3 * (5 / 8 - 15 / 64 * x + 9 / 64 * x ^ 2) := by
    rw [← he]; nlinarith [ht2]
  have hden : 2 / 5 ≤ (p + t) * (1 + x) := by nlinarith [hx1.1]
  have habs : |p - t| * ((p + t) * (1 + x)) ≤ |x| ^ 3 * (4 / 5) := by
    have := congrArg abs hkey
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by positivity : 0 < p + t),
      abs_of_pos hpos, abs_pow] at this
    calc |p - t| * ((p + t) * (1 + x)) = |p - t| * (p + t) * (1 + x) := by ring
      _ = _ := this
      _ ≤ |x| ^ 3 * (4 / 5) := by gcongr
  rw [abs_sub_comm]
  have h0 : 0 ≤ |p - t| := abs_nonneg _
  nlinarith [pow_nonneg (abs_nonneg x) 3]

/-- Cubic terms of the product of two second-order polynomials. -/
theorem abs_cubic_le {x y ε : ℝ} (hxe : |x| ≤ ε) (hye : |y| ≤ ε) (hε : ε ≤ 1 / 2) :
    |-3 * x * y ^ 2 / 16 - 3 * x ^ 2 * y / 16 + 9 * x ^ 2 * y ^ 2 / 64| ≤ ε ^ 3 := by
  have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) hxe
  have b1 : |x * y ^ 2| ≤ ε ^ 3 := by
    rw [abs_mul, abs_pow, pow_succ' ε 2]
    exact mul_le_mul hxe (pow_le_pow_left₀ (abs_nonneg _) hye 2) (by positivity) hε0
  have b2 : |x ^ 2 * y| ≤ ε ^ 3 := by
    rw [abs_mul, abs_pow, pow_succ ε 2]
    exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hxe 2) hye (abs_nonneg _) (by positivity)
  have b3 : |x ^ 2 * y ^ 2| ≤ ε ^ 3 := by
    rw [abs_mul, abs_pow, abs_pow]
    have h1 : |x| ^ 2 * |y| ^ 2 ≤ ε ^ 2 * ε ^ 2 :=
      mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hxe 2) (pow_le_pow_left₀ (abs_nonneg _) hye 2)
        (by positivity) (by positivity)
    have h2 : ε ^ 2 * ε ^ 2 ≤ ε ^ 3 := by
      have : ε ^ 2 * ε ^ 2 = ε ^ 3 * ε := by ring
      rw [this]; nlinarith [pow_nonneg hε0 3]
    exact h1.trans h2
  rw [abs_le] at b1 b2 b3 ⊢
  constructor <;> linarith [b1.1, b1.2, b2.1, b2.2, b3.1, b3.2]

/-- The cosine of the angle between the edges with squared lengths `a`, `b`, the third being `c`. -/
noncomputable def cosArg (a b c : ℝ) : ℝ := (a + b - c) / (2 * √(a * b))

/-- First-order term of the cosine: with `P = (a₀ x + b₀ y - c₀ z) / (2 √(a₀ b₀))` and
`u = cosArg a₀ b₀ c₀`, it is `P - u (x + y) / 2`. -/
noncomputable def cosLin (a₀ b₀ c₀ x y z : ℝ) : ℝ :=
  (a₀ * x + b₀ * y - c₀ * z) / (2 * √(a₀ * b₀)) - cosArg a₀ b₀ c₀ * (x + y) / 2

/-- Second-order term of the cosine. -/
noncomputable def cosQuad (a₀ b₀ c₀ x y z : ℝ) : ℝ :=
  -((a₀ * x + b₀ * y - c₀ * z) / (2 * √(a₀ * b₀))) * (x + y) / 2 +
    cosArg a₀ b₀ c₀ * (3 * (x ^ 2 + y ^ 2) / 8 + x * y / 4)

set_option maxHeartbeats 800000 in
/-- **The cosine of a perturbed triangle to second order.** The squared lengths `a₀ (1 + x)`,
`b₀ (1 + y)`, `c₀ (1 + z)` have relative errors at most `ε ≤ 1/2`, and `a₀ + b₀ + c₀ ≤ 2 R √(a₀ b₀)`
(bounded side ratio). Then the cosine differs from `u + cosLin + cosQuad` by at most `(7 + 5 R) ε³`,
where `u` is the unperturbed cosine. -/
theorem abs_cosArg_expansion_le {a₀ b₀ c₀ x y z ε R : ℝ} (ha : 0 < a₀) (hb : 0 < b₀)
    (hx : |x| ≤ ε) (hy : |y| ≤ ε) (hz : |z| ≤ ε) (hε : ε ≤ 1 / 2)
    (hc : 0 ≤ c₀) (hu : |cosArg a₀ b₀ c₀| ≤ 1) (hR : a₀ + b₀ + c₀ ≤ 2 * R * √(a₀ * b₀)) :
    |cosArg (a₀ * (1 + x)) (b₀ * (1 + y)) (c₀ * (1 + z)) - cosArg a₀ b₀ c₀ -
        cosLin a₀ b₀ c₀ x y z - cosQuad a₀ b₀ c₀ x y z| ≤ (7 + 5 * R) * ε ^ 3 := by
  have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) hx
  have hx1 := abs_le.mp hx
  have hy1 := abs_le.mp hy
  have hx' : |x| ≤ 1 / 2 := hx.trans hε
  have hy' : |y| ≤ 1 / 2 := hy.trans hε
  have hq0 : 0 < √(a₀ * b₀) := Real.sqrt_pos.mpr (mul_pos ha hb)
  set q0 := √(a₀ * b₀) with hq0def
  set u := cosArg a₀ b₀ c₀ with hudef
  set P := (a₀ * x + b₀ * y - c₀ * z) / (2 * q0) with hP
  have hS : |P| ≤ R * ε := by
    rw [hP, abs_div, abs_of_pos (by positivity : 0 < 2 * q0), div_le_iff₀ (by positivity)]
    have h1 : |a₀ * x + b₀ * y - c₀ * z| ≤ a₀ * ε + b₀ * ε + c₀ * ε := by
      calc _ ≤ |a₀ * x + b₀ * y| + |c₀ * z| := abs_sub _ _
        _ ≤ |a₀ * x| + |b₀ * y| + |c₀ * z| := by gcongr; exact abs_add_le _ _
        _ ≤ _ := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos ha, abs_of_pos hb]
          rw [abs_of_nonneg hc]; gcongr
    calc _ ≤ (a₀ + b₀ + c₀) * ε := by linarith
      _ ≤ 2 * R * q0 * ε := by gcongr
      _ = _ := by ring
  have hR0 : 0 ≤ R := by
    by_contra h
    have h := not_le.mp h
    nlinarith [mul_pos (neg_pos.mpr h) hq0]
  have hsq : √(a₀ * (1 + x) * (b₀ * (1 + y))) = q0 * √(1 + x) * √(1 + y) := by
    have : a₀ * (1 + x) * (b₀ * (1 + y)) = a₀ * b₀ * (1 + x) * (1 + y) := by ring
    rw [this, Real.sqrt_mul (by nlinarith [mul_pos ha hb, hx1.1]), Real.sqrt_mul (by positivity)]
  have hf : cosArg (a₀ * (1 + x)) (b₀ * (1 + y)) (c₀ * (1 + z)) =
      (u + P) * (1 / √(1 + x) * (1 / √(1 + y))) := by
    have h1 : 0 < √(1 + x) := Real.sqrt_pos.mpr (by linarith [hx1.1])
    have h2 : 0 < √(1 + y) := Real.sqrt_pos.mpr (by linarith [hy1.1])
    rw [cosArg, hsq, hudef, cosArg, hP]
    field_simp
    ring
  -- the factor ρ
  set tx := 1 / √(1 + x) with htx
  set ty := 1 / √(1 + y) with hty
  have ex := abs_invSqrt_sub_le hx'
  have ey := abs_invSqrt_sub_le hy'
  rw [← htx] at ex
  rw [← hty] at ey
  have hpx : |invSqrtPoly x| ≤ 27 / 20 := by
    rw [invSqrtPoly, abs_le]; constructor <;> nlinarith [hx1.1, hx1.2]
  have hty0 : |ty| ≤ 3 / 2 := by
    have h2 : 0 < √(1 + y) := Real.sqrt_pos.mpr (by linarith [hy1.1])
    have h3 : (1 / 2 : ℝ) ≤ 1 + y := by linarith [hy1.1, hε]
    have h4 : (2 / 3 : ℝ) ≤ √(1 + y) := by
      rw [show (2 / 3 : ℝ) = √((2 / 3) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by nlinarith)
    rw [hty, abs_of_pos (by positivity), div_le_iff₀ h2]; nlinarith
  have hexx : |x| ^ 3 ≤ ε ^ 3 := by gcongr
  have heyy : |y| ^ 3 ≤ ε ^ 3 := by gcongr
  set g2 := 3 * (x ^ 2 + y ^ 2) / 8 + x * y / 4 with hg2
  have hrho : |tx * ty - (1 - (x + y) / 2 + g2)| ≤ 7 * ε ^ 3 := by
    have e1 : tx * ty - (1 - (x + y) / 2 + g2) =
        (tx - invSqrtPoly x) * ty + invSqrtPoly x * (ty - invSqrtPoly y) +
          (-3 * x * y ^ 2 / 16 - 3 * x ^ 2 * y / 16 + 9 * x ^ 2 * y ^ 2 / 64) := by
      rw [hg2, invSqrtPoly, invSqrtPoly]; ring
    rw [e1]
    have c3 := abs_cubic_le hx hy hε
    calc _ ≤ |(tx - invSqrtPoly x) * ty + invSqrtPoly x * (ty - invSqrtPoly y)| + _ := abs_add_le _ _
      _ ≤ (|tx - invSqrtPoly x| * |ty| + |invSqrtPoly x| * |ty - invSqrtPoly y|) + ε ^ 3 := by
          gcongr
          rw [← abs_mul, ← abs_mul]; exact (abs_add_le _ _)
      _ ≤ (2 * ε ^ 3 * (3 / 2) + 27 / 20 * (2 * ε ^ 3)) + ε ^ 3 := by
          gcongr
          · exact ex.trans (by linarith)
          · exact ey.trans (by linarith)
      _ ≤ 7 * ε ^ 3 := by nlinarith [pow_nonneg hε0 3]
  have hg2b : |g2| ≤ ε ^ 2 := by
    have hxx : x ^ 2 ≤ ε ^ 2 := sq_le_sq' hx1.1 hx1.2
    have hyy : y ^ 2 ≤ ε ^ 2 := sq_le_sq' hy1.1 hy1.2
    have hxy : |x * y| ≤ ε ^ 2 := by
      rw [abs_mul, sq]; exact mul_le_mul hx hy (abs_nonneg _) hε0
    have := abs_le.mp hxy
    rw [abs_le, hg2]; constructor <;> linarith [sq_nonneg x, sq_nonneg y, sq_nonneg ε, this.1, this.2]
  set D := tx * ty - (1 - (x + y) / 2 + g2) with hD
  have hε3 : ε ^ 3 ≤ ε ^ 2 / 2 := by
    have : ε ^ 3 = ε ^ 2 * ε := by ring
    rw [this]; nlinarith [pow_nonneg hε0 2]
  have hid : cosArg (a₀ * (1 + x)) (b₀ * (1 + y)) (c₀ * (1 + z)) - u -
      cosLin a₀ b₀ c₀ x y z - cosQuad a₀ b₀ c₀ x y z = u * D + P * (D + g2) := by
    rw [hf, hD]
    simp only [cosLin, cosQuad, ← hudef]
    ring
  rw [hid]
  have hDg : |D + g2| ≤ 9 / 2 * ε ^ 2 := by
    calc _ ≤ |D| + |g2| := abs_add_le _ _
      _ ≤ 7 * ε ^ 3 + ε ^ 2 := add_le_add hrho hg2b
      _ ≤ _ := by linarith
  calc _ ≤ |u * D| + |P * (D + g2)| := abs_add_le _ _
    _ ≤ 1 * (7 * ε ^ 3) + (R * ε) * (9 / 2 * ε ^ 2) := by
        rw [abs_mul, abs_mul]
        gcongr
    _ ≤ _ := by nlinarith [pow_nonneg hε0 3, mul_nonneg hR0 (pow_nonneg hε0 3)]

/-- Constants of the second-order angle bound. -/
noncomputable def angK (R m : ℝ) : ℝ :=
  3 * ((R + 1) + (R + 1) + (7 + 5 * R)) ^ 3 / m ^ 5 + (7 + 5 * R) / m +
    ((R + 1) + (7 + 5 * R)) * ((R + 1) + (R + 1) + (7 + 5 * R)) / m ^ 3

/-- Pure algebra behind the angle expansion: if `Δ = ℓ + q₂ + E` with `ℓ = O(ε)`, `q₂ = O(ε²)`,
`E = O(ε³)`, and `T` is the Taylor defect, then `T - E/q + u (ℓ² - Δ²)/(2 q³)` is `O(ε³)`. -/
theorem abs_angle_algebra_le {u ℓ q₂ E T q m ε R : ℝ} (hm : 0 < m) (hq : m ≤ q) (hu : |u| ≤ 1)
    (hR : 0 ≤ R) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) (hℓ : |ℓ| ≤ (R + 1) * ε)
    (hq₂ : |q₂| ≤ (R + 1) * ε ^ 2) (hE : |E| ≤ (7 + 5 * R) * ε ^ 3)
    (hT : |T| ≤ 3 * |ℓ + q₂ + E| ^ 3 / m ^ 5) :
    |T - E / q + u * (ℓ ^ 2 - (ℓ + q₂ + E) ^ 2) / (2 * q ^ 3)| ≤ angK R m * ε ^ 3 := by
  have hq0 : 0 < q := lt_of_lt_of_le hm hq
  have hε2 : ε ^ 2 ≤ ε := by nlinarith
  have hε3 : ε ^ 3 ≤ ε ^ 2 := by nlinarith [pow_nonneg hε0 2]
  set A := R + 1 with hA
  set B := R + 1 with hB
  set C := 7 + 5 * R with hC
  have hA0 : 0 ≤ A := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hΔ : |ℓ + q₂ + E| ≤ (A + B + C) * ε := by
    calc _ ≤ |ℓ| + |q₂| + |E| := by
          calc _ ≤ |ℓ + q₂| + |E| := abs_add_le _ _
            _ ≤ _ := by gcongr; exact abs_add_le _ _
      _ ≤ A * ε + B * ε ^ 2 + C * ε ^ 3 := by linarith
      _ ≤ A * ε + B * ε + C * ε := by gcongr <;> linarith
      _ = _ := by ring
  have hT' : |T| ≤ 3 * ((A + B + C) * ε) ^ 3 / m ^ 5 := by
    refine hT.trans ?_
    gcongr
  have hT'' : |T| ≤ 3 * (A + B + C) ^ 3 / m ^ 5 * ε ^ 3 := by
    refine hT'.trans (le_of_eq ?_); ring
  have hEq : |E / q| ≤ C / m * ε ^ 3 := by
    rw [abs_div, abs_of_pos hq0]
    calc _ ≤ |E| / m := by gcongr
      _ ≤ (C * ε ^ 3) / m := by gcongr
      _ = _ := by ring
  have h2 : |ℓ ^ 2 - (ℓ + q₂ + E) ^ 2| ≤ 2 * ((B + C) * (A + B + C)) * ε ^ 3 := by
    have e : ℓ ^ 2 - (ℓ + q₂ + E) ^ 2 = -((q₂ + E) * (ℓ + (ℓ + q₂ + E))) := by ring
    rw [e, abs_neg, abs_mul]
    have h1 : |q₂ + E| ≤ (B + C) * ε ^ 2 := by
      calc _ ≤ |q₂| + |E| := abs_add_le _ _
        _ ≤ B * ε ^ 2 + C * ε ^ 3 := by linarith
        _ ≤ B * ε ^ 2 + C * ε ^ 2 := by gcongr
        _ = _ := by ring
    have h3 : |ℓ + (ℓ + q₂ + E)| ≤ 2 * (A + B + C) * ε := by
      calc _ ≤ |ℓ| + |ℓ + q₂ + E| := abs_add_le _ _
        _ ≤ A * ε + (A + B + C) * ε := by linarith
        _ ≤ _ := by nlinarith [mul_nonneg hA0 hε0, mul_nonneg (by linarith : (0:ℝ) ≤ B + C) hε0]
    calc _ ≤ ((B + C) * ε ^ 2) * (2 * (A + B + C) * ε) := by gcongr
      _ = _ := by ring
  have hU : |u * (ℓ ^ 2 - (ℓ + q₂ + E) ^ 2) / (2 * q ^ 3)| ≤
      (B + C) * (A + B + C) / m ^ 3 * ε ^ 3 := by
    rw [abs_div, abs_mul, abs_of_pos (by positivity : 0 < 2 * q ^ 3)]
    have hq3 : m ^ 3 ≤ q ^ 3 := by gcongr
    rw [div_le_iff₀ (by positivity)]
    calc |u| * |ℓ ^ 2 - (ℓ + q₂ + E) ^ 2| ≤ 1 * (2 * ((B + C) * (A + B + C)) * ε ^ 3) := by
          gcongr
      _ = (B + C) * (A + B + C) / m ^ 3 * ε ^ 3 * (2 * m ^ 3) := by field_simp
      _ ≤ _ := by
          gcongr
  calc _ ≤ |T - E / q| + |u * (ℓ ^ 2 - (ℓ + q₂ + E) ^ 2) / (2 * q ^ 3)| := abs_add_le _ _
    _ ≤ (|T| + |E / q|) + (B + C) * (A + B + C) / m ^ 3 * ε ^ 3 := by
        gcongr; exact abs_sub _ _
    _ ≤ (3 * (A + B + C) ^ 3 / m ^ 5 * ε ^ 3 + C / m * ε ^ 3) +
          (B + C) * (A + B + C) / m ^ 3 * ε ^ 3 := by gcongr
    _ = _ := by simp only [angK]; ring

/-- The numerator perturbation is `O(ε)` for a triangle with bounded side ratio. -/
theorem abs_numPert_le {a₀ b₀ c₀ x y z ε R : ℝ} (ha : 0 < a₀) (hb : 0 < b₀) (hc : 0 ≤ c₀)
    (hx : |x| ≤ ε) (hy : |y| ≤ ε) (hz : |z| ≤ ε) (hR : a₀ + b₀ + c₀ ≤ 2 * R * √(a₀ * b₀)) :
    |(a₀ * x + b₀ * y - c₀ * z) / (2 * √(a₀ * b₀))| ≤ R * ε := by
  have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) hx
  have hq0 : 0 < √(a₀ * b₀) := Real.sqrt_pos.mpr (mul_pos ha hb)
  rw [abs_div, abs_of_pos (by positivity : 0 < 2 * √(a₀ * b₀)), div_le_iff₀ (by positivity)]
  have h1 : |a₀ * x + b₀ * y - c₀ * z| ≤ a₀ * ε + b₀ * ε + c₀ * ε := by
    calc _ ≤ |a₀ * x + b₀ * y| + |c₀ * z| := abs_sub _ _
      _ ≤ |a₀ * x| + |b₀ * y| + |c₀ * z| := by gcongr; exact abs_add_le _ _
      _ ≤ _ := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos ha, abs_of_pos hb, abs_of_nonneg hc]; gcongr
  calc _ ≤ (a₀ + b₀ + c₀) * ε := by linarith
    _ ≤ 2 * R * √(a₀ * b₀) * ε := by gcongr
    _ = _ := by ring

/-- **A triangle angle to second order.** Under the hypotheses of `abs_cosArg_expansion_le`, and
with the cosines before and after in `[-s, s]`, `s < 1`, the angle `triAngle` of the perturbed
triangle differs from the unperturbed one by
`-(ℓ + q₂)/q - u ℓ²/(2 q³)` up to `angK R m ε³`, where `u` is the unperturbed cosine, `ℓ`, `q₂` are
`cosLin`, `cosQuad`, `q = √(1 - u²)` and `m = √(1 - s²)`. -/
theorem abs_triAngle_expansion_le {a₀ b₀ c₀ x y z ε R s : ℝ} (ha : 0 < a₀) (hb : 0 < b₀)
    (hc : 0 ≤ c₀) (hx : |x| ≤ ε) (hy : |y| ≤ ε) (hz : |z| ≤ ε) (hε : ε ≤ 1 / 2)
    (hR : a₀ + b₀ + c₀ ≤ 2 * R * √(a₀ * b₀)) (hs0 : 0 ≤ s) (hs : s < 1)
    (hu : cosArg a₀ b₀ c₀ ∈ Set.Icc (-s) s)
    (hf : cosArg (a₀ * (1 + x)) (b₀ * (1 + y)) (c₀ * (1 + z)) ∈ Set.Icc (-s) s) :
    |triAngle (a₀ * (1 + x)) (b₀ * (1 + y)) (c₀ * (1 + z)) - triAngle a₀ b₀ c₀ +
        (cosLin a₀ b₀ c₀ x y z + cosQuad a₀ b₀ c₀ x y z) / qq (cosArg a₀ b₀ c₀) +
        cosArg a₀ b₀ c₀ * cosLin a₀ b₀ c₀ x y z ^ 2 / (2 * qq (cosArg a₀ b₀ c₀) ^ 3)| ≤
      angK R √(1 - s ^ 2) * ε ^ 3 := by
  have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) hx
  have hm : 0 < √(1 - s ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hq := qq_ge hs hu
  have hu1 : |cosArg a₀ b₀ c₀| ≤ 1 := (abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩)
  have hq0 : 0 < √(a₀ * b₀) := Real.sqrt_pos.mpr (mul_pos ha hb)
  have hR0 : 0 ≤ R := by
    by_contra h
    have h := not_le.mp h
    nlinarith [mul_pos (neg_pos.mpr h) hq0]
  set u := cosArg a₀ b₀ c₀ with hudef
  set f := cosArg (a₀ * (1 + x)) (b₀ * (1 + y)) (c₀ * (1 + z)) with hfdef
  set ℓ := cosLin a₀ b₀ c₀ x y z with hℓdef
  set q₂ := cosQuad a₀ b₀ c₀ x y z with hq₂def
  set E := f - u - ℓ - q₂ with hEdef
  have hEb : |E| ≤ (7 + 5 * R) * ε ^ 3 := abs_cosArg_expansion_le ha hb hx hy hz hε hc hu1 hR
  have hP := abs_numPert_le ha hb hc hx hy hz hR
  have hxy : |x + y| ≤ 2 * ε := (abs_add_le _ _).trans (by linarith)
  have hℓb : |ℓ| ≤ (R + 1) * ε := by
    rw [hℓdef, cosLin]
    calc _ ≤ |(a₀ * x + b₀ * y - c₀ * z) / (2 * √(a₀ * b₀))| + |u * (x + y) / 2| := abs_sub _ _
      _ ≤ R * ε + ε := by
        gcongr
        rw [abs_div, abs_mul]
        have : |u| * |x + y| ≤ 1 * (2 * ε) := by gcongr
        norm_num
        linarith
      _ = _ := by ring
  have hq₂b : |q₂| ≤ (R + 1) * ε ^ 2 := by
    rw [hq₂def, cosQuad]
    have hxx : x ^ 2 ≤ ε ^ 2 := sq_le_sq' (abs_le.mp hx).1 (abs_le.mp hx).2
    have hyy : y ^ 2 ≤ ε ^ 2 := sq_le_sq' (abs_le.mp hy).1 (abs_le.mp hy).2
    have hxy2 : |x * y| ≤ ε ^ 2 := by
      rw [abs_mul, sq]; exact mul_le_mul hx hy (abs_nonneg _) hε0
    have hxy3 := abs_le.mp hxy2
    have hg : |3 * (x ^ 2 + y ^ 2) / 8 + x * y / 4| ≤ ε ^ 2 := by
      rw [abs_le]; constructor <;> linarith [sq_nonneg x, sq_nonneg y, sq_nonneg ε]
    have hp : |-((a₀ * x + b₀ * y - c₀ * z) / (2 * √(a₀ * b₀))) * (x + y) / 2| ≤ R * ε ^ 2 := by
      rw [abs_div, abs_mul, abs_neg]
      have : |(a₀ * x + b₀ * y - c₀ * z) / (2 * √(a₀ * b₀))| * |x + y| ≤ R * ε * (2 * ε) := by
        gcongr
      norm_num
      linarith
    calc _ ≤ |-((a₀ * x + b₀ * y - c₀ * z) / (2 * √(a₀ * b₀))) * (x + y) / 2| +
          |u * (3 * (x ^ 2 + y ^ 2) / 8 + x * y / 4)| := abs_add_le _ _
      _ ≤ R * ε ^ 2 + ε ^ 2 := by
        gcongr
        rw [abs_mul]
        calc _ ≤ 1 * ε ^ 2 := by gcongr
          _ = _ := one_mul _
      _ = _ := by ring
  have hT := abs_arccos_taylor_le hs0 hs hu hf
  set T := arccos f - arccos u + (f - u) / qq u + u * (f - u) ^ 2 / (2 * qq u ^ 3) with hTdef
  have hΔ : f - u = ℓ + q₂ + E := by rw [hEdef]; ring
  have hT' : |T| ≤ 3 * |ℓ + q₂ + E| ^ 3 / √(1 - s ^ 2) ^ 5 := by rw [← hΔ]; exact hT
  have key := abs_angle_algebra_le hm hq hu1 hR0 hε0 hε hℓb hq₂b hEb hT'
  have heq : triAngle (a₀ * (1 + x)) (b₀ * (1 + y)) (c₀ * (1 + z)) - triAngle a₀ b₀ c₀ +
        (ℓ + q₂) / qq u + u * ℓ ^ 2 / (2 * qq u ^ 3) =
      T - E / qq u + u * (ℓ ^ 2 - (ℓ + q₂ + E) ^ 2) / (2 * qq u ^ 3) := by
    have hqu : qq u ≠ 0 := (lt_of_lt_of_le hm hq).ne'
    have h1 : triAngle (a₀ * (1 + x)) (b₀ * (1 + y)) (c₀ * (1 + z)) = arccos f := rfl
    have h2 : triAngle a₀ b₀ c₀ = arccos u := rfl
    rw [h1, h2, hTdef, hΔ]
    clear_value T f u ℓ q₂ E
    generalize arccos f = A
    generalize arccos u = B
    generalize qq u = qv at *
    field_simp
    ring
  rw [heq]
  exact key

/-- **Non-vacuity.** The hypotheses of `abs_triAngle_expansion_le` hold for the equilateral
triangle with all squared lengths `1`, perturbed by the relative error `ε = 1/10` in each length
(`R = 3/2`, `s = 3/5`). -/
example : |triAngle (1 * (1 + 1 / 10)) (1 * (1 + 1 / 10)) (1 * (1 + 1 / 10)) - triAngle 1 1 1 +
      (cosLin 1 1 1 (1 / 10) (1 / 10) (1 / 10) + cosQuad 1 1 1 (1 / 10) (1 / 10) (1 / 10)) /
        qq (cosArg 1 1 1) +
      cosArg 1 1 1 * cosLin 1 1 1 (1 / 10) (1 / 10) (1 / 10) ^ 2 / (2 * qq (cosArg 1 1 1) ^ 3)| ≤
    angK (3 / 2) √(1 - (3 / 5 : ℝ) ^ 2) * (1 / 10) ^ 3 := by
  have h1 : √((1 : ℝ) * 1) = 1 := by simp
  have h2 : √((1 * (1 + 1 / 10) : ℝ) * (1 * (1 + 1 / 10))) = 11 / 10 := by
    rw [show ((1 * (1 + 1 / 10) : ℝ) * (1 * (1 + 1 / 10))) = (11 / 10) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  refine abs_triAngle_expansion_le (R := 3 / 2) (s := 3 / 5) (ε := 1 / 10) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [abs_of_pos]) (by norm_num [abs_of_pos])
    (by norm_num [abs_of_pos]) (by norm_num) (by rw [h1]; norm_num) (by norm_num) (by norm_num)
    ?_ ?_
  · rw [cosArg, h1]; constructor <;> norm_num
  · rw [cosArg, h2]; constructor <;> norm_num

end Lightlike.CMS
