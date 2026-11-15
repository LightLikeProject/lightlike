import Mathlib
import Lightlike.Regge.CMS.Quadratic

/-!
# First-order sensitivity of a triangle angle to its opposite side (RC6b, step 5)

In the vertex expansion the two sides at the vertex are exact to relative order `h³`, and only the
opposite side is perturbed, by a relative error of order `h²`. The angle then moves by the first
order term `c₀ z / (2 √(a₀ b₀) q)`, `q = √(1 - u²)` the sine of the angle, with an error of order
`h³`.

## Main results

* `abs_triAngle_firstorder_le`: for relative errors `|x|, |y| ≤ ε₃`, `|z| ≤ ε₂`, `ε₃ ≤ ε₂ ≤ 1/2`,
  `|θ' - θ - c₀ z / (2 √(a₀ b₀) q)| ≤ KT R m (ε₃ + ε₂²)`.
-/

open Real

namespace Lightlike.CMS

/-- The constant of `abs_triAngle_firstorder_le`. -/
noncomputable def KT (R m : ℝ) : ℝ := angK R m + 2 * (2 * R + 1) / m + (2 * R + 1) ^ 2 / (2 * m ^ 3)

theorem abs_div_le_of_le {t B q m : ℝ} (hm : 0 < m) (hq : m ≤ q) (ht : |t| ≤ B) :
    |t / q| ≤ B / m := by
  have hq0 : 0 < q := lt_of_lt_of_le hm hq
  rw [abs_div, abs_of_pos hq0]
  have hB : 0 ≤ B := le_trans (abs_nonneg _) ht
  calc |t| / q ≤ B / q := by gcongr
    _ ≤ B / m := div_le_div_of_nonneg_left hB hm hq

set_option maxHeartbeats 1600000 in
/-- **First-order sensitivity of the angle.** -/
theorem abs_triAngle_firstorder_le {a₀ b₀ c₀ x y z ε₂ ε₃ R s : ℝ} (ha : 0 < a₀) (hb : 0 < b₀)
    (hc : 0 ≤ c₀) (hx : |x| ≤ ε₃) (hy : |y| ≤ ε₃) (hz : |z| ≤ ε₂) (h32 : ε₃ ≤ ε₂)
    (hε : ε₂ ≤ 1 / 2) (hR : a₀ + b₀ + c₀ ≤ 2 * R * √(a₀ * b₀)) (hs0 : 0 ≤ s) (hs : s < 1)
    (hu : cosArg a₀ b₀ c₀ ∈ Set.Icc (-s) s)
    (hf : cosArg (a₀ * (1 + x)) (b₀ * (1 + y)) (c₀ * (1 + z)) ∈ Set.Icc (-s) s) :
    |triAngle (a₀ * (1 + x)) (b₀ * (1 + y)) (c₀ * (1 + z)) - triAngle a₀ b₀ c₀ -
        c₀ * z / (2 * √(a₀ * b₀) * qq (cosArg a₀ b₀ c₀))| ≤ KT R √(1 - s ^ 2) * (ε₃ + ε₂ ^ 2) := by
  have hε3 : 0 ≤ ε₃ := le_trans (abs_nonneg _) hx
  have hε2 : 0 ≤ ε₂ := le_trans hε3 h32
  have hm : 0 < √(1 - s ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hq0 : 0 < √(a₀ * b₀) := Real.sqrt_pos.mpr (mul_pos ha hb)
  have hR0 : 0 ≤ R := by
    by_contra h
    have h := not_le.mp h
    nlinarith [mul_pos (neg_pos.mpr h) hq0]
  have hmain := abs_triAngle_expansion_le ha hb hc (hx.trans h32) (hy.trans h32) hz hε hR hs0 hs hu hf
  have hq := qq_ge hs hu
  have hu1 : |cosArg a₀ b₀ c₀| ≤ 1 := abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
  set u := cosArg a₀ b₀ c₀ with hudef
  set ℓ := cosLin a₀ b₀ c₀ x y z with hℓdef
  set q₂ := cosQuad a₀ b₀ c₀ x y z with hq₂def
  set D := c₀ * z / (2 * √(a₀ * b₀)) with hD
  have hab : |a₀ * x + b₀ * y| / (2 * √(a₀ * b₀)) ≤ R * ε₃ := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : |a₀ * x + b₀ * y| ≤ a₀ * ε₃ + b₀ * ε₃ := by
      calc _ ≤ |a₀ * x| + |b₀ * y| := abs_add_le _ _
        _ ≤ _ := by
          rw [abs_mul, abs_mul, abs_of_pos ha, abs_of_pos hb]; gcongr
    have : (a₀ + b₀) * ε₃ ≤ (2 * R * √(a₀ * b₀)) * ε₃ := by gcongr; linarith
    nlinarith
  have hDb : |D| ≤ R * ε₂ := by
    rw [hD, abs_div, abs_mul, abs_of_nonneg hc, abs_of_pos (by positivity : (0 : ℝ) < 2 * √(a₀ * b₀)),
      div_le_iff₀ (by positivity)]
    have : c₀ * |z| ≤ c₀ * ε₂ := by gcongr
    have : c₀ * ε₂ ≤ (2 * R * √(a₀ * b₀)) * ε₂ := by gcongr; linarith
    nlinarith
  have hℓD : |ℓ + D| ≤ (R + 1) * ε₃ := by
    have e : ℓ + D = (a₀ * x + b₀ * y) / (2 * √(a₀ * b₀)) - u * (x + y) / 2 := by
      rw [hℓdef, cosLin, hD]; ring
    rw [e]
    calc _ ≤ |(a₀ * x + b₀ * y) / (2 * √(a₀ * b₀))| + |u * (x + y) / 2| := abs_sub _ _
      _ ≤ R * ε₃ + ε₃ := by
        gcongr
        · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * √(a₀ * b₀))]; exact hab
        · rw [abs_div, abs_mul]
          have : |u| * |x + y| ≤ 1 * (2 * ε₃) := by
            gcongr; exact (abs_add_le _ _).trans (by linarith)
          norm_num; linarith
      _ = _ := by ring
  have hℓb : |ℓ| ≤ (2 * R + 1) * ε₂ := by
    have : |ℓ| ≤ |ℓ + D| + |D| := by
      calc |ℓ| = |(ℓ + D) - D| := by ring_nf
        _ ≤ _ := abs_sub _ _
    nlinarith
  have hq₂b : |q₂| ≤ (2 * R + 1) * ε₂ ^ 2 := by
    have hP : |(a₀ * x + b₀ * y - c₀ * z) / (2 * √(a₀ * b₀))| ≤ 2 * R * ε₂ := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * √(a₀ * b₀)), div_le_iff₀ (by positivity)]
      have h1 : |a₀ * x + b₀ * y - c₀ * z| ≤ a₀ * ε₂ + b₀ * ε₂ + c₀ * ε₂ := by
        calc _ ≤ |a₀ * x + b₀ * y| + |c₀ * z| := abs_sub _ _
          _ ≤ |a₀ * x| + |b₀ * y| + |c₀ * z| := by gcongr; exact abs_add_le _ _
          _ ≤ _ := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_pos ha, abs_of_pos hb, abs_of_nonneg hc]
            have := hx.trans h32; have := hy.trans h32; gcongr
      have : (a₀ + b₀ + c₀) * ε₂ ≤ (2 * R * √(a₀ * b₀)) * ε₂ := by gcongr
      nlinarith
    have hxx : x ^ 2 ≤ ε₂ ^ 2 := sq_le_sq' (abs_le.mp (hx.trans h32)).1 (abs_le.mp (hx.trans h32)).2
    have hyy : y ^ 2 ≤ ε₂ ^ 2 := sq_le_sq' (abs_le.mp (hy.trans h32)).1 (abs_le.mp (hy.trans h32)).2
    have hxy2 : |x * y| ≤ ε₂ ^ 2 := by
      rw [abs_mul, sq]; exact mul_le_mul (hx.trans h32) (hy.trans h32) (abs_nonneg _) hε2
    have hxy3 := abs_le.mp hxy2
    have hg : |3 * (x ^ 2 + y ^ 2) / 8 + x * y / 4| ≤ ε₂ ^ 2 := by
      rw [abs_le]; constructor <;> linarith [sq_nonneg x, sq_nonneg y, sq_nonneg ε₂]
    have hxy : |x + y| ≤ 2 * ε₂ := (abs_add_le _ _).trans (by linarith [hx.trans h32, hy.trans h32])
    rw [hq₂def, cosQuad]
    calc _ ≤ |-((a₀ * x + b₀ * y - c₀ * z) / (2 * √(a₀ * b₀))) * (x + y) / 2| +
          |u * (3 * (x ^ 2 + y ^ 2) / 8 + x * y / 4)| := abs_add_le _ _
      _ ≤ 2 * R * ε₂ ^ 2 + ε₂ ^ 2 := by
        gcongr
        · rw [abs_div, abs_mul, abs_neg]
          have : |(a₀ * x + b₀ * y - c₀ * z) / (2 * √(a₀ * b₀))| * |x + y| ≤ (2 * R * ε₂) * (2 * ε₂) := by
            gcongr
          norm_num
          nlinarith
        · rw [abs_mul]
          calc _ ≤ 1 * ε₂ ^ 2 := by gcongr
            _ = _ := one_mul _
      _ = _ := by ring
  -- assemble
  have h1 : |(ℓ + D) / qq u| ≤ (R + 1) * ε₃ / √(1 - s ^ 2) := abs_div_le_of_le hm hq hℓD
  have h2 : |q₂ / qq u| ≤ (2 * R + 1) * ε₂ ^ 2 / √(1 - s ^ 2) := abs_div_le_of_le hm hq hq₂b
  have hq3 : √(1 - s ^ 2) ^ 3 ≤ qq u ^ 3 := by gcongr
  have h3 : |u * ℓ ^ 2 / (2 * qq u ^ 3)| ≤ (2 * R + 1) ^ 2 * ε₂ ^ 2 / (2 * √(1 - s ^ 2) ^ 3) := by
    have hq0' : 0 < qq u := lt_of_lt_of_le hm hq
    rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * qq u ^ 3)]
    have hl2 : |ℓ ^ 2| ≤ (2 * R + 1) ^ 2 * ε₂ ^ 2 := by
      rw [abs_pow]
      calc _ ≤ ((2 * R + 1) * ε₂) ^ 2 := by gcongr
        _ = _ := by ring
    have hnum : |u| * |ℓ ^ 2| ≤ (2 * R + 1) ^ 2 * ε₂ ^ 2 := by
      calc _ ≤ 1 * ((2 * R + 1) ^ 2 * ε₂ ^ 2) := by gcongr
        _ = _ := one_mul _
    calc _ ≤ (2 * R + 1) ^ 2 * ε₂ ^ 2 / (2 * qq u ^ 3) := by gcongr
      _ ≤ _ := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        linarith
  have hX : triAngle (a₀ * (1 + x)) (b₀ * (1 + y)) (c₀ * (1 + z)) - triAngle a₀ b₀ c₀ -
        c₀ * z / (2 * √(a₀ * b₀) * qq u) =
      (triAngle (a₀ * (1 + x)) (b₀ * (1 + y)) (c₀ * (1 + z)) - triAngle a₀ b₀ c₀ +
        (ℓ + q₂) / qq u + u * ℓ ^ 2 / (2 * qq u ^ 3)) - (ℓ + D) / qq u - q₂ / qq u -
        u * ℓ ^ 2 / (2 * qq u ^ 3) := by
    have hqu : qq u ≠ 0 := (lt_of_lt_of_le hm hq).ne'
    rw [hD]; field_simp; ring
  rw [hX]
  have hε3' : ε₂ ^ 3 ≤ ε₂ ^ 2 := by nlinarith [sq_nonneg ε₂]
  have hang : 0 ≤ angK R √(1 - s ^ 2) := by
    unfold angK; positivity
  have hpos : 0 ≤ KT R √(1 - s ^ 2) := by unfold KT; positivity
  calc _ ≤ |triAngle (a₀ * (1 + x)) (b₀ * (1 + y)) (c₀ * (1 + z)) - triAngle a₀ b₀ c₀ +
        (ℓ + q₂) / qq u + u * ℓ ^ 2 / (2 * qq u ^ 3)| + |(ℓ + D) / qq u| + |q₂ / qq u| +
        |u * ℓ ^ 2 / (2 * qq u ^ 3)| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        refine (abs_sub _ _).trans ?_
        gcongr
        exact (abs_sub _ _)
    _ ≤ angK R √(1 - s ^ 2) * ε₂ ^ 3 + (R + 1) * ε₃ / √(1 - s ^ 2) +
        (2 * R + 1) * ε₂ ^ 2 / √(1 - s ^ 2) + (2 * R + 1) ^ 2 * ε₂ ^ 2 / (2 * √(1 - s ^ 2) ^ 3) := by
        gcongr
    _ ≤ KT R √(1 - s ^ 2) * (ε₃ + ε₂ ^ 2) := by
        unfold KT
        have e1 : (R + 1) * ε₃ / √(1 - s ^ 2) ≤ 2 * (2 * R + 1) / √(1 - s ^ 2) * ε₃ := by
          rw [div_mul_eq_mul_div]; gcongr; nlinarith
        have e2 : (2 * R + 1) * ε₂ ^ 2 / √(1 - s ^ 2) ≤ 2 * (2 * R + 1) / √(1 - s ^ 2) * ε₂ ^ 2 := by
          rw [div_mul_eq_mul_div]; gcongr; nlinarith
        have e3 : angK R √(1 - s ^ 2) * ε₂ ^ 3 ≤ angK R √(1 - s ^ 2) * ε₂ ^ 2 := by gcongr
        have e4 : (2 * R + 1) ^ 2 * ε₂ ^ 2 / (2 * √(1 - s ^ 2) ^ 3) =
            (2 * R + 1) ^ 2 / (2 * √(1 - s ^ 2) ^ 3) * ε₂ ^ 2 := by ring
        have p1 : 0 ≤ angK R √(1 - s ^ 2) := hang
        have p2 : 0 ≤ 2 * (2 * R + 1) / √(1 - s ^ 2) := by positivity
        have p3 : 0 ≤ (2 * R + 1) ^ 2 / (2 * √(1 - s ^ 2) ^ 3) := by positivity
        generalize angK R √(1 - s ^ 2) = A at *
        generalize 2 * (2 * R + 1) / √(1 - s ^ 2) = B at *
        generalize (2 * R + 1) ^ 2 / (2 * √(1 - s ^ 2) ^ 3) = C at *
        rw [e4]
        linarith [mul_nonneg p1 hε3, mul_nonneg p3 hε3]

/-- **Non-vacuity.** The equilateral triangle with unit squared lengths, with the opposite side
lengthened by the relative error `1/10` (`R = 3/2`, `s = 3/5`). -/
example : |triAngle (1 * (1 + 0)) (1 * (1 + 0)) (1 * (1 + 1 / 10)) - triAngle 1 1 1 -
      1 * (1 / 10) / (2 * √(1 * 1) * qq (cosArg 1 1 1))| ≤
    KT (3 / 2) √(1 - (3 / 5 : ℝ) ^ 2) * (0 + (1 / 10) ^ 2) := by
  have h1 : √((1 : ℝ) * 1) = 1 := by simp
  refine abs_triAngle_firstorder_le (R := 3 / 2) (s := 3 / 5) (ε₂ := 1 / 10) (ε₃ := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [abs_of_pos])
    (by norm_num) (by norm_num) (by rw [h1]; norm_num) (by norm_num) (by norm_num) ?_ ?_
  · rw [cosArg, h1]; constructor <;> norm_num
  · rw [cosArg]
    have h2 : √((1 * (1 + 0) : ℝ) * (1 * (1 + 0))) = 1 := by simp
    rw [h2]; constructor <;> norm_num

end Lightlike.CMS
