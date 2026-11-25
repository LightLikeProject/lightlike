import Mathlib
import Lightlike.Geometry.HeatTraceExpansion.SphereTrace

/-!
# The heat expansion of the unit 2-sphere

Trust check of `T-GE8`: `∑ₗ (2l+1) e^{-t l(l+1)} = 1/t + 1/3 + t/15 + O(t²)` as `t → 0⁺`.

* `Lightlike.Rows.G1_062.exp_quarter_bound`: `|e^{t/4} - (1 + t/4 + t²/32)| ≤ t³/288` on `[0,1]`.
* `Lightlike.Rows.G1_062.sphere_arith`: the real-number bookkeeping for the product.
* `Lightlike.Rows.G1_062.sphereTrace_bound`: `|Z(t) - (1/t + 1/3 + t/15)| ≤ K t²` on `(0,1]`.
* `Lightlike.Rows.G1_062.sphereTrace_hasHeatExpansion`: `HasHeatExpansion sphereTrace 2 sphereCoeff 3`,
  i.e. `a₀ = 1`, `a₁ = 1/3`, `a₂ = 1/15` (with the normalisation `(4π)^{-1} · vol = 1`).
* `Lightlike.Rows.G1_062.sphere_a1_check`: `a₁ = (4π)⁻¹ · ∫ R/6` numerically on the unit
  2-sphere (`R = 2`, `vol = 4π`); this is an arithmetic check, not the Gauss–Bonnet theorem.
-/

open Set Filter Topology

namespace Lightlike.Rows.G1_062

/-- Taylor bound for `e^{t/4}` on `[0,1]`. -/
lemma exp_quarter_bound (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    |Real.exp (t / 4) - (1 + t / 4 + t ^ 2 / 32)| ≤ t ^ 3 / 288 := by
  have hx : |t / 4| ≤ 1 := by
    rw [abs_of_nonneg (by linarith)]; linarith
  have h := Real.exp_bound hx (n := 3) (by norm_num)
  calc |Real.exp (t / 4) - (1 + t / 4 + t ^ 2 / 32)|
      = |Real.exp (t / 4) - ∑ m ∈ Finset.range 3, (t / 4) ^ m / (m.factorial : ℝ)| := by
        congr 2
        simp [Finset.sum_range_succ, Nat.factorial]
        ring
    _ ≤ |t / 4| ^ 3 * (((3 : ℕ).succ : ℝ) / ((3 : ℕ).factorial * (3 : ℕ))) := h
    _ = t ^ 3 / 288 := by
        rw [abs_of_nonneg (by linarith)]
        norm_num [Nat.factorial]
        ring

/-- Bookkeeping for the product `e^{t/4} · S(t)`. -/
lemma sphere_arith (C t : ℝ) (hC : 0 ≤ C) (ht0 : 0 < t) (ht1 : t ≤ 1) (S E : ℝ)
    (hS : |S - (1 / t + 1 / 12 + 7 * t / 480)| ≤ C * t ^ 2)
    (hE : |E - (1 + t / 4 + t ^ 2 / 32)| ≤ t ^ 3 / 288) :
    |E * S - (1 / t + 1 / 3 + t / 15)| ≤ (3 * C + 3) * t ^ 2 := by
  set Q := 1 / t + 1 / 12 + 7 * t / 480 with hQ
  set P := 1 + t / 4 + t ^ 2 / 32 with hP
  set s := S - Q with hs
  set r := E - P with hr
  have hQt : t * Q = 1 + t / 12 + 7 * t ^ 2 / 480 := by
    rw [hQ]; field_simp
  have hPQ : P * Q - (1 / t + 1 / 3 + t / 15) = t ^ 2 * (7 / 1920 + 1 / 384) + 7 * t ^ 3 / 15360 := by
    rw [hP, hQ]; field_simp; ring
  have hid : E * S - (1 / t + 1 / 3 + t / 15) =
      r * S + P * s + (t ^ 2 * (7 / 1920 + 1 / 384) + 7 * t ^ 3 / 15360) := by
    rw [← hPQ, hr, hs]; ring
  have ht2 : t ^ 2 ≤ 1 := by nlinarith
  have ht3 : t ^ 3 ≤ t ^ 2 := by nlinarith [sq_nonneg t]
  have ht3' : t ^ 3 ≤ 1 := by nlinarith
  have hsa := abs_le.mp hS
  have htS : |t * S| ≤ 2 + C := by
    have : t * S = t * Q + t * s := by rw [hs]; ring
    rw [this, hQt]
    have hts : |t * s| ≤ C := by
      rw [abs_mul, abs_of_pos ht0]
      calc t * |s| ≤ t * (C * t ^ 2) := by gcongr
        _ = C * t ^ 3 := by ring
        _ ≤ C * 1 := by gcongr
        _ = C := by ring
    have := abs_le.mp hts
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg t]
  have hrS : |r * S| ≤ (2 + C) / 288 * t ^ 2 := by
    have h1 : |r * S| * t ≤ (2 + C) / 288 * t ^ 2 * t := by
      calc |r * S| * t = |r| * |t * S| := by
            rw [abs_mul, abs_mul, abs_of_pos ht0]; ring
        _ ≤ t ^ 3 / 288 * (2 + C) := by gcongr
        _ = (2 + C) / 288 * t ^ 2 * t := by ring
    exact le_of_mul_le_mul_right h1 ht0
  have hP2 : |P| ≤ 2 := by
    rw [hP, abs_of_nonneg (by positivity)]; nlinarith
  have hPs : |P * s| ≤ 2 * (C * t ^ 2) := by
    rw [abs_mul]
    exact mul_le_mul hP2 hS (abs_nonneg _) (by norm_num)
  have hrem : |t ^ 2 * (7 / 1920 + 1 / 384) + 7 * t ^ 3 / 15360| ≤ t ^ 2 := by
    rw [abs_of_nonneg (by positivity)]; nlinarith
  rw [hid]
  calc _ ≤ |r * S + P * s| + |t ^ 2 * (7 / 1920 + 1 / 384) + 7 * t ^ 3 / 15360| := abs_add_le _ _
    _ ≤ (|r * S| + |P * s|) + t ^ 2 := by
        gcongr; exact abs_add_le _ _
    _ ≤ (3 * C + 3) * t ^ 2 := by nlinarith [sq_nonneg t]

/-- On `(0,1]`, `|Z(t) - (1/t + 1/3 + t/15)| ≤ K t²` for the unit 2-sphere heat trace. -/
theorem sphereTrace_bound : ∃ K : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 →
    |sphereTrace t - (1 / t + 1 / 3 + t / 15)| ≤ K * t ^ 2 := by
  obtain ⟨C, hC, hCb⟩ := thetaHalf_expansion
  refine ⟨3 * C + 3, fun t ht0 ht1 => ?_⟩
  rw [sphereTrace_eq]
  have hb : |thetaHalf t - (1 / t + 1 / 12 + 7 * t / 480)| ≤ C * t ^ 2 := by
    have := hCb t ht0 ht1
    convert this using 2
    ring
  exact sphere_arith C t hC ht0 ht1 _ _ hb (exp_quarter_bound t ht0.le ht1)

/-- The coefficients `a₀ = 1`, `a₁ = 1/3`, `a₂ = 1/15` (further ones unused). -/
noncomputable def sphereCoeff : ℕ → ℝ
  | 0 => 1
  | 1 => 1 / 3
  | _ => 1 / 15

/-- **Trust check (T-GE8).** The heat trace of the unit round 2-sphere has the expansion
`1/t + 1/3 + t/15 + O(t²)`, i.e. `a₀ = 1`, `a₁ = 1/3`, `a₂ = 1/15`. -/
theorem sphereTrace_hasHeatExpansion :
    HasHeatExpansion sphereTrace 2 sphereCoeff 3 := by
  obtain ⟨K, hK⟩ := sphereTrace_bound
  unfold HasHeatExpansion
  refine Asymptotics.IsBigO.of_bound K ?_
  have hmem : Ioc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioc_mem_nhdsGT (by norm_num)
  filter_upwards [hmem] with t ht
  obtain ⟨ht0, ht1⟩ := ht
  have e0 : t ^ (((0 : ℕ) : ℝ) - (2 : ℕ) / 2) = 1 / t := by
    have : (((0 : ℕ) : ℝ) - (2 : ℕ) / 2) = -1 := by norm_num
    rw [this, Real.rpow_neg_one]; simp
  have e1 : t ^ (((1 : ℕ) : ℝ) - (2 : ℕ) / 2) = 1 := by
    have : (((1 : ℕ) : ℝ) - (2 : ℕ) / 2) = 0 := by norm_num
    rw [this, Real.rpow_zero]
  have e2 : t ^ (((2 : ℕ) : ℝ) - (2 : ℕ) / 2) = t := by
    have : (((2 : ℕ) : ℝ) - (2 : ℕ) / 2) = 1 := by norm_num
    rw [this, Real.rpow_one]
  have e3 : t ^ (((3 : ℕ) : ℝ) - (2 : ℕ) / 2) = t ^ 2 := by
    have : (((3 : ℕ) : ℝ) - (2 : ℕ) / 2) = ((2 : ℕ) : ℝ) := by norm_num
    rw [this, Real.rpow_natCast]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [e0, e1, e2, e3]
  have := hK t ht0 ht1
  simp only [sphereCoeff, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ t ^ 2)]
  convert this using 2
  ring

/-- `a₁ = (4π)⁻¹ ∫ R/6` for the unit 2-sphere: scalar curvature `R = 2`, volume `4π`,
so `(4π)⁻¹ · (2/6) · 4π = 1/3`. An arithmetic check of the coefficient, not Gauss–Bonnet. -/
theorem sphere_a1_check : (4 * Real.pi)⁻¹ * ((2 / 6) * (4 * Real.pi)) = 1 / 3 := by
  have : (4 * Real.pi) ≠ 0 := by positivity
  field_simp
  norm_num

end Lightlike.Rows.G1_062
