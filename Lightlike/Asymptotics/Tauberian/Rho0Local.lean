import Lightlike.Asymptotics.Tauberian.CrossingMeasure

/-!
# The local bound for the crossing measure

`rho0_local`: `ρ₀ [c - ½, c + ½] ≤ K c^{-3/4} e^{2√(a c)}` for `c ≥ 1`, the analogue for `ρ₀` of
the local bound of MZ (5.14); it follows from the pointwise upper bound `crossingDensity_le`.
-/

open MeasureTheory Set Real Filter

noncomputable section

namespace Lightlike.Tauberian

/-- `c^{3/4} = √c · √√c`. -/
lemma rpow_three_quarter {c : ℝ} (hc : 0 < c) : c ^ (3 / 4 : ℝ) = √c * √(√c) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hc.le, ← Real.rpow_add hc]
  norm_num

/-- The constant of the local bound. -/
def rho0K (a : ℝ) : ℝ :=
  (Real.sqrt 2 * a / √(a / 2)) * (Real.exp (2 * √(a / 2)) / √(2 * √(a / 2)))

/-- **Pointwise bound on a window**: for `c ≥ 1` and `c/2 ≤ y ≤ c + 1/2`. -/
lemma crossingDensity_window {a c y : ℝ} (ha : 0 < a) (hc : 1 ≤ c) (hy1 : c / 2 ≤ y) (hy2 : y ≤ c + 1 / 2) :
    crossingDensity a y ≤ rho0K a * (c ^ (-(3 / 4 : ℝ)) * Real.exp (2 * √(a * c))) := by
  have hc0 : 0 < c := by linarith
  have hy0 : 0 < y := by linarith
  have h0 := crossingDensity_le ha hy0
  set q : ℝ := √(a / 2) with hq
  have hq0 : 0 < q := Real.sqrt_pos.2 (by positivity)
  set r : ℝ := √(2 * q) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 (by positivity)
  set u : ℝ := √c with hu
  have hu0 : 0 < u := Real.sqrt_pos.2 hc0
  set w : ℝ := √u with hw
  have hw0 : 0 < w := Real.sqrt_pos.2 hu0
  have hlow : √(a * (c / 2)) = q * u := by
    rw [show a * (c / 2) = a / 2 * c by ring, Real.sqrt_mul (by positivity)]
  have hlow2 : √(2 * √(a * (c / 2))) = r * w := by
    rw [hlow, show 2 * (q * u) = 2 * q * u by ring, Real.sqrt_mul (by positivity)]
  have h1 : q * u ≤ √(a * y) := by
    rw [← hlow]; exact Real.sqrt_le_sqrt (by nlinarith)
  have h2 : r * w ≤ √(2 * √(a * y)) := by
    rw [← hlow2]; exact Real.sqrt_le_sqrt (by nlinarith)
  have h3 : √(a * y) ≤ √(a * c) + √(a / 2) := by
    calc √(a * y) ≤ √(a * c + a / 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ ≤ √(a * c) + √(a / 2) := by
          rw [Real.sqrt_le_iff]
          refine ⟨by positivity, ?_⟩
          have e1 := Real.sq_sqrt (show 0 ≤ a * c by positivity)
          have e2 := Real.sq_sqrt (show 0 ≤ a / 2 by positivity)
          nlinarith [mul_nonneg (Real.sqrt_nonneg (a * c)) (Real.sqrt_nonneg (a / 2))]
  have h4 : Real.exp (2 * √(a * y)) ≤ Real.exp (2 * √(a * c)) * Real.exp (2 * q) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by rw [hq]; linarith)
  have hc34 : c ^ (-(3 / 4 : ℝ)) = 1 / (u * w) := by
    rw [Real.rpow_neg hc0.le, rpow_three_quarter hc0]; simp [hu, hw]
  rw [hc34]
  refine h0.trans ?_
  have hA : 0 < √(a * y) := lt_of_lt_of_le (by positivity) h1
  have hB : 0 < √(2 * √(a * y)) := lt_of_lt_of_le (by positivity) h2
  have e1 : 2 * Real.sqrt 2 * a / (2 * √(a * y)) = Real.sqrt 2 * a / √(a * y) := by field_simp
  rw [e1]
  have hE0 : 0 ≤ Real.exp (2 * √(a * y)) := (Real.exp_pos _).le
  have t1 : Real.sqrt 2 * a / √(a * y) ≤ Real.sqrt 2 * a / (q * u) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) h1
  have t2 : Real.exp (2 * √(a * y)) / √(2 * √(a * y)) ≤
      Real.exp (2 * √(a * c)) * Real.exp (2 * q) / (r * w) := by
    calc Real.exp (2 * √(a * y)) / √(2 * √(a * y)) ≤ Real.exp (2 * √(a * y)) / (r * w) :=
          div_le_div_of_nonneg_left hE0 (by positivity) h2
      _ ≤ _ := div_le_div_of_nonneg_right h4 (by positivity)
  calc Real.sqrt 2 * a / √(a * y) * (Real.exp (2 * √(a * y)) / √(2 * √(a * y)))
      ≤ Real.sqrt 2 * a / (q * u) * (Real.exp (2 * √(a * c)) * Real.exp (2 * q) / (r * w)) :=
        mul_le_mul t1 t2 (by positivity) (by positivity)
    _ = rho0K a * (1 / (u * w) * Real.exp (2 * √(a * c))) := by
        unfold rho0K
        rw [← hq, ← hr]
        field_simp

lemma rho0K_nonneg {a : ℝ} (ha : 0 < a) : 0 ≤ rho0K a := by unfold rho0K; positivity

/-- **The local bound for `ρ₀`.** -/
theorem rho0_local {a c : ℝ} (ha : 0 < a) (hc : 1 ≤ c) :
    (rho0 a).real (Icc (c - 1 / 2) (c + 1 / 2)) ≤
      rho0K a * (c ^ (-(3 / 4 : ℝ)) * Real.exp (2 * √(a * c))) := by
  have hc0 : 0 < c := by linarith
  set B : ℝ := rho0K a * (c ^ (-(3 / 4 : ℝ)) * Real.exp (2 * √(a * c))) with hB
  have hB0 : 0 ≤ B := by
    rw [hB]
    exact mul_nonneg (rho0K_nonneg ha) (mul_nonneg (Real.rpow_nonneg hc0.le _) (Real.exp_pos _).le)
  have hsub : Icc (c - 1 / 2) (c + 1 / 2) ⊆ Ioi (0 : ℝ) := fun y hy => by
    have := hy.1; simp only [mem_Ioi]; linarith
  have hd : (Measure.dirac (0 : ℝ)) (Icc (c - 1 / 2) (c + 1 / 2)) = 0 := by
    rw [Measure.dirac_apply' _ measurableSet_Icc]
    have : (0 : ℝ) ∉ Icc (c - 1 / 2) (c + 1 / 2) := fun h => by have := h.1; linarith
    rw [Set.indicator_of_notMem this]
  have hm : (rho0 a) (Icc (c - 1 / 2) (c + 1 / 2)) ≤ ENNReal.ofReal B := by
    unfold rho0
    rw [Measure.add_apply, hd, zero_add, withDensity_apply _ measurableSet_Icc,
      Measure.restrict_restrict measurableSet_Icc, Set.inter_eq_left.2 hsub]
    calc ∫⁻ y in Icc (c - 1 / 2) (c + 1 / 2), ENNReal.ofReal (crossingDensity a y)
        ≤ ∫⁻ y in Icc (c - 1 / 2) (c + 1 / 2), ENNReal.ofReal B := by
          refine setLIntegral_mono' measurableSet_Icc fun y hy => ?_
          exact ENNReal.ofReal_le_ofReal (crossingDensity_window ha hc (by linarith [hy.1]) hy.2)
      _ = ENNReal.ofReal B := by
          rw [setLIntegral_const, Real.volume_Icc, show c + 1 / 2 - (c - 1 / 2) = 1 by ring]
          simp
  have hfin : (rho0 a) (Icc (c - 1 / 2) (c + 1 / 2)) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hm
  rw [Measure.real, ← ENNReal.toReal_ofReal hB0]
  exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hm

end Lightlike.Tauberian
