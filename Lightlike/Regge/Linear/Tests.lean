import Mathlib
import Lightlike.Regge.Linear.Converge

/-!
# Trust checks for the linearized Regge convergence

* **Non-vacuity.** A concrete symmetric perturbation `h` with smooth compactly supported entries
  and a weight `f` satisfy every hypothesis of `linearized_regge_converges`, and the integral of
  `f` against the linearized curvature is positive.
* **Wrong model.** Dropping the `∂₀∂₁ h₀₁` term from the curvature gives the limit `0` for this
  `h`, which the vertex deficits do not approach.
-/

open Set MeasureTheory Lightlike

namespace Lightlike.Regge.Linear

noncomputable section

/-- A bump function equal to `1` on the unit ball. -/
def bumpOne : ContDiffBump (0 : Fin 2 → ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The weight: a bump supported in the ball of radius `1/2`. -/
def bumpHalf : ContDiffBump (0 : Fin 2 → ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

/-- The off-diagonal entry `x₀ x₁` times the bump. -/
def phi (x : Fin 2 → ℝ) : ℝ := bumpOne x * (x 0 * x 1)

/-- The test perturbation: `h₀₁ = h₁₀ = φ`, `h₀₀ = h₁₁ = 0`. -/
def hEx (x : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, phi x; phi x, 0]

lemma phi_contDiff : ContDiff ℝ 3 phi := by
  have h1 : ContDiff ℝ 3 (bumpOne : (Fin 2 → ℝ) → ℝ) := by
    simpa using bumpOne.contDiff (n := 3)
  have h2 : ContDiff ℝ 3 (fun x : Fin 2 → ℝ => x 0 * x 1) :=
    (contDiff_apply ℝ (fun _ : Fin 2 => ℝ) 0).mul (contDiff_apply ℝ (fun _ : Fin 2 => ℝ) 1)
  exact h1.mul h2

lemma phi_compact : HasCompactSupport phi :=
  bumpOne.hasCompactSupport.mul_right

lemma phi_eq {x : Fin 2 → ℝ} (hx : ‖x‖ < 1) : phi x = x 0 * x 1 := by
  unfold phi
  rw [bumpOne.one_of_mem_closedBall (by simpa [bumpOne] using hx.le), one_mul]

lemma pd1_phi {x : Fin 2 → ℝ} (hx : ‖x‖ < 1) : Lightlike.pd 1 phi x = x 0 := by
  have hev : phi =ᶠ[nhds x] fun z : Fin 2 → ℝ => z 0 * z 1 := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (show x ∈ Metric.ball (0 : Fin 2 → ℝ) 1 by
      simpa using hx)] with z hz
    exact phi_eq (by simpa using hz)
  unfold Lightlike.pd
  rw [hev.fderiv_eq]
  have : HasFDerivAt (fun z : Fin 2 → ℝ => z 0 * z 1)
      ((x 0) • (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ) +
        (x 1) • (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ)) x := by
    have h0 := (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) 0 x)
    have h1 := (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) 1 x)
    exact h0.mul h1
  rw [this.fderiv]
  simp

lemma pd_zero (k : Fin 2) : Lightlike.pd k (fun _ : Fin 2 → ℝ => (0 : ℝ)) = fun _ => 0 := by
  funext x; simp [Lightlike.pd]

lemma pd0_pd1_phi {x : Fin 2 → ℝ} (hx : ‖x‖ < 1) : Lightlike.pd 0 (Lightlike.pd 1 phi) x = 1 := by
  have hev : Lightlike.pd 1 phi =ᶠ[nhds x] fun y : Fin 2 → ℝ => y 0 := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (show x ∈ Metric.ball (0 : Fin 2 → ℝ) 1 by
      simpa using hx)] with z hz
    exact pd1_phi (by simpa using hz)
  unfold Lightlike.pd
  rw [Filter.EventuallyEq.fderiv_eq (f := fun y : Fin 2 → ℝ => y 0) (by
    filter_upwards [hev] with z hz using hz)]
  have := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) 0 x
  rw [this.fderiv]
  simp

/-- On the unit ball the linearized curvature of `hEx` is `1`. -/
lemma linCurv_hEx {x : Fin 2 → ℝ} (hx : ‖x‖ < 1) : linCurv hEx x = 1 := by
  have h00 : (fun y => hEx y 0 0) = fun _ => 0 := by funext y; simp [hEx]
  have h11 : (fun y => hEx y 1 1) = fun _ => 0 := by funext y; simp [hEx]
  have h01 : (fun y => hEx y 0 1) = phi := by funext y; simp [hEx]
  simp only [linCurv, curv, jetOf, h00, h11, h01, pd_zero, pd0_pd1_phi hx]
  norm_num

lemma hEx_contDiff : ∀ i j, ContDiff ℝ 3 fun x => hEx x i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [hEx, phi_contDiff, contDiff_const]

lemma hEx_compact : ∀ i j, HasCompactSupport fun x => hEx x i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [hEx, phi_compact] <;> exact HasCompactSupport.zero

/-- The curvature with the `∂₀∂₁ h₀₁` term dropped (a deliberately wrong model). -/
def wrongCurv (h : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 → ℝ) : ℝ :=
  -(Lightlike.pd 1 (Lightlike.pd 1 fun y => h y 0 0) x
    + Lightlike.pd 0 (Lightlike.pd 0 fun y => h y 1 1) x) / 2

lemma wrongCurv_hEx (x : Fin 2 → ℝ) : wrongCurv hEx x = 0 := by
  have h00 : (fun y => hEx y 0 0) = fun _ => 0 := by funext y; simp [hEx]
  have h11 : (fun y => hEx y 1 1) = fun _ => 0 := by funext y; simp [hEx]
  simp [wrongCurv, h00, h11, pd_zero]

lemma weight_integral_pos : 0 < ∫ x, bumpHalf x * linCurv hEx x := by
  have : (fun x => bumpHalf x * linCurv hEx x) = fun x => bumpHalf x := by
    funext x
    by_cases hx : ‖x‖ < 1
    · rw [linCurv_hEx hx, mul_one]
    · have : bumpHalf x = 0 := by
        by_contra hne
        have hmem : x ∈ Function.support (bumpHalf : (Fin 2 → ℝ) → ℝ) := hne
        rw [bumpHalf.support_eq] at hmem
        simp only [Metric.mem_ball, dist_zero_right, bumpHalf] at hmem
        linarith
      rw [this, zero_mul]
  rw [this]
  exact bumpHalf.integral_pos

/-- **Non-vacuity.** The hypotheses of `linearized_regge_converges` are met by `hEx` and a bump
weight, and the limit `∫ f · linCurv h` is strictly positive. -/
theorem nonvacuity :
    ∃ C : ℝ, 0 < ∫ x, bumpHalf x * linCurv hEx x ∧ ∀ n : ℕ, 0 < n →
      |∑' v : ℤ × ℤ, bumpHalf (gpt n v) * linDef hEx (1 / (n : ℝ)) (gpt n v)
        - ∫ x, bumpHalf x * linCurv hEx x| ≤ C / n := by
  obtain ⟨C, hC⟩ := linearized_regge_converges (h := hEx) (hEx_contDiff 0 0) (hEx_contDiff 0 1)
    (hEx_contDiff 1 1) (hEx_compact 0 0) (hEx_compact 0 1) (hEx_compact 1 1)
    (fun x => by simp [hEx]) (f := bumpHalf) (by simpa using bumpHalf.contDiff (n := 1))
    bumpHalf.hasCompactSupport
  exact ⟨C, weight_integral_pos, hC⟩

/-- **Wrong model.** With the `∂₀∂₁ h₀₁` term dropped, the limit would be `0` for `hEx`, and the
weighted vertex deficits do not converge to it at any rate `C / n`. -/
theorem wrong_model_fails :
    ¬ ∃ C : ℝ, ∀ n : ℕ, 0 < n →
      |∑' v : ℤ × ℤ, bumpHalf (gpt n v) * linDef hEx (1 / (n : ℝ)) (gpt n v)
        - ∫ x, bumpHalf x * wrongCurv hEx x| ≤ C / n := by
  rintro ⟨C2, hC2⟩
  obtain ⟨C1, hI, hC1⟩ := nonvacuity
  set I := ∫ x, bumpHalf x * linCurv hEx x with hIdef
  have hw : ∫ x, bumpHalf x * wrongCurv hEx x = 0 := by simp [wrongCurv_hEx]
  obtain ⟨n, hn⟩ := exists_nat_gt ((|C1| + |C2|) / I)
  have hpos : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
  have hn0 : 0 < n := by exact_mod_cast hpos
  have h1 := hC1 n hn0
  have h2 := hC2 n hn0
  rw [hw, sub_zero] at h2
  set S := ∑' v : ℤ × ℤ, bumpHalf (gpt n v) * linDef hEx (1 / (n : ℝ)) (gpt n v)
  have h3 : I ≤ |S| + |S - I| := by
    have : I = S - (S - I) := by ring
    calc I = S - (S - I) := this
      _ ≤ |S - (S - I)| := le_abs_self _
      _ ≤ |S| + |S - I| := abs_sub _ _
  have h4 : C1 / n ≤ |C1| / n := div_le_div_of_nonneg_right (le_abs_self _) hpos.le
  have h5 : C2 / n ≤ |C2| / n := div_le_div_of_nonneg_right (le_abs_self _) hpos.le
  have h6 : (|C1| + |C2|) / n < I := by
    rw [div_lt_iff₀ hpos]
    rw [div_lt_iff₀ hI] at hn
    linarith
  rw [add_div] at h6
  linarith

end

end Lightlike.Regge.Linear
