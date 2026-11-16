import Lightlike.Asymptotics.Lorentzian.Eq57
import Lightlike.Oscillatory.PhaseReductionTests

/-!
# Non-vacuity of the two-point stationary-phase formula

For the model phase `S(x) = -(x² - 1)² + iθ (3x - x³)/2` on `ℝ¹` the hypotheses of
`weighted_two_points_eq57` hold together (`toy_two_points`): the critical points with `Re S = 0` in
the support of the amplitude are `±1`, with `S(±1) = ±iθ`, `Re S ≤ 0`, and the Hessians of `-S` are
`8 ± 3iθ ≠ 0`. This shows that the assumptions of `lorVertex_asymptotic_formula` are not
contradictory in the shape they have there (two parity-related nondegenerate critical points with
purely imaginary values `±iθ`).
-/

open Complex Filter Asymptotics MeasureTheory Lightlike.Oscillatory
open scoped Real ContDiff Topology

namespace Lightlike.Asymptotics.Lorentzian

/-- The toy polynomial `e(w) = -(w² - 1)² + iθ (3w - w³)/2`. -/
noncomputable def toyPoly (θ : ℝ) (w : ℂ) : ℂ := -((w ^ 2 - 1) ^ 2) + I * θ * (3 * w - w ^ 3) / 2

/-- The toy phase on `ℝ¹`. -/
noncomputable def toyAction (θ : ℝ) (x : Fin 1 → ℝ) : ℂ := toyPoly θ (x 0 : ℂ)

theorem hasDerivAt_toyPoly (θ : ℝ) (w : ℂ) :
    HasDerivAt (toyPoly θ) ((w ^ 2 - 1) * (-4 * w - 3 / 2 * I * θ)) w := by
  have h1 := ((((hasDerivAt_pow 2 w).sub_const 1).pow 2).neg)
  have h2 := (((hasDerivAt_id w).const_mul 3).sub (hasDerivAt_pow 3 w)).const_mul (I * θ) |>.div_const 2
  have := h1.add h2
  refine this.congr_deriv ?_
  push_cast
  ring

theorem hasDerivAt_toyPoly' (θ : ℝ) (w : ℂ) :
    HasDerivAt (fun w : ℂ => (w ^ 2 - 1) * (-4 * w - 3 / 2 * I * θ))
      (2 * w * (-4 * w - 3 / 2 * I * θ) + (w ^ 2 - 1) * (-4)) w := by
  have h1 := ((hasDerivAt_pow 2 w).sub_const 1)
  have h2 := (((hasDerivAt_id w).const_mul (-4)).sub_const (3 / 2 * I * θ))
  have := h1.mul h2
  refine this.congr_deriv ?_
  simp only [id]
  push_cast
  ring

theorem contDiff_toyAction (θ : ℝ) : ContDiff ℝ ∞ (toyAction θ) := by
  have hL : ContDiff ℝ ∞ (fun y : Fin 1 → ℝ => ((y 0 : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)).contDiff
  unfold toyAction toyPoly
  exact (((hL.pow 2).sub contDiff_const).pow 2).neg.add
    (((contDiff_const.mul (contDiff_const.mul hL |>.sub (hL.pow 3))) |>.div_const 2))

/-- The real part of the toy phase on `ℝ¹` is `-(x² - 1)²`. -/
theorem toyAction_re (θ : ℝ) (x : Fin 1 → ℝ) : (toyAction θ x).re = -((x 0 ^ 2 - 1) ^ 2) := by
  simp [toyAction, toyPoly, pow_succ, Complex.mul_re, Complex.mul_im]

/-- Values at `x = ±1`. -/
theorem toyAction_one (θ : ℝ) : toyAction θ (fun _ => 1) = I * θ := by
  simp [toyAction, toyPoly]
  ring

theorem toyAction_neg_one (θ : ℝ) : toyAction θ (fun _ => -1) = -(I * θ) := by
  simp [toyAction, toyPoly]
  ring

/-- The derivative of the toy phase vanishes at `x = ±1`. -/
theorem fderiv_toyAction (θ : ℝ) (x : Fin 1 → ℝ) (hx : x 0 = 1 ∨ x 0 = -1) :
    fderiv ℝ (toyAction θ) x = 0 := by
  have h := hasFDerivAt_comp_coord (e := toyPoly θ) (x := x) (hasDerivAt_toyPoly θ _)
  rw [show (fun y : Fin 1 → ℝ => toyPoly θ (y 0 : ℂ)) = toyAction θ from rfl] at h
  rw [h.fderiv]
  have : (((x 0 : ℝ) : ℂ) ^ 2 - 1) = 0 := by
    rcases hx with hx | hx <;> simp [hx]
  rw [this, zero_mul]
  ext
  simp

/-- The Hessian of the toy phase is `e''(x₀)`. -/
theorem hessMat_toyAction (θ : ℝ) (x : Fin 1 → ℝ) :
    hessMat (toyAction θ) x = fun _ _ =>
      2 * (x 0 : ℂ) * (-4 * (x 0 : ℂ) - 3 / 2 * I * θ) + ((x 0 : ℂ) ^ 2 - 1) * (-4) := by
  have h1 : (fun y : Fin 1 → ℝ => coordDeriv (toyAction θ) 0 y) =
      fun y => (fun w : ℂ => (w ^ 2 - 1) * (-4 * w - 3 / 2 * I * θ)) (y 0 : ℂ) :=
    funext fun y => coordDeriv_comp_coord (e := toyPoly θ) (hasDerivAt_toyPoly θ _) 0
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  simp only [hessMat, h1]
  rw [coordDeriv_comp_coord (hasDerivAt_toyPoly' θ _)]

/-- **Non-vacuity of the two-point formula**: for the toy phase `S(x) = -(x²-1)² + iθ(3x - x³)/2` on
`ℝ¹` (critical points `±1` with `S(±1) = ±iθ`, Hessians `-8 ∓ 3iθ`), the amplitude `smallAmp` of
radius `4` (equal to `1` on `[-2, 2]`) and `aFar = 0`, every hypothesis of `weighted_two_points_eq57`
holds simultaneously. -/
theorem toy_two_points (θ : ℝ) :
    (fun lam : ℕ => ((1 : ℂ) * (((lam : ℝ) ^ (0 : ℝ) : ℝ) : ℂ)) *
        (∫ x, (smallAmp (δ := 4) (by norm_num) x + (fun _ => (0 : ℂ)) x) *
          cexp ((lam : ℝ) * toyAction θ x)) -
      (((lam : ℝ) ^ ((0 : ℝ) - ((1 : ℕ) : ℝ) / 2) : ℝ) : ℂ) *
        (eq57Constant 1 1 1 (-hessMat (toyAction θ) (fun _ => 1)) (fun _ => 1) *
            cexp (I * (lam : ℝ) * θ) +
          eq57Constant 1 1 1 (-hessMat (toyAction θ) (fun _ => -1)) (fun _ => 1) *
            cexp (-(I * (lam : ℝ) * θ))))
      =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ ((0 : ℝ) - ((1 : ℕ) : ℝ) / 2 - 1)) := by
  have hδ : (0 : ℝ) < 4 := by norm_num
  have hone : ∀ x : Fin 1 → ℝ, ‖x‖ ≤ 2 → smallAmp hδ x = 1 := by
    intro x hx
    have := (smallBump hδ).one_of_mem_closedBall (x := x) (by
      rw [mem_closedBall_zero_iff]; simp only [smallBump]; linarith)
    simp [smallAmp, this]
  have hnorm : ∀ x : Fin 1 → ℝ, (x 0 = 1 ∨ x 0 = -1) → ‖x‖ ≤ 2 := by
    intro x hx
    rw [pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i
    rw [Subsingleton.elim i 0, Real.norm_eq_abs]
    rcases hx with hx | hx <;> simp [hx]
  have hx₁ : ∀ x : Fin 1 → ℝ, (x 0 = 1 ∨ x 0 = -1) → x ∈ tsupport (smallAmp hδ) := fun x hx =>
    subset_tsupport _ (Function.mem_support.mpr (by rw [hone x (hnorm x hx)]; exact one_ne_zero))
  have hdet : ∀ s : ℝ, (s = 1 ∨ s = -1) →
      (-hessMat (toyAction θ) (fun _ => s)).det ≠ 0 := by
    intro s hs
    rw [hessMat_toyAction, Matrix.det_unique]
    intro h
    have h' : -(2 * ((s : ℝ) : ℂ) * (-4 * ((s : ℝ) : ℂ) - 3 / 2 * I * θ) +
        (((s : ℝ) : ℂ) ^ 2 - 1) * (-4)) = 0 := h
    have := congrArg Complex.re h'
    rcases hs with rfl | rfl <;> simp [Complex.mul_re, Complex.mul_im] at this
  have hamp : ∀ x : Fin 1 → ℝ, (x 0 = 1 ∨ x 0 = -1) →
      (1 : ℂ) * smallAmp hδ x = 1 * 1 * ∏ _e : Fin 10, (1 : ℂ) := by
    intro x hx
    rw [hone x (hnorm x hx)]; simp
  have h := weighted_two_points_eq57 (S := toyAction θ) (aLoc := smallAmp hδ)
    (aFar := fun _ => 0) (contDiff_toyAction θ) (contDiff_smallAmp hδ)
    (by have := (smallBump hδ).hasCompactSupport
        exact (this.comp_left (g := ((↑) : ℝ → ℂ)) ofReal_zero))
    (fun x _ => by rw [toyAction_re]; exact neg_nonpos.mpr (sq_nonneg _))
    (fun _ => 1) (fun _ => -1)
    (fun h => by have := congrFun h 0; norm_num at this)
    (fun x hx => by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, -⟩
        rw [toyAction_re] at h1
        have : (x 0 ^ 2 - 1) ^ 2 = 0 := by linarith
        have h2 : x 0 ^ 2 = 1 := by nlinarith [sq_nonneg (x 0 ^ 2 - 1)]
        have h3 : x 0 = 1 ∨ x 0 = -1 := by
          have : (x 0 - 1) * (x 0 + 1) = 0 := by nlinarith
          rcases mul_eq_zero.mp this with h | h
          · left; linarith
          · right; linarith
        rcases h3 with h3 | h3
        · left; funext i; rw [Subsingleton.elim i 0]; exact h3
        · right; funext i; rw [Subsingleton.elim i 0]; exact h3
      · rintro (rfl | rfl)
        · exact ⟨by rw [toyAction_re]; simp, fderiv_toyAction θ _ (Or.inl rfl)⟩
        · exact ⟨by rw [toyAction_re]; simp, fderiv_toyAction θ _ (Or.inr rfl)⟩)
    (hx₁ _ (Or.inl rfl)) (hx₁ _ (Or.inr rfl))
    (hdet 1 (Or.inl rfl)) (hdet (-1) (Or.inr rfl))
    (fun τ => by simp) (by simp only [zero_mul, integral_zero]; exact isBigO_zero _ _) θ (toyAction_one θ) (toyAction_neg_one θ) 1 0 1 1 1
    (fun _ => 1) (fun _ => 1) (hamp _ (Or.inl rfl)) (hamp _ (Or.inr rfl))
  simpa using h

end Lightlike.Asymptotics.Lorentzian
