module

public import Mathlib

/-!
# The freeze-out equation `dY/dx = -(λ/x²)(Y² - Y_eq²)`: statement and uniqueness

Row G1-034 (milestone CO7).  `Y_eq` is a function `e : ℝ → ℝ`, the coupling is `lam`, and the
solution starts at `x₀ > 0` with `Y(x₀) = Y₀`.

* `rhs lam e x y`: the right-hand side `-(lam/x²)(y² - e(x)²)`.
* `IsSol lam e x₀ Y₀ Y`: `Y` is a (global, forward) solution from `x₀`.
* `lip_rhs`: the right-hand side is Lipschitz in `y` on a ball, uniformly in `x ≥ x₀`.
* `IsSol.eqOn`: two solutions agree on `[x₀, ∞)`.
-/

@[expose] public section

namespace Lightlike.Cosmology.FreezeOut

open Set Metric

/-- The right-hand side `-(λ/x²)(y² - Y_eq(x)²)` of the freeze-out equation. -/
noncomputable def rhs (lam : ℝ) (e : ℝ → ℝ) (x y : ℝ) : ℝ := -(lam / x ^ 2) * (y ^ 2 - e x ^ 2)

/-- `Y` solves `dY/dx = rhs lam e x (Y x)` on `[x₀, ∞)` with `Y x₀ = Y₀` (one-sided derivative
at `x₀`). -/
def IsSol (lam : ℝ) (e : ℝ → ℝ) (x₀ Y₀ : ℝ) (Y : ℝ → ℝ) : Prop :=
  Y x₀ = Y₀ ∧ ∀ x, x₀ ≤ x → HasDerivWithinAt Y (rhs lam e x (Y x)) (Ici x₀) x

/-- A solution is continuous on `[x₀, ∞)`. -/
lemma IsSol.continuousOn {lam e x₀ Y₀ Y} (h : IsSol lam e x₀ Y₀ Y) : ContinuousOn Y (Ici x₀) :=
  fun x hx => (h.2 x hx).continuousWithinAt

/-- The right-hand side is Lipschitz in `y` on `closedBall 0 R`, uniformly for `t ≥ x₀ > 0`. -/
lemma lip_rhs {lam : ℝ} (hlam : 0 ≤ lam) (e : ℝ → ℝ) {x₀ : ℝ} (hx₀ : 0 < x₀) (R : ℝ)
    (hR : 0 ≤ R) {t : ℝ} (ht : x₀ ≤ t) :
    LipschitzOnWith ⟨lam / x₀ ^ 2 * (2 * R), by positivity⟩ (rhs lam e t) (closedBall 0 R) := by
  refine LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_
  simp only [mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hy hz
  simp only [rhs, Real.dist_eq]
  have ht0 : 0 < t := lt_of_lt_of_le hx₀ ht
  have h1 : lam / t ^ 2 ≤ lam / x₀ ^ 2 :=
    div_le_div_of_nonneg_left hlam (by positivity) (pow_le_pow_left₀ hx₀.le ht 2)
  have h2 : |y + z| ≤ 2 * R := by
    calc |y + z| ≤ |y| + |z| := abs_add_le _ _
      _ ≤ 2 * R := by linarith
  have h3 : -(lam / t ^ 2) * (y ^ 2 - e t ^ 2) - -(lam / t ^ 2) * (z ^ 2 - e t ^ 2)
      = -(lam / t ^ 2) * ((y - z) * (y + z)) := by ring
  rw [h3, abs_mul, abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ lam / t ^ 2)]
  have h4 : 0 ≤ |y - z| := abs_nonneg _
  calc lam / t ^ 2 * (|y - z| * |y + z|) ≤ lam / x₀ ^ 2 * (|y - z| * (2 * R)) := by
        apply mul_le_mul h1 _ (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left h2 h4
    _ = lam / x₀ ^ 2 * (2 * R) * |y - z| := by ring

/-- **Uniqueness**: two solutions with the same initial value agree on `[x₀, ∞)`. -/
theorem IsSol.eqOn {lam : ℝ} (hlam : 0 ≤ lam) {e : ℝ → ℝ} {x₀ Y₀ : ℝ} (hx₀ : 0 < x₀)
    {Y Z : ℝ → ℝ} (hY : IsSol lam e x₀ Y₀ Y) (hZ : IsSol lam e x₀ Y₀ Z) :
    EqOn Y Z (Ici x₀) := by
  intro x hx
  have hx : x₀ ≤ x := hx
  have hc : IsCompact (Icc x₀ (x + 1)) := isCompact_Icc
  obtain ⟨B1, hB1⟩ := hc.exists_bound_of_continuousOn (hY.continuousOn.mono Icc_subset_Ici_self)
  obtain ⟨B2, hB2⟩ := hc.exists_bound_of_continuousOn (hZ.continuousOn.mono Icc_subset_Ici_self)
  set R := max (max B1 B2) 0 with hRdef
  have hR : 0 ≤ R := le_max_right _ _
  have key := ODE_solution_unique_of_mem_Icc_right
    (v := rhs lam e) (s := fun _ => closedBall 0 R) (a := x₀) (b := x + 1)
    (K := ⟨lam / x₀ ^ 2 * (2 * R), by positivity⟩)
    (fun t ht => lip_rhs hlam e hx₀ R hR ht.1)
    (hY.continuousOn.mono (Icc_subset_Ici_self))
    (fun t ht => (hY.2 t ht.1).mono (Ici_subset_Ici.2 ht.1))
    (fun t ht => by
      simp only [mem_closedBall, dist_zero_right]
      exact (hB1 t (Ico_subset_Icc_self ht)).trans
        ((le_max_left _ _).trans (le_max_left _ _)))
    (hZ.continuousOn.mono (Icc_subset_Ici_self))
    (fun t ht => (hZ.2 t ht.1).mono (Ici_subset_Ici.2 ht.1))
    (fun t ht => by
      simp only [mem_closedBall, dist_zero_right]
      exact (hB2 t (Ico_subset_Icc_self ht)).trans
        ((le_max_right _ _).trans (le_max_left _ _)))
    (hY.1.trans hZ.1.symm)
  exact key ⟨hx, by linarith⟩

end Lightlike.Cosmology.FreezeOut

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_034.IsSol := _root_.Lightlike.Cosmology.FreezeOut.IsSol
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_034.IsSol.continuousOn := _root_.Lightlike.Cosmology.FreezeOut.IsSol.continuousOn
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_034.IsSol.eqOn := _root_.Lightlike.Cosmology.FreezeOut.IsSol.eqOn
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_034.lip_rhs := _root_.Lightlike.Cosmology.FreezeOut.lip_rhs
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_034.rhs := _root_.Lightlike.Cosmology.FreezeOut.rhs
