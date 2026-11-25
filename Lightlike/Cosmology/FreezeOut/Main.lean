module

public import Mathlib
public import Lightlike.Cosmology.FreezeOut.Basic
public import Lightlike.Cosmology.FreezeOut.Bounds
public import Lightlike.Cosmology.FreezeOut.Limit
public import Lightlike.Cosmology.FreezeOut.Truncation

/-!
# The freeze-out equation: unique global solution with a finite limit (CO7)

Row G1-034, milestone CO7 (docs/tasks/milestones.md:85; source key `kolb-turner-1990`).

For `λ ≥ 0`, `x₀ > 0`, `Y₀ ≥ 0` and `Y_eq` continuous and bounded by `M` on `[x₀, ∞)`, the equation
`dY/dx = −(λ/x²)(Y² − Y_eq²)`, `Y(x₀) = Y₀`, has a unique global forward solution, it is
nonnegative, and it has a finite limit `Y_∞` with
`Y₀/(1 + λY₀/x₀) ≤ Y_∞ ≤ Y₀ + λM²/x₀`.  For `Y_eq ≡ 0` (`M = 0`) the limit is exactly
`Y₀/(1 + λY₀/x₀)`.

* `freezeout_exists_unique_limit`: the main theorem.
* `freezeout_zero_eq_limit`: the `Y_eq ≡ 0` check.
-/

@[expose] public section

namespace Lightlike.Cosmology.FreezeOut

open Set Filter Topology

/-- **Freeze-out equation** `dY/dx = −(λ/x²)(Y² − Y_eq²)`: there is a unique global solution
(on `[x₀, ∞)`), it is nonnegative, and it has a finite limit `Y_∞` at infinity with the two-sided
bounds `Y₀/(1 + λY₀/x₀) ≤ Y_∞ ≤ Y₀ + λM²/x₀`, where `|Y_eq| ≤ M`. -/
theorem freezeout_exists_unique_limit {lam : ℝ} (hlam : 0 ≤ lam) {e : ℝ → ℝ} {x₀ Y₀ M : ℝ}
    (hx₀ : 0 < x₀) (hY₀ : 0 ≤ Y₀) (he : ContinuousOn e (Ici x₀))
    (hM : ∀ x, x₀ ≤ x → |e x| ≤ M) :
    ∃ Y : ℝ → ℝ, IsSol lam e x₀ Y₀ Y ∧ (∀ x, x₀ ≤ x → 0 ≤ Y x) ∧
      (∀ Z : ℝ → ℝ, IsSol lam e x₀ Y₀ Z → EqOn Y Z (Ici x₀)) ∧
      ∃ Yinf : ℝ, Tendsto Y atTop (𝓝 Yinf) ∧ Y₀ / (1 + lam * Y₀ / x₀) ≤ Yinf ∧
        Yinf ≤ Y₀ + lam * M ^ 2 / x₀ := by
  obtain ⟨Y, hY, hnn⟩ := exists_isSol hlam hx₀ hY₀ he hM
  exact ⟨Y, hY, hnn, fun Z hZ => hY.eqOn hlam hx₀ hZ, hY.limit hlam hx₀ hY₀ hM hnn⟩

/-- `Bsol` is the solution for `Y_eq ≡ 0`. -/
lemma isSol_Bsol {lam : ℝ} (hlam : 0 ≤ lam) {x₀ Y₀ : ℝ} (hx₀ : 0 < x₀) (hY₀ : 0 ≤ Y₀) :
    IsSol lam (fun _ => 0) x₀ Y₀ (Bsol lam x₀ Y₀) := by
  refine ⟨by simp [Bsol], fun x hx => ?_⟩
  have := (hasDerivAt_Bsol hlam hx₀ hY₀ hx).hasDerivWithinAt (s := Ici x₀)
  simpa [rhs] using this

/-- **Check `Y_eq ≡ 0`**: the solution is `Y₀ / (1 + λY₀(1/x₀ − 1/x))` and
`Y_∞ = Y₀/(1 + λY₀/x₀)` exactly. -/
theorem freezeout_zero_eq_limit {lam : ℝ} (hlam : 0 ≤ lam) {x₀ Y₀ : ℝ} (hx₀ : 0 < x₀)
    (hY₀ : 0 ≤ Y₀) {Y : ℝ → ℝ} (hY : IsSol lam (fun _ => 0) x₀ Y₀ Y) :
    EqOn Y (Bsol lam x₀ Y₀) (Ici x₀) ∧
      Tendsto Y atTop (𝓝 (Y₀ / (1 + lam * Y₀ / x₀))) := by
  have heq : EqOn Y (Bsol lam x₀ Y₀) (Ici x₀) := hY.eqOn hlam hx₀ (isSol_Bsol hlam hx₀ hY₀)
  refine ⟨heq, ?_⟩
  have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hden : Tendsto (fun x : ℝ => 1 + lam * Y₀ * (x₀⁻¹ - x⁻¹)) atTop
      (𝓝 (1 + lam * Y₀ * (x₀⁻¹ - 0))) :=
    (tendsto_const_nhds.sub hinv).const_mul _ |>.const_add 1
  have hne : (1 + lam * Y₀ * (x₀⁻¹ - 0)) ≠ 0 := by
    have : 0 ≤ lam * Y₀ * (x₀⁻¹ - 0) := by
      apply mul_nonneg (mul_nonneg hlam hY₀); simp [hx₀.le]
    linarith
  have hB : Tendsto (Bsol lam x₀ Y₀) atTop (𝓝 (Y₀ / (1 + lam * Y₀ * (x₀⁻¹ - 0)))) :=
    tendsto_const_nhds.div hden hne
  have hval : Y₀ / (1 + lam * Y₀ * (x₀⁻¹ - 0)) = Y₀ / (1 + lam * Y₀ / x₀) := by
    rw [sub_zero]; simp only [div_eq_mul_inv]
  rw [hval] at hB
  exact hB.congr' (by
    filter_upwards [eventually_ge_atTop x₀] with x hx using (heq hx).symm)

end Lightlike.Cosmology.FreezeOut

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_034.freezeout_exists_unique_limit := _root_.Lightlike.Cosmology.FreezeOut.freezeout_exists_unique_limit
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_034.freezeout_zero_eq_limit := _root_.Lightlike.Cosmology.FreezeOut.freezeout_zero_eq_limit
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_034.isSol_Bsol := _root_.Lightlike.Cosmology.FreezeOut.isSol_Bsol
