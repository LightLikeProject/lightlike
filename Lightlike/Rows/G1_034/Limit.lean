module

public import Mathlib
public import Lightlike.Rows.G1_034.Basic
public import Lightlike.Rows.G1_034.Bounds

/-!
# The freeze-out equation: upper bound and limit of a nonnegative solution

Row G1-034 (milestone CO7).  For a solution `Y` of `dY/dx = -(λ/x²)(Y² - e²)` with `|e| ≤ M`:

* `IsSol.upper`: `Y x ≤ Y₀ + λ M² / x₀`.
* `IsSol.limit`: if `Y ≥ 0`, then `Y` has a finite limit `Y_∞` with
  `Y₀ / (1 + λ Y₀ / x₀) ≤ Y_∞ ≤ Y₀ + λ M² / x₀`.
-/

@[expose] public section

namespace Lightlike.Rows.G1_034

open Set Filter Topology

/-- `Y x + λM²/x` is antitone for a solution with `|e| ≤ M`. -/
lemma IsSol.antitone {lam : ℝ} (hlam : 0 ≤ lam) {e : ℝ → ℝ} {x₀ Y₀ M : ℝ} (hx₀ : 0 < x₀)
    {Y : ℝ → ℝ} (h : IsSol lam e x₀ Y₀ Y) (hM : ∀ x, x₀ ≤ x → |e x| ≤ M) :
    AntitoneOn (fun x => Y x + lam * M ^ 2 / x) (Ici x₀) := by
  refine antitoneOn_add_div hx₀ h.continuousOn h.2 fun x hx => ?_
  have hx0 : 0 < x := lt_of_lt_of_le hx₀ hx
  have he : e x ^ 2 ≤ M ^ 2 := sq_le_sq' (by linarith [abs_le.1 (hM x hx)])
    (abs_le.1 (hM x hx)).2
  have h1 : rhs lam e x (Y x) = lam / x ^ 2 * (e x ^ 2 - Y x ^ 2) := by
    simp only [rhs]; ring
  rw [h1]
  have h2 : e x ^ 2 - Y x ^ 2 ≤ M ^ 2 := by nlinarith [sq_nonneg (Y x)]
  calc lam / x ^ 2 * (e x ^ 2 - Y x ^ 2) ≤ lam / x ^ 2 * M ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = lam * M ^ 2 / x ^ 2 := by ring

/-- **Upper bound**: a solution with `|e| ≤ M` satisfies `Y x ≤ Y₀ + λ M² / x₀`. -/
theorem IsSol.upper {lam : ℝ} (hlam : 0 ≤ lam) {e : ℝ → ℝ} {x₀ Y₀ M : ℝ} (hx₀ : 0 < x₀)
    {Y : ℝ → ℝ} (h : IsSol lam e x₀ Y₀ Y) (hM : ∀ x, x₀ ≤ x → |e x| ≤ M) :
    ∀ x, x₀ ≤ x → Y x ≤ Y₀ + lam * M ^ 2 / x₀ := by
  intro x hx
  have hA := h.antitone hlam hx₀ hM (show x₀ ∈ Ici x₀ from le_rfl) (show x ∈ Ici x₀ from hx) hx
  simp only [h.1] at hA
  have : 0 ≤ lam * M ^ 2 / x := by
    have : 0 < x := lt_of_lt_of_le hx₀ hx
    positivity
  linarith

/-- A nonnegative solution with `|e| ≤ M` has a finite limit `Y_∞`, bounded on both sides. -/
theorem IsSol.limit {lam : ℝ} (hlam : 0 ≤ lam) {e : ℝ → ℝ} {x₀ Y₀ M : ℝ} (hx₀ : 0 < x₀)
    (hY₀ : 0 ≤ Y₀) {Y : ℝ → ℝ} (h : IsSol lam e x₀ Y₀ Y) (hM : ∀ x, x₀ ≤ x → |e x| ≤ M)
    (hnn : ∀ x, x₀ ≤ x → 0 ≤ Y x) :
    ∃ L, Tendsto Y atTop (𝓝 L) ∧ Y₀ / (1 + lam * Y₀ / x₀) ≤ L ∧ L ≤ Y₀ + lam * M ^ 2 / x₀ := by
  obtain ⟨L, hL⟩ := exists_tendsto_of_antitoneOn hx₀ (by positivity : 0 ≤ lam * M ^ 2)
    (h.antitone hlam hx₀ hM) hnn
  refine ⟨L, hL, ?_, ?_⟩
  · refine ge_of_tendsto hL ?_
    filter_upwards [eventually_ge_atTop x₀] with x hx
    have hb := h.bsol_le hlam hx₀ hY₀ hnn x hx
    refine le_trans ?_ hb
    have hD := one_le_denom hlam hx₀ hY₀ hx
    have hle : 1 + lam * Y₀ * (x₀⁻¹ - x⁻¹) ≤ 1 + lam * Y₀ / x₀ := by
      have : 0 ≤ lam * Y₀ * x⁻¹ := by
        have : 0 < x := lt_of_lt_of_le hx₀ hx
        positivity
      rw [div_eq_mul_inv]
      nlinarith
    simp only [Bsol]
    exact div_le_div_of_nonneg_left hY₀ (by linarith) hle
  · exact le_of_tendsto hL (by
      filter_upwards [eventually_ge_atTop x₀] with x hx
      exact h.upper hlam hx₀ hM x hx)

end Lightlike.Rows.G1_034
