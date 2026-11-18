import Lightlike.GR.Kerr

/-!
# Kerr: the horizon, its angular velocity and surface gravity, and the sign of `a`

For `0 < M`, `|a| ≤ M`, the outer horizon is `r₊ = M + √(M² - a²)` (`kerrRplus`), a root of
`Δ = r² - 2Mr + a²` with `r₊² + a² = 2 M r₊` (`kerrΔ_rplus`, `rplus_sq_add`). With
`Ω_H = a/(2 M r₊)` (`kerrOmega`) the Killing field `χ = ∂_t + Ω_H ∂_φ` has vanishing norm on `r = r₊` for
every `θ` (`kerr_chi_null`), where the metric is read off from the Boyer–Lindquist form. The surface gravity,
as the standard value `κ = Δ'(r₊)/(2 (r₊² + a²))`, is `√(M² - a²)/(2 M r₊)` (`kerrKappa_eq`); for `a = 0` the
horizon is `r₊ = 2M`, `Ω_H = 0`, `κ = 1/(4M)` (`kerr_schwarzschild_limit`).

Reversing the sign of `g_{tφ}` alone is the substitution `a ↦ -a` (`kerrMetric_neg`): that metric is again Kerr.

Gap row GE6. Definition of `κ` through `Δ'(r₊)/(2(r₊²+a²))` is the standard closed form, not derived here from
`χ^μ ∇_μ χ^ν = κ χ^ν` (the Boyer–Lindquist chart is singular at the horizon). Compared with Visser, *The Kerr spacetime: A brief
introduction* (arXiv:0706.0622v3): `r₊`, `Ω_H = a/(2 m r₊)` (eq. 112) and the null generator `(1, 0, 0, Ω_H)` (eqs. 113-114, p. 26);
the surface gravity `κ` does not occur in that text and is not source-checked (Wald, ch. 12, Carter 1968: not read).
-/

open Matrix Real

noncomputable section

namespace Lightlike

variable (M a : ℝ)

/-- The outer horizon radius `r₊ = M + √(M² - a²)`. -/
def kerrRplus : ℝ := M + √(M ^ 2 - a ^ 2)

/-- The angular velocity of the horizon `Ω_H = a/(2 M r₊)`. -/
def kerrOmega : ℝ := a / (2 * M * kerrRplus M a)

/-- The surface gravity `κ = Δ'(r₊)/(2 (r₊² + a²))` with `Δ' = 2r - 2M`. -/
def kerrKappa : ℝ := (2 * kerrRplus M a - 2 * M) / (2 * (kerrRplus M a ^ 2 + a ^ 2))

lemma rplus_sq_add (h : a ^ 2 ≤ M ^ 2) : kerrRplus M a ^ 2 + a ^ 2 = 2 * M * kerrRplus M a := by
  have hs : √(M ^ 2 - a ^ 2) ^ 2 = M ^ 2 - a ^ 2 := Real.sq_sqrt (by linarith)
  unfold kerrRplus
  nlinarith [hs]

/-- `r₊` is a root of `Δ`. -/
lemma kerrΔ_rplus (h : a ^ 2 ≤ M ^ 2) : kerrRplus M a ^ 2 - 2 * M * kerrRplus M a + a ^ 2 = 0 := by
  have := rplus_sq_add M a h
  linarith

/-- **Surface gravity.** `κ = √(M² - a²)/(2 M r₊)`. -/
theorem kerrKappa_eq (hM : 0 < M) (h : a ^ 2 ≤ M ^ 2) :
    kerrKappa M a = √(M ^ 2 - a ^ 2) / (2 * M * kerrRplus M a) := by
  have h1 := rplus_sq_add M a h
  unfold kerrKappa
  rw [h1]
  have : 2 * kerrRplus M a - 2 * M = 2 * √(M ^ 2 - a ^ 2) := by unfold kerrRplus; ring
  rw [this]
  have hr : 0 < kerrRplus M a := by
    unfold kerrRplus; have := Real.sqrt_nonneg (M ^ 2 - a ^ 2); linarith
  field_simp

/-- **The Killing field `χ = ∂_t + Ω_H ∂_φ` is null on the horizon**, for every `θ`:
`g_tt + 2 Ω_H g_{tφ} + Ω_H² g_{φφ} = 0` at `r = r₊`. -/
theorem kerr_chi_null (hM : 0 < M) (h : a ^ 2 ≤ M ^ 2) (t : ℝ) :
    let y : Fin 4 → ℝ := ![0, kerrRplus M a, t, 0]
    kerrMetric M a y 0 0 + 2 * kerrOmega M a * kerrMetric M a y 0 3 +
      kerrOmega M a ^ 2 * kerrMetric M a y 3 3 = 0 := by
  intro y
  have hr : 0 < kerrRplus M a := by
    unfold kerrRplus; have := Real.sqrt_nonneg (M ^ 2 - a ^ 2); linarith
  have h1 := rplus_sq_add M a h
  have hS : 0 < kerrRplus M a ^ 2 + a ^ 2 * cos t ^ 2 := by positivity
  have hc := sin_sq_add_cos_sq t
  have hMr : 2 * M * kerrRplus M a ≠ 0 := by positivity
  simp only [kerrMetric, kerrS, kerrOmega, y]
  simp
  field_simp
  set r := kerrRplus M a
  have hc2 : cos t ^ 2 = 1 - sin t ^ 2 := by linarith
  rw [hc2]
  have hM2 : 2 * M * r = r ^ 2 + a ^ 2 := h1.symm
  rw [show (2 : ℝ) ^ 2 * M ^ 2 * r ^ 2 = (2 * M * r) ^ 2 by ring]
  rw [hM2]
  ring

/-- **`a = 0`.** The horizon is `r₊ = 2M`, `Ω_H = 0` and `κ = 1/(4M)`. -/
theorem kerr_schwarzschild_limit (hM : 0 < M) :
    kerrRplus M 0 = 2 * M ∧ kerrOmega M 0 = 0 ∧ kerrKappa M 0 = 1 / (4 * M) := by
  have hr : kerrRplus M 0 = 2 * M := by
    unfold kerrRplus
    rw [show M ^ 2 - (0 : ℝ) ^ 2 = M ^ 2 by ring, Real.sqrt_sq hM.le]; ring
  refine ⟨hr, by simp [kerrOmega], ?_⟩
  unfold kerrKappa
  rw [hr]
  field_simp
  ring

/-- **Reversing the sign of `g_{tφ}` is `a ↦ -a`.** -/
theorem kerrMetric_neg (y : Fin 4 → ℝ) (i j : Fin 4) :
    kerrMetric M (-a) y i j =
      if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then -kerrMetric M a y i j else kerrMetric M a y i j := by
  fin_cases i <;> fin_cases j <;> simp [kerrMetric, kerrS, kerrD] <;> ring

end Lightlike
