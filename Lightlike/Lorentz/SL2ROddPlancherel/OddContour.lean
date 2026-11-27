import Mathlib
import Lightlike.Lorentz.SL2ROddPlancherel.RhoCoth
import Lightlike.Lorentz.SL2ROddPlancherel.StripShift

/-!
# Shifting the odd Plancherel density by `±i/2`

For an entire function `P` with `‖P(x + iy)‖ ≤ C/(1 + x²)²` on the strip between `0` and `σ`, `σ = ±1/2`,

  `∫ ρ coth(πρ) · P(ρ + σ i) dρ = ∫ rhoCoth(x - σ i) · P(x) dx`   (`integral_rhoCoth_shift_pos`, `_neg`),

because `z ↦ rhoCoth(z - σ i) P(z)` is holomorphic on the closed strip (`rhoCoth` is the holomorphic extension
of `z coth(πz)`; the pole of `coth` at the origin is removable) and `rhoCoth(x - σ i) = (x - σ i) tanh(πx)`.
This is the contour step of the odd Plancherel identity (`docs/notes/sl2r-odd-plancherel-route.md`).
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real

noncomputable section

namespace Lightlike.Lorentz.SL2ROddPlancherel

/-- `1 + |x| ≤ 2 (1 + x²)`. -/
lemma one_add_abs_le (x : ℝ) : 1 + |x| ≤ 2 * (1 + x ^ 2) := by
  have : |x| ≤ 1 + x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x, sq_nonneg (|x| - 1 / 2)]
  nlinarith [sq_nonneg x]

/-- **The core shift**: `f(z) = rhoCoth(z - σ i) P(z)` has equal integrals along `Im = a` and `Im = b` when every
`y ∈ [a, b]` has `|y - σ| ≤ 1/2` and `P` decays like `C/(1 + x²)²` on the strip. -/
theorem integral_rhoCoth_shift_core {P : ℂ → ℂ} (hP : Differentiable ℂ P) {a b σ C : ℝ} (hab : a ≤ b)
    (hyσ : ∀ y : ℝ, a ≤ y → y ≤ b → |y - σ| ≤ 1 / 2)
    (hb : ∀ x y : ℝ, a ≤ y → y ≤ b → ‖P ((x : ℂ) + (y : ℂ) * I)‖ ≤ C / (1 + x ^ 2) ^ 2) :
    ∫ x : ℝ, rhoCoth (((x : ℂ) + (b : ℂ) * I) - (σ : ℂ) * I) * P ((x : ℂ) + (b : ℂ) * I) =
      ∫ x : ℝ, rhoCoth (((x : ℂ) + (a : ℂ) * I) - (σ : ℂ) * I) * P ((x : ℂ) + (a : ℂ) * I) := by
  obtain ⟨M, hM0, hM⟩ := exists_norm_rhoCoth_le
  set f : ℂ → ℂ := fun z => rhoCoth (z - (σ : ℂ) * I) * P z with hf
  have hbound : ∀ x y : ℝ, a ≤ y → y ≤ b →
      ‖f ((x : ℂ) + (y : ℂ) * I)‖ ≤ (2 * M * C) / (1 + x ^ 2) := by
    intro x y hy1 hy2
    have him : |(((x : ℂ) + (y : ℂ) * I) - (σ : ℂ) * I).im| ≤ 1 / 2 := by
      simpa using hyσ y hy1 hy2
    have h1 := hM _ him
    have hre : (((x : ℂ) + (y : ℂ) * I) - (σ : ℂ) * I).re = x := by simp
    rw [hre] at h1
    have h2 := hb x y hy1 hy2
    have hC : 0 ≤ C := by
      have := le_trans (norm_nonneg _) (hb 0 y hy1 hy2)
      simpa using this
    have hpos : 0 < 1 + x ^ 2 := by positivity
    simp only [hf, norm_mul]
    calc ‖rhoCoth (((x : ℂ) + (y : ℂ) * I) - (σ : ℂ) * I)‖ * ‖P ((x : ℂ) + (y : ℂ) * I)‖
        ≤ (M * (1 + |x|)) * (C / (1 + x ^ 2) ^ 2) := by gcongr
      _ ≤ (M * (2 * (1 + x ^ 2))) * (C / (1 + x ^ 2) ^ 2) := by
          gcongr; exact one_add_abs_le x
      _ = (2 * M * C) / (1 + x ^ 2) := by field_simp
  have hd : DifferentiableOn ℂ f {z : ℂ | a ≤ z.im ∧ z.im ≤ b} := by
    refine DifferentiableOn.mul ?_ hP.differentiableOn
    refine differentiableOn_rhoCoth.comp (by fun_prop) ?_
    intro z hz
    have h := hyσ z.im hz.1 hz.2
    show |(z - (σ : ℂ) * I).im| < 1
    have : (z - (σ : ℂ) * I).im = z.im - σ := by simp
    rw [this]
    exact lt_of_le_of_lt h (by norm_num)
  exact integral_shift_strip (f := f) hab hd hbound

/-- **Shift by `+i/2`**: `∫ ρ coth(πρ) P(ρ + i/2) dρ = ∫ rhoCoth(x - i/2) P(x) dx`. -/
theorem integral_rhoCoth_shift_pos {P : ℂ → ℂ} (hP : Differentiable ℂ P) {C : ℝ}
    (hb : ∀ x y : ℝ, 0 ≤ y → y ≤ 1 / 2 → ‖P ((x : ℂ) + (y : ℂ) * I)‖ ≤ C / (1 + x ^ 2) ^ 2) :
    ∫ ρ : ℝ, rhoCoth (ρ : ℂ) * P ((ρ : ℂ) + I / 2) =
      ∫ x : ℝ, rhoCoth ((x : ℂ) - I / 2) * P (x : ℂ) := by
  have h := integral_rhoCoth_shift_core hP (a := 0) (b := 1 / 2) (σ := 1 / 2) (C := C) (by norm_num)
    (fun y h1 h2 => by rw [abs_le]; constructor <;> linarith) hb
  have hl : (fun x : ℝ => rhoCoth (((x : ℂ) + ((1 / 2 : ℝ) : ℂ) * I) - ((1 / 2 : ℝ) : ℂ) * I) *
      P ((x : ℂ) + ((1 / 2 : ℝ) : ℂ) * I)) = fun ρ : ℝ => rhoCoth (ρ : ℂ) * P ((ρ : ℂ) + I / 2) := by
    funext x
    rw [show ((x : ℂ) + ((1 / 2 : ℝ) : ℂ) * I) - ((1 / 2 : ℝ) : ℂ) * I = x by ring,
      show (x : ℂ) + ((1 / 2 : ℝ) : ℂ) * I = x + I / 2 by push_cast; ring]
  have hr : (fun x : ℝ => rhoCoth (((x : ℂ) + ((0 : ℝ) : ℂ) * I) - ((1 / 2 : ℝ) : ℂ) * I) *
      P ((x : ℂ) + ((0 : ℝ) : ℂ) * I)) = fun x : ℝ => rhoCoth ((x : ℂ) - I / 2) * P (x : ℂ) := by
    funext x
    rw [show ((x : ℂ) + ((0 : ℝ) : ℂ) * I) - ((1 / 2 : ℝ) : ℂ) * I = x - I / 2 by push_cast; ring,
      show (x : ℂ) + ((0 : ℝ) : ℂ) * I = x by push_cast; ring]
  rw [hl, hr] at h
  exact h

/-- **Shift by `-i/2`**: `∫ ρ coth(πρ) P(ρ - i/2) dρ = ∫ rhoCoth(x + i/2) P(x) dx`. -/
theorem integral_rhoCoth_shift_neg {P : ℂ → ℂ} (hP : Differentiable ℂ P) {C : ℝ}
    (hb : ∀ x y : ℝ, -(1 / 2) ≤ y → y ≤ 0 → ‖P ((x : ℂ) + (y : ℂ) * I)‖ ≤ C / (1 + x ^ 2) ^ 2) :
    ∫ ρ : ℝ, rhoCoth (ρ : ℂ) * P ((ρ : ℂ) - I / 2) =
      ∫ x : ℝ, rhoCoth ((x : ℂ) + I / 2) * P (x : ℂ) := by
  have h := integral_rhoCoth_shift_core hP (a := -(1 / 2)) (b := 0) (σ := -(1 / 2)) (C := C)
    (by norm_num) (fun y h1 h2 => by rw [abs_le]; constructor <;> linarith) hb
  have hl : (fun x : ℝ => rhoCoth (((x : ℂ) + ((-(1 / 2) : ℝ) : ℂ) * I) - ((-(1 / 2) : ℝ) : ℂ) * I) *
      P ((x : ℂ) + ((-(1 / 2) : ℝ) : ℂ) * I)) = fun ρ : ℝ => rhoCoth (ρ : ℂ) * P ((ρ : ℂ) - I / 2) := by
    funext x
    rw [show ((x : ℂ) + ((-(1 / 2) : ℝ) : ℂ) * I) - ((-(1 / 2) : ℝ) : ℂ) * I = x by ring,
      show (x : ℂ) + ((-(1 / 2) : ℝ) : ℂ) * I = x - I / 2 by push_cast; ring]
  have hr : (fun x : ℝ => rhoCoth (((x : ℂ) + ((0 : ℝ) : ℂ) * I) - ((-(1 / 2) : ℝ) : ℂ) * I) *
      P ((x : ℂ) + ((0 : ℝ) : ℂ) * I)) = fun x : ℝ => rhoCoth ((x : ℂ) + I / 2) * P (x : ℂ) := by
    funext x
    rw [show ((x : ℂ) + ((0 : ℝ) : ℂ) * I) - ((-(1 / 2) : ℝ) : ℂ) * I = x + I / 2 by push_cast; ring,
      show (x : ℂ) + ((0 : ℝ) : ℂ) * I = x by push_cast; ring]
  rw [hl, hr] at h
  exact h.symm

end Lightlike.Lorentz.SL2ROddPlancherel
