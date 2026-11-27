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

/-- `rhoCoth` is continuous along the real axis. -/
lemma continuous_rhoCoth_real : Continuous fun ρ : ℝ => rhoCoth (ρ : ℂ) := by
  have h := differentiableOn_rhoCoth.continuousOn
  exact h.comp_continuous Complex.continuous_ofReal fun ρ => by simp

/-- `ρ coth(πρ) P(ρ)` is integrable when `P` is continuous and decays like `C/(1 + ρ²)²`. -/
lemma integrable_rhoCoth_mul {P : ℝ → ℂ} (hP : Continuous P) {C : ℝ}
    (hb : ∀ x : ℝ, ‖P x‖ ≤ C / (1 + x ^ 2) ^ 2) : Integrable fun ρ : ℝ => rhoCoth (ρ : ℂ) * P ρ := by
  obtain ⟨M, hM0, hM⟩ := exists_norm_rhoCoth_le
  have hC : 0 ≤ C := by
    have := le_trans (norm_nonneg _) (hb 0)
    simpa using this
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (2 * M * C))
    (continuous_rhoCoth_real.mul hP).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  have hpos : 0 < 1 + x ^ 2 := by positivity
  have h1 := hM (x : ℂ) (by simp)
  simp only [Complex.ofReal_re] at h1
  rw [norm_mul]
  calc ‖rhoCoth (x : ℂ)‖ * ‖P x‖ ≤ (M * (1 + |x|)) * (C / (1 + x ^ 2) ^ 2) := by
        gcongr; exact hb x
    _ ≤ (M * (2 * (1 + x ^ 2))) * (C / (1 + x ^ 2) ^ 2) := by gcongr; exact one_add_abs_le x
    _ = 2 * M * C * (1 + x ^ 2)⁻¹ := by field_simp

/-- **The contour identity for the odd density.** For entire `a`, `b` with `‖a(x + iy)‖, ‖b(x + iy)‖ ≤ C/(1 + x²)`
on `|y| ≤ 1`,
`∫ ρ coth(πρ) (a(ρ - i/2) + a(ρ + i/2)) (b(ρ + i/2) + b(ρ - i/2)) dρ`
splits into four terms, each shifted onto the real axis by `±i/2`:
`∫ rhoCoth(x + i/2) a b + ∫ rhoCoth(x - i/2) a b + ∫ rhoCoth(x + i/2) a(x) b(x + i)
 + ∫ rhoCoth(x - i/2) a(x) b(x - i)`. -/
theorem odd_density_contour {a b : ℂ → ℂ} (ha : Differentiable ℂ a) (hb : Differentiable ℂ b) {C : ℝ}
    (hA : ∀ x y : ℝ, |y| ≤ 1 → ‖a ((x : ℂ) + (y : ℂ) * I)‖ ≤ C / (1 + x ^ 2))
    (hB : ∀ x y : ℝ, |y| ≤ 1 → ‖b ((x : ℂ) + (y : ℂ) * I)‖ ≤ C / (1 + x ^ 2)) :
    ∫ ρ : ℝ, rhoCoth (ρ : ℂ) * ((a ((ρ : ℂ) - I / 2) + a ((ρ : ℂ) + I / 2)) *
        (b ((ρ : ℂ) + I / 2) + b ((ρ : ℂ) - I / 2))) =
      (∫ x : ℝ, rhoCoth ((x : ℂ) + I / 2) * (a x * b x)) +
      (∫ x : ℝ, rhoCoth ((x : ℂ) - I / 2) * (a x * b x)) +
      (∫ x : ℝ, rhoCoth ((x : ℂ) + I / 2) * (a x * b (x + I))) +
      (∫ x : ℝ, rhoCoth ((x : ℂ) - I / 2) * (a x * b (x - I))) := by
  have hC : 0 ≤ C := by
    have := le_trans (norm_nonneg _) (hA 0 0 (by simp))
    simpa using this
  -- the product bound `C²/(1+x²)²` on each strip
  have hprod : ∀ (u v : ℂ → ℂ) (y₁ y₂ : ℝ) (x y : ℝ),
      (∀ x y : ℝ, |y| ≤ 1 → ‖u ((x : ℂ) + (y : ℂ) * I)‖ ≤ C / (1 + x ^ 2)) →
      (∀ x y : ℝ, |y| ≤ 1 → ‖v ((x : ℂ) + (y : ℂ) * I)‖ ≤ C / (1 + x ^ 2)) → |y + y₁| ≤ 1 → |y + y₂| ≤ 1 →
      ‖u ((x : ℂ) + (y : ℂ) * I + (y₁ : ℂ) * I) * v ((x : ℂ) + (y : ℂ) * I + (y₂ : ℂ) * I)‖ ≤
        C ^ 2 / (1 + x ^ 2) ^ 2 := by
    intro u v y₁ y₂ x y hu hv h1 h2
    rw [norm_mul]
    have e1 : (x : ℂ) + (y : ℂ) * I + (y₁ : ℂ) * I = (x : ℂ) + ((y + y₁ : ℝ) : ℂ) * I := by push_cast; ring
    have e2 : (x : ℂ) + (y : ℂ) * I + (y₂ : ℂ) * I = (x : ℂ) + ((y + y₂ : ℝ) : ℂ) * I := by push_cast; ring
    rw [e1, e2]
    calc ‖u ((x : ℂ) + ((y + y₁ : ℝ) : ℂ) * I)‖ * ‖v ((x : ℂ) + ((y + y₂ : ℝ) : ℂ) * I)‖
        ≤ (C / (1 + x ^ 2)) * (C / (1 + x ^ 2)) := by
          gcongr
          · exact hu x _ h1
          · exact hv x _ h2
      _ = C ^ 2 / (1 + x ^ 2) ^ 2 := by field_simp
  have hcont : ∀ u : ℂ → ℂ, Differentiable ℂ u → Continuous u := fun u hu => hu.continuous
  -- the four terms on the original line, each shifted
  have hint : ∀ (P : ℂ → ℂ) (σ : ℝ), Differentiable ℂ P →
      (∀ x : ℝ, ‖P ((x : ℂ) + (σ : ℂ) * I)‖ ≤ C ^ 2 / (1 + x ^ 2) ^ 2) →
      Integrable fun ρ : ℝ => rhoCoth (ρ : ℂ) * P ((ρ : ℂ) + (σ : ℂ) * I) := by
    intro P σ hP hbd
    exact integrable_rhoCoth_mul (P := fun ρ : ℝ => P ((ρ : ℂ) + (σ : ℂ) * I))
      ((hcont P hP).comp (by fun_prop)) hbd
  have e3 : ∀ ρ : ℝ, (ρ : ℂ) - I / 2 = (ρ : ℂ) + (((-(1 / 2) : ℝ) : ℂ)) * I := fun ρ => by push_cast; ring
  have e4 : ∀ ρ : ℝ, (ρ : ℂ) + I / 2 = (ρ : ℂ) + (((1 / 2 : ℝ) : ℂ)) * I := fun ρ => by push_cast; ring
  -- T3: P = a b, shift by -1/2
  have T3 : ∫ ρ : ℝ, rhoCoth (ρ : ℂ) * (a ((ρ : ℂ) - I / 2) * b ((ρ : ℂ) - I / 2)) =
      ∫ x : ℝ, rhoCoth ((x : ℂ) + I / 2) * (a x * b x) := by
    have := integral_rhoCoth_shift_neg (P := fun w => a w * b w) (ha.mul hb) (C := C ^ 2)
      (fun x y h1 h2 => by
        have := hprod a b 0 0 x y hA hB (by rw [abs_le]; constructor <;> linarith)
          (by rw [abs_le]; constructor <;> linarith)
        simpa using this)
    exact this
  have T4 : ∫ ρ : ℝ, rhoCoth (ρ : ℂ) * (a ((ρ : ℂ) + I / 2) * b ((ρ : ℂ) + I / 2)) =
      ∫ x : ℝ, rhoCoth ((x : ℂ) - I / 2) * (a x * b x) := by
    have := integral_rhoCoth_shift_pos (P := fun w => a w * b w) (ha.mul hb) (C := C ^ 2)
      (fun x y h1 h2 => by
        have := hprod a b 0 0 x y hA hB (by rw [abs_le]; constructor <;> linarith)
          (by rw [abs_le]; constructor <;> linarith)
        simpa using this)
    exact this
  have T1 : ∫ ρ : ℝ, rhoCoth (ρ : ℂ) * (a ((ρ : ℂ) - I / 2) * b ((ρ : ℂ) + I / 2)) =
      ∫ x : ℝ, rhoCoth ((x : ℂ) + I / 2) * (a x * b (x + I)) := by
    have := integral_rhoCoth_shift_neg (P := fun w => a w * b (w + I)) (ha.mul (hb.comp (by fun_prop)))
      (C := C ^ 2)
      (fun x y h1 h2 => by
        have := hprod a b 0 1 x y hA hB (by rw [abs_le]; constructor <;> linarith)
          (by rw [abs_le]; constructor <;> linarith)
        simpa using this)
    have e : ∀ ρ : ℝ, b ((ρ : ℂ) - I / 2 + I) = b ((ρ : ℂ) + I / 2) := fun ρ => by congr 1; ring
    simp only [e] at this
    exact this
  have T2 : ∫ ρ : ℝ, rhoCoth (ρ : ℂ) * (a ((ρ : ℂ) + I / 2) * b ((ρ : ℂ) - I / 2)) =
      ∫ x : ℝ, rhoCoth ((x : ℂ) - I / 2) * (a x * b (x - I)) := by
    have := integral_rhoCoth_shift_pos (P := fun w => a w * b (w - I)) (ha.mul (hb.comp (by fun_prop)))
      (C := C ^ 2)
      (fun x y h1 h2 => by
        have := hprod a b 0 (-1) x y hA hB (by rw [abs_le]; constructor <;> linarith)
          (by rw [abs_le]; constructor <;> linarith)
        simpa [sub_eq_add_neg] using this)
    have e : ∀ ρ : ℝ, b ((ρ : ℂ) + I / 2 - I) = b ((ρ : ℂ) - I / 2) := fun ρ => by congr 1; ring
    simp only [e] at this
    exact this
  -- integrability of the four original terms
  have I3 : Integrable fun ρ : ℝ => rhoCoth (ρ : ℂ) * (a ((ρ : ℂ) - I / 2) * b ((ρ : ℂ) - I / 2)) := by
    have := hint (fun w => a w * b w) (-(1 / 2)) (ha.mul hb) (fun x => by
      have := hprod a b 0 0 x (-(1 / 2)) hA hB (by rw [abs_le]; constructor <;> linarith)
        (by rw [abs_le]; constructor <;> linarith)
      simpa using this)
    simpa [e3] using this
  have I4 : Integrable fun ρ : ℝ => rhoCoth (ρ : ℂ) * (a ((ρ : ℂ) + I / 2) * b ((ρ : ℂ) + I / 2)) := by
    have := hint (fun w => a w * b w) (1 / 2) (ha.mul hb) (fun x => by
      have := hprod a b 0 0 x (1 / 2) hA hB (by rw [abs_le]; constructor <;> linarith)
        (by rw [abs_le]; constructor <;> linarith)
      simpa using this)
    simpa [e4] using this
  have I1 : Integrable fun ρ : ℝ => rhoCoth (ρ : ℂ) * (a ((ρ : ℂ) - I / 2) * b ((ρ : ℂ) + I / 2)) := by
    have := hint (fun w => a w * b (w + I)) (-(1 / 2)) (ha.mul (hb.comp (by fun_prop))) (fun x => by
      have := hprod a b 0 1 x (-(1 / 2)) hA hB (by rw [abs_le]; constructor <;> linarith)
        (by rw [abs_le]; constructor <;> linarith)
      simpa using this)
    refine this.congr (Eventually.of_forall fun ρ => ?_)
    show rhoCoth (ρ : ℂ) * (a ((ρ : ℂ) + ((-(1 / 2) : ℝ) : ℂ) * I) *
        b ((ρ : ℂ) + ((-(1 / 2) : ℝ) : ℂ) * I + I)) = _
    rw [show (ρ : ℂ) + ((-(1 / 2) : ℝ) : ℂ) * I = ρ - I / 2 by push_cast; ring,
      show (ρ : ℂ) - I / 2 + I = ρ + I / 2 by ring]
  have I2 : Integrable fun ρ : ℝ => rhoCoth (ρ : ℂ) * (a ((ρ : ℂ) + I / 2) * b ((ρ : ℂ) - I / 2)) := by
    have := hint (fun w => a w * b (w - I)) (1 / 2) (ha.mul (hb.comp (by fun_prop))) (fun x => by
      have := hprod a b 0 (-1) x (1 / 2) hA hB (by rw [abs_le]; constructor <;> linarith)
        (by rw [abs_le]; constructor <;> linarith)
      simpa [sub_eq_add_neg] using this)
    refine this.congr (Eventually.of_forall fun ρ => ?_)
    show rhoCoth (ρ : ℂ) * (a ((ρ : ℂ) + ((1 / 2 : ℝ) : ℂ) * I) *
        b ((ρ : ℂ) + ((1 / 2 : ℝ) : ℂ) * I - I)) = _
    rw [show (ρ : ℂ) + ((1 / 2 : ℝ) : ℂ) * I = ρ + I / 2 by push_cast; ring,
      show (ρ : ℂ) + I / 2 - I = ρ - I / 2 by ring]
  -- expand and conclude
  have hexp : ∀ ρ : ℝ, rhoCoth (ρ : ℂ) * ((a ((ρ : ℂ) - I / 2) + a ((ρ : ℂ) + I / 2)) *
      (b ((ρ : ℂ) + I / 2) + b ((ρ : ℂ) - I / 2))) =
      rhoCoth (ρ : ℂ) * (a ((ρ : ℂ) - I / 2) * b ((ρ : ℂ) - I / 2)) +
      rhoCoth (ρ : ℂ) * (a ((ρ : ℂ) + I / 2) * b ((ρ : ℂ) + I / 2)) +
      rhoCoth (ρ : ℂ) * (a ((ρ : ℂ) - I / 2) * b ((ρ : ℂ) + I / 2)) +
      rhoCoth (ρ : ℂ) * (a ((ρ : ℂ) + I / 2) * b ((ρ : ℂ) - I / 2)) := fun ρ => by ring
  simp_rw [hexp]
  have h3 := integral_add I3 I4
  have h31 := integral_add (I3.add I4) I1
  have h312 := integral_add ((I3.add I4).add I1) I2
  simp only [Pi.add_apply] at h3 h31 h312
  rw [h312, h31, h3, T3, T4, T1, T2]

end Lightlike.Lorentz.SL2ROddPlancherel
