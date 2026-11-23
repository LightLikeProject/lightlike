import Lightlike.GR.AdSConformal
import Lightlike.GR.AdSInversion

/-!
# The conformal boundary of global anti-de Sitter space and the action of its isometries on it

In the coordinates `(t, ρ, θ, φ)` of `AdSConformal.lean` (`r = tan ρ`) the conformal boundary of global anti-de Sitter space
is the timelike hypersurface `ρ = π/2` (`adsBoundary`), a copy of `ℝ × S²`; the compactified metric `adsCompact`
restricts there to `-dt² + dθ² + sin²θ dφ²` (`adsCompact_boundary`), the metric `adsBdyMetric` on the coordinates
`(t, θ, φ)` of the boundary. The conformal class of this metric, not the metric itself, is canonical: the defining
function `cos ρ` of the boundary is fixed only up to a positive factor.

The isometries of global anti-de Sitter space that are manifest in these coordinates, the time translation
`t ↦ t + a` and the rotation `φ ↦ φ + c`, preserve `adsGlobal` (`adsGlobal_timeShift`, `adsGlobal_rotate`) and the
compactified metric (`adsCompact_timeShift`, `adsCompact_rotate`) and act on the boundary by isometries, a fortiori
conformal transformations, of `adsBdyMetric` (`adsBdyMetric_timeShift`, `adsBdyMetric_rotate`); they preserve the
boundary `ρ = π/2` (`timeShift_mem_adsBoundary`, `rotate_mem_adsBoundary`).
The action of the dilations, translations and special conformal transformations of the Poincaré patch on its boundary
is in `AdSConformal.lean` and `AdSInversion.lean` (`dilation_conformal_boundary`, `inversion_conformal_boundary`,
`specialConformal3_conformal`).

Gap row GE7 (the conformal boundary of anti-de Sitter space). Sources read: D. Harlow, *Jerusalem Lectures on Black
Holes and Quantum Information*, arXiv:1409.1231, section 6.1, eqs. (6.4)-(6.6); Aharony-Gubser-Maldacena-Ooguri-Oz,
arXiv:hep-th/9905111, section 2 (global AdS, its conformal map to one half of the Einstein static universe).
-/

open Matrix Real

noncomputable section

namespace Lightlike

/-- The conformal boundary of global anti-de Sitter space in the coordinates `(t, ρ, θ, φ)`: `ρ = π/2`. -/
def adsBoundary : Set (Fin 4 → ℝ) := {p | p 1 = π / 2}

/-- The boundary metric `-dt² + dθ² + sin²θ dφ²` of `ℝ × S²` in the coordinates `(t, θ, φ)`. -/
def adsBdyMetric (y : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ := diagonal ![-1, 1, sin (y 1) ^ 2]

/-- **The compactified metric restricted to the boundary** `ρ = π/2`: in the coordinates `(t, ρ, θ, φ)` it is
`-dt² + dρ² + dθ² + sin²θ dφ²`, whose `(t, θ, φ)` block is `adsBdyMetric`. -/
theorem adsCompact_boundary {y : Fin 4 → ℝ} (hy : y ∈ adsBoundary) :
    adsCompact y = diagonal ![-1, 1, 1, sin (y 2) ^ 2] ∧
      ∀ i j : Fin 3, adsBdyMetric ![y 0, y 2, y 3] i j =
        adsCompact y (![0, 2, 3] i) (![0, 2, 3] j) := by
  have h : y 1 = π / 2 := hy
  refine ⟨by simp [adsCompact, h], ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [adsBdyMetric, adsCompact, h]

/-- The time translation `t ↦ t + a`. -/
def adsTimeShift (a : ℝ) (y : Fin 4 → ℝ) : Fin 4 → ℝ := y + Pi.single 0 a

/-- The rotation `φ ↦ φ + c` of the sphere. -/
def adsRotate (c : ℝ) (y : Fin 4 → ℝ) : Fin 4 → ℝ := y + Pi.single 3 c

/-- **The time translation is an isometry of global anti-de Sitter space.** -/
theorem adsGlobal_timeShift (a : ℝ) (y : Fin 4 → ℝ) :
    pullback adsGlobal (adsTimeShift a) y = adsGlobal y := by
  have : adsTimeShift a = fun z => z + Pi.single 0 a := rfl
  rw [this, pullback_eq_mul, jac_translation]
  simp [adsGlobal]

/-- **The rotation `φ ↦ φ + c` is an isometry of global anti-de Sitter space.** -/
theorem adsGlobal_rotate (c : ℝ) (y : Fin 4 → ℝ) :
    pullback adsGlobal (adsRotate c) y = adsGlobal y := by
  have : adsRotate c = fun z => z + Pi.single 3 c := rfl
  rw [this, pullback_eq_mul, jac_translation]
  simp [adsGlobal]

/-- The time translation is an isometry of the compactified metric. -/
theorem adsCompact_timeShift (a : ℝ) (y : Fin 4 → ℝ) :
    pullback adsCompact (adsTimeShift a) y = adsCompact y := by
  have : adsTimeShift a = fun z => z + Pi.single 0 a := rfl
  rw [this, pullback_eq_mul, jac_translation]
  simp [adsCompact]

/-- The rotation is an isometry of the compactified metric. -/
theorem adsCompact_rotate (c : ℝ) (y : Fin 4 → ℝ) :
    pullback adsCompact (adsRotate c) y = adsCompact y := by
  have : adsRotate c = fun z => z + Pi.single 3 c := rfl
  rw [this, pullback_eq_mul, jac_translation]
  simp [adsCompact]

/-- The time translation preserves the boundary `ρ = π/2`. -/
theorem timeShift_mem_adsBoundary {a : ℝ} {y : Fin 4 → ℝ} (hy : y ∈ adsBoundary) :
    adsTimeShift a y ∈ adsBoundary := by
  simpa [adsBoundary, adsTimeShift] using hy

/-- The rotation preserves the boundary `ρ = π/2`. -/
theorem rotate_mem_adsBoundary {c : ℝ} {y : Fin 4 → ℝ} (hy : y ∈ adsBoundary) :
    adsRotate c y ∈ adsBoundary := by
  simpa [adsBoundary, adsRotate] using hy

/-- **The time translation acts on the boundary `ℝ × S²` by an isometry** (conformal factor `1`). -/
theorem adsBdyMetric_timeShift (a : ℝ) (y : Fin 3 → ℝ) :
    pullback adsBdyMetric (fun z => z + Pi.single 0 a) y = (1 : ℝ) • adsBdyMetric y := by
  rw [pullback_eq_mul, jac_translation]
  simp [adsBdyMetric]

/-- **The rotation acts on the boundary `ℝ × S²` by an isometry** (conformal factor `1`). -/
theorem adsBdyMetric_rotate (c : ℝ) (y : Fin 3 → ℝ) :
    pullback adsBdyMetric (fun z => z + Pi.single 2 c) y = (1 : ℝ) • adsBdyMetric y := by
  rw [pullback_eq_mul, jac_translation]
  simp [adsBdyMetric]

end Lightlike
