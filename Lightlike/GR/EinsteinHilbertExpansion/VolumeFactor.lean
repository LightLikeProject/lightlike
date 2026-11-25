import Mathlib
import Lightlike.GR.EinsteinHilbertExpansion.MetricExpansion

/-!
# The volume factor `√(-g)` to second order in `κ`

Row G3-255.  With `g = η + κ h` and `A = η⁻¹ h`, `-det g = det (1 + κ A)` (for `det η = -1`), and
`√(-g) = 1 + κ/2 · tr A + κ² (tr(A)²/8 - tr(A²)/4) + O(κ³)`, i.e.
`√(-g) = 1 + κ/2 h + κ² (h²/8 - h_{μν} h^{μν}/4) + O(κ³)`.  This is the origin of the graviton
cubic and quartic vertices.  We avoid Taylor series for the square root: we exhibit the polynomial
`volOrder2` and prove that its square agrees with `det (1 + ε A)` through order `ε²`, with an explicit
remainder starting at `ε³`.

* `volOrder2`: the second-order volume factor.
* `volOrder2_sq`: `volOrder2² = 1 + ε t₁ + ε² (t₁² - t₂)/2 + ε³ t₁ b + ε⁴ b²`, `b = t₁²/8 - t₂/4`.
* `det_one_add_smul_sub_volOrder2_sq`: `det (1 + ε A) - volOrder2² = ε³ · (…)` on `4 × 4` matrices.
-/

open Matrix

namespace Lightlike.Rows.G3_255

/-- The second-order expansion `1 + ε t₁/2 + ε² (t₁²/8 - t₂/4)` of `√(det (1 + ε A))`, where
`t₁ = tr A` and `t₂ = tr A²`. -/
noncomputable def volOrder2 (ε t₁ t₂ : ℝ) : ℝ := 1 + ε * t₁ / 2 + ε ^ 2 * (t₁ ^ 2 / 8 - t₂ / 4)

/-- The square of `volOrder2` is the determinant polynomial through order `ε²`, with explicit
higher-order terms. -/
theorem volOrder2_sq (ε t₁ t₂ : ℝ) :
    volOrder2 ε t₁ t₂ ^ 2 =
      1 + ε * t₁ + ε ^ 2 * ((t₁ ^ 2 - t₂) / 2)
        + ε ^ 3 * (t₁ * (t₁ ^ 2 / 8 - t₂ / 4)) + ε ^ 4 * (t₁ ^ 2 / 8 - t₂ / 4) ^ 2 := by
  unfold volOrder2
  ring

/-- **The determinant `det (1 + ε A)` agrees with the square of `volOrder2` through order `ε²`**:
the difference is `ε³` times an explicit polynomial in `ε` and the traces. -/
theorem det_one_add_smul_sub_volOrder2_sq (ε : ℝ) (A : Matrix (Fin 4) (Fin 4) ℝ) :
    (1 + ε • A).det - volOrder2 ε A.trace (A * A).trace ^ 2 =
      ε ^ 3 * (((A.trace ^ 3 - 3 * A.trace * (A * A).trace + 2 * (A * A * A).trace) / 6)
          - A.trace * (A.trace ^ 2 / 8 - (A * A).trace / 4)
          + ε * (A.det - (A.trace ^ 2 / 8 - (A * A).trace / 4) ^ 2)) := by
  rw [det_one_add_smul_fin4, volOrder2_sq]
  ring

/-- The first-order truncation: `volOrder2` at `ε = 0` is `1`. -/
@[simp] theorem volOrder2_zero (t₁ t₂ : ℝ) : volOrder2 0 t₁ t₂ = 1 := by
  simp [volOrder2]

end Lightlike.Rows.G3_255
