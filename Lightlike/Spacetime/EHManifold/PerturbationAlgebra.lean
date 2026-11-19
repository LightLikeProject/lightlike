import Lightlike.Spacetime.EHManifold.Perturbation

/-!
# A symmetric tensor field times a smooth function

`SymBilinField.smulFun χ hχ h` is the field `p ↦ χ(p) h_p` for a smooth function `χ`; its chart components
are `χ` times those of `h` (`SymBilinField.coordComp_smulFun`), and it vanishes where `χ` or `h` does.

Supporting definitions for cutting a perturbation of a metric into pieces with a partition of unity; no
catalogue entry.
-/

open Bundle Manifold Set
open scoped Manifold ContDiff Matrix

noncomputable section

namespace Lightlike

set_option synthInstance.maxHeartbeats 400000

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]

/-- **The field `χ h`** for a smooth function `χ` and a symmetric bilinear field `h`. -/
def SymBilinField.smulFun (χ : M → ℝ) (hχ : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ χ)
    (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) : SymBilinField 𝓘(ℝ, Fin n → ℝ) M where
  h x := χ x • h.h x
  symm x v w := by
    show χ x * h.h x v w = χ x * h.h x w v
    rw [h.symm x v w]
  contMDiff := hχ.smul_section h.contMDiff

@[simp] lemma SymBilinField.smulFun_h (χ : M → ℝ) (hχ : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ χ)
    (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (x : M) : (h.smulFun χ hχ).h x = χ x • h.h x := rfl

/-- The chart components of `χ h` are `χ` times those of `h`. -/
lemma SymBilinField.coordComp_smulFun (χ : M → ℝ) (hχ : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ χ)
    (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (x₀ : M) (y : Fin n → ℝ) :
    (h.smulFun χ hχ).coordComp x₀ y =
      χ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) • h.coordComp x₀ y := by
  ext i j
  rfl

/-- `χ h` vanishes where `χ` vanishes. -/
lemma SymBilinField.smulFun_eq_zero_of_fun (χ : M → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ χ) (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) {x : M}
    (hx : χ x = 0) : (h.smulFun χ hχ).h x = 0 := by
  refine ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => ?_
  show χ x * h.h x v w = 0
  rw [hx, zero_mul]

/-- `χ h` vanishes where `h` vanishes. -/
lemma SymBilinField.smulFun_eq_zero_of_field (χ : M → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ χ) (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) {x : M}
    (hx : h.h x = 0) : (h.smulFun χ hχ).h x = 0 := by
  refine ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => ?_
  have h0 : h.h x v w = 0 := by
    rw [hx]
    rfl
  show χ x * h.h x v w = 0
  rw [h0, mul_zero]

end Lightlike
