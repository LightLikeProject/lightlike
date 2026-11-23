import Lightlike.Rows.G1_031.Einstein

/-!
# Tensor modes obey `h'' + 2𝓗 h' - ∇²h = 0` (row G1-031)

Conformal time, flat slicing.  The tensor mode is the plus polarisation
`h_{μν} = a² f diag(0, 1, -1, 0)` with `f` independent of `x¹, x²`.  The background satisfies the
spatial Einstein equation `fieldEq … (confMetric a) 1 1 = 0`.  Then the linearized field equation
(derivative of `fieldEq` along `confMetric a + ε h` at `ε = 0`) vanishes in all components iff
`f'' + 2𝓗 f' - ∇² f = 0`.
-/

open Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike.Rows.G1_031

open Lightlike Lightlike.Cosmology

variable {a : ℝ → ℝ} {f : (Fin 4 → ℝ) → ℝ} {x : Fin 4 → ℝ}

/-- The spatial background equation: `fieldEq` of the background in the `(1,1)` component is
`-2𝓗' - 𝓗² + a² (Λ - κ p)`. -/
theorem fieldEq_conf_11 (hfa : ContDiff ℝ ∞ a) (hne : ∀ t, a t ≠ 0) (κ Λ ρ p : ℝ) :
    fieldEq κ Λ ρ p a (confMetric a) 1 1 x =
      -2 * dH a 0 x - Hf a x ^ 2 + a (x 0) ^ 2 * (Λ - κ * p) := by
  have hpos := hne (x 0)
  unfold fieldEq fluidT einsteinTensor
  rw [ricci_conf hfa hne, scalar_conf hfa hne]
  simp [dl, confMetric_apply, sgn]
  field_simp
  ring

/-- **Linearized Einstein equation for tensor modes**: if the background satisfies the spatial
Einstein equation at `x`, the first variation of the field equation is
`dl μ ν cp μ · ½ (f'' + 2𝓗 f' - f_{33})`. -/
theorem hasDerivAt_fieldEq_tPert_of_background (hfa : ContDiff ℝ ∞ a) (hne : ∀ t, a t ≠ 0)
    (hf : ContDiff ℝ ∞ f) (h1 : pd 1 f = fun _ => 0) (h2 : pd 2 f = fun _ => 0)
    (κ Λ ρ p : ℝ) (hbg : fieldEq κ Λ ρ p a (confMetric a) 1 1 x = 0) (μ ν : Fin 4) :
    HasDerivAt (fun t : ℝ => fieldEq κ Λ ρ p a (fun z => confMetric a z + t • tPert a f z) μ ν x)
      (dl μ ν * cp μ * ((1 / 2) * (pd 0 (pd 0 f) x + 2 * Hf a x * pd 0 f x - pd 3 (pd 3 f) x))) 0 := by
  have h := hasDerivAt_fieldEq_tPert hfa hne hf h1 h2 κ Λ ρ p μ ν (x := x)
  rw [fieldEq_conf_11 hfa hne] at hbg
  have e : (-2 * dH a 0 x - Hf a x ^ 2 + a (x 0) ^ 2 * (Λ - κ * p)) * f x = 0 := by
    rw [hbg, zero_mul]
  convert h using 1
  rw [e, add_zero]

/-- **Tensor modes obey `h'' + 2𝓗 h' - ∇²h = 0`.**  With the spatial background equation at `x`, the
linearized field equation holds in every component iff
`f_{00} + 2𝓗 f_0 - (f_{11} + f_{22} + f_{33}) = 0` at `x`. -/
theorem tensor_mode_equation (hfa : ContDiff ℝ ∞ a) (hne : ∀ t, a t ≠ 0)
    (hf : ContDiff ℝ ∞ f) (h1 : pd 1 f = fun _ => 0) (h2 : pd 2 f = fun _ => 0)
    (κ Λ ρ p : ℝ) (hbg : fieldEq κ Λ ρ p a (confMetric a) 1 1 x = 0) :
    (∀ μ ν : Fin 4, deriv
        (fun t : ℝ => fieldEq κ Λ ρ p a (fun z => confMetric a z + t • tPert a f z) μ ν x) 0 = 0) ↔
      pd 0 (pd 0 f) x + 2 * Hf a x * pd 0 f x -
        (pd 1 (pd 1 f) x + pd 2 (pd 2 f) x + pd 3 (pd 3 f) x) = 0 := by
  have e1 : pd 1 (pd 1 f) x = 0 := by rw [h1]; exact pd_const _ _ _
  have e2 : pd 2 (pd 2 f) x = 0 := by rw [h2]; exact pd_const _ _ _
  rw [e1, e2, zero_add, zero_add]
  simp only [(hasDerivAt_fieldEq_tPert_of_background hfa hne hf h1 h2 κ Λ ρ p hbg _ _).deriv]
  constructor
  · intro h
    have := h 1 1
    simpa [dl, cp] using this
  · intro h μ ν
    have : pd 0 (pd 0 f) x + 2 * Hf a x * pd 0 f x - pd 3 (pd 3 f) x = 0 := h
    rw [this]; ring

end Lightlike.Rows.G1_031
