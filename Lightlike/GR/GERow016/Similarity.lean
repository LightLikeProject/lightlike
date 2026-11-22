import Lightlike.GR.ConformalPoincare

/-!
# Similarities (Poincaré × dilations) act conformally on the compactified Minkowski space

Pass-4 extension of gap row GE7. `conformal_of_linear_conformal`: an affine map `x ↦ Λ x + a` with
`Λᵀ η Λ = σ η` (a Lorentz transformation times a dilation, `σ = c²`) pulls the compactified metric `Ω² η`
(`compactCart`) back to `(σ Ω²(Λ x + a)/Ω²(x)) • Ω² η`. The case `Λ = c • 1` is the dilation `x ↦ c x`
(`dilation_conformal`), whose factor on the compactification is `c² Ω²(c x)/Ω²(x)`; together with
`poincare_conformal` this is the Weyl-Poincaré subgroup of the conformal group `SO(2,4)` acting on the
compactified Minkowski space (Aharony-Gubser-Maldacena-Ooguri-Oz, arXiv:hep-th/9905111, section 2.2).
-/

open Matrix Real

noncomputable section

namespace Lightlike

/-- **Linear conformal maps of Minkowski space act conformally on its compactification**: if
`Λᵀ η Λ = σ η` then the pullback of `compactCart` by `x ↦ Λ x + a` is
`(σ Ω²(Λ x + a)/Ω²(x)) • compactCart x`. -/
theorem conformal_of_linear_conformal {Λ : Matrix (Fin 4) (Fin 4) ℝ} {σ : ℝ}
    (hΛ : Λᵀ * eta 4 * Λ = σ • eta 4) (a y : Fin 4 → ℝ) :
    pullback compactCart (poincareMap Λ a) y =
      (σ * cfC (poincareMap Λ a y) / cfC y) • compactCart y := by
  have e : compactCart = fun x => cfC x • minkCart x := rfl
  have h1 : pullback minkCart (poincareMap Λ a) y = σ • minkCart y := by
    rw [pullback_eq_mul, jac_poincareMap]
    simpa [minkCart] using hΛ
  rw [e, pullback_smul_field cfC minkCart, h1]
  simp only [smul_smul]
  congr 1
  field_simp [(cfC_pos y).ne']

/-- The dilation `x ↦ c x` of Minkowski space as an affine map. -/
theorem poincareMap_smul_one (c : ℝ) (x : Fin 4 → ℝ) :
    poincareMap (c • (1 : Matrix (Fin 4) (Fin 4) ℝ)) 0 x = c • x := by
  simp [poincareMap, Matrix.smul_mulVec]

/-- The dilation `x ↦ c x` scales `η` by `c²`. -/
theorem dilation_lorentz (c : ℝ) :
    (c • (1 : Matrix (Fin 4) (Fin 4) ℝ))ᵀ * eta 4 * (c • (1 : Matrix (Fin 4) (Fin 4) ℝ)) =
      (c ^ 2) • eta 4 := by
  simp [Matrix.transpose_smul, smul_smul, sq]

/-- **Dilations act conformally on the compactified Minkowski space**: the pullback of the compactified metric by
`x ↦ c x` is `(c² Ω²(c x)/Ω²(x))` times the compactified metric. -/
theorem dilation_conformal (c : ℝ) (y : Fin 4 → ℝ) :
    pullback compactCart (fun x => c • x) y =
      (c ^ 2 * cfC (c • y) / cfC y) • compactCart y := by
  have h := conformal_of_linear_conformal (dilation_lorentz c) 0 y
  have e : poincareMap (c • (1 : Matrix (Fin 4) (Fin 4) ℝ)) 0 = fun x => c • x := by
    funext x; exact poincareMap_smul_one c x
  rw [e] at h
  rw [h]

end Lightlike
