module

public import Lightlike.Poincare.LightCone

/-!
# Unitarity of the massless helicity representations

For every `SL(2,ℂ)`-invariant measure `μ` on the forward light cone (for instance `d³p / |p|`), the massless induced
representation of helicity `n/2` preserves `∫ |ψ|² dμ` (`lintegral_normSq_helicityAct_of_invariant`): the helicity
character has modulus one. Only the invariance of `μ` is used.

## References

* X. Bekaert, N. Boulanger, *The unitary representations of the Poincaré group in any spacetime dimension*,
  arXiv:hep-th/0611263v2, §3.2 (the Poincaré-invariant scalar product on the orbit, page 11 of v2) and §3.3
  (helicity representations, pages 14–15).
-/

@[expose] public section

noncomputable section

open Matrix MeasureTheory Lightlike.Lorentz

namespace Lightlike.Poincare

/-- The Borel σ-algebra on the light cone. -/
instance instMeasurableSpaceLightCone : MeasurableSpace LightCone := borel _

instance instBorelSpaceLightCone : BorelSpace LightCone := ⟨rfl⟩

lemma continuous_smul_lightCone (A : SL2C) : Continuous fun P : LightCone => A • P := by
  refine Continuous.subtype_mk ?_ _
  show Continuous fun P : LightCone => actP A P.1
  unfold actP
  have h : Continuous fun P : LightCone => (P.1 : Matrix (Fin 2) (Fin 2) ℂ) := continuous_subtype_val
  exact (continuous_const.matrix_mul h).matrix_mul continuous_const

/-- The action of `A` on the light cone as a measurable equivalence. -/
def coneActEquiv (A : SL2C) : LightCone ≃ᵐ LightCone where
  toFun P := A • P
  invFun P := A⁻¹ • P
  left_inv P := inv_smul_smul A P
  right_inv P := smul_inv_smul A P
  measurable_toFun := (continuous_smul_lightCone A).measurable
  measurable_invFun := (continuous_smul_lightCone A⁻¹).measurable

lemma norm_helicityAct (n : ℤ) (A : SL2C) (ψ : LightCone → ℂ) (P : LightCone) :
    ‖helicityAct n A ψ P‖ = ‖ψ (A⁻¹ • P)‖ := by
  simp only [helicityAct, inducedActG, helicityChar, MonoidHom.coe_mk, OneHom.coe_mk,
    LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, norm_mul]
  rw [norm_helicity, one_mul]

/-- **Unitarity of the massless helicity representations**, for every invariant measure on the light cone. -/
theorem lintegral_normSq_helicityAct_of_invariant (μ : Measure LightCone)
    (hμ : ∀ A : SL2C, Measure.map (fun P : LightCone => A • P) μ = μ) (n : ℤ) (A : SL2C)
    (ψ : LightCone → ℂ) :
    ∫⁻ P, ENNReal.ofReal (‖helicityAct n A ψ P‖ ^ 2) ∂μ = ∫⁻ P, ENNReal.ofReal (‖ψ P‖ ^ 2) ∂μ := by
  simp only [norm_helicityAct]
  exact (show MeasurePreserving (fun P : LightCone => A⁻¹ • P) μ μ from
      ⟨(continuous_smul_lightCone A⁻¹).measurable, hμ A⁻¹⟩).lintegral_comp_emb
    (coneActEquiv A⁻¹).measurableEmbedding (fun P => ENNReal.ofReal (‖ψ P‖ ^ 2))

end Lightlike.Poincare
