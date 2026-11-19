import Lightlike.OperatorAlgebras.Spectral.Stone.Theorem
import Lightlike.OperatorAlgebras.Spectral.Stone.Exponential
import Lightlike.OperatorAlgebras.UnitaryGroup

/-!
# Bridge between the ported Stone theorem and `UnitaryGroup`

The Stone modules ported from physicslib4 speak of a family `U : ℝ → (H ≃ₗᵢ[ℂ] H)` with the predicates
`IsOneParameterUnitaryGroup` and `IsStronglyContinuous` and the generator `Spectral.Stone.generator U`. The structure
`OperatorAlgebras.UnitaryGroup` and its generator `UnitaryGroup.generator` are defined in `UnitaryGroup.lean`. This file
shows that they agree: a `UnitaryGroup` is a strongly continuous one-parameter group (`isOneParameterUnitaryGroup`,
`isStronglyContinuous`), and the two generators are equal (`generator_eq`).
-/

open Filter Topology

namespace Lightlike.OperatorAlgebras.Spectral.Stone

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The family of a `UnitaryGroup` satisfies the group law of the ported development. -/
theorem isOneParameterUnitaryGroup (U : UnitaryGroup H) :
    IsOneParameterUnitaryGroup (fun t => (U t : H ≃ₗᵢ[ℂ] H)) where
  map_zero ψ := by
    have := congrArg (fun e : H ≃ₗᵢ[ℂ] H => e ψ) U.map_zero'
    simpa using this
  map_add s t ψ := by
    have := congrArg (fun e : H ≃ₗᵢ[ℂ] H => e ψ) (U.map_add' s t)
    simpa using this

/-- The family of a `UnitaryGroup` is strongly continuous. -/
theorem isStronglyContinuous (U : UnitaryGroup H) : IsStronglyContinuous (fun t => (U t : H ≃ₗᵢ[ℂ] H)) :=
  fun ψ => U.continuous' ψ

/-- The generator quotient of the ported development is `-i` times the slope of the orbit. -/
lemma generatorQuotient_eq_slope (U : UnitaryGroup H) (ψ : H) (t : ℝ) :
    generatorQuotient (fun s => (U s : H ≃ₗᵢ[ℂ] H)) ψ t = (-Complex.I) • slope (fun s => U s ψ) 0 t := by
  have h0 : U 0 ψ = ψ := by simpa using congrArg (fun e : H ≃ₗᵢ[ℂ] H => e ψ) U.map_zero'
  unfold generatorQuotient
  rw [slope_def_module, h0, sub_zero, ← Complex.coe_smul, smul_smul]
  congr 1
  by_cases ht : t = 0
  · simp [ht]
  · simp [Complex.inv_I, mul_comm]

/-- The slope of the orbit is `i` times the generator quotient. -/
lemma slope_eq_generatorQuotient (U : UnitaryGroup H) (ψ : H) (t : ℝ) :
    slope (fun s => U s ψ) 0 t = Complex.I • generatorQuotient (fun s => (U s : H ≃ₗᵢ[ℂ] H)) ψ t := by
  rw [generatorQuotient_eq_slope, smul_smul]
  simp

/-- **The two generators agree**: the generator of the ported development of the family of a `UnitaryGroup` is
`UnitaryGroup.generator`. -/
theorem generator_eq (U : UnitaryGroup H) :
    generator (fun t => (U t : H ≃ₗᵢ[ℂ] H)) = U.generator := by
  have key : ∀ ψ : H, (∃ χ : H, Tendsto (generatorQuotient (fun t => (U t : H ≃ₗᵢ[ℂ] H)) ψ) (𝓝[≠] 0) (𝓝 χ)) ↔
      DifferentiableAt ℝ (fun t => U t ψ) 0 := by
    intro ψ
    constructor
    · rintro ⟨χ, hχ⟩
      have h1 : Tendsto (slope (fun s => U s ψ) 0) (𝓝[≠] 0) (𝓝 (Complex.I • χ)) := by
        have := hχ.const_smul Complex.I
        refine this.congr fun t => ?_
        exact (slope_eq_generatorQuotient U ψ t).symm
      exact (hasDerivAt_iff_tendsto_slope.2 h1).differentiableAt
    · intro hd
      refine ⟨(-Complex.I) • deriv (fun t => U t ψ) 0, ?_⟩
      have h1 := hd.hasDerivAt
      rw [hasDerivAt_iff_tendsto_slope] at h1
      have := h1.const_smul (-Complex.I)
      exact this.congr fun t => (generatorQuotient_eq_slope U ψ t).symm
  refine LinearPMap.ext (Submodule.ext fun ψ => key ψ) ?_
  intro x hf hg
  have hf' := hf
  obtain ⟨χ, hχ⟩ := hf'
  have hd : DifferentiableAt ℝ (fun t => U t x) 0 := (key x).1 ⟨χ, hχ⟩
  have h1 := hd.hasDerivAt
  rw [hasDerivAt_iff_tendsto_slope] at h1
  have h2 : Tendsto (generatorQuotient (fun t => (U t : H ≃ₗᵢ[ℂ] H)) x) (𝓝[≠] 0)
      (𝓝 ((-Complex.I) • deriv (fun t => U t x) 0)) :=
    (h1.const_smul (-Complex.I)).congr fun t => (generatorQuotient_eq_slope U x t).symm
  show limUnder (𝓝[≠] (0 : ℝ)) (generatorQuotient (fun t => (U t : H ≃ₗᵢ[ℂ] H)) x) =
    (-Complex.I) • deriv (fun t => U t x) 0
  exact h2.limUnder_eq

/-- The group `e^{itA}` of a self-adjoint operator as a `UnitaryGroup`. -/
noncomputable def spectralGroup {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) : UnitaryGroup H where
  toFun := fun t => expUnitary hA t
  map_zero' := by
    ext ψ
    exact (generator_expUnitary hA).1.map_zero ψ
  map_add' := by
    intro s t
    ext ψ
    exact (generator_expUnitary hA).1.map_add s t ψ
  continuous' := fun ψ => (generator_expUnitary hA).2.1 ψ

/-- **The generator of `e^{itA}` is `A`**, in terms of `UnitaryGroup.generator`. -/
theorem spectralGroup_generator {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) :
    (spectralGroup hA).generator = A := by
  rw [← generator_eq]
  exact (generator_expUnitary hA).2.2

end Lightlike.OperatorAlgebras.Spectral.Stone
