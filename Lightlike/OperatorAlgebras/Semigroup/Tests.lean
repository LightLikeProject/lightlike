import Lightlike.OperatorAlgebras.Semigroup.Generation

/-!
# Checks of the semigroup definitions and the generation theorem

* The constant semigroup `S t = 1` has the generator `0` with full domain (a known value of the
  definition of the generator).
* The hypotheses of `hille_yosida_generation` hold for the operator `0` with full domain, so the
  theorem applies (non-vacuity).
* A wrong model: the operator `A = id` on `𝕜` has `λ - A` not bounded below by `λ` for `λ = 1`
  (indeed `e^{t}` is not a contraction semigroup), so the hypotheses are false.
-/

open Filter Topology NNReal
open scoped LinearPMap

noncomputable section

namespace Lightlike.OperatorAlgebras

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- The constant semigroup `S t = 1`. -/
def trivialSemigroup : ContractionSemigroup 𝕜 X where
  S := fun _ => 1
  zero := rfl
  add := fun _ _ => by ext; rfl
  norm_le := fun _ => ContinuousLinearMap.norm_id_le
  tendsto_zero := fun _ => tendsto_const_nhds

/-- The generator of the constant semigroup is `0` with full domain. -/
example (x : X) : (trivialSemigroup (𝕜 := 𝕜) (X := X)).IsGeneratorDomain x ∧
    (trivialSemigroup (𝕜 := 𝕜) (X := X)).genVal x = 0 := by
  have h : Tendsto (fun t : ℝ≥0 => (trivialSemigroup (𝕜 := 𝕜) (X := X)).quot t x) (𝓝[>] 0) (𝓝 0) := by
    simp [ContractionSemigroup.quot, trivialSemigroup]
  exact ⟨⟨0, h⟩, tendsto_nhds_unique ((trivialSemigroup (𝕜 := 𝕜) (X := X)).tendsto_genVal ⟨0, h⟩) h⟩

/-- Non-vacuity: `0` with full domain satisfies the hypotheses, so it generates a contraction
semigroup. -/
example [CompleteSpace X] : ∃ S : ContractionSemigroup 𝕜 X,
    S.generator = ((0 : X →ₗ[𝕜] X).toPMap ⊤) := by
  refine hille_yosida_generation _ ?_ ?_ ?_
  · simp
  · intro l hl x
    have e : ((0 : X →ₗ[𝕜] X).toPMap ⊤) x = 0 := rfl
    rw [e, sub_zero, norm_smul, RCLike.norm_ofReal, abs_of_pos hl]
  · intro l hl y
    refine ⟨⟨((l : ℝ) : 𝕜)⁻¹ • y, trivial⟩, ?_⟩
    have : ((l : ℝ) : 𝕜) ≠ 0 := by exact_mod_cast hl.ne'
    have e : ((0 : X →ₗ[𝕜] X).toPMap ⊤) ⟨((l : ℝ) : 𝕜)⁻¹ • y, trivial⟩ = 0 := rfl
    rw [e, sub_zero]
    show ((l : ℝ) : 𝕜) • (((l : ℝ) : 𝕜)⁻¹ • y) = y
    rw [smul_smul, mul_inv_cancel₀ this, one_smul]

/-- Wrong model: for `A = id` on `𝕜` the lower bound fails at `λ = 1`. -/
example : ¬ (∀ l : ℝ, 0 < l → ∀ x : ((LinearMap.id : 𝕜 →ₗ[𝕜] 𝕜).toPMap ⊤).domain,
    l * ‖(x : 𝕜)‖ ≤ ‖(l : 𝕜) • (x : 𝕜) - ((LinearMap.id : 𝕜 →ₗ[𝕜] 𝕜).toPMap ⊤) x‖) := by
  intro h
  have := h 1 one_pos ⟨1, trivial⟩
  have e : ((LinearMap.id : 𝕜 →ₗ[𝕜] 𝕜).toPMap ⊤) ⟨1, trivial⟩ = 1 := rfl
  simp only [e] at this
  norm_num at this

end Lightlike.OperatorAlgebras
