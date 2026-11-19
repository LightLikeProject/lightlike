import Lightlike.OperatorAlgebras.Semigroup.LaplaceResolvent
import Lightlike.OperatorAlgebras.Semigroup.Generation

/-!
# The converse of the Hille–Yosida generation theorem

The generator `A` of a strongly continuous semigroup of contractions has dense domain, and `λ - A` is
bounded below by `λ` and surjective for every `λ > 0`
(`contractionSemigroup_generator_hypotheses`): density from `t⁻¹ ∫₀ᵗ S s x ds`, the lower bound from
`ContractionSemigroup.norm_dissip`, and surjectivity from the resolvent `∫₀^∞ e^{-λ t} S t y dt`.
Together with `hille_yosida_generation` this is the equivalence of the Hille–Yosida theorem
(`hilleYosida_contraction`).
-/

open Filter Topology NNReal MeasureTheory Set
open scoped LinearPMap

noncomputable section

namespace Lightlike.OperatorAlgebras

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [CompleteSpace X]

/-- **The generator of a contraction semigroup satisfies the hypotheses of the Hille–Yosida
theorem**: dense domain, `λ - A` bounded below by `λ` and surjective for every `λ > 0`. -/
theorem contractionSemigroup_generator_hypotheses (S : ContractionSemigroup 𝕜 X) :
    Dense (S.generator.domain : Set X) ∧
    (∀ l : ℝ, 0 < l → ∀ x : S.generator.domain,
      l * ‖(x : X)‖ ≤ ‖(l : 𝕜) • (x : X) - S.generator x‖) ∧
    (∀ l : ℝ, 0 < l → ∀ y : X, ∃ x : S.generator.domain,
      (l : 𝕜) • (x : X) - S.generator x = y) := by
  let _ : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
  have : IsScalarTower ℝ 𝕜 X := inferInstance
  refine ⟨S.dense_generatorDomain, fun l hl x => S.norm_dissip hl x.2, fun l hl y => ?_⟩
  have hdom : S.resolvent l y ∈ S.generator.domain := ⟨_, S.tendsto_quot_resolvent hl y⟩
  refine ⟨⟨S.resolvent l y, hdom⟩, ?_⟩
  have hgen : S.generator ⟨S.resolvent l y, hdom⟩ = l • S.resolvent l y - y :=
    tendsto_nhds_unique (S.tendsto_genVal hdom) (S.tendsto_quot_resolvent hl y)
  rw [hgen, (RCLike.real_smul_eq_coe_smul (K := 𝕜) l (S.resolvent l y)).symm]
  abel

/-- **The Hille–Yosida theorem for contraction semigroups.** An operator `A` with dense domain is the
generator of a strongly continuous contraction semigroup if and only if, for every `λ > 0`, `λ - A` is
bounded below by `λ` and surjective. -/
theorem hilleYosida_contraction (A : X →ₗ.[𝕜] X) :
    (∃ S : ContractionSemigroup 𝕜 X, S.generator = A) ↔
      Dense (A.domain : Set X) ∧
      (∀ l : ℝ, 0 < l → ∀ x : A.domain, l * ‖(x : X)‖ ≤ ‖(l : 𝕜) • (x : X) - A x‖) ∧
      (∀ l : ℝ, 0 < l → ∀ y : X, ∃ x : A.domain, (l : 𝕜) • (x : X) - A x = y) := by
  constructor
  · rintro ⟨S, rfl⟩
    exact contractionSemigroup_generator_hypotheses S
  · rintro ⟨h1, h2, h3⟩
    exact hille_yosida_generation A h1 h2 h3

end Lightlike.OperatorAlgebras
