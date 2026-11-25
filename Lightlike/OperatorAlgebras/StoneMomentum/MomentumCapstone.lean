import Lightlike.OperatorAlgebras.TranslationCore
import Lightlike.OperatorAlgebras.Spectral.StoneConsistency
import Lightlike.OperatorAlgebras.MomentumDeficiency
import Lightlike.OperatorAlgebras.Spectral.Unbounded.Basic

/-!
# Milestone OP1, assembled: Stone's theorem and the momentum operator

The pieces of milestone OP1 are proved in `Lightlike/OperatorAlgebras/` in two vocabularies: the
`UnitaryGroup` and its generator (`UnitaryGroup.generator_isSelfAdjoint`, `stoneGroup`,
`UnitaryGroup.eq_of_generator_eq`), and the unbounded-operator layer of `Spectral/Unbounded`
(`IsEssentiallySelfAdjoint`, with the closure as Mathlib's `LinearPMap.closure`). This file states
the trust checks of OP1 in one place and in the second vocabulary:

* `stone_theorem`: Stone's theorem in both directions on any complex Hilbert space.
* `momentumSmoothR`: `-i d/dx` on `C_c^∞(ℝ) ⊆ L²(ℝ)`, as a `LinearPMap`;
  `momentumSmoothR_isEssentiallySelfAdjoint`: it is essentially self-adjoint, its closure is the
  generator of the translation group (`closure_momentumSmoothR`), and the translation group is
  `e^{itP}` for that closure (`translationGroup_eq_spectralGroup`).
* `momentumMin_deficiency_indices`, `momentumMin_not_isEssentiallySelfAdjoint`: on `L²(0, 1)`,
  `-i d/dx` on the `C²` functions supported inside `(0, 1)` has deficiency indices `(1, 1)` and
  hence is not essentially self-adjoint (`deficiencySpace_of_isEssentiallySelfAdjoint`).
-/

open scoped InnerProductSpace LinearPMap ContDiff

namespace Lightlike.OperatorAlgebras.OPRow154

open Lightlike.OperatorAlgebras

/-- **Stone's theorem, both directions**, on a complex Hilbert space: the generator of a strongly
continuous one-parameter unitary group is self-adjoint, and every self-adjoint operator is the
generator of exactly one such group. -/
theorem stone_theorem {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    (∀ U : UnitaryGroup H, IsSelfAdjoint U.generator) ∧
      ∀ A : H →ₗ.[ℂ] H, IsSelfAdjoint A → ∃! U : UnitaryGroup H, U.generator = A := by
  refine ⟨fun U => U.generator_isSelfAdjoint, fun A hA => ⟨stoneGroup hA, generator_stoneGroup hA, ?_⟩⟩
  intro U hU
  exact UnitaryGroup.eq_of_generator_eq (by rw [hU, generator_stoneGroup hA])

/-- **The momentum operator `-i d/dx` on `C_c^∞(ℝ)`** as an operator on `L²(ℝ)`: the generator of
the translation group restricted to the classes of smooth compactly supported functions. -/
noncomputable def momentumSmoothR : L2R →ₗ.[ℂ] L2R :=
  translationGroup.generator.domRestrict smoothCS

lemma momentumSmoothR_domain : momentumSmoothR.domain = smoothCS := by
  unfold momentumSmoothR
  rw [LinearPMap.domRestrict_domain]
  exact inf_eq_left.2 smoothCS_le_domain

/-- On a `C_c^∞` function the operator is `-i d/dx`. -/
theorem momentumSmoothR_ofCS {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (h : ofCS hg.continuous hc ∈ momentumSmoothR.domain) :
    momentumSmoothR ⟨ofCS hg.continuous hc, h⟩ =
      (-Complex.I) • ofCS (continuous_deriv_of_two (hg.of_le (by norm_num))) hc.deriv := by
  obtain ⟨h', hh⟩ := translationGroup_generator_ofCS (hg.of_le (by norm_num)) hc
  rw [← hh]
  exact LinearPMap.domRestrict_apply (rfl : _ = ((⟨ofCS hg.continuous hc, h'⟩ :
    translationGroup.generator.domain) : L2R))

lemma momentumSmoothR_le : momentumSmoothR ≤ translationGroup.generator := by
  refine ⟨fun x hx => ?_, fun x y hxy => ?_⟩
  · have hiff : ∀ z : L2R, z ∈ momentumSmoothR.domain ↔ z ∈ smoothCS ⊓ translationGroup.generator.domain :=
      fun z => by unfold momentumSmoothR; rw [LinearPMap.domRestrict_domain]
    exact ((hiff x).1 hx).2
  · exact LinearPMap.domRestrict_apply hxy

/-- The closure of `-i d/dx` on `C_c^∞(ℝ)` is the generator of the translation group. -/
theorem closure_momentumSmoothR : momentumSmoothR.closure = translationGroup.generator :=
  UnitaryGroup.closure_domRestrict_generator dense_smoothCS smoothCS_le_domain smoothCS_invariant

/-- **`-i d/dx` is essentially self-adjoint on `C_c^∞(ℝ)`.** -/
theorem momentumSmoothR_isEssentiallySelfAdjoint :
    Spectral.Unbounded.IsEssentiallySelfAdjoint momentumSmoothR := by
  have hsa : IsSelfAdjoint translationGroup.generator := translationGroup.generator_isSelfAdjoint
  have hdomA : Spectral.Unbounded.HasDenseDomain translationGroup.generator := hsa.dense_domain
  have hD : Spectral.Unbounded.HasDenseDomain momentumSmoothR := by
    unfold Spectral.Unbounded.HasDenseDomain
    rw [momentumSmoothR_domain]; exact dense_smoothCS
  have hsym : Spectral.Unbounded.IsSymmetric momentumSmoothR := by
    rw [Spectral.Unbounded.isSymmetric_iff_le_adjoint hD]
    have h2 := Spectral.Unbounded.adjoint_le_adjoint_of_le hD momentumSmoothR_le
    rw [LinearPMap.isSelfAdjoint_def.1 hsa] at h2
    exact momentumSmoothR_le.trans h2
  have hclos : momentumSmoothR.IsClosable := Spectral.Unbounded.isClosable_of_isSymmetric hD hsym
  exact ⟨hsym, hclos, by rw [closure_momentumSmoothR]; exact hsa⟩

/-- `C_c^∞(ℝ)` is a domain of essential self-adjointness with a unique self-adjoint extension:
the generator of the translation group. -/
theorem momentumSmoothR_unique_selfAdjoint_extension :
    ∃! B : L2R →ₗ.[ℂ] L2R, IsSelfAdjoint B ∧ momentumSmoothR ≤ B := by
  have := Spectral.Unbounded.existsUnique_isSelfAdjoint_extension momentumSmoothR_isEssentiallySelfAdjoint
  exact this

/-- **The translation group is generated by the closure of `-i d/dx` on `C_c^∞(ℝ)`**: it is the
group `e^{itP}` of the self-adjoint operator `P = momentumSmoothR.closure`, given by the spectral
theorem. -/
theorem translationGroup_eq_spectralGroup :
    translationGroup = Spectral.Stone.spectralGroup
      momentumSmoothR_isEssentiallySelfAdjoint.isSelfAdjoint_closure :=
  UnitaryGroup.eq_of_generator_eq (by
    rw [Spectral.Stone.spectralGroup_generator, closure_momentumSmoothR])

/-- Operators with the same adjoint have the same deficiency spaces. -/
lemma deficiencySpace_congr {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {A B : H →ₗ.[ℂ] H} (h : A† = B†) (z : ℂ) :
    deficiencySpace A z = deficiencySpace B z := by
  have key : ∀ (P Q : H →ₗ.[ℂ] H), P = Q → ∀ ψ : H,
      (∃ h : ψ ∈ P.domain, P ⟨ψ, h⟩ = z • ψ) → ∃ h : ψ ∈ Q.domain, Q ⟨ψ, h⟩ = z • ψ := by
    intro P Q hPQ ψ
    subst hPQ
    exact id
  ext ψ
  exact ⟨key _ _ h ψ, key _ _ h.symm ψ⟩

/-- An essentially self-adjoint operator has no deficiency at a non-real `z`. -/
theorem deficiencySpace_of_isEssentiallySelfAdjoint {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {T : H →ₗ.[ℂ] H}
    (hT : Spectral.Unbounded.HasDenseDomain T) (h : Spectral.Unbounded.IsEssentiallySelfAdjoint T)
    {z : ℂ} (hz : z.im ≠ 0) : deficiencySpace T z = ⊥ := by
  rw [← deficiencySpace_of_isSelfAdjoint h.isSelfAdjoint_closure hz]
  exact deficiencySpace_congr (Spectral.Unbounded.adjoint_closure_eq_adjoint hT h.isClosable).symm z

/-- **`-i d/dx` on `L²(0, 1)` without boundary conditions has deficiency indices `(1, 1)` and is
not essentially self-adjoint** (in particular the indices are not `(0, 0)`). -/
theorem momentumMin_not_isEssentiallySelfAdjoint :
    ¬ Spectral.Unbounded.IsEssentiallySelfAdjoint momentumMin := by
  intro h
  have hz := deficiencySpace_of_isEssentiallySelfAdjoint dense_momentumMin_domain h
    (z := Complex.I) (by simp)
  have h1 := (deficiency_indices_momentumMin).2.1
  rw [deficiencyDim, hz, rank_bot] at h1
  exact zero_ne_one h1

/-- **Milestone trust check, `L²[0,1]`**: the deficiency indices of `-i d/dx` without boundary
conditions are `(1, 1)`. -/
theorem momentumMin_deficiency_indices :
    Dense (momentumMin.domain : Set L2I) ∧ deficiencyDim momentumMin Complex.I = 1 ∧
      deficiencyDim momentumMin (-Complex.I) = 1 :=
  deficiency_indices_momentumMin

end Lightlike.OperatorAlgebras.OPRow154
