import Lightlike.OperatorAlgebras.FiniteRankApprox
import Lightlike.OperatorAlgebras.TraceClass.BoundedSesquilinearForm
import Lightlike.OperatorAlgebras.TraceClass.TracePairingSurjectivity

/-!
# The dual of the compact operators: the representing operator

Second brick toward `T-OP6-P1` (`K* ≅ S¹`). A continuous functional `f` on the compact operators `𝒦(H)` of a complex Hilbert
space gives, on rank-one operators, the bounded sesquilinear form `(x, y) ↦ conj (f |x⟩⟨y|)` (`‖|x⟩⟨y|‖ = ‖x‖ ‖y‖`), hence a bounded operator
`T` with `⟪y, T x⟫ = f |x⟩⟨y|` (`compactFunctionalOperator_inner`). The next brick shows `T` is trace class.
-/

open scoped InnerProductSpace

namespace Lightlike.OperatorAlgebras

open TraceClass

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The compact operators as a normed space (a submodule of the bounded operators). -/
abbrev CompactOps (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :=
  compactOperator (RingHom.id ℂ) H H

/-- The rank-one operator `|x⟩⟨y|` as a compact operator. -/
noncomputable def rankOneCompact (x y : H) : CompactOps H :=
  ⟨InnerProductSpace.rankOne ℂ x y, isCompactOperator_rankOne x y⟩

lemma norm_rankOneCompact (x y : H) : ‖rankOneCompact x y‖ = ‖x‖ * ‖y‖ :=
  InnerProductSpace.norm_rankOne x y

lemma rankOneCompact_add_right (x y z : H) :
    rankOneCompact x (y + z) = rankOneCompact x y + rankOneCompact x z := by
  apply Subtype.ext
  change InnerProductSpace.rankOne ℂ x (y + z) = InnerProductSpace.rankOne ℂ x y + InnerProductSpace.rankOne ℂ x z
  ext v
  simp [InnerProductSpace.rankOne_apply]

lemma rankOneCompact_smul_right (c : ℂ) (x y : H) :
    rankOneCompact x (c • y) = (starRingEnd ℂ c) • rankOneCompact x y := by
  apply Subtype.ext
  change InnerProductSpace.rankOne ℂ x (c • y) = (starRingEnd ℂ c) • InnerProductSpace.rankOne ℂ x y
  ext v
  simp [InnerProductSpace.rankOne_apply]

lemma rankOneCompact_add_left (x z y : H) :
    rankOneCompact (x + z) y = rankOneCompact x y + rankOneCompact z y := by
  apply Subtype.ext
  change InnerProductSpace.rankOne ℂ (x + z) y = InnerProductSpace.rankOne ℂ x y + InnerProductSpace.rankOne ℂ z y
  ext v
  simp [InnerProductSpace.rankOne_apply]

lemma rankOneCompact_smul_left (c : ℂ) (x y : H) :
    rankOneCompact (c • x) y = c • rankOneCompact x y := by
  apply Subtype.ext
  change InnerProductSpace.rankOne ℂ (c • x) y = c • InnerProductSpace.rankOne ℂ x y
  ext v
  simp

/-- The bounded sesquilinear form `(x, y) ↦ conj (f |x⟩⟨y|)` of a continuous functional `f` on the compact operators. -/
noncomputable def sesquilinearFormOfCompactFunctional (f : CompactOps H →L[ℂ] ℂ) : BoundedSesquilinearForm H :=
  { form :=
      { toFun := fun x =>
          { toFun := fun y => starRingEnd ℂ (f (rankOneCompact x y))
            map_add' := fun y z => by rw [rankOneCompact_add_right, map_add]; simp
            map_smul' := fun c y => by rw [rankOneCompact_smul_right, map_smul]; simp }
        map_add' := fun x z => by
          apply LinearMap.ext; intro y
          change starRingEnd ℂ (f (rankOneCompact (x + z) y)) = _
          rw [rankOneCompact_add_left, map_add]; simp
        map_smul' := fun c x => by
          apply LinearMap.ext; intro y
          change starRingEnd ℂ (f (rankOneCompact (c • x) y)) = _
          rw [rankOneCompact_smul_left, map_smul]; simp }
    bound := by
      refine ⟨‖f‖, fun x y => ?_⟩
      change ‖starRingEnd ℂ (f (rankOneCompact x y))‖ ≤ ‖f‖ * ‖x‖ * ‖y‖
      rw [← RCLike.star_def, norm_star]
      calc ‖f (rankOneCompact x y)‖ ≤ ‖f‖ * ‖rankOneCompact x y‖ := f.le_opNorm _
        _ = ‖f‖ * ‖x‖ * ‖y‖ := by rw [norm_rankOneCompact, mul_assoc] }

/-- The bounded operator `T` of a continuous functional `f` on the compact operators. -/
noncomputable def compactFunctionalOperator (f : CompactOps H →L[ℂ] ℂ) : H →L[ℂ] H :=
  (sesquilinearFormOfCompactFunctional f).operator

/-- **`⟪y, T x⟫ = f |x⟩⟨y|`**. -/
theorem compactFunctionalOperator_inner (f : CompactOps H →L[ℂ] ℂ) (x y : H) :
    ⟪y, compactFunctionalOperator f x⟫_ℂ = f (rankOneCompact x y) := by
  rw [compactFunctionalOperator, BoundedSesquilinearForm.operator_inner]
  change starRingEnd ℂ (starRingEnd ℂ (f (rankOneCompact x y))) = _
  simp

end Lightlike.OperatorAlgebras
