import Mathlib

/-!
# Periodic functions as functions on the circle

Row G3-188 (PL5), step 4 of the pass-4 plan.  `exists_circle_lift`: a continuous `2π`-periodic function on the
line is `ψ ∘ Circle.exp` for a continuous function `ψ` of the circle.
-/

open Set

namespace Lightlike.PL.Schoenflies

theorem exists_circle_lift {X : Type*} [TopologicalSpace X] {G : ℝ → X} (hG : Continuous G)
    (hper : Function.Periodic G (2 * Real.pi)) :
    ∃ ψ : Circle → X, Continuous ψ ∧ ∀ s, ψ (Circle.exp s) = G s := by
  let ψ' : AddCircle (2 * Real.pi) → X := hper.lift
  have hψ' : Continuous ψ' := by
    refine ((QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (2 * Real.pi))).continuous_iff).2 ?_
    exact hG
  refine ⟨ψ' ∘ AddCircle.homeomorphCircle'.symm, hψ'.comp AddCircle.homeomorphCircle'.symm.continuous, fun s => ?_⟩
  have : (AddCircle.homeomorphCircle'.symm (Circle.exp s)) = ((s : ℝ) : AddCircle (2 * Real.pi)) := by
    rw [Homeomorph.symm_apply_eq]; rfl
  simp only [Function.comp_apply, this]
  rfl

end Lightlike.PL.Schoenflies
