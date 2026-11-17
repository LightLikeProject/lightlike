import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Strongly continuous one-parameter unitary groups and their generators

The operator type is Mathlib's `LinearPMap` (a partially defined linear map `H →ₗ.[ℂ] H`), with its adjoint
and `IsSelfAdjoint` (`Mathlib/Analysis/InnerProductSpace/LinearPMap.lean`). This file adds what Mathlib
does not have: the structure `UnitaryGroup H` of a strongly continuous one-parameter group of unitaries
(`U 0 = 1`, `U (s + t) = U s ∘ U t`, `t ↦ U t ψ` continuous for every `ψ`), and its **generator**, the
operator `A` with `U t = exp (i t A)`, defined as `A ψ = -i d/dt U t ψ |_{t = 0}` on the vectors where the
derivative exists.

The statements of Stone's theorem built on these definitions are the proof tasks `T-OP1-P1` to
`T-OP1-P3` (`Tasks/OP/`). The exponential `exp (i t A)` of an unbounded operator is not in Mathlib, so
the group is tied to `A` through the generator, not through a functional calculus.
-/

open scoped InnerProductSpace

namespace Lightlike.OperatorAlgebras

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **A strongly continuous one-parameter unitary group** on a complex Hilbert space `H`: unitaries
`U t` with `U 0 = 1`, `U (s + t) = U s ∘ U t`, and `t ↦ U t ψ` continuous for every vector `ψ`. -/
@[ext]
structure UnitaryGroup where
  /-- The unitary `U t`. -/
  toFun : ℝ → (H ≃ₗᵢ[ℂ] H)
  /-- `U 0` is the identity. -/
  map_zero' : toFun 0 = LinearIsometryEquiv.refl ℂ H
  /-- `U (s + t) = U s ∘ U t`. -/
  map_add' : ∀ s t, toFun (s + t) = (toFun t).trans (toFun s)
  /-- Strong continuity: `t ↦ U t ψ` is continuous for every `ψ`. -/
  continuous' : ∀ ψ : H, Continuous fun t => toFun t ψ

namespace UnitaryGroup

variable {H}

instance : CoeFun (UnitaryGroup H) (fun _ => ℝ → (H ≃ₗᵢ[ℂ] H)) := ⟨UnitaryGroup.toFun⟩

/-- The domain of the generator: the vectors `ψ` for which `t ↦ U t ψ` is differentiable at `0`. -/
def generatorDomain (U : UnitaryGroup H) : Submodule ℂ H where
  carrier := {ψ | DifferentiableAt ℝ (fun t => U t ψ) 0}
  add_mem' := by
    intro a b ha hb
    have h : (fun t => U t (a + b)) = fun t => U t a + U t b := by
      funext t; exact map_add _ _ _
    show DifferentiableAt ℝ (fun t => U t (a + b)) 0
    rw [h]
    exact DifferentiableAt.add ha hb
  zero_mem' := by
    show DifferentiableAt ℝ (fun t => U t 0) 0
    have h : (fun t => U t (0 : H)) = fun _ => (0 : H) := by
      funext t; exact map_zero _
    rw [h]
    exact differentiableAt_const _
  smul_mem' := by
    intro c a ha
    have h : (fun t => U t (c • a)) = fun t => c • U t a := by
      funext t; exact map_smul _ _ _
    show DifferentiableAt ℝ (fun t => U t (c • a)) 0
    rw [h]
    exact DifferentiableAt.const_smul ha c

variable [CompleteSpace H]

/-- **The generator of a unitary group**: `A ψ = -i d/dt U t ψ |_{t = 0}` on `generatorDomain`, so that
formally `U t = exp (i t A)`. -/
noncomputable def generator (U : UnitaryGroup H) : H →ₗ.[ℂ] H where
  domain := U.generatorDomain
  toFun :=
    { toFun := fun ψ => (-Complex.I) • deriv (fun t => U t ψ.1) 0
      map_add' := by
        intro a b
        have ha : DifferentiableAt ℝ (fun t => U t a.1) 0 := a.2
        have hb : DifferentiableAt ℝ (fun t => U t b.1) 0 := b.2
        have h : (fun t => U t ((a + b : U.generatorDomain) : H)) =
            fun t => U t a.1 + U t b.1 := by
          funext t; exact map_add _ _ _
        show (-Complex.I) • deriv (fun t => U t ((a + b : U.generatorDomain) : H)) 0 = _
        rw [h]
        have hd := deriv_add ha hb
        rw [show ((fun t => U t a.1) + fun t => U t b.1) = fun t => U t a.1 + U t b.1 from rfl] at hd
        rw [hd, smul_add]
      map_smul' := by
        intro c a
        have ha : DifferentiableAt ℝ (fun t => U t a.1) 0 := a.2
        have h : (fun t => U t ((c • a : U.generatorDomain) : H)) = fun t => c • U t a.1 := by
          funext t; exact map_smul _ _ _
        show (-Complex.I) • deriv (fun t => U t ((c • a : U.generatorDomain) : H)) 0 = c • _
        rw [h]
        have hd := deriv_const_smul c ha
        rw [show (c • fun t => U t a.1) = fun t => c • U t a.1 from rfl] at hd
        rw [hd, smul_comm] }

end UnitaryGroup

end Lightlike.OperatorAlgebras
