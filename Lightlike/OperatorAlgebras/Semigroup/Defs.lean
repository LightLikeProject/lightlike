import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Contraction semigroups and their generators

A *contraction semigroup* on a Banach space `X` over `𝕜 = ℝ` or `ℂ` is a family `S t : X →L[𝕜] X`,
`t ≥ 0`, with `S 0 = 1`, `S (s + t) = S s ∘ S t`, `‖S t‖ ≤ 1`, and strongly continuous at `0`: `S t x → x`
as `t → 0⁺`. Its *generator* is the operator `A x = lim_{t→0⁺} (S t x - x) / t`, defined on the `x` for
which the limit exists (`ContractionSemigroup.generator`, a `LinearPMap`).

The definitions are the standard ones (see the Math 7334 lecture notes, Georgia Tech, Spring 2017,
Section 1, <https://loss.math.gatech.edu/17SPRINGTEA/7334/NOTES/section4hilleyosida.pdf>, Definitions 1.1
and 1.2 and the generator before Theorem 1.3). The overall structure was cross-checked against the Lean 4
package `hille-yosida` of M. Douglas (`mrdouglasny/hille-yosida`, v0.1.0, Apache-2.0), which is not a
dependency; the definitions here were written independently.

## Main definitions

* `ContractionSemigroup 𝕜 X`: the semigroup.
* `ContractionSemigroup.IsGeneratorDomain S x`: the difference quotient converges at `x`.
* `ContractionSemigroup.generator S`: the generator, as a `LinearPMap`.
-/

open Filter Topology NNReal
open scoped LinearPMap

noncomputable section

namespace Lightlike.OperatorAlgebras

variable (𝕜 : Type*) [RCLike 𝕜] (X : Type*) [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- A **contraction semigroup** on `X`: `S t`, `t ≥ 0`, with `S 0 = 1`, `S (s + t) = S s ∘ S t`,
`‖S t‖ ≤ 1`, strongly continuous at `0`. -/
structure ContractionSemigroup where
  /-- The operators `S t`. -/
  S : ℝ≥0 → X →L[𝕜] X
  /-- `S 0` is the identity. -/
  zero : S 0 = 1
  /-- The semigroup law. -/
  add : ∀ s t, S (s + t) = (S s).comp (S t)
  /-- Each `S t` is a contraction. -/
  norm_le : ∀ t, ‖S t‖ ≤ 1
  /-- Strong continuity at `0`. -/
  tendsto_zero : ∀ x, Tendsto (fun t : ℝ≥0 => S t x) (𝓝 0) (𝓝 x)

variable {𝕜 X}

namespace ContractionSemigroup

variable (S : ContractionSemigroup 𝕜 X)

instance : CoeFun (ContractionSemigroup 𝕜 X) (fun _ => ℝ≥0 → X →L[𝕜] X) := ⟨ContractionSemigroup.S⟩

/-- The difference quotient `t⁻¹ (S t x - x)`. -/
def quot (t : ℝ≥0) (x : X) : X := (((t : ℝ)⁻¹ : ℝ) : 𝕜) • (S t x - x)

lemma quot_add (t : ℝ≥0) (x y : X) : S.quot t (x + y) = S.quot t x + S.quot t y := by
  simp only [quot, map_add]
  rw [← smul_add]
  congr 1
  abel

lemma quot_smul (t : ℝ≥0) (c : 𝕜) (x : X) : S.quot t (c • x) = c • S.quot t x := by
  simp only [quot, map_smul]
  rw [← smul_sub, smul_comm]

/-- `x` is in the **domain of the generator** if the difference quotient `t⁻¹ (S t x - x)` converges as
`t → 0⁺`. -/
def IsGeneratorDomain (x : X) : Prop :=
  ∃ y : X, Tendsto (fun t : ℝ≥0 => S.quot t x) (𝓝[>] 0) (𝓝 y)

/-- The domain of the generator is a subspace. -/
def generatorDomain : Submodule 𝕜 X where
  carrier := {x | S.IsGeneratorDomain x}
  zero_mem' := ⟨0, by simp [quot]⟩
  add_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, (ha.add hb).congr fun t => (S.quot_add t x y).symm⟩
  smul_mem' := by
    rintro c x ⟨a, ha⟩
    exact ⟨c • a, (ha.const_smul c).congr fun t => (S.quot_smul t c x).symm⟩

variable [T2Space X]

set_option linter.unusedSectionVars false

open Classical in
/-- The value of the generator at `x` (the limit of the difference quotient; `0` outside the domain). -/
def genVal (x : X) : X := if h : S.IsGeneratorDomain x then h.choose else 0

lemma tendsto_genVal {x : X} (hx : S.IsGeneratorDomain x) :
    Tendsto (fun t : ℝ≥0 => S.quot t x) (𝓝[>] 0) (𝓝 (S.genVal x)) := by
  rw [genVal, dif_pos hx]
  exact hx.choose_spec

/-- The **generator** of the semigroup, as a partially defined linear map. -/
def generator : X →ₗ.[𝕜] X where
  domain := S.generatorDomain
  toFun :=
    { toFun := fun x => S.genVal (x : X)
      map_add' := fun x y => by
        refine tendsto_nhds_unique (S.tendsto_genVal (x + y).2) ?_
        have := (S.tendsto_genVal x.2).add (S.tendsto_genVal y.2)
        refine this.congr fun t => ?_
        simp [S.quot_add]
      map_smul' := fun c x => by
        refine tendsto_nhds_unique (S.tendsto_genVal (c • x).2) ?_
        have := (S.tendsto_genVal x.2).const_smul c
        refine this.congr fun t => ?_
        simp [S.quot_smul] }

end ContractionSemigroup

end Lightlike.OperatorAlgebras
