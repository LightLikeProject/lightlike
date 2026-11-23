module

public import Mathlib

/-!
# Swampland conjectures as explicit hypotheses on a scalar potential (row G1-046, milestone CO23)

Units `8πG = 1` (reduced Planck mass `1`), field space an inner-product space `E` with the flat
metric. Nothing here is a claim about nature: each conjecture is a `Prop` about a potential
`V : E → ℝ` (or a mass function), and every result is a theorem from it.

* `gradNorm V φ` : `|∇V|(φ)`, the norm of `fderiv ℝ V φ` (the dual norm, which is the norm of the
  gradient in an inner-product space).
* `DeSitterConjecture c V` : `|∇V| ≥ c V` wherever `V > 0` (obied-2018, Section 2).
* `RefinedDeSitterConjecture c c' V` : at every point with `V > 0`, either `|∇V| ≥ c V` or the
  Hessian has a direction of curvature `≤ -c' V` (the refinement reviewed in palti-2019).
* `DistanceConjecture m φ₀ α` : a tower mass `m` decays exponentially in the field distance
  (ooguri-vafa-2006, Section 2).
* `slowRollEps V φ` : the first slow-roll parameter `ε_V = ½ (|∇V|/V)²`.

Checks proved here (in `Lightlike/Rows/G1_046/Checks.lean`): the exponential potential satisfies the
de Sitter conjecture with `c = λ`, a potential with a de Sitter critical point violates it, and
slow roll (`ε_V < 1`) contradicts it for `c > √2`.
-/

@[expose] public section

namespace Lightlike.Rows.G1_046

open Real

section Defs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `|∇V|(φ)`: the norm of the differential of `V` at `φ`. -/
noncomputable def gradNorm (V : E → ℝ) (φ : E) : ℝ := ‖fderiv ℝ V φ‖

/-- **The de Sitter conjecture** `|∇V|/V ≥ c`, stated as a hypothesis on the potential `V`:
at every point where `V > 0`, `c · V φ ≤ |∇V|(φ)`. -/
def DeSitterConjecture (c : ℝ) (V : E → ℝ) : Prop :=
  ∀ φ, 0 < V φ → c * V φ ≤ gradNorm V φ

/-- **The refined de Sitter conjecture**: at every point where `V > 0`, either `|∇V| ≥ c V` or the
Hessian has a unit direction `v` with `∇²V(v, v) ≤ -c' V` (the smallest Hessian eigenvalue is at
most `-c' V`). -/
def RefinedDeSitterConjecture (c c' : ℝ) (V : E → ℝ) : Prop :=
  ∀ φ, 0 < V φ → c * V φ ≤ gradNorm V φ ∨
    ∃ v : E, ‖v‖ = 1 ∧ iteratedFDeriv ℝ 2 V φ ![v, v] ≤ -c' * V φ

/-- **The distance conjecture** as a hypothesis on a tower mass `m` around a base point `φ₀`:
there are `α > 0`, `C` and `D` such that `0 ≤ m φ ≤ C e^{-α d(φ, φ₀)}` once `d(φ, φ₀) ≥ D`. -/
def DistanceConjecture (m : E → ℝ) (φ₀ : E) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∃ C D : ℝ, ∀ φ, D ≤ dist φ φ₀ →
    0 ≤ m φ ∧ m φ ≤ C * Real.exp (-α * dist φ φ₀)

/-- The first slow-roll parameter `ε_V = ½ (|∇V|/V)²` (units `8πG = 1`). -/
noncomputable def slowRollEps (V : E → ℝ) (φ : E) : ℝ := (gradNorm V φ / V φ) ^ 2 / 2

end Defs

/-- The exponential potential `V₀ e^{-λφ}` on a single field. -/
noncomputable def expPotential (V₀ l : ℝ) : ℝ → ℝ := fun φ => V₀ * Real.exp (-(l * φ))

/-- The potential `Λ + m² φ² / 2` on a single field (a de Sitter critical point at `φ = 0`). -/
noncomputable def quadPotential (Λ m : ℝ) : ℝ → ℝ := fun φ => Λ + m ^ 2 * φ ^ 2 / 2

theorem hasDerivAt_expPotential (V₀ l φ : ℝ) :
    HasDerivAt (expPotential V₀ l) (-l * expPotential V₀ l φ) φ := by
  have h : HasDerivAt (fun y => V₀ * Real.exp (-(l * y)))
      (V₀ * (Real.exp (-(l * φ)) * (-(l * 1)))) φ :=
    (((hasDerivAt_id' φ).const_mul l).fun_neg.exp).const_mul V₀
  unfold expPotential
  convert h using 1
  ring

theorem hasDerivAt_quadPotential (Λ m φ : ℝ) :
    HasDerivAt (quadPotential Λ m) (m ^ 2 * φ) φ := by
  have h : HasDerivAt (fun y => Λ + m ^ 2 * y ^ 2 / 2)
      (m ^ 2 * (↑2 * φ ^ (2 - 1) * 1) / 2) φ :=
    ((((hasDerivAt_id' φ).pow 2).const_mul (m ^ 2)).div_const 2).const_add Λ
  unfold quadPotential
  convert h using 1
  push_cast
  ring

/-- On a single field, `|∇V| = |V'|`. -/
theorem gradNorm_real (V : ℝ → ℝ) (φ : ℝ) : gradNorm V φ = |deriv V φ| := by
  unfold gradNorm
  rw [← norm_deriv_eq_norm_fderiv, Real.norm_eq_abs]

end Lightlike.Rows.G1_046
