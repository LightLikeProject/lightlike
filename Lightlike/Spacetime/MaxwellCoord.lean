import Lightlike.Spacetime.Curvature

/-!
# The source-free Maxwell equations in coordinates

For a coordinate metric `g` and a field strength `F` (matrix-valued functions of the coordinates on an open set
`U ⊆ ℝⁿ`), `IsSourceFreeMaxwell g F U` says: `F` is antisymmetric, `dF = 0`
(`∂_μ F_{νρ} + ∂_ν F_{ρμ} + ∂_ρ F_{μν} = 0`) and `∂_μ(√|det g| F^{μν}) = 0` with `F^{μν} = g^{μα} g^{νβ} F_{αβ}`.

Source read (pdftotext): S. M. Carroll, *Lecture Notes on General Relativity*, arXiv:gr-qc/9712019: the curved-space
Maxwell equations `∇_μ F^{νμ} = 4π J^ν` (4.24) and `∇_[μ F_{νλ]} = 0` (4.25), p. 107; the source-free form
`g^{μν} ∇_μ F_{νσ} = 0`, `∇_[μ F_{νρ]} = 0` (7.109), p. 201; the divergence of a vector
`∇_μ V^μ = |g|^{-1/2} ∂_μ(|g|^{1/2} V^μ)` (3.28), p. 61; `∇_[μ ω_ν] = ∂_[μ ω_ν]` for a symmetric connection (3.29),
p. 62. **Difference (representation):** the equations are stated in the coordinate form above; the equivalence of
`∂_μ(√|g| F^{μν}) = 0` with `∇_μ F^{μν} = 0` for antisymmetric `F` (the analogue of (3.28) for an antisymmetric
tensor, not stated in the source) and of the cyclic sum of partial derivatives with `∇_[μ F_{νρ]}` (from (3.29)) is
not proved here.

Physlib's electromagnetism (`Physlib/Electromagnetism`, read-only check) is formulated on flat Minkowski space
`SpaceTime d`; it has no curved-metric Maxwell equations, so this coordinate form is new (named difference: a curved
coordinate metric instead of Minkowski space).

Supporting definition for gap row G3-056 (Reissner–Nordström, `Lightlike/GR/ReissnerNordstrom.lean`).
-/

open Matrix

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- `F^{μν} = g^{μα} g^{νβ} F_{αβ}`, the field strength with both indices raised (`g` symmetric). -/
def raiseBoth (G F : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := G⁻¹ * F * G⁻¹

/-- **The source-free Maxwell equations in coordinates** for the metric `g` and the field strength `F` on `U`. -/
structure IsSourceFreeMaxwell (g F : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (U : Set (Fin n → ℝ)) : Prop where
  /-- `F` is a 2-form. -/
  antisymm : ∀ x ∈ U, (F x)ᵀ = -F x
  /-- `dF = 0`. -/
  closed : ∀ x ∈ U, ∀ μ ν ρ : Fin n,
    pd μ (fun y => F y ν ρ) x + pd ν (fun y => F y ρ μ) x + pd ρ (fun y => F y μ ν) x = 0
  /-- `∂_μ(√|det g| F^{μν}) = 0`. -/
  divergence : ∀ x ∈ U, ∀ ν : Fin n,
    ∑ μ, pd μ (fun y => Real.sqrt |(g y).det| * raiseBoth (g y) (F y) μ ν) x = 0

end Lightlike
