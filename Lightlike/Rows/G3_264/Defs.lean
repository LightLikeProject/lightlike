module

public import Mathlib

/-!
# The Einstein–Hilbert truncation as an ODE system for `(g, λ)`: the vector field

Row G3-264 (task T-AS2). The Einstein–Hilbert truncation of the functional renormalization
group for gravity (Reuter 1998, `reuter-1998`) is a two-dimensional flow for the dimensionless
Newton constant `g = G_k k²` and the dimensionless cosmological constant `λ = Λ_k / k²`, with
`t = log k`:

```
∂ₜ g = (2 + η) g ,
∂ₜ λ = −(2 − η) λ + (g / 4π) · (10 / x − 8 − (5/3) η / x) ,     x = 1 − 2λ ,
η    = g B₁(λ) / (1 − g B₂(λ)) .
```

Here `η` is the anomalous dimension of Newton's constant. With the optimized cutoff (Litim 2004,
`litim-2004`; shape function `R₀(z) = (1 − z) θ(1 − z)`) in `d = 4` the threshold functions are
`Φᵖₙ(w) = 1 / (Γ(n+1) (1+w)ᵖ)` and `Φ̃ᵖₙ(w) = 1 / (Γ(n+2) (1+w)ᵖ)`, and the coefficient
functions evaluate to

```
B₁(λ) = (1 / 3π) (5 / x − 9 / x² − 7) ,
B₂(λ) = (1 / 12π) (6 / x² − 5 / x) .
```

These closed forms were reduced by hand from the general-`d` expressions of the Einstein–Hilbert
literature; no equation number of the sources is claimed here. The numbers they give (fixed point
`g* ≈ 0.707`, `λ* ≈ 0.193`) agree with Litim's optimized-cutoff values, and the file
`Lightlike/Rows/G3_264/FixedPoint.lean` proves them for this ODE. The statements concern the ODE
only, not the field theory it truncates.

Main definitions
* `EH.denom`, `EH.B1`, `EH.B2`: `x = 1 − 2λ` and the coefficient functions.
* `EH.eta`: the anomalous dimension.
* `EH.betaG`, `EH.betaLam`: the beta functions of `g` and `λ`.
* `EH.field`: the vector field `(g, λ) ↦ (β_g, β_λ)`.
-/

@[expose] public section

noncomputable section

namespace Lightlike.AsymptoticSafety.EH

open Real

/-- `x = 1 − 2λ`, the denominator of the optimized threshold functions. -/
def denom (lam : ℝ) : ℝ := 1 - 2 * lam

/-- The coefficient `B₁(λ)` (optimized cutoff, `d = 4`). -/
def B1 (lam : ℝ) : ℝ :=
  (1 / (3 * π)) * (5 / denom lam - 9 / denom lam ^ 2 - 7)

/-- The coefficient `B₂(λ)` (optimized cutoff, `d = 4`). -/
def B2 (lam : ℝ) : ℝ :=
  (1 / (12 * π)) * (6 / denom lam ^ 2 - 5 / denom lam)

/-- The anomalous dimension `η(g, λ) = g B₁ / (1 − g B₂)`. -/
def eta (g lam : ℝ) : ℝ := g * B1 lam / (1 - g * B2 lam)

/-- `β_g = (2 + η) g`. -/
def betaG (g lam : ℝ) : ℝ := (2 + eta g lam) * g

/-- `β_λ = −(2 − η) λ + (g / 4π) (10/x − 8 − (5/3) η / x)`. -/
def betaLam (g lam : ℝ) : ℝ :=
  -(2 - eta g lam) * lam
    + g / (4 * π) * (10 / denom lam - 8 - (5 / 3) * eta g lam / denom lam)

/-- The vector field `(g, λ) ↦ (β_g, β_λ)` of the Einstein–Hilbert ODE `∂ₜ(g, λ) = field (g, λ)`. -/
def field (p : ℝ × ℝ) : ℝ × ℝ := (betaG p.1 p.2, betaLam p.1 p.2)

/-- The Gaussian fixed point `(0, 0)` is a zero of the vector field. -/
theorem field_gaussian : field (0, 0) = 0 := by
  simp [field, betaG, betaLam, eta, B1, B2, denom]

end Lightlike.AsymptoticSafety.EH
