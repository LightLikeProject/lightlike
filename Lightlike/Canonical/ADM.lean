import Mathlib
import Lightlike.Spacetime.Curvature

/-!
# The ADM constraints and their smeared form, in coordinates

The definitions of milestone CA1 in the coordinate form: the canonical data of the ADM formulation of
general relativity on a spatial slice `ℝᵈ` (a chart; no foliated spacetime yet), the Hamiltonian and momentum
constraints, and the bracket of smeared constraints computed on test fields.

* **Data.** A spatial metric `h : ℝᵈ → Matrix (Fin d) (Fin d) ℝ` (components `h_ij(x)`) and a momentum
  density `π : ℝᵈ → Matrix (Fin d) (Fin d) ℝ` (components `π^{ij}(x)`, a tensor density of weight one).
  The spatial curvature is `Lightlike.scalarCurvature h` of `Lightlike/Spacetime/Curvature.lean`: no
  curvature is defined here.
* **Constraints.** `hamiltonianDensity h π = (tr (hπhπ) − (tr hπ)²/(d − 1))/√det h − √det h · R[h]`
  (units `16πG = 1`) and `momentumDensity ξ h π = π^{ij} (ℒ_ξ h)_ij`, the form obtained from
  `−2 ξ^i h_ij ∇_k π^{jk}` by an integration by parts (no boundary term for a compactly supported `ξ`).
  The smeared constraints are `H[N] = ∫ N ℋ` and `D[ξ] = ∫ π^{ij} ℒ_ξ h_ij`.
* **Bracket on test fields.** For functionals `F, G` of `(h, π)` the field-theoretic bracket
  `{F,G} = ∫ (δF/δh_ij δG/δπ^ij − δF/δπ^ij δG/δh_ij)` is computed without functional derivatives with
  respect to `h`: `∫ δF/δh · δG/δπ` is the derivative of `F` along the `h`-variation `δG/δπ`. So
  `admBracket F G Fπ Gπ h π = dF_{(h,π)}[(Gπ, 0)] − dG_{(h,π)}[(Fπ, 0)]`, where `Fπ`, `Gπ` are the
  `π`-gradients (`IsPiGradient`), which for the constraints are explicit algebraic expressions.
  Derivatives are Gateaux derivatives `d/dt|₀` along compactly supported variations; nothing is an
  infinite-dimensional reduction.

Conventions to be compared with Hojman–Kuchař–Teitelboim 1976 (that source has not been read at the
cited location): units, the sign of the bracket, and the sign convention of the Lie bracket of vector
fields `[ξ,η]^k = ξ^j ∂_j η^k − η^j ∂_j ξ^k`.
-/

open MeasureTheory Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike.Canonical

variable {d : ℕ}

/-- A tensor field on the chart `ℝᵈ`: its components `T_ij(x)` or `T^ij(x)`. -/
abbrev TensorField (d : ℕ) := (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ

/-- A vector field on the chart: its components `ξ^k(x)`. -/
abbrev VectorField (d : ℕ) := (Fin d → ℝ) → Fin d → ℝ

/-- The Lie derivative of a covariant 2-tensor, `(ℒ_ξ h)_ij = ξ^k ∂_k h_ij + h_kj ∂_i ξ^k + h_ik ∂_j ξ^k`. -/
def lieDeriv (ξ : VectorField d) (h : TensorField d) (i j : Fin d) (x : Fin d → ℝ) : ℝ :=
  ∑ k, ξ x k * Lightlike.pd k (fun y => h y i j) x +
    ∑ k, h x k j * Lightlike.pd i (fun y => ξ y k) x +
    ∑ k, h x i k * Lightlike.pd j (fun y => ξ y k) x

/-- The Lie derivative `ℒ_ξ h` as a tensor field (a matrix at every point). -/
def lieTensor (ξ : VectorField d) (h : TensorField d) : TensorField d :=
  fun x => Matrix.of fun i j => lieDeriv ξ h i j x

/-- The Lie bracket of vector fields, `[ξ,η]^k = ξ^j ∂_j η^k − η^j ∂_j ξ^k`. -/
def lieBracket (ξ η : VectorField d) (x : Fin d → ℝ) (k : Fin d) : ℝ :=
  ∑ j, (ξ x j * Lightlike.pd j (fun y => η y k) x - η x j * Lightlike.pd j (fun y => ξ y k) x)

/-- The momentum constraint density of the smearing `ξ`: `π^{ij} (ℒ_ξ h)_ij`; its integral is
`∫ ξ^i R_i` with the ADM 1962 eq. (3.14b) `R_i = −2 π^{ij}{}_{|j}`, after an integration by parts.

**Differences from the cited sources, approved by the maintainers (17 November 2026): (a) same setting as the source, (b) partial, (c) convention, (d) and (e) representation** (compared with ADM 1962 eqs. (3.14a), (3.14b) at that location, and with Thiemann, arXiv:gr-qc/0110034, §I.1.1, eqs. (I.1.1.27), (I.1.1.28), (I.1.1.36), (I.1.1.37) (the lecture-note version of the cited book); Hojman-Kuchar-Teitelboim 1976 has not been read): (a) `C^∞` data and compactly supported test fields
(`π` only continuous for `{D, D}`); (b) one global chart `ℝᵈ`, no manifold and no foliation; (c) units
`16πG = 1`, and the kinetic coefficient `1/(d - 1)` in dimension `d` (ADM: `1/2` for `d = 3`); (d) the momentum constraint in the Lie-derivative form `π^{ij} ℒ_ξ h_ij`, equal to the ADM
`∫ ξ^i (−2 π^{ij}{}_{|j})` by an integration by parts, formalised as `Lightlike.Canonical.momentumConstraint_eq_adm_of_smooth`; (e) the bracket is defined
through `π`-gradients and Gateaux derivatives, without `δ/δh`, and the signs of the bracket and of the Lie
bracket `[ξ,η]` are fixed here by `admBracket` and `lieBracket`. -/
def momentumDensity (ξ : VectorField d) (h π : TensorField d) (x : Fin d → ℝ) : ℝ :=
  ∑ i, ∑ j, π x i j * lieDeriv ξ h i j x

/-- The kinetic part of the Hamiltonian constraint, `(tr (hπhπ) − (tr hπ)²/(d − 1))/√det h`. For `d = 3`
this is the ADM `(π^{ij}π_ij − ½π²)/√g`; the coefficient `1/(d − 1)` is the one for which the algebra of the
constraints closes in dimension `d` (for `d = 1` it is the Lean junk value `0`, so `2 ≤ d` is assumed
wherever the algebra is stated). Why `1/(d - 1)`: the Legendre transform gives `π^{ij} = √h (K^{ij} − K h^{ij})`,
so `tr π = √h K (1 − d)`, and the kinetic term `K_ij K^ij − K²` becomes `π^{ij}π_ij − π²/(d − 1)`, which is
`π^{ij}π_ij − π²/2` only at `d = 3`. A grid computation in dimension two (`scripts/adm_algebra_check.py`,
numerical evidence) gives `{H[N],H[M]} = 4.97 = D[Y]` with this coefficient and `2.68` with `1/2`. -/
def kineticDensity (h π : TensorField d) (x : Fin d → ℝ) : ℝ :=
  ((h x * π x * h x * π x).trace - (1 / ((d : ℝ) - 1)) * ((h x * π x).trace) ^ 2) / Real.sqrt (h x).det

/-- The `π`-gradient of the smeared Hamiltonian constraint `H[N]`, as a covariant tensor field:
`δH[N]/δπ^{ij} = N (2 (hπh)_ji − (2/(d − 1)) (tr hπ) h_ji)/√det h` (the transpose is only visible for
non-symmetric data). -/
def hamiltonianPiGradient (N : (Fin d → ℝ) → ℝ) (h π : TensorField d) : TensorField d :=
  fun x => ((N x / Real.sqrt (h x).det) •
    (2 • (h x * π x * h x) - (2 / ((d : ℝ) - 1) * (h x * π x).trace) • h x)).transpose

/-- The Hamiltonian constraint density `ℋ = (tr (hπhπ) − (tr hπ)²/(d − 1))/√det h − √det h · R[h]`, with the
spatial scalar curvature `R` of `Lightlike.scalarCurvature` (units `16πG = 1`). For `d = 3` this is ADM 1962 eq.
(3.14a), `R⁰ = −√g [³R + g⁻¹(½π² − π^{ij}π_ij)]`.

**Differences from the cited sources, approved by the maintainers (17 November 2026): (a) same setting as the source, (b) partial, (c) convention, (d) and (e) representation** (compared with ADM 1962 eqs. (3.14a), (3.14b) at that location, and with Thiemann, arXiv:gr-qc/0110034, §I.1.1, eqs. (I.1.1.27), (I.1.1.28), (I.1.1.36), (I.1.1.37) (the lecture-note version of the cited book); Hojman-Kuchar-Teitelboim 1976 has not been read): (a) `C^∞` data and compactly supported test fields
(`π` only continuous for `{D, D}`); (b) one global chart `ℝᵈ`, no manifold and no foliation; (c) units
`16πG = 1`, and the kinetic coefficient `1/(d - 1)` in dimension `d` (ADM: `1/2` for `d = 3`); (d) the momentum constraint in the Lie-derivative form `π^{ij} ℒ_ξ h_ij`, equal to the ADM
`∫ ξ^i (−2 π^{ij}{}_{|j})` by an integration by parts, formalised as `Lightlike.Canonical.momentumConstraint_eq_adm_of_smooth`; (e) the bracket is defined
through `π`-gradients and Gateaux derivatives, without `δ/δh`, and the signs of the bracket and of the Lie
bracket `[ξ,η]` are fixed here by `admBracket` and `lieBracket`. -/
def hamiltonianDensity (h π : TensorField d) (x : Fin d → ℝ) : ℝ :=
  kineticDensity h π x - Real.sqrt (h x).det * Lightlike.scalarCurvature h x

/-- The smeared Hamiltonian constraint `H[N] = ∫ N ℋ dx` (`N` the lapse test function). -/
def hamiltonianConstraint (N : (Fin d → ℝ) → ℝ) (h π : TensorField d) : ℝ :=
  ∫ x, N x * hamiltonianDensity h π x

/-- The smeared momentum constraint `D[ξ] = ∫ π^{ij} (ℒ_ξ h)_ij dx` (`ξ` the shift test field). -/
def momentumConstraint (ξ : VectorField d) (h π : TensorField d) : ℝ :=
  ∫ x, momentumDensity ξ h π x

/-- Data `(h, π)` satisfy the Hamiltonian constraint at `x`. -/
def HamiltonianConstraintAt (h π : TensorField d) (x : Fin d → ℝ) : Prop :=
  hamiltonianDensity h π x = 0

/-- The covariant divergence of the momentum density, `∇_k π^{ik} = ∂_k π^{ik} + Γ^i_{kl} π^{kl}`
(for a symmetric tensor density of weight one), with the Christoffel symbols of
`Lightlike.christoffel`. -/
def momentumDivergence (h π : TensorField d) (i : Fin d) (x : Fin d → ℝ) : ℝ :=
  ∑ k, Lightlike.pd k (fun y => π y i k) x + ∑ k, ∑ l, Lightlike.christoffel h i k l x * π x k l

/-- Data `(h, π)` satisfy the momentum constraint at `x`: `∇_k π^{ik} = 0` for every `i`. -/
def MomentumConstraintAt (h π : TensorField d) (x : Fin d → ℝ) : Prop :=
  ∀ i, momentumDivergence h π i x = 0

/-! ### The bracket on test fields -/

/-- The Gateaux derivative of a functional `F` of `(h, π)` at `(h, π)` in the direction `(k, p)`:
`d/dt|₀ F (h + t k, π + t p)`. -/
def dirDeriv (F : TensorField d → TensorField d → ℝ) (h π k p : TensorField d) : ℝ :=
  deriv (fun t : ℝ => F (fun x => h x + t • k x) (fun x => π x + t • p x)) 0

/-- The **admissible data** of the ADM formulation: a smooth, positive definite spatial metric and a continuous
momentum density. -/
def Admissible (h π : TensorField d) : Prop :=
  (∀ i j, ContDiff ℝ ∞ (fun x => h x i j)) ∧ (∀ x, (h x).PosDef) ∧ ∀ i j, Continuous (fun x => π x i j)

/-- `Fπ` is the **`π`-gradient** of the functional `F` on admissible data: for every admissible `(h, π)` and
compactly supported smooth variation `p` of `π`, `dF[(0, p)] = ∫ ∑_ij (Fπ)_ij p^{ij} dx`
(so `Fπ = δF/δπ^{ij}`, a covariant tensor field). -/
def IsPiGradient (F : TensorField d → TensorField d → ℝ) (Fπ : TensorField d → TensorField d → TensorField d) : Prop :=
  ∀ h π p : TensorField d, Admissible h π →
    (∀ i j, HasCompactSupport (fun x => p x i j)) → (∀ i j, ContDiff ℝ ∞ (fun x => p x i j)) →
    dirDeriv F h π 0 p = ∫ x, ∑ i, ∑ j, Fπ h π x i j * p x i j

/-- The bracket of two functionals of `(h, π)` with `π`-gradients `Fπ`, `Gπ`:
`{F,G} = dF[(δG/δπ, 0)] − dG[(δF/δπ, 0)]`, the field-theoretic `∫ (δF/δh δG/δπ − δF/δπ δG/δh)`.

**Differences from the cited sources, approved by the maintainers (17 November 2026): (a) same setting as the source, (b) partial, (c) convention, (d) and (e) representation** (compared with ADM 1962 eqs. (3.14a), (3.14b) at that location, and with Thiemann, arXiv:gr-qc/0110034, §I.1.1, eqs. (I.1.1.27), (I.1.1.28), (I.1.1.36), (I.1.1.37) (the lecture-note version of the cited book); Hojman-Kuchar-Teitelboim 1976 has not been read): (a) `C^∞` data and compactly supported test fields
(`π` only continuous for `{D, D}`); (b) one global chart `ℝᵈ`, no manifold and no foliation; (c) units
`16πG = 1`, and the kinetic coefficient `1/(d - 1)` in dimension `d` (ADM: `1/2` for `d = 3`); (d) the momentum constraint in the Lie-derivative form `π^{ij} ℒ_ξ h_ij`, equal to the ADM
`∫ ξ^i (−2 π^{ij}{}_{|j})` by an integration by parts, formalised as `Lightlike.Canonical.momentumConstraint_eq_adm_of_smooth`; (e) the bracket is defined
through `π`-gradients and Gateaux derivatives, without `δ/δh`, and the signs of the bracket and of the Lie
bracket `[ξ,η]` are fixed here by `admBracket` and `lieBracket`. -/
def admBracket (F G : TensorField d → TensorField d → ℝ) (Fπ Gπ : TensorField d → TensorField d → TensorField d)
    (h π : TensorField d) : ℝ :=
  dirDeriv F h π (Gπ h π) 0 - dirDeriv G h π (Fπ h π) 0

end Lightlike.Canonical
