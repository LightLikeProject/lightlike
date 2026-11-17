import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Physlib.ClassicalMechanics.HamiltonianMechanics.PoissonBracket
import PhyslibAlpha.ClassicalMechanics.MomentMap.Basic

/-!
# Constrained Hamiltonian systems on a flat phase space

The core definitions of milestone GC4, on the phase space `X × X` of Physlib (`X` a real inner product space, a
point `(p, q)` with `p` a momentum and `q` a position, an observable a function `f p q`), with Physlib's Poisson
bracket `{f, g} = ⟨∂_q f, ∂_p g⟩ - ⟨∂_p f, ∂_q g⟩` (`ClassicalMechanics.poissonBracket`) and its
`IsSymplecticForm` (the moment-map file). Finite dimensions only, no manifolds.

* `phaseGrad`, `gradForm`, `poissonBracket_eq_gradForm`, `isSymplecticForm_gradForm`: the bracket is
  `Ω (∇f, ∇g)` for the standard form `Ω`, which is a symplectic form in Physlib's sense.
* `constraintSet`, `IsRegularConstraints`: the constraint surface as the zero set of a submersion (the gradients of
  the constraints are linearly independent on it).
* `bracketMatrix`, `IsFirstClass`, `IsSecondClass`, `bracketRank`: the classification by the bracket matrix
  `C_{ab} = {φ_a, φ_b}` (Dirac); a constraint is first class when its brackets with the constraints vanish on the
  surface and second class when `C` is nonsingular.
* `reducedDim`, `reducedDimAllFirstClass`: the count of degrees of freedom, `2n - 2m + r` for `m` independent
  constraints with bracket matrix of rank `r`, and the wrong count `2n - 2m` of treating all as first class.
* `diracBracket`: `{f, g}_D = {f, g} - Σ {f, φ_a} (C⁻¹)_{ab} {φ_b, g}`.
* `orbitDirections`, `momentTangent`: for a linear symplectic action (Physlib's `AffineSymplecticAction`) the
  tangent space of an orbit and of a level set of its moment map, for the reduction of Marsden and Weinstein
  without quotient manifolds.

The proved basic API is `Lightlike/Gauge/ConstraintsAPI.lean`; the Jacobi identities of the Poisson and of the
Dirac bracket are in `Lightlike/Gauge/PoissonJacobi.lean` and `Lightlike/Gauge/DiracJacobi.lean`; the example of
the particle on a circle and the wrong count are in `Lightlike/Tests/Constraints.lean`.

## References

* M. Henneaux and C. Teitelboim, *Quantization of Gauge Systems*, Princeton University Press (1992), Chapter 1:
  constrained Hamiltonian systems, first- and second-class constraints, the Dirac bracket.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Math. 1764, Springer (2001), the
  Marsden-Weinstein-Meyer theorem.
-/

open InnerProductSpace
open ClassicalMechanics
open scoped ContDiff

namespace Lightlike.Gauge

variable {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

/-- The phase space of a particle with configuration space `X`, in Physlib's convention: a point is
`(p, q) ∈ X × X`, `p` a momentum and `q` a position, and an observable is a function `f p q`. -/
noncomputable def phaseGrad (f : X → X → ℝ) (p q : X) : X × X :=
  (gradient (fun p' => f p' q) p, gradient (fun q' => f p q') q)

/-- The standard bilinear form on gradients, `Ω (u, v) = ⟨u_q, v_p⟩ - ⟨u_p, v_q⟩`: the Poisson bracket of
Physlib is `{f, g} = Ω (∇f, ∇g)`. -/
noncomputable def gradForm : LinearMap.BilinForm ℝ (X × X) :=
  LinearMap.mk₂ ℝ (fun u v => ⟪u.2, v.1⟫_ℝ - ⟪u.1, v.2⟫_ℝ)
    (fun u u' v => by simp [inner_add_left]; ring)
    (fun c u v => by simp [inner_smul_left]; ring)
    (fun u v v' => by simp [inner_add_right]; ring)
    (fun c u v => by simp [inner_smul_right]; ring)

/-- Physlib's Poisson bracket is `Ω (∇f, ∇g)`. -/
theorem poissonBracket_eq_gradForm (f g : X → X → ℝ) (p q : X) :
    poissonBracket f g p q = gradForm (phaseGrad f p q) (phaseGrad g p q) := rfl

omit [CompleteSpace X] in
/-- **The standard form on `X × X` is a symplectic form in Physlib's sense** (`IsSymplecticForm` of the moment
map file): alternating and non-degenerate. -/
theorem isSymplecticForm_gradForm : IsSymplecticForm (gradForm : LinearMap.BilinForm ℝ (X × X)) := by
  refine ⟨?_, ?_⟩
  · intro u
    simp only [gradForm, LinearMap.mk₂_apply]
    rw [real_inner_comm]; ring
  · constructor
    · intro u hu
      have h1 : ⟪u.2, u.2⟫_ℝ = 0 := by simpa [gradForm] using hu (u.2, 0)
      have h2 : ⟪u.1, u.1⟫_ℝ = 0 := by simpa [gradForm] using hu (0, u.1)
      exact Prod.ext (inner_self_eq_zero.mp h2) (inner_self_eq_zero.mp h1)
    · intro y hy
      have h1 : ⟪y.1, y.1⟫_ℝ = 0 := by simpa [gradForm] using hy (0, y.1)
      have h2 : ⟪y.2, y.2⟫_ℝ = 0 := by simpa [gradForm] using hy (y.2, 0)
      exact Prod.ext (inner_self_eq_zero.mp h1) (inner_self_eq_zero.mp h2)

section Constraints

variable {m : ℕ}

/-- The pairing of the gradient of an observable with a tangent vector of `X × X`:
`df(v) = ⟨∇_p f, v_p⟩ + ⟨∇_q f, v_q⟩`. -/
noncomputable def pairing (u v : X × X) : ℝ := ⟪u.1, v.1⟫_ℝ + ⟪u.2, v.2⟫_ℝ

/-- The constraint surface `Σ = {x | φ_a(x) = 0 for all a}` of `m` constraint functions on the phase space. -/
def constraintSet (φ : Fin m → X → X → ℝ) : Set (X × X) := {x | ∀ a, φ a x.1 x.2 = 0}

/-- **Regular constraints** (the constraint surface is the zero set of a submersion): the constraint functions
are smooth on the phase space and their gradients are linearly independent at every point of the surface
(equivalently the derivative of `φ = (φ_a)` is onto there). -/
def IsRegularConstraints (φ : Fin m → X → X → ℝ) : Prop :=
  (∀ a, ContDiff ℝ ∞ (fun x : X × X => φ a x.1 x.2)) ∧
    ∀ x ∈ constraintSet φ, LinearIndependent ℝ (fun a => phaseGrad (φ a) x.1 x.2)

/-- The matrix `C_{ab} = {φ_a, φ_b}` of the Poisson brackets of the constraints at a point. -/
noncomputable def bracketMatrix (φ : Fin m → X → X → ℝ) (p q : X) : Matrix (Fin m) (Fin m) ℝ :=
  fun a b => poissonBracket (φ a) (φ b) p q

/-- All constraints are **first class**: their brackets vanish on the constraint surface. -/
def IsFirstClass (φ : Fin m → X → X → ℝ) : Prop :=
  ∀ x ∈ constraintSet φ, bracketMatrix φ x.1 x.2 = 0

/-- All constraints are **second class**: the matrix of their brackets is nonsingular on the constraint surface
(Dirac). -/
def IsSecondClass (φ : Fin m → X → X → ℝ) : Prop :=
  ∀ x ∈ constraintSet φ, (bracketMatrix φ x.1 x.2).det ≠ 0

/-- The rank of the bracket matrix at a point: the number of second-class constraints among `m` independent
constraints where it is constant on the surface; the others (`m - rank`) are first class. -/
noncomputable def bracketRank (φ : Fin m → X → X → ℝ) (x : X × X) : ℕ :=
  (bracketMatrix φ x.1 x.2).rank

/-- **The dimension of the reduced phase space** of a phase space of dimension `2n` with `m` independent
constraints whose bracket matrix has rank `r` on the surface: `2n - 2 (m - r) - r = 2n - 2m + r` (each first-class
constraint removes two dimensions, each second-class one). -/
def reducedDim (n m r : ℕ) : ℕ := 2 * n - 2 * m + r

/-- The count of degrees of freedom if every constraint were treated as first class: `2n - 2m`. It is wrong
as soon as a constraint is second class (`reducedDim n m r` with `r > 0`). -/
def reducedDimAllFirstClass (n m : ℕ) : ℕ := 2 * n - 2 * m

/-- **The Dirac bracket** of two observables for second-class constraints:
`{f, g}_D = {f, g} - Σ_{ab} {f, φ_a} (C⁻¹)_{ab} {φ_b, g}` with `C_{ab} = {φ_a, φ_b}` (the inverse is Mathlib's
`Matrix.inv`, which is `0` where `C` is singular). -/
noncomputable def diracBracket (φ : Fin m → X → X → ℝ) (f g : X → X → ℝ) (p q : X) : ℝ :=
  poissonBracket f g p q -
    ∑ a, ∑ b, poissonBracket f (φ a) p q * (bracketMatrix φ p q)⁻¹ a b * poissonBracket (φ b) g p q

end Constraints

section Reduction

variable {E : Type} [AddCommGroup E] [Module ℝ E] {g : Type} [LieRing g] [LieAlgebra ℝ g]

/-- The orbit directions of a linear symplectic action at a point `x`: the span of the vectors `A Z x`, the
tangent space of the orbit of `x`. -/
noncomputable def orbitDirections {σ : LinearMap.BilinForm ℝ E} (ρ : AffineSymplecticAction σ g) (x : E) :
    Submodule ℝ E :=
  LinearMap.range ((LinearMap.applyₗ x).comp ρ.A)

/-- The `σ`-orthogonal of the orbit directions at `x`: the tangent space at `x` of a level set of the moment map
of a linear action (`dμ_Z(x)(v) = -σ(A Z x, v)`). -/
noncomputable def momentTangent {σ : LinearMap.BilinForm ℝ E} (ρ : AffineSymplecticAction σ g) (x : E) : Submodule ℝ E :=
  LinearMap.BilinForm.orthogonal σ (orbitDirections ρ x)

end Reduction

end Lightlike.Gauge
