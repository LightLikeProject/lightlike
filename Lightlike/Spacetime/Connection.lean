module

public import Lightlike.Spacetime.Lorentzian
public import Lightlike.Spacetime.NondegMetricBase
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion

/-!
# Connections, curvature and the Einstein equations on a Lorentzian manifold

Core definitions of the manifold-level theory, independent of charts: an affine connection on a
Lorentzian manifold `(M, g)`, its torsion, its compatibility with `g`, the Levi-Civita
connection, the Riemann, Ricci and scalar curvature, and the Einstein equations with a
cosmological constant. The coordinate formulas of `Curvature.lean` are the same objects in a chart
(the comparison is a statement in `Tasks/Spacetime/`, not proved here).

## Conventions

* Signature `(-,+,…,+)` (`Lorentzian.lean`). Physlib uses `(+,-,…,-)`; nothing here uses Physlib's
  Lorentz definitions, so no bridge lemma is needed yet (it is added with the first use).
* A connection is Mathlib's `CovariantDerivative I E (TangentSpace I)`: `∇ Y x` is the linear map
  `v ↦ ∇_v Y`. The torsion is Mathlib's `CovariantDerivative.torsion`,
  `T(X, Y) = ∇_X Y - ∇_Y X - [X, Y]` (written there as `cov Y x (X x) - cov X x (Y x) - [X, Y] x`).
* **Curvature sign** (the convention of a Mathlib proposal,
  <https://github.com/leanprover-community/mathlib4/pull/45069>, so that a later switch is a
  rename): `R(X, Y) Z = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_{[X,Y]} Z`. Ricci is the trace over the first
  slot, `Ric(Y, Z) = tr (X ↦ R(X, Y) Z)`, so that the round sphere has positive Ricci curvature and
  the scalar curvature is `S = g^{ij} Ric_ij`. With this, the coordinate `riemann`, `ricci`
  and `scalarCurvature` of `Curvature.lean` agree with the ones here for the chart expression
  (statement `LorentzianMetric.scalarCurvature_chart` in `Tasks/Spacetime/`).

## Main definitions

* `Lightlike.curvatureAt`, `ricciAt`, `scalarCurvatureAt`: the curvature of a connection.
* `Lightlike.IsMetricCompatible`, `Lightlike.IsLeviCivita`: the Levi-Civita conditions.
* `Lightlike.LorentzianMetric.SatisfiesEinstein`: the Einstein equations on a manifold.

**Relation to `Lightlike.Cosmology.IsEinsteinSolution`.** That predicate is on coordinate
components (a `IsCoordMetric` on an open set of `ℝⁿ`); `SatisfiesEinstein` is on a Lorentzian
metric of a manifold with a Levi-Civita connection. The comparison in a chart is stated, not
proved, in `Tasks/Spacetime/`.

**Limits.** Definitions only. Curvature is defined through extensions of tangent vectors to
vector fields (Mathlib's `TensorialAt.extend`), so that it is a tensor only after
`curvatureAt_apply` (a task); Ricci and scalar curvature are defined with a basis of the tangent
space and are basis independent only through that tensoriality. No existence of a Levi-Civita
connection of a Lorentzian metric is proved here (a task); Mathlib has it for Riemannian metrics.

**References.** R. M. Wald, *General Relativity* (University of Chicago Press, 1984), ch. 3;
B. O'Neill, *Semi-Riemannian Geometry* (Academic Press, 1983), ch. 3 and 4.
-/

@[expose] public section

open Bundle Manifold Set VectorField NormedSpace FiberBundle
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [CompleteSpace E]

/-- A connection on the tangent bundle of `M` (Mathlib's covariant derivative on `TM`). -/
abbrev Connection (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] :=
  CovariantDerivative I E (TangentSpace I : M → Type _)

namespace Connection

variable (cov : Connection I M)

/-- **Riemann curvature** of `cov` at `x`, `R(X₀, Y₀) Z₀ = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_{[X,Y]} Z`
(the module's sign convention), computed with extensions `X, Y, Z` of the tangent vectors
to vector fields; it does not depend on the extensions (a task, tensoriality). -/
def curvatureAt (x : M) (X₀ Y₀ Z₀ : TangentSpace I x) : TangentSpace I x :=
  let X := extend E X₀
  let Y := extend E Y₀
  let Z := extend E Z₀
  cov (fun y => cov Z y (Y y)) x (X x) - cov (fun y => cov Z y (X y)) x (Y x)
    - cov Z x (mlieBracket I X Y x)

/-- The (0,4) curvature of a metric `g`: `g(R(X, Y) Z, W)`. -/
def riemannLowerAt (g : NondegMetric I M) (x : M) (X₀ Y₀ Z₀ W₀ : TangentSpace I x) : ℝ :=
  g.g x (cov.curvatureAt x X₀ Y₀ Z₀) W₀

/-- **Ricci tensor** `Ric(Y, Z) = tr (X ↦ R(X, Y) Z)`, the trace taken in a basis of the tangent
space (any basis, by tensoriality). -/
def ricciAt (x : M) (Y₀ Z₀ : TangentSpace I x) : ℝ :=
  let b := Module.finBasis ℝ E
  ∑ i, b.coord i (cov.curvatureAt x (b i : TangentSpace I x) Y₀ Z₀)

/-- **Scalar curvature** `S = g^{ij} Ric_ij` of a Lorentzian metric, with the inverse of the Gram
matrix of a basis of the tangent space. -/
def scalarCurvatureAt (g : NondegMetric I M) (x : M) : ℝ :=
  let b := Module.finBasis ℝ E
  let G : Matrix _ _ ℝ := Matrix.of fun i j => g.g x (b i : TangentSpace I x) (b j : TangentSpace I x)
  ∑ i, ∑ j, G⁻¹ i j * cov.ricciAt x (b i : TangentSpace I x) (b j : TangentSpace I x)

/-- `cov` is **compatible with `g`**: `X (g(σ, τ)) = g(∇_X σ, τ) + g(σ, ∇_X τ)` for fields
differentiable at `x`. -/
def IsMetricCompatible (g : NondegMetric I M) : Prop :=
  ∀ (X σ τ : Π x : M, TangentSpace I x) (x : M),
    MDiffAt (T% X) x → MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      mfderiv I 𝓘(ℝ) (fun y => g.g y (σ y) (τ y)) x (X x) =
        g.g x (cov σ x (X x)) (τ x) + g.g x (σ x) (cov τ x (X x))

/-- `cov` is the **Levi-Civita connection** of `g`: torsion-free and compatible with `g`. -/
def IsLeviCivita (g : NondegMetric I M) : Prop :=
  cov.torsion = 0 ∧ cov.IsMetricCompatible g

/-- The covariant derivative `(∇_X R)(Y, Z) W` of the curvature at `x`, with the Leibniz rule applied to
the four slots (extensions as in `curvatureAt`). -/
def covDerivCurvatureAt (x : M) (X₀ Y₀ Z₀ W₀ : TangentSpace I x) : TangentSpace I x :=
  cov (fun y => cov.curvatureAt y (extend E Y₀ y) (extend E Z₀ y) (extend E W₀ y)) x X₀
    - cov.curvatureAt x (cov (extend E Y₀) x X₀) Z₀ W₀
    - cov.curvatureAt x Y₀ (cov (extend E Z₀) x X₀) W₀
    - cov.curvatureAt x Y₀ Z₀ (cov (extend E W₀) x X₀)

/-- The covariant derivative `(∇_X T)(v, w) = X(T(v, w)) - T(∇_X v, w) - T(v, ∇_X w)` of a field of
bilinear forms `T` at `x`. -/
def covDerivBilinAt (T : Π x : M, TangentSpace I x → TangentSpace I x → ℝ) (x : M)
    (X₀ v₀ w₀ : TangentSpace I x) : ℝ :=
  (show ℝ from mfderiv I 𝓘(ℝ) (fun y => T y (extend E v₀ y) (extend E w₀ y)) x X₀)
    - T x (cov (extend E v₀) x X₀) w₀ - T x v₀ (cov (extend E w₀) x X₀)

/-- The divergence `(div T)(w) = g^{ij} (∇_i T)(e_j, w)` of a field of bilinear forms for the metric
`g`, in a basis `e` of the tangent space with the inverse of its Gram matrix. -/
def divBilinAt (g : NondegMetric I M)
    (T : Π x : M, TangentSpace I x → TangentSpace I x → ℝ) (x : M) (w₀ : TangentSpace I x) : ℝ :=
  let b := Module.finBasis ℝ E
  let G : Matrix _ _ ℝ := Matrix.of fun i j => g.g x (b i : TangentSpace I x) (b j : TangentSpace I x)
  ∑ i, ∑ j, G⁻¹ i j * cov.covDerivBilinAt T x (b i : TangentSpace I x) (b j : TangentSpace I x) w₀

/-- The **Einstein tensor** `G = Ric - (S/2) g` as a field of bilinear forms. -/
def einsteinField (g : NondegMetric I M) :
    Π x : M, TangentSpace I x → TangentSpace I x → ℝ :=
  fun x v w => cov.ricciAt x v w - cov.scalarCurvatureAt g x / 2 * g.g x v w

end Connection

namespace LorentzianMetric

variable {n : ℕ} (g : LorentzianMetric I M n)

/-- **The Einstein equations with cosmological constant `Λ`** for `g` and its connection `cov`
(`cov` is Levi-Civita for `g`): `Ric - (S/2) g + Λ g = 0` at every point. The vacuum equations are
`Λ = 0`. On a chart this is `Cosmology.IsEinsteinSolution`'s coordinate statement. -/
def SatisfiesEinstein (cov : Connection I M) (Λ : ℝ) : Prop :=
  cov.IsLeviCivita g ∧ ∀ x (v w : TangentSpace I x),
    cov.ricciAt x v w - cov.scalarCurvatureAt g x / 2 * g.g x v w + Λ * g.g x v w = 0

end LorentzianMetric

namespace NondegMetric

variable (g : NondegMetric I M)

/-- **The Einstein equations with cosmological constant `Λ`** for a metric of any signature `g` and its connection
`cov` (`cov` is Levi-Civita for `g`): `Ric - (S/2) g + Λ g = 0` at every point. -/
def SatisfiesEinstein (cov : Connection I M) (Λ : ℝ) : Prop :=
  cov.IsLeviCivita g ∧ ∀ x (v w : TangentSpace I x),
    cov.ricciAt x v w - cov.scalarCurvatureAt g x / 2 * g.g x v w + Λ * g.g x v w = 0

end NondegMetric

end Lightlike
