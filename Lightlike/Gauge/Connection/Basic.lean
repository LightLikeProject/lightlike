import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Ring.Units

/-!
# Connections on a trivial bundle over a normed space, and their curvature

Source (read 19 November 2026): G. Svetlichny, *Preparation for Gauge Theory*, arXiv:math-ph/9902027v1, pp. 40-42.
Parallel transport solves `df/dt = -Γ(x(t), f) dx/dt` (p. 40); for a principal `G`-bundle it is the group element
`P exp(-∫ A)`, and transport around the small parallelogram `x, x + ξ, x + ξ + η, x + η` is, to second order in
`ξ, η`, multiplication by `exp(F(η, ξ))` with the curvature 2-form `F(η, ξ) = dA(η, ξ) + [A(η), A(ξ)]` (eq. (62)).

Here (the local form of the source, a trivialisation over an open set `U`, with a matrix group inside a complete
normed algebra `𝔄`): a connection is an `A : E → (E →L[ℝ] 𝔄)` that is `C²` on an open `U` (`Connection`); its
curvature at `x` is `curvature A x η ξ = dA(η, ξ) + [A(η), A(ξ)]` with
`dA(η, ξ) = ∂_η A(ξ) - ∂_ξ A(η)` and `[a, b] = a b - b a`, exactly the normalisation of (62) (no factor `1/2`).

* `curvature_antisymm`: `F(η, ξ) = -F(ξ, η)`.
* `curvature_congr`: `F` at `x` depends only on `A` near `x`.
* `curvature_of_commute`: for a commutative `𝔄` (the abelian case, e.g. `U(1)`), `F = dA`.
-/

open ContinuousLinearMap
open scoped Topology

noncomputable section

namespace Lightlike.Gauge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄]

/-- A connection (local principal gauge potential) on the trivial bundle `U × 𝔄ˣ` over an open set `U` of `E`: an
`𝔄`-valued one-form `x ↦ A(x)`, twice continuously differentiable on `U` (Svetlichny p. 30: `A_U` is a `g`-valued
1-form on `U`). Values off `U` play no role. -/
structure Connection (E 𝔄 : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedRing 𝔄]
    [NormedAlgebra ℝ 𝔄] where
  /-- The open set `U` of the trivialisation. -/
  domain : Set E
  /-- `U` is open. -/
  isOpen_domain : IsOpen domain
  /-- The one-form. -/
  A : E → E →L[ℝ] 𝔄
  /-- It is `C²` on `U`. -/
  contDiffOn : ContDiffOn ℝ 2 A domain

/-- **The curvature 2-form** (Svetlichny eq. (62)): `F(η, ξ) = dA(η, ξ) + [A(η), A(ξ)]`, with
`dA(η, ξ) = ∂_η A(ξ) - ∂_ξ A(η)`. -/
def curvature (A : E → E →L[ℝ] 𝔄) (x η ξ : E) : 𝔄 :=
  (fderiv ℝ A x η) ξ - (fderiv ℝ A x ξ) η + (A x η * A x ξ - A x ξ * A x η)

/-- The curvature is antisymmetric. -/
theorem curvature_antisymm (A : E → E →L[ℝ] 𝔄) (x η ξ : E) :
    curvature A x η ξ = -curvature A x ξ η := by
  unfold curvature; abel

/-- **The curvature is local**: it depends only on the germ of `A` at `x`. -/
theorem curvature_congr {A B : E → E →L[ℝ] 𝔄} {x : E} (h : A =ᶠ[𝓝 x] B) (η ξ : E) :
    curvature A x η ξ = curvature B x η ξ := by
  unfold curvature; rw [h.fderiv_eq, h.eq_of_nhds]

/-- **The abelian case**: if the values of `A` commute, the curvature is `dA`. -/
theorem curvature_of_commute (A : E → E →L[ℝ] 𝔄) (x η ξ : E) (h : Commute (A x η) (A x ξ)) :
    curvature A x η ξ = (fderiv ℝ A x η) ξ - (fderiv ℝ A x ξ) η := by
  unfold curvature; rw [h.eq, sub_self, add_zero]

end Lightlike.Gauge
