import Lightlike.Spacetime.LeviCivita

/-!
# The Lie derivative of a metric and Killing fields (GE12)

For a metric `g` of any signature (`NondegMetric`) and vector fields `X, V, W`,
`lieDerivMetric g X V W x = X (g(V, W)) - g([X, V], W) - g(V, [X, W])` at `x`: the Lie derivative `(L_X g)(V, W)`, defined
from the Lie bracket `VectorField.mlieBracket` and the derivative of the function `g(V, W)`.

* `lieDerivMetric_eq_of_isLeviCivita`: for the Levi-Civita connection (any torsion-free connection compatible with `g`),
  `(L_X g)(V, W) = g(∇_V X, W) + g(V, ∇_W X)` at every point where `X, V, W` are differentiable.
* `IsKillingAt`: the Killing equation `g(∇_v X, w) + g(v, ∇_w X) = 0` for all tangent vectors `v, w` at `x`.
* `isKillingAt_iff_lieDerivMetric_eq_zero`: for a Levi-Civita connection, `X` is Killing at `x` iff `(L_X g)(V, W)(x) = 0` for
  all vector fields `V, W` differentiable at `x`; so a Killing field is a field whose flow preserves `g` to first order.

**Limits.** `X` is a field differentiable at `x`; the Killing equation is the pointwise one, not the statement that the flow of
`X` is an isometry (flows are not in this file). The Lie derivative is defined on fields, not shown tensorial in `V, W` here
(the equality with the connection expression shows it at Levi-Civita points). Manifolds as in `LeviCivita.lean`
(`IsManifold I 2`, `CompleteSpace E`, no boundary assumption beyond what Mathlib's covariant derivative needs).
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsManifold I 2 M] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- **The Lie derivative of the metric**: `(L_X g)(V, W) = X (g(V, W)) - g([X, V], W) - g(V, [X, W])` at `x`. -/
def lieDerivMetric (g : NondegMetric I M) (X V W : Π x : M, TangentSpace I x) (x : M) : ℝ :=
  mvfderiv I (gpair g V W) x (X x) - g.g x (mlieBracket I X V x) (W x) - g.g x (V x) (mlieBracket I X W x)

/-- **A Killing field at `x`** for the connection `cov`: `g(∇_v X, w) + g(v, ∇_w X) = 0` for all `v, w` at `x`. -/
def IsKillingAt (cov : Connection I M) (g : NondegMetric I M) (X : Π y : M, TangentSpace I y) (x : M) : Prop :=
  ∀ v w : TangentSpace I x, g.g x (cov X x v) w + g.g x v (cov X x w) = 0

variable {g : NondegMetric I M} {cov : Connection I M}

/-- `L_X g` is symmetric: `(L_X g)(V, W) = (L_X g)(W, V)`. -/
theorem lieDerivMetric_symm (X V W : Π y : M, TangentSpace I y) (x : M) :
    lieDerivMetric g X V W x = lieDerivMetric g X W V x := by
  have h : gpair g V W = gpair g W V := funext fun y => g.symm y (V y) (W y)
  unfold lieDerivMetric
  rw [h, g.symm x (mlieBracket I X V x) (W x), g.symm x (V x) (mlieBracket I X W x)]
  ring

/-- The zero field has `L_0 g = 0`. -/
theorem lieDerivMetric_zero (V W : Π y : M, TangentSpace I y) (x : M) :
    lieDerivMetric g (0 : Π y : M, TangentSpace I y) V W x = 0 := by
  unfold lieDerivMetric
  simp [mlieBracket_zero_left]

/-- **`(L_X g)(V, W) = g(∇_V X, W) + g(V, ∇_W X)`** for a torsion-free connection compatible with `g`. -/
theorem lieDerivMetric_eq_of_isLeviCivita (h : cov.IsLeviCivita g)
    {X V W : Π y : M, TangentSpace I y} {x : M}
    (hX : MDiffAt (T% X) x) (hV : MDiffAt (T% V) x) (hW : MDiffAt (T% W) x) :
    lieDerivMetric g X V W x = g.g x (cov X x (V x)) (W x) + g.g x (V x) (cov X x (W x)) := by
  have c1 : mvfderiv I (gpair g V W) x (X x) =
      g.g x (cov V x (X x)) (W x) + g.g x (V x) (cov W x (X x)) := h.2 X V W x hX hV hW
  have tV := ((CovariantDerivative.torsion_eq_zero_iff cov).1 h.1) hX hV
  have tW := ((CovariantDerivative.torsion_eq_zero_iff cov).1 h.1) hX hW
  unfold lieDerivMetric
  rw [c1, ← tV, ← tW]
  simp only [map_sub, ContinuousLinearMap.sub_apply]
  ring

/-- **Killing at `x` iff `L_X g = 0` at `x`** for a Levi-Civita connection. -/
theorem isKillingAt_iff_lieDerivMetric_eq_zero (h : cov.IsLeviCivita g)
    {X : Π y : M, TangentSpace I y} {x : M} (hX : MDiffAt (T% X) x) :
    IsKillingAt cov g X x ↔
      ∀ V W : Π y : M, TangentSpace I y, MDiffAt (T% V) x → MDiffAt (T% W) x →
        lieDerivMetric g X V W x = 0 := by
  constructor
  · intro hK V W hV hW
    rw [lieDerivMetric_eq_of_isLeviCivita h hX hV hW]
    exact hK _ _
  · intro hL v w
    have := hL (FiberBundle.extend E v) (FiberBundle.extend E w) (mdifferentiableAt_extend _ _ v)
      (mdifferentiableAt_extend _ _ w)
    rw [lieDerivMetric_eq_of_isLeviCivita h hX (mdifferentiableAt_extend _ _ v) (mdifferentiableAt_extend _ _ w)] at this
    simpa [FiberBundle.extend_apply_self] using this

end Lightlike
