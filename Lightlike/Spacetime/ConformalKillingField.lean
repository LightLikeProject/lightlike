import Lightlike.Spacetime.LieMetric

/-!
# Conformal Killing fields on a manifold (G1-013)

Gourgoulhon (gr-qc/0703035, Appendix B.1.3), eq. (B.8): "a vector field which obeys `(L̃v)ᵢⱼ = 0` is called a conformal
Killing vector. It is the generator of some conformal isometry ... every Killing vector is a conformal Killing vector."
For a metric `g` of any signature on a manifold (`NondegMetric`), `X` is **conformal Killing at `x` with factor `σ`** when
`L_X g = 2σ g` at `x` on all fields differentiable at `x` (`IsConformalKillingAt`, with `lieDerivMetric` of `LieMetric.lean`):

* `isConformalKillingAt_of_isKillingAt`: for the Levi-Civita connection, a Killing field is conformal Killing with `σ = 0`;
* `isConformalKillingAt_add`, `isConformalKillingAt_const_smul`: conformal Killing fields at `x` form a vector space, the
  factors adding.

The flat-space statements, including the classification of the conformal Killing fields of a flat metric in dimension at
least three, are in `ConformalKilling.lean` (namespace `Flat`). **Limits.** The bridge between the two in a flat chart is
not stated.
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsManifold I 2 M] [CompleteSpace E] [FiniteDimensional ℝ E]
  {g : NondegMetric I M} {cov : Connection I M}

/-- **A conformal Killing field at `x`** with conformal factor `σ`: `L_X g = 2σ g` at `x`. -/
def IsConformalKillingAt (g : NondegMetric I M) (X : Π y : M, TangentSpace I y) (σ : ℝ) (x : M) : Prop :=
  ∀ V W : Π y : M, TangentSpace I y, MDiffAt (T% V) x → MDiffAt (T% W) x →
    lieDerivMetric g X V W x = 2 * σ * g.g x (V x) (W x)

/-- **A Killing field is conformal Killing** (`σ = 0`), for the Levi-Civita connection. -/
theorem isConformalKillingAt_of_isKillingAt (h : cov.IsLeviCivita g) {X : Π y : M, TangentSpace I y} {x : M}
    (hX : MDiffAt (T% X) x) (hK : IsKillingAt cov g X x) : IsConformalKillingAt g X 0 x := by
  intro V W hV hW
  rw [(isKillingAt_iff_lieDerivMetric_eq_zero h hX).1 hK V W hV hW]
  ring

omit [FiniteDimensional ℝ E] in
/-- The Lie derivative of the metric is additive in the field. -/
theorem lieDerivMetric_add {X Y : Π y : M, TangentSpace I y} {x : M} (hX : MDiffAt (T% X) x)
    (hY : MDiffAt (T% Y) x) (V W : Π y : M, TangentSpace I y) :
    lieDerivMetric g (X + Y) V W x = lieDerivMetric g X V W x + lieDerivMetric g Y V W x := by
  unfold lieDerivMetric
  rw [mlieBracket_add_left hX hY, mlieBracket_add_left hX hY]
  simp only [Pi.add_apply, map_add, add_apply]
  ring

omit [FiniteDimensional ℝ E] in
/-- The Lie derivative of the metric is homogeneous in the field. -/
theorem lieDerivMetric_const_smul {X : Π y : M, TangentSpace I y} {x : M} (hX : MDiffAt (T% X) x) (c : ℝ)
    (V W : Π y : M, TangentSpace I y) :
    lieDerivMetric g (c • X) V W x = c * lieDerivMetric g X V W x := by
  unfold lieDerivMetric
  rw [mlieBracket_const_smul_left hX, mlieBracket_const_smul_left hX]
  simp only [Pi.smul_apply, map_smul, smul_apply, smul_eq_mul]
  ring

omit [FiniteDimensional ℝ E] in
/-- On a manifold, the sum of two conformal Killing fields is conformal Killing, with the sum of the conformal factors. -/
theorem isConformalKillingAt_add {X Y : Π y : M, TangentSpace I y} {σ τ : ℝ} {x : M} (hX : MDiffAt (T% X) x)
    (hY : MDiffAt (T% Y) x) (h1 : IsConformalKillingAt g X σ x) (h2 : IsConformalKillingAt g Y τ x) :
    IsConformalKillingAt g (X + Y) (σ + τ) x := by
  intro V W hV hW
  rw [lieDerivMetric_add hX hY, h1 V W hV hW, h2 V W hV hW]
  ring

omit [FiniteDimensional ℝ E] in
/-- On a manifold, a constant multiple of a conformal Killing field is conformal Killing, with the multiplied
conformal factor. -/
theorem isConformalKillingAt_const_smul {X : Π y : M, TangentSpace I y} {σ : ℝ} {x : M} (hX : MDiffAt (T% X) x)
    (c : ℝ) (h : IsConformalKillingAt g X σ x) : IsConformalKillingAt g (c • X) (c * σ) x := by
  intro V W hV hW
  rw [lieDerivMetric_const_smul hX c, h V W hV hW]
  ring

end Lightlike
