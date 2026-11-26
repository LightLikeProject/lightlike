import Lightlike.Spacetime.LieMetric

/-!
# The Lie derivative of covariant tensor fields (GE12)

For a vector field `X` on a smooth manifold, the Lie derivative of a covector field `α` and of a covariant
2-tensor field `T` (a section of `T*M ⊗ T*M`, not necessarily symmetric) are defined from the Lie bracket
`VectorField.mlieBracket` and the derivative of the scalar function obtained by evaluating the tensor on fields:

* `lieDerivCovector α X V x = X (α(V)) - α([X, V])`;
* `lieDerivTensor2 T X V W x = X (T(V, W)) - T([X, V], W) - T(V, [X, W])`.

* `lieDerivMetric_eq_lieDerivTensor2`: for the metric `g` (a 2-tensor field `g.g`), `lieDerivMetric` is
  `lieDerivTensor2` at `T = g.g`.
* `lieDerivTensor2_symm`: the Lie derivative of a symmetric 2-tensor is symmetric.
* `lieDerivTensor2_zero_left`, `lieDerivTensor2_zero_tensor`: the Lie derivative along the zero field, and of the zero tensor,
  vanishes.

**Limits.** As for `lieDerivMetric`, the Lie derivative is defined on arguments that are fields, with no claim here that it
is tensorial in `V, W` (it is, for fields smooth near the point; that is not proved in this file). Tensors of other types
(contravariant, mixed) and the Lie derivative of the tensor itself as a tensor field are not defined.
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsManifold I 2 M] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- **The Lie derivative of a covector field**: `(L_X α)(V) = X (α(V)) - α([X, V])` at `x`, where `α x` is a
linear form on the tangent space at `x`. -/
def lieDerivCovector (α : Π x : M, TangentSpace I x →L[ℝ] ℝ) (X V : Π x : M, TangentSpace I x) (x : M) : ℝ :=
  mvfderiv I (fun y => α y (V y)) x (X x) - α x (mlieBracket I X V x)

/-- **The Lie derivative of a covariant 2-tensor field** `T`:
`(L_X T)(V, W) = X (T(V, W)) - T([X, V], W) - T(V, [X, W])` at `x`. For `T = g.g` it is `lieDerivMetric`. -/
def lieDerivTensor2 (T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (X V W : Π x : M, TangentSpace I x) (x : M) : ℝ :=
  mvfderiv I (fun y => T y (V y) (W y)) x (X x) - T x (mlieBracket I X V x) (W x) - T x (V x) (mlieBracket I X W x)

/-- `lieDerivMetric` is the Lie derivative of the 2-tensor field `g.g`. -/
theorem lieDerivMetric_eq_lieDerivTensor2 (g : NondegMetric I M) (X V W : Π x : M, TangentSpace I x) (x : M) :
    lieDerivMetric g X V W x = lieDerivTensor2 g.g X V W x := rfl

/-- The Lie derivative of a symmetric 2-tensor field is symmetric in the two arguments. -/
theorem lieDerivTensor2_symm {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    (hT : ∀ (x : M) (v w : TangentSpace I x), T x v w = T x w v) (X V W : Π x : M, TangentSpace I x) (x : M) :
    lieDerivTensor2 T X V W x = lieDerivTensor2 T X W V x := by
  have h : (fun y => T y (V y) (W y)) = fun y => T y (W y) (V y) := funext fun y => hT y _ _
  unfold lieDerivTensor2
  rw [h, hT x (mlieBracket I X V x) (W x), hT x (V x) (mlieBracket I X W x)]
  ring

/-- The Lie derivative along the zero field vanishes. -/
theorem lieDerivTensor2_zero_left (T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (V W : Π x : M, TangentSpace I x) (x : M) :
    lieDerivTensor2 T (0 : Π y : M, TangentSpace I y) V W x = 0 := by
  unfold lieDerivTensor2
  simp [mlieBracket_zero_left]

/-- The Lie derivative of the zero tensor vanishes. -/
theorem lieDerivTensor2_zero_tensor (X V W : Π x : M, TangentSpace I x) (x : M) :
    lieDerivTensor2 (fun _ : M => (0 : TangentSpace I _ →L[ℝ] TangentSpace I _ →L[ℝ] ℝ)) X V W x = 0 := by
  unfold lieDerivTensor2
  simp [mvfderiv_const]

end Lightlike
