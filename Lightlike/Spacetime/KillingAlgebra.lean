import Lightlike.Spacetime.BianchiSecond
import Lightlike.Spacetime.LieMetric

/-!
# Killing fields form a Lie algebra (GE12)

`IsKillingNear g X x`: `(L_X g)(V, W) = 0` near `x` for all fields `V, W` smooth near `x` (`lieDerivMetric`).

* `lieDerivMetric_lieBracket`: if `X` and `Y` are smooth near `x` and Killing near `x`, then `L_{[X,Y]} g = 0` at `x`
  (the Jacobi identity and `[X, Y] f = X (Y f) - Y (X f)`; no connection is used);
* `IsKillingNear.lieBracket`: the bracket of two Killing fields is Killing near `x`.

* `lieDerivMetric_add_left`, `lieDerivMetric_smul_left`, `IsKillingNear.zero`, `.add`, `.smul`: `L_X g` is additive and
  homogeneous in `X`, so zero, sums and real multiples of Killing fields are Killing (the Lie algebra structure on
  global Killing fields is in `KillingLieAlgebra.lean`).

**Limits.** A metric of any signature, fields smooth near the point; "Killing" is `L_X g = 0` as in `LieMetric.lean`.
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle Filter
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [IsManifold 𝓘(ℝ, E) 2 M] [CompleteSpace E]
variable (g : NondegMetric 𝓘(ℝ, E) M)

/-- **`X` is a Killing field near `x`**: `L_X g (V, W) = 0` near `x` for all fields smooth near `x`. -/
def IsKillingNear (X : Π y : M, TangentSpace 𝓘(ℝ, E) y) (x : M) : Prop :=
  ∀ᶠ y in 𝓝 x, ∀ V W : Π y : M, TangentSpace 𝓘(ℝ, E) y, SmoothNear V y → SmoothNear W y →
    lieDerivMetric g X V W y = 0

variable {g}

/-- The derivative of `g(V, W)` along a Killing field, near `x`. -/
theorem IsKillingNear.dirDeriv_gpair {X V W : Π y : M, TangentSpace 𝓘(ℝ, E) y} {x : M}
    (hK : IsKillingNear g X x) (hV : SmoothNear V x) (hW : SmoothNear W x) :
    dirDeriv (gpair g V W) X =ᶠ[𝓝 x]
      gpair g (mlieBracket 𝓘(ℝ, E) X V) W + gpair g V (mlieBracket 𝓘(ℝ, E) X W) := by
  filter_upwards [hK, eventually_eventually_nhds.2 hV, eventually_eventually_nhds.2 hW] with y hy hVy hWy
  have hy := hy V W hVy hWy
  unfold lieDerivMetric at hy
  show mvfderiv 𝓘(ℝ, E) (gpair g V W) y (X y) = _
  simp only [Pi.add_apply, gpair]
  linarith

/-- The Jacobi identity: `[[X, Y], V] = [X, [Y, V]] - [Y, [X, V]]` at `x`. -/
theorem mlieBracket_jacobi {X Y V : Π y : M, TangentSpace 𝓘(ℝ, E) y} {x : M}
    (hX : SmoothNear X x) (hY : SmoothNear Y x) (hV : SmoothNear V x) :
    mlieBracket 𝓘(ℝ, E) (mlieBracket 𝓘(ℝ, E) X Y) V x =
      mlieBracket 𝓘(ℝ, E) X (mlieBracket 𝓘(ℝ, E) Y V) x - mlieBracket 𝓘(ℝ, E) Y (mlieBracket 𝓘(ℝ, E) X V) x := by
  haveI : IsManifold 𝓘(ℝ, E) (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp [minSmoothness])
  have c2 : ∀ {V : Π y : M, TangentSpace 𝓘(ℝ, E) y}, SmoothNear V x →
      ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) (minSmoothness ℝ 2)
        (fun q : M => (⟨q, V q⟩ : TangentBundle 𝓘(ℝ, E) M)) x :=
    fun hV => (hV.self_of_nhds).of_le (by simp [minSmoothness])
  haveI : IsManifold 𝓘(ℝ, E) (minSmoothness ℝ 3) M := IsManifold.of_le (n := ∞) (by simp [minSmoothness])
  have j1 := leibniz_identity_mlieBracket_apply (c2 hX) (c2 hY) (c2 hV)
  rw [j1]
  abel

/-- **`L_{[X,Y]} g = 0` at `x`** for two fields smooth near `x` and Killing near `x`. -/
theorem lieDerivMetric_lieBracket {X Y : Π y : M, TangentSpace 𝓘(ℝ, E) y} {x : M}
    (hXs : SmoothNear X x) (hYs : SmoothNear Y x) (hX : IsKillingNear g X x) (hY : IsKillingNear g Y x)
    {V W : Π y : M, TangentSpace 𝓘(ℝ, E) y} (hV : SmoothNear V x) (hW : SmoothNear W x) :
    lieDerivMetric g (mlieBracket 𝓘(ℝ, E) X Y) V W x = 0 := by
  have mX := mdiffAt_of_smoothNear hXs
  have mY := mdiffAt_of_smoothNear hYs
  have mV := mdiffAt_of_smoothNear hV
  have mW := mdiffAt_of_smoothNear hW
  have sYV := smoothNear_mlieBracket hYs hV
  have sYW := smoothNear_mlieBracket hYs hW
  have sXV := smoothNear_mlieBracket hXs hV
  have sXW := smoothNear_mlieBracket hXs hW
  have mYV := mdiffAt_of_smoothNear sYV
  have mYW := mdiffAt_of_smoothNear sYW
  have mXV := mdiffAt_of_smoothNear sXV
  have mXW := mdiffAt_of_smoothNear sXW
  have hgs : ∀ᶠ y in 𝓝 x, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (gpair g V W) y := by
    filter_upwards [hV, hW] with y hVy hWy using contMDiffAt_gpair g hVy hWy
  have hd := mfderiv_mlieBracket (gpair g V W) X Y x hgs mX mY
  have hd' : mvfderiv 𝓘(ℝ, E) (gpair g V W) x (mlieBracket 𝓘(ℝ, E) X Y x) =
      mvfderiv 𝓘(ℝ, E) (dirDeriv (gpair g V W) Y) x (X x) -
        mvfderiv 𝓘(ℝ, E) (dirDeriv (gpair g V W) X) x (Y x) := hd
  -- the second derivative along `X` of `g(V, W)` after `Y`
  have step : ∀ {A B : Π y : M, TangentSpace 𝓘(ℝ, E) y}, SmoothNear A x → SmoothNear B x →
      IsKillingNear g A x → IsKillingNear g B x →
      mvfderiv 𝓘(ℝ, E) (dirDeriv (gpair g V W) B) x (A x) =
        g.g x (mlieBracket 𝓘(ℝ, E) A (mlieBracket 𝓘(ℝ, E) B V) x) (W x) +
        g.g x (mlieBracket 𝓘(ℝ, E) B V x) (mlieBracket 𝓘(ℝ, E) A W x) +
        (g.g x (mlieBracket 𝓘(ℝ, E) A V x) (mlieBracket 𝓘(ℝ, E) B W x) +
          g.g x (V x) (mlieBracket 𝓘(ℝ, E) A (mlieBracket 𝓘(ℝ, E) B W) x)) := by
    intro A B hAs hBs hA hB
    have mA := mdiffAt_of_smoothNear hAs
    have sBV := smoothNear_mlieBracket hBs hV
    have sBW := smoothNear_mlieBracket hBs hW
    have mBV := mdiffAt_of_smoothNear sBV
    have mBW := mdiffAt_of_smoothNear sBW
    have mAV := mdiffAt_of_smoothNear (smoothNear_mlieBracket hAs hV)
    have mAW := mdiffAt_of_smoothNear (smoothNear_mlieBracket hAs hW)
    have mABV := mdiffAt_of_smoothNear (smoothNear_mlieBracket hAs sBV)
    have mABW := mdiffAt_of_smoothNear (smoothNear_mlieBracket hAs sBW)
    rw [mvfderiv_congr (hB.dirDeriv_gpair hV hW), mvfderiv_add (mdiffAt_gpair g mBV mW) (mdiffAt_gpair g mV mBW)]
    have l1 := hA.self_of_nhds (mlieBracket 𝓘(ℝ, E) B V) W sBV hW
    have l2 := hA.self_of_nhds V (mlieBracket 𝓘(ℝ, E) B W) hV sBW
    unfold lieDerivMetric at l1 l2
    simp only [add_apply]
    show mvfderiv 𝓘(ℝ, E) (gpair g (mlieBracket 𝓘(ℝ, E) B V) W) x (A x) +
      mvfderiv 𝓘(ℝ, E) (gpair g V (mlieBracket 𝓘(ℝ, E) B W)) x (A x) = _
    linarith
  have s1 := step hXs hYs hX hY
  have s2 := step hYs hXs hY hX
  have j := mlieBracket_jacobi hXs hYs hV
  have j' := mlieBracket_jacobi hXs hYs hW
  unfold lieDerivMetric
  rw [hd', s1, s2, j, j']
  simp only [map_sub, ContinuousLinearMap.sub_apply]
  ring

/-- **Killing fields form a Lie algebra**: the bracket of two Killing fields is Killing. -/
theorem IsKillingNear.lieBracket {X Y : Π y : M, TangentSpace 𝓘(ℝ, E) y} {x : M}
    (hXs : SmoothNear X x) (hYs : SmoothNear Y x) (hX : IsKillingNear g X x) (hY : IsKillingNear g Y x) :
    IsKillingNear g (mlieBracket 𝓘(ℝ, E) X Y) x := by
  filter_upwards [eventually_eventually_nhds.2 hXs, eventually_eventually_nhds.2 hYs,
    eventually_eventually_nhds.2 hX, eventually_eventually_nhds.2 hY] with y hXsy hYsy hXy hYy V W hV hW
  exact lieDerivMetric_lieBracket hXsy hYsy hXy hYy hV hW

/-- `L_X g` is additive in `X`: `(L_{X+Y} g)(V, W) = (L_X g)(V, W) + (L_Y g)(V, W)` at `x`, for fields differentiable at `x`. -/
theorem lieDerivMetric_add_left {X Y V W : Π y : M, TangentSpace 𝓘(ℝ, E) y} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    lieDerivMetric g (X + Y) V W x = lieDerivMetric g X V W x + lieDerivMetric g Y V W x := by
  unfold lieDerivMetric
  rw [mlieBracket_add_left hX hY, mlieBracket_add_left hX hY]
  simp only [Pi.add_apply, map_add, ContinuousLinearMap.add_apply]
  ring

/-- `L_X g` is homogeneous in `X`: `(L_{c X} g)(V, W) = c (L_X g)(V, W)` at `x`, for `X` differentiable at `x`. -/
theorem lieDerivMetric_smul_left {X V W : Π y : M, TangentSpace 𝓘(ℝ, E) y} {x : M}
    (c : ℝ) (hX : MDiffAt (T% X) x) :
    lieDerivMetric g (c • X) V W x = c * lieDerivMetric g X V W x := by
  unfold lieDerivMetric
  rw [mlieBracket_const_smul_left hX, mlieBracket_const_smul_left hX]
  simp only [Pi.smul_apply, map_smul, smul_apply, smul_eq_mul]
  ring

/-- The zero field is Killing. -/
theorem IsKillingNear.zero (x : M) : IsKillingNear g (0 : Π y : M, TangentSpace 𝓘(ℝ, E) y) x :=
  Filter.Eventually.of_forall fun _ _ _ _ _ => lieDerivMetric_zero _ _ _

/-- **Killing fields are closed under sums.** -/
theorem IsKillingNear.add {X Y : Π y : M, TangentSpace 𝓘(ℝ, E) y} {x : M}
    (hXs : SmoothNear X x) (hYs : SmoothNear Y x) (hX : IsKillingNear g X x) (hY : IsKillingNear g Y x) :
    IsKillingNear g (X + Y) x := by
  filter_upwards [eventually_eventually_nhds.2 hXs, eventually_eventually_nhds.2 hYs, hX, hY]
    with y hXsy hYsy hXy hYy V W hV hW
  rw [lieDerivMetric_add_left (mdiffAt_of_smoothNear hXsy) (mdiffAt_of_smoothNear hYsy),
    hXy V W hV hW, hYy V W hV hW]
  ring

/-- **Killing fields are closed under real multiples.** -/
theorem IsKillingNear.smul {X : Π y : M, TangentSpace 𝓘(ℝ, E) y} {x : M} (c : ℝ)
    (hXs : SmoothNear X x) (hX : IsKillingNear g X x) : IsKillingNear g (c • X) x := by
  filter_upwards [eventually_eventually_nhds.2 hXs, hX] with y hXsy hXy V W hV hW
  rw [lieDerivMetric_smul_left c (mdiffAt_of_smoothNear hXsy), hXy V W hV hW]
  ring

end Lightlike
