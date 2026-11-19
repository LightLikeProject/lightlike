import Lightlike.Spacetime.BianchiSecond
import Lightlike.Spacetime.Corners.CurvatureSymmetries

/-!
# The second Bianchi identity, for any model with corners

For a locally smooth torsion-free connection `cov` on a manifold modelled with corners on a finite-dimensional space
(boundary and corners allowed, no Hausdorff hypothesis): `bianchi_second_provedW` states
`(∇_X R)(Y,Z)W + (∇_Y R)(Z,X)W + (∇_Z R)(X,Y)W = 0` with `covDerivCurvatureAt` of `Connection.lean`.

Proof (operator form): near `x` the curvature field is `R(Y,Z)W = D_Y D_Z W - D_Z D_Y W - D_{[Y,Z]} W`
(`Rf_eventuallyW`), `∇_X` of it is computed with the additivity of `cov` (`cov_RfW`), the triple compositions
`D_X D_Y D_Z W` cancel in the cyclic sum, `D_X D_V W - D_V D_X W = R(X,V) W + D_{[X,V]} W`, the Jacobi identity
removes `Σ D_{[X,[Y,Z]]}` (`bianchi_second_fieldsW`), and torsion freeness together with the linearity and antisymmetry
of the curvature in its first slots turns the remaining terms `R(∇_X Y, Z) + R(Y, ∇_X Z)` into `R([X,Y], Z)`.

**Differences from the task `T-GE1-P7`** (which stays open): the task is for any `ModelWithCorners`, with
`IsLeviCivita`, and no Hausdorff hypothesis; this theorem holds for any `ModelWithCorners`, with a locally smooth
connection (`LocallySmoothConnectionW`, no Hausdorff hypothesis), `[IsManifold I 2 M]`, and only `cov.torsion = 0`. The
comparison with Wald, *General Relativity*, eq. (3.2.13), is pending: the source was not read at the cited location.

This is the Corners layer: the version for any model with corners of `Lightlike/Spacetime/BianchiSecond.lean`, with a
`W` suffix where the boundaryless file owns the name.
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle Filter
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsManifold I 2 M] [CompleteSpace E]
variable (cov : Connection I M) [LocallySmoothConnectionW cov]

/-- `D_V U = ∇_V U` as a field. -/
def ddW (V U : Π y : M, TangentSpace I y) : Π y : M, TangentSpace I y :=
  fun y => cov U y (V y)

/-- `∇_V U` is smooth near `x` for fields smooth near `x`. -/
theorem smoothNear_ddW {V U : Π y : M, TangentSpace I y} {x : M}
    (hV : SmoothNearW V x) (hU : SmoothNearW U x) : SmoothNearW (ddW cov V U) x := by
  filter_upwards [eventually_eventually_nhds.2 hV, eventually_eventually_nhds.2 hU] with y hVy hUy
  exact contMDiffAt_covApplyW cov hVy.self_of_nhds hUy

/-- A field smooth near `x` is differentiable at `x`. -/
theorem mdiffAt_of_smoothNearW {V : Π y : M, TangentSpace I y} {x : M} (hV : SmoothNearW V x) :
    MDiffAt (T% V) x := hV.self_of_nhds.mdifferentiableAt (by simp)

/-- A connection is additive and compatible with the subtraction of fields smooth at `x`. -/
theorem cov_add_subW {A B C : Π y : M, TangentSpace I y} {x : M}
    (hA : SmoothNearW A x) (hB : SmoothNearW B x) (hC : SmoothNearW C x) (u : TangentSpace I x) :
    cov (fun y => A y - B y - C y) x u = cov A x u - cov B x u - cov C x u := by
  have mA := mdiffAt_of_smoothNearW hA
  have mB := mdiffAt_of_smoothNearW hB
  have mC := mdiffAt_of_smoothNearW hC
  have hcov := cov.isCovariantDerivativeOn (s := Set.univ)
  have mB' : MDiffAt (T% ((-1 : ℝ) • B)) x := MDifferentiableAt.smul_section mdifferentiableAt_const mB
  have mC' : MDiffAt (T% ((-1 : ℝ) • C)) x := MDifferentiableAt.smul_section mdifferentiableAt_const mC
  have e : (fun y => A y - B y - C y) = A + ((-1 : ℝ) • B) + ((-1 : ℝ) • C) := by
    funext y; simp [sub_eq_add_neg]
  rw [e, hcov.add (mdifferentiableAt_add_section mA mB') mC', hcov.add mA mB',
    hcov.smul_const (-1) mB, hcov.smul_const (-1) mC]
  simp [sub_eq_add_neg]

variable (x₀ : M)

/-- The components of the curvature at any point of the chart domain. -/
theorem hv_curvatureAt'W {p : M} (hp : p ∈ (tTrivW (I := I) (E := E) x₀).baseSet)
    (X₀ Y₀ Z₀ : TangentSpace I p) :
    hvW x₀ p (cov.curvatureAt p X₀ Y₀ Z₀) = RhatW cov x₀ p (hvW x₀ p X₀) (hvW x₀ p Y₀) (hvW x₀ p Z₀) := by
  have h2 := curvature_hatW cov x₀ hp (eventually_extendW p X₀) (eventually_extendW p Y₀)
    (eventually_extendW p Z₀)
  simp only [FiberBundle.extend_apply_self] at h2
  unfold Connection.curvatureAt
  dsimp only
  simp only [FiberBundle.extend_apply_self]
  exact h2

/-- `RhatW` is subtractive in its first argument. -/
theorem Rhat_sub_leftW (p : M) (a a' b c : E) :
    RhatW cov x₀ p (a - a') b c = RhatW cov x₀ p a b c - RhatW cov x₀ p a' b c := by
  unfold RhatW
  simp only [map_sub, sub_apply]
  abel

/-- The curvature is additive (subtractive) in its first slot. -/
theorem curvatureAt_sub_leftW (x : M) (a b Y₀ Z₀ : TangentSpace I x) :
    cov.curvatureAt x (a - b) Y₀ Z₀ = cov.curvatureAt x a Y₀ Z₀ - cov.curvatureAt x b Y₀ Z₀ := by
  have hx : x ∈ (tTrivW (I := I) (E := E) x).baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have key : hvW x x (cov.curvatureAt x (a - b) Y₀ Z₀) =
      hvW x x (cov.curvatureAt x a Y₀ Z₀ - cov.curvatureAt x b Y₀ Z₀) := by
    rw [hv_subW x hx, hv_curvatureAt'W cov x hx, hv_curvatureAt'W cov x hx, hv_curvatureAt'W cov x hx, hv_subW x hx]
    exact Rhat_sub_leftW cov x x _ _ _ _
  exact (symmL_hvW x hx _).symm.trans ((congrArg ((tTrivW (I := I) (E := E) x).symmL ℝ x) key).trans (symmL_hvW x hx _))

/-- `A - B - C` is smooth near `x` for fields smooth near `x`. -/
theorem smoothNear_sub3W {A B C : Π y : M, TangentSpace I y} {x : M}
    (hA : SmoothNearW A x) (hB : SmoothNearW B x) (hC : SmoothNearW C x) :
    SmoothNearW (fun y => A y - B y - C y) x := by
  filter_upwards [hA, hB, hC] with y hAy hBy hCy
  exact (hAy.sub_section hBy).sub_section hCy

/-- The curvature as a field: `y ↦ R(Y y, Z y) W y`. -/
def RfW (Y Z W : Π y : M, TangentSpace I y) : Π y : M, TangentSpace I y :=
  fun y => cov.curvatureAt y (Y y) (Z y) (W y)

/-- Near `x` the curvature field is `∇_Y ∇_Z W - ∇_Z ∇_Y W - ∇_{[Y,Z]} W` (from `curvatureAt_apply_eventuallyW`). -/
theorem Rf_eventuallyW {Y Z W : Π y : M, TangentSpace I y} {x : M}
    (hY : SmoothNearW Y x) (hZ : SmoothNearW Z x) (hW : SmoothNearW W x) :
    RfW cov Y Z W =ᶠ[nhds x] fun y => ddW cov Y (ddW cov Z W) y - ddW cov Z (ddW cov Y W) y -
      ddW cov (mlieBracket I Y Z) W y := by
  filter_upwards [eventually_eventually_nhds.2 hY, eventually_eventually_nhds.2 hZ,
    eventually_eventually_nhds.2 hW] with y hYy hZy hWy
  exact curvatureAt_apply_eventuallyW cov Y Z W y hYy hZy hWy

/-- `∇_u` of the curvature field `R(Y,Z)W` at `x` in terms of third derivatives. -/
theorem cov_RfW {Y Z W : Π y : M, TangentSpace I y} {x : M}
    (hY : SmoothNearW Y x) (hZ : SmoothNearW Z x) (hW : SmoothNearW W x) (u : TangentSpace I x) :
    cov (RfW cov Y Z W) x u = cov (ddW cov Y (ddW cov Z W)) x u - cov (ddW cov Z (ddW cov Y W)) x u -
      cov (ddW cov (mlieBracket I Y Z) W) x u := by
  have hA := smoothNear_ddW cov hY (smoothNear_ddW cov hZ hW)
  have hB := smoothNear_ddW cov hZ (smoothNear_ddW cov hY hW)
  have hC := smoothNear_ddW cov (smoothNear_mlieBracketW hY hZ) hW
  have hR : SmoothNearW (RfW cov Y Z W) x := by
    have hcomb := smoothNear_sub3W hA hB hC
    filter_upwards [eventually_eventually_nhds.2 (Rf_eventuallyW cov hY hZ hW), eventually_eventually_nhds.2 hcomb]
      with y hEq hc
    exact hc.self_of_nhds.congr_of_eventuallyEq (hEq.mono fun q hq => by simp only [hq])
  have hcov := cov.isCovariantDerivativeOn (s := Set.univ)
  rw [hcov.congr_of_eventuallyEq (mdiffAt_of_smoothNearW hR) (mdiffAt_of_smoothNearW (smoothNear_sub3W hA hB hC)) Filter.univ_mem (Rf_eventuallyW cov hY hZ hW)]
  exact cov_add_subW cov hA hB hC u

/-- One term of the operator proof of the second Bianchi identity. -/
theorem bianchi_termW {X Y Z W : Π y : M, TangentSpace I y} {x : M}
    (hX : SmoothNearW X x) (hY : SmoothNearW Y x) (hZ : SmoothNearW Z x) (hW : SmoothNearW W x) :
    cov (RfW cov Y Z W) x (X x) - cov.curvatureAt x (Y x) (Z x) (cov W x (X x)) =
      cov (ddW cov Y (ddW cov Z W)) x (X x) - cov (ddW cov Z (ddW cov Y W)) x (X x)
        - cov (ddW cov Z (ddW cov X W)) x (Y x) + cov (ddW cov Y (ddW cov X W)) x (Z x)
        - cov.curvatureAt x (X x) (mlieBracket I Y Z x) (W x)
        - cov W x (mlieBracket I X (mlieBracket I Y Z) x) := by
  have hXW : SmoothNearW (ddW cov X W) x := smoothNear_ddW cov hX hW
  have hV : SmoothNearW (mlieBracket I Y Z) x := smoothNear_mlieBracketW hY hZ
  have h1 := cov_RfW cov hY hZ hW (X x)
  have h2 := curvatureAt_apply_eventuallyW cov Y Z (ddW cov X W) x hY hZ hXW
  have h3 := curvatureAt_apply_eventuallyW cov X (mlieBracket I Y Z) W x hX hV hW
  have h4 : (ddW cov X W) x = cov W x (X x) := rfl
  rw [h4] at h2
  rw [h1, h2]
  rw [h3]
  have e1 : (fun y => cov (ddW cov X W) y (Z y)) = ddW cov Z (ddW cov X W) := rfl
  have e2 : (fun y => cov (ddW cov X W) y (Y y)) = ddW cov Y (ddW cov X W) := rfl
  have e3 : (fun y => cov W y (mlieBracket I Y Z y)) = ddW cov (mlieBracket I Y Z) W := rfl
  rw [e1, e2, e3]
  abel

/-- The cyclic sum of `[D_X, R(Y,Z)] W` at `x` is `-Σ R(X, [Y,Z]) W` (operator Jacobi identity, the Jacobi identity of the Lie bracket). -/
theorem bianchi_second_fieldsW {X Y Z W : Π y : M, TangentSpace I y} {x : M}
    (hX : SmoothNearW X x) (hY : SmoothNearW Y x) (hZ : SmoothNearW Z x) (hW : SmoothNearW W x) :
    (cov (RfW cov Y Z W) x (X x) - cov.curvatureAt x (Y x) (Z x) (cov W x (X x))) +
      (cov (RfW cov Z X W) x (Y x) - cov.curvatureAt x (Z x) (X x) (cov W x (Y x))) +
      (cov (RfW cov X Y W) x (Z x) - cov.curvatureAt x (X x) (Y x) (cov W x (Z x))) =
    -(cov.curvatureAt x (X x) (mlieBracket I Y Z x) (W x) +
      cov.curvatureAt x (Y x) (mlieBracket I Z X x) (W x) +
      cov.curvatureAt x (Z x) (mlieBracket I X Y x) (W x)) := by
  rw [bianchi_termW cov hX hY hZ hW, bianchi_termW cov hY hZ hX hW, bianchi_termW cov hZ hX hY hW]
  have j := jacobi_cycW hX hY hZ
  have hj : cov W x (mlieBracket I X (mlieBracket I Y Z) x) +
      cov W x (mlieBracket I Y (mlieBracket I Z X) x) +
      cov W x (mlieBracket I Z (mlieBracket I X Y) x) = 0 := by
    rw [← map_add, ← map_add, j, map_zero]
  have h3 : cov W x (mlieBracket I Z (mlieBracket I X Y) x) =
      -(cov W x (mlieBracket I X (mlieBracket I Y Z) x)) -
        cov W x (mlieBracket I Y (mlieBracket I Z X) x) := by
    rw [eq_neg_of_add_eq_zero_right hj]; abel
  rw [h3]
  abel

/-- **The second Bianchi identity** for a torsion-free smooth connection. -/
theorem bianchi_second_provedW (hT : cov.torsion = 0) (x : M) (X₀ Y₀ Z₀ W₀ : TangentSpace I x) :
    cov.covDerivCurvatureAt x X₀ Y₀ Z₀ W₀ + cov.covDerivCurvatureAt x Y₀ Z₀ X₀ W₀ +
      cov.covDerivCurvatureAt x Z₀ X₀ Y₀ W₀ = 0 := by
  set X := FiberBundle.extend E X₀ with hXd
  set Y := FiberBundle.extend E Y₀ with hYd
  set Z := FiberBundle.extend E Z₀ with hZd
  set W := FiberBundle.extend E W₀ with hWd
  have hX : SmoothNearW X x := eventually_extendW x X₀
  have hY : SmoothNearW Y x := eventually_extendW x Y₀
  have hZ : SmoothNearW Z x := eventually_extendW x Z₀
  have hW : SmoothNearW W x := eventually_extendW x W₀
  have hXx : X x = X₀ := FiberBundle.extend_apply_self E X₀
  have hYx : Y x = Y₀ := FiberBundle.extend_apply_self E Y₀
  have hZx : Z x = Z₀ := FiberBundle.extend_apply_self E Z₀
  have hWx : W x = W₀ := FiberBundle.extend_apply_self E W₀
  have F := bianchi_second_fieldsW cov hX hY hZ hW
  rw [hXx, hYx, hZx, hWx] at F
  have tXY := cov_torsionW hT (X := X) (Y := Y) (x := x) (mdiffAt_of_smoothNearW hX) (mdiffAt_of_smoothNearW hY)
  have tYZ := cov_torsionW hT (X := Y) (Y := Z) (x := x) (mdiffAt_of_smoothNearW hY) (mdiffAt_of_smoothNearW hZ)
  have tZX := cov_torsionW hT (X := Z) (Y := X) (x := x) (mdiffAt_of_smoothNearW hZ) (mdiffAt_of_smoothNearW hX)
  rw [hXx, hYx] at tXY
  rw [hYx, hZx] at tYZ
  rw [hZx, hXx] at tZX
  unfold Connection.covDerivCurvatureAt
  have e1 : (fun y => cov.curvatureAt y (extend E Y₀ y) (extend E Z₀ y) (extend E W₀ y)) = RfW cov Y Z W := rfl
  have e2 : (fun y => cov.curvatureAt y (extend E Z₀ y) (extend E X₀ y) (extend E W₀ y)) = RfW cov Z X W := rfl
  have e3 : (fun y => cov.curvatureAt y (extend E X₀ y) (extend E Y₀ y) (extend E W₀ y)) = RfW cov X Y W := rfl
  rw [e1, e2, e3]
  have F2 : cov (RfW cov Y Z W) x X₀ =
      -(cov.curvatureAt x X₀ (mlieBracket I Y Z x) W₀ +
        cov.curvatureAt x Y₀ (mlieBracket I Z X x) W₀ +
        cov.curvatureAt x Z₀ (mlieBracket I X Y x) W₀) +
      cov.curvatureAt x Y₀ Z₀ (cov W x X₀) -
      (cov (RfW cov Z X W) x Y₀ - cov.curvatureAt x Z₀ X₀ (cov W x Y₀)) -
      (cov (RfW cov X Y W) x Z₀ - cov.curvatureAt x X₀ Y₀ (cov W x Z₀)) := by
    rw [← F]; abel
  have A1 := curvatureAt_antisymm_leftW cov x Y₀ (cov Z x X₀) W₀
  have A2 := curvatureAt_antisymm_leftW cov x Z₀ (cov X x Y₀) W₀
  have A3 := curvatureAt_antisymm_leftW cov x X₀ (cov Y x Z₀) W₀
  have A4 := curvatureAt_antisymm_leftW cov x Z₀ (cov Y x X₀) W₀
  have A5 := curvatureAt_antisymm_leftW cov x X₀ (cov Z x Y₀) W₀
  have A6 := curvatureAt_antisymm_leftW cov x Y₀ (cov X x Z₀) W₀
  have B1 := curvatureAt_antisymm_leftW cov x X₀ (mlieBracket I Y Z x) W₀
  have B2 := curvatureAt_antisymm_leftW cov x Y₀ (mlieBracket I Z X x) W₀
  have B3 := curvatureAt_antisymm_leftW cov x Z₀ (mlieBracket I X Y x) W₀
  have S1 := curvatureAt_sub_leftW cov x (cov Z x Y₀) (cov Y x Z₀) X₀ W₀
  have S2 := curvatureAt_sub_leftW cov x (cov X x Z₀) (cov Z x X₀) Y₀ W₀
  have S3 := curvatureAt_sub_leftW cov x (cov Y x X₀) (cov X x Y₀) Z₀ W₀
  rw [tYZ] at S1
  rw [tZX] at S2
  rw [tXY] at S3
  rw [F2, B1, B2, B3, S1, S2, S3, A1, A2, A3]
  simp only [← hXd, ← hYd, ← hZd, ← hWd]
  abel
end Lightlike
