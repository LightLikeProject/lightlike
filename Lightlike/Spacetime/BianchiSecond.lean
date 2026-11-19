import Lightlike.Spacetime.CurvatureSymmetries

/-!
# The second Bianchi identity

For a smooth torsion-free connection `cov` on a Hausdorff manifold modelled on a finite-dimensional space (no
boundary): `bianchi_second_proved` states `(∇_X R)(Y,Z)W + (∇_Y R)(Z,X)W + (∇_Z R)(X,Y)W = 0` with `covDerivCurvatureAt`
of `Connection.lean`.

Proof (operator form): near `x` the curvature field is `R(Y,Z)W = D_Y D_Z W - D_Z D_Y W - D_{[Y,Z]} W`
(`Rf_eventually`), `∇_X` of it is computed with the additivity of `cov` (`cov_Rf`), the triple compositions
`D_X D_Y D_Z W` cancel in the cyclic sum, `D_X D_V W - D_V D_X W = R(X,V) W + D_{[X,V]} W`, the Jacobi identity
`jacobi_cyc` removes `Σ D_{[X,[Y,Z]]}` (`bianchi_second_fields`), and torsion freeness together with the
linearity and antisymmetry of the curvature in its first slots turns the remaining terms `R(∇_X Y, Z) + R(Y, ∇_X Z)`
into `R([X,Y], Z)`.

**Former task `T-GE1-P7`, closed by `bianchi_second_proved`.** Differences from the task statement (approved on 18 November 2026, updated
for the metrics of any signature of GE11): (1) no boundary and a finite-dimensional model space `E` (`ModelWithCorners` `𝓘(ℝ, E)`) instead of any
`ModelWithCorners` (this matches the source, where manifolds are charts onto open subsets of `ℝⁿ`); the connection is locally smooth
(`LocallySmoothConnection`), with no Hausdorff hypothesis; the task also assumes `[IsManifold I 2 M]`, so that is not a difference; (2) more general:
only `cov.torsion = 0` is assumed, not `IsLeviCivita` (no metric occurs). The statement was compared with Carroll, *Lecture Notes on General Relativity*
(1997), ch. 3, eqs. (3.87) and (3.88) (read at those locations): Carroll proves `∇_{[λ} R_{ρσ]μν} = 0` for the Christoffel connection and remarks that a
general connection has additional torsion terms; here the cyclic sum runs over the derivative slot and the two vector slots of `R(·,·)W`, which is the same
identity for the Christoffel connection by the pair symmetry (3.79) (kind: representation). The general statement (any `ModelWithCorners`) is the
milestone GE11. The comparison with Wald, *General Relativity*, eq. (3.2.13), is pending: the source was not read at the cited location.
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle Filter
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [IsManifold 𝓘(ℝ, E) 2 M] [CompleteSpace E]
variable (cov : Connection 𝓘(ℝ, E) M) [LocallySmoothConnection cov]

/-- `D_V U = ∇_V U` as a field. -/
def dd (V U : Π y : M, TangentSpace 𝓘(ℝ, E) y) : Π y : M, TangentSpace 𝓘(ℝ, E) y :=
  fun y => cov U y (V y)

/-- `∇_V U` is smooth near `x` for fields smooth near `x`. -/
theorem smoothNear_dd {V U : Π y : M, TangentSpace 𝓘(ℝ, E) y} {x : M}
    (hV : SmoothNear V x) (hU : SmoothNear U x) : SmoothNear (dd cov V U) x := by
  filter_upwards [eventually_eventually_nhds.2 hV, eventually_eventually_nhds.2 hU] with y hVy hUy
  exact contMDiffAt_covApply cov hVy.self_of_nhds hUy

/-- A field smooth near `x` is differentiable at `x`. -/
theorem mdiffAt_of_smoothNear {V : Π y : M, TangentSpace 𝓘(ℝ, E) y} {x : M} (hV : SmoothNear V x) :
    MDiffAt (T% V) x := hV.self_of_nhds.mdifferentiableAt (by simp)

/-- A connection is additive and compatible with the subtraction of fields smooth at `x`. -/
theorem cov_add_sub {A B C : Π y : M, TangentSpace 𝓘(ℝ, E) y} {x : M}
    (hA : SmoothNear A x) (hB : SmoothNear B x) (hC : SmoothNear C x) (u : TangentSpace 𝓘(ℝ, E) x) :
    cov (fun y => A y - B y - C y) x u = cov A x u - cov B x u - cov C x u := by
  have mA := mdiffAt_of_smoothNear hA
  have mB := mdiffAt_of_smoothNear hB
  have mC := mdiffAt_of_smoothNear hC
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
theorem hv_curvatureAt' {p : M} (hp : p ∈ (tTriv (E := E) x₀).baseSet)
    (X₀ Y₀ Z₀ : TangentSpace 𝓘(ℝ, E) p) :
    hv x₀ p (cov.curvatureAt p X₀ Y₀ Z₀) = Rhat cov x₀ p (hv x₀ p X₀) (hv x₀ p Y₀) (hv x₀ p Z₀) := by
  have h2 := curvature_hat cov x₀ hp (eventually_extend p X₀) (eventually_extend p Y₀)
    (eventually_extend p Z₀)
  simp only [FiberBundle.extend_apply_self] at h2
  unfold Connection.curvatureAt
  dsimp only
  simp only [FiberBundle.extend_apply_self]
  exact h2

/-- `Rhat` is subtractive in its first argument. -/
theorem Rhat_sub_left (p : M) (a a' b c : E) :
    Rhat cov x₀ p (a - a') b c = Rhat cov x₀ p a b c - Rhat cov x₀ p a' b c := by
  unfold Rhat
  simp only [map_sub, sub_apply]
  abel

/-- The curvature is additive (subtractive) in its first slot. -/
theorem curvatureAt_sub_left (x : M) (a b Y₀ Z₀ : TangentSpace 𝓘(ℝ, E) x) :
    cov.curvatureAt x (a - b) Y₀ Z₀ = cov.curvatureAt x a Y₀ Z₀ - cov.curvatureAt x b Y₀ Z₀ := by
  have hx : x ∈ (tTriv (E := E) x).baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have key : hv x x (cov.curvatureAt x (a - b) Y₀ Z₀) =
      hv x x (cov.curvatureAt x a Y₀ Z₀ - cov.curvatureAt x b Y₀ Z₀) := by
    rw [hv_sub x hx, hv_curvatureAt' cov x hx, hv_curvatureAt' cov x hx, hv_curvatureAt' cov x hx, hv_sub x hx]
    exact Rhat_sub_left cov x x _ _ _ _
  exact (symmL_hv x hx _).symm.trans ((congrArg ((tTriv (E := E) x).symmL ℝ x) key).trans (symmL_hv x hx _))

/-- `A - B - C` is smooth near `x` for fields smooth near `x`. -/
theorem smoothNear_sub3 {A B C : Π y : M, TangentSpace 𝓘(ℝ, E) y} {x : M}
    (hA : SmoothNear A x) (hB : SmoothNear B x) (hC : SmoothNear C x) :
    SmoothNear (fun y => A y - B y - C y) x := by
  filter_upwards [hA, hB, hC] with y hAy hBy hCy
  exact (hAy.sub_section hBy).sub_section hCy

/-- The curvature as a field: `y ↦ R(Y y, Z y) W y`. -/
def Rf (Y Z W : Π y : M, TangentSpace 𝓘(ℝ, E) y) : Π y : M, TangentSpace 𝓘(ℝ, E) y :=
  fun y => cov.curvatureAt y (Y y) (Z y) (W y)

/-- Near `x` the curvature field is `∇_Y ∇_Z W - ∇_Z ∇_Y W - ∇_{[Y,Z]} W` (from `curvatureAt_apply_eventually`). -/
theorem Rf_eventually {Y Z W : Π y : M, TangentSpace 𝓘(ℝ, E) y} {x : M}
    (hY : SmoothNear Y x) (hZ : SmoothNear Z x) (hW : SmoothNear W x) :
    Rf cov Y Z W =ᶠ[nhds x] fun y => dd cov Y (dd cov Z W) y - dd cov Z (dd cov Y W) y -
      dd cov (mlieBracket 𝓘(ℝ, E) Y Z) W y := by
  filter_upwards [eventually_eventually_nhds.2 hY, eventually_eventually_nhds.2 hZ,
    eventually_eventually_nhds.2 hW] with y hYy hZy hWy
  exact curvatureAt_apply_eventually cov Y Z W y hYy hZy hWy

/-- `∇_u` of the curvature field `R(Y,Z)W` at `x` in terms of third derivatives. -/
theorem cov_Rf {Y Z W : Π y : M, TangentSpace 𝓘(ℝ, E) y} {x : M}
    (hY : SmoothNear Y x) (hZ : SmoothNear Z x) (hW : SmoothNear W x) (u : TangentSpace 𝓘(ℝ, E) x) :
    cov (Rf cov Y Z W) x u = cov (dd cov Y (dd cov Z W)) x u - cov (dd cov Z (dd cov Y W)) x u -
      cov (dd cov (mlieBracket 𝓘(ℝ, E) Y Z) W) x u := by
  have hA := smoothNear_dd cov hY (smoothNear_dd cov hZ hW)
  have hB := smoothNear_dd cov hZ (smoothNear_dd cov hY hW)
  have hC := smoothNear_dd cov (smoothNear_mlieBracket hY hZ) hW
  have hR : SmoothNear (Rf cov Y Z W) x := by
    have hcomb := smoothNear_sub3 hA hB hC
    filter_upwards [eventually_eventually_nhds.2 (Rf_eventually cov hY hZ hW), eventually_eventually_nhds.2 hcomb]
      with y hEq hc
    exact hc.self_of_nhds.congr_of_eventuallyEq (hEq.mono fun q hq => by simp only [hq])
  have hcov := cov.isCovariantDerivativeOn (s := Set.univ)
  rw [hcov.congr_of_eventuallyEq (mdiffAt_of_smoothNear hR) (mdiffAt_of_smoothNear (smoothNear_sub3 hA hB hC)) Filter.univ_mem (Rf_eventually cov hY hZ hW)]
  exact cov_add_sub cov hA hB hC u

/-- One term of the operator proof of the second Bianchi identity. -/
theorem bianchi_term {X Y Z W : Π y : M, TangentSpace 𝓘(ℝ, E) y} {x : M}
    (hX : SmoothNear X x) (hY : SmoothNear Y x) (hZ : SmoothNear Z x) (hW : SmoothNear W x) :
    cov (Rf cov Y Z W) x (X x) - cov.curvatureAt x (Y x) (Z x) (cov W x (X x)) =
      cov (dd cov Y (dd cov Z W)) x (X x) - cov (dd cov Z (dd cov Y W)) x (X x)
        - cov (dd cov Z (dd cov X W)) x (Y x) + cov (dd cov Y (dd cov X W)) x (Z x)
        - cov.curvatureAt x (X x) (mlieBracket 𝓘(ℝ, E) Y Z x) (W x)
        - cov W x (mlieBracket 𝓘(ℝ, E) X (mlieBracket 𝓘(ℝ, E) Y Z) x) := by
  have hXW : SmoothNear (dd cov X W) x := smoothNear_dd cov hX hW
  have hV : SmoothNear (mlieBracket 𝓘(ℝ, E) Y Z) x := smoothNear_mlieBracket hY hZ
  have h1 := cov_Rf cov hY hZ hW (X x)
  have h2 := curvatureAt_apply_eventually cov Y Z (dd cov X W) x hY hZ hXW
  have h3 := curvatureAt_apply_eventually cov X (mlieBracket 𝓘(ℝ, E) Y Z) W x hX hV hW
  have h4 : (dd cov X W) x = cov W x (X x) := rfl
  rw [h4] at h2
  rw [h1, h2]
  rw [h3]
  have e1 : (fun y => cov (dd cov X W) y (Z y)) = dd cov Z (dd cov X W) := rfl
  have e2 : (fun y => cov (dd cov X W) y (Y y)) = dd cov Y (dd cov X W) := rfl
  have e3 : (fun y => cov W y (mlieBracket 𝓘(ℝ, E) Y Z y)) = dd cov (mlieBracket 𝓘(ℝ, E) Y Z) W := rfl
  rw [e1, e2, e3]
  abel

/-- The cyclic sum of `[D_X, R(Y,Z)] W` at `x` is `-Σ R(X, [Y,Z]) W` (operator Jacobi identity, the Jacobi identity of the Lie bracket). -/
theorem bianchi_second_fields {X Y Z W : Π y : M, TangentSpace 𝓘(ℝ, E) y} {x : M}
    (hX : SmoothNear X x) (hY : SmoothNear Y x) (hZ : SmoothNear Z x) (hW : SmoothNear W x) :
    (cov (Rf cov Y Z W) x (X x) - cov.curvatureAt x (Y x) (Z x) (cov W x (X x))) +
      (cov (Rf cov Z X W) x (Y x) - cov.curvatureAt x (Z x) (X x) (cov W x (Y x))) +
      (cov (Rf cov X Y W) x (Z x) - cov.curvatureAt x (X x) (Y x) (cov W x (Z x))) =
    -(cov.curvatureAt x (X x) (mlieBracket 𝓘(ℝ, E) Y Z x) (W x) +
      cov.curvatureAt x (Y x) (mlieBracket 𝓘(ℝ, E) Z X x) (W x) +
      cov.curvatureAt x (Z x) (mlieBracket 𝓘(ℝ, E) X Y x) (W x)) := by
  rw [bianchi_term cov hX hY hZ hW, bianchi_term cov hY hZ hX hW, bianchi_term cov hZ hX hY hW]
  have j := jacobi_cyc hX hY hZ
  have hj : cov W x (mlieBracket 𝓘(ℝ, E) X (mlieBracket 𝓘(ℝ, E) Y Z) x) +
      cov W x (mlieBracket 𝓘(ℝ, E) Y (mlieBracket 𝓘(ℝ, E) Z X) x) +
      cov W x (mlieBracket 𝓘(ℝ, E) Z (mlieBracket 𝓘(ℝ, E) X Y) x) = 0 := by
    rw [← map_add, ← map_add, j, map_zero]
  have h3 : cov W x (mlieBracket 𝓘(ℝ, E) Z (mlieBracket 𝓘(ℝ, E) X Y) x) =
      -(cov W x (mlieBracket 𝓘(ℝ, E) X (mlieBracket 𝓘(ℝ, E) Y Z) x)) -
        cov W x (mlieBracket 𝓘(ℝ, E) Y (mlieBracket 𝓘(ℝ, E) Z X) x) := by
    rw [eq_neg_of_add_eq_zero_right hj]; abel
  rw [h3]
  abel

/-- **The second Bianchi identity** for a torsion-free smooth connection. -/
theorem bianchi_second_proved (hT : cov.torsion = 0) (x : M) (X₀ Y₀ Z₀ W₀ : TangentSpace 𝓘(ℝ, E) x) :
    cov.covDerivCurvatureAt x X₀ Y₀ Z₀ W₀ + cov.covDerivCurvatureAt x Y₀ Z₀ X₀ W₀ +
      cov.covDerivCurvatureAt x Z₀ X₀ Y₀ W₀ = 0 := by
  set X := FiberBundle.extend E X₀ with hXd
  set Y := FiberBundle.extend E Y₀ with hYd
  set Z := FiberBundle.extend E Z₀ with hZd
  set W := FiberBundle.extend E W₀ with hWd
  have hX : SmoothNear X x := eventually_extend x X₀
  have hY : SmoothNear Y x := eventually_extend x Y₀
  have hZ : SmoothNear Z x := eventually_extend x Z₀
  have hW : SmoothNear W x := eventually_extend x W₀
  have hXx : X x = X₀ := FiberBundle.extend_apply_self E X₀
  have hYx : Y x = Y₀ := FiberBundle.extend_apply_self E Y₀
  have hZx : Z x = Z₀ := FiberBundle.extend_apply_self E Z₀
  have hWx : W x = W₀ := FiberBundle.extend_apply_self E W₀
  have F := bianchi_second_fields cov hX hY hZ hW
  rw [hXx, hYx, hZx, hWx] at F
  have tXY := cov_torsion hT (X := X) (Y := Y) (x := x) (mdiffAt_of_smoothNear hX) (mdiffAt_of_smoothNear hY)
  have tYZ := cov_torsion hT (X := Y) (Y := Z) (x := x) (mdiffAt_of_smoothNear hY) (mdiffAt_of_smoothNear hZ)
  have tZX := cov_torsion hT (X := Z) (Y := X) (x := x) (mdiffAt_of_smoothNear hZ) (mdiffAt_of_smoothNear hX)
  rw [hXx, hYx] at tXY
  rw [hYx, hZx] at tYZ
  rw [hZx, hXx] at tZX
  unfold Connection.covDerivCurvatureAt
  have e1 : (fun y => cov.curvatureAt y (extend E Y₀ y) (extend E Z₀ y) (extend E W₀ y)) = Rf cov Y Z W := rfl
  have e2 : (fun y => cov.curvatureAt y (extend E Z₀ y) (extend E X₀ y) (extend E W₀ y)) = Rf cov Z X W := rfl
  have e3 : (fun y => cov.curvatureAt y (extend E X₀ y) (extend E Y₀ y) (extend E W₀ y)) = Rf cov X Y W := rfl
  rw [e1, e2, e3]
  have F2 : cov (Rf cov Y Z W) x X₀ =
      -(cov.curvatureAt x X₀ (mlieBracket 𝓘(ℝ, E) Y Z x) W₀ +
        cov.curvatureAt x Y₀ (mlieBracket 𝓘(ℝ, E) Z X x) W₀ +
        cov.curvatureAt x Z₀ (mlieBracket 𝓘(ℝ, E) X Y x) W₀) +
      cov.curvatureAt x Y₀ Z₀ (cov W x X₀) -
      (cov (Rf cov Z X W) x Y₀ - cov.curvatureAt x Z₀ X₀ (cov W x Y₀)) -
      (cov (Rf cov X Y W) x Z₀ - cov.curvatureAt x X₀ Y₀ (cov W x Z₀)) := by
    rw [← F]; abel
  have A1 := curvatureAt_antisymm_left cov x Y₀ (cov Z x X₀) W₀
  have A2 := curvatureAt_antisymm_left cov x Z₀ (cov X x Y₀) W₀
  have A3 := curvatureAt_antisymm_left cov x X₀ (cov Y x Z₀) W₀
  have A4 := curvatureAt_antisymm_left cov x Z₀ (cov Y x X₀) W₀
  have A5 := curvatureAt_antisymm_left cov x X₀ (cov Z x Y₀) W₀
  have A6 := curvatureAt_antisymm_left cov x Y₀ (cov X x Z₀) W₀
  have B1 := curvatureAt_antisymm_left cov x X₀ (mlieBracket 𝓘(ℝ, E) Y Z x) W₀
  have B2 := curvatureAt_antisymm_left cov x Y₀ (mlieBracket 𝓘(ℝ, E) Z X x) W₀
  have B3 := curvatureAt_antisymm_left cov x Z₀ (mlieBracket 𝓘(ℝ, E) X Y x) W₀
  have S1 := curvatureAt_sub_left cov x (cov Z x Y₀) (cov Y x Z₀) X₀ W₀
  have S2 := curvatureAt_sub_left cov x (cov X x Z₀) (cov Z x X₀) Y₀ W₀
  have S3 := curvatureAt_sub_left cov x (cov Y x X₀) (cov X x Y₀) Z₀ W₀
  rw [tYZ] at S1
  rw [tZX] at S2
  rw [tXY] at S3
  rw [F2, B1, B2, B3, S1, S2, S3, A1, A2, A3]
  simp only [← hXd, ← hYd, ← hZd, ← hWd]
  abel
end Lightlike
