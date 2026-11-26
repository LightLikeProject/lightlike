import Lightlike.Spacetime.BianchiSecond
import Lightlike.Spacetime.LieMetric

/-!
# Hypersurfaces: unit normal, second fundamental form, Gauss and Codazzi relations (GE13)

A hypersurface is given as a level set of a smooth function `φ` near a point `x₀`: the leaves `φ = c` near `x₀` foliate a
neighbourhood. `IsUnitNormal g φ n ε x₀` says that `n` is a smooth field near `x₀` with `g(n, n) = ε = ±1` and that the tangent
vectors of the leaves (the kernel of `dφ`) are exactly the vectors `g`-orthogonal to `n`, so the leaves are non-null.
A field `X` is tangent (`IsTangentNear φ X x₀`) when `dφ (X) = 0` near `x₀`.

* `lieBracket_isTangentNear`: the bracket of two tangent fields is tangent (`mfderiv_mlieBracket`);
* `secondFF`: the second fundamental form (extrinsic curvature) `K(v, w) = g(∇_v n, w)`;
* `secondFF_symm_fields`: `K` is symmetric on tangent fields (torsion free, metric compatible connection);
  `exists_tangent_extension`: a tangent vector extends to a smooth tangent field;
* `Dfield`: the tangential connection `D_Y Z = (∇_Y Z)^T` of the leaves; `dd_eq_Dfield`: `∇_Y Z = D_Y Z - ε K(Y, Z) n`;
* `gauss_relation`: `g(R(X, Y) Z, W) = g(R^D(X, Y) Z, W) - ε (K(Y, Z) K(X, W) - K(X, Z) K(Y, W))` for tangent fields,
  with `R^D = gaussCurv` the curvature of `D` (metric compatible connection);
* `codazzi_relation`: `g(R(X, Y) Z, n) = -((D_X K)(Y, Z) - (D_Y K)(X, Z))` (Levi-Civita connection), `covK` is `D_X K`.

**Limits.** The leaves are not given a manifold structure, so the intrinsic Levi-Civita curvature of
a leaf is not an object here (the induced metric is defined pointwise in `HypersurfaceInduced.lean`, as `g` restricted to
`ker dφ`): `D` is the tangential part of `∇` on tangent fields, and `gaussCurv` is its curvature (`D` is
torsion free and compatible with the restriction of `g` on tangent fields; that it is *the* Levi-Civita connection of the
leaf is not stated). The unit normal is a hypothesis here; `exists_isUnitNormal` (`HypersurfaceNormal.lean`) constructs it for a function `φ` whose
gradient at `x₀` is not null.
The trust checks of the milestone (the sphere in `ℝ³`, a slice of FLRW) are not in this file. Manifolds as in
`CurvatureSymmetries.lean` (no boundary, `T2Space`, smooth connection).
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle Filter
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [IsManifold 𝓘(ℝ, E) 2 M] [CompleteSpace E]

namespace Hypersurface

/-- **A unit normal field to the level sets of `φ` near `x₀`.** -/
structure IsUnitNormal (g : NondegMetric 𝓘(ℝ, E) M) (φ : M → ℝ) (n : Π y : M, TangentSpace 𝓘(ℝ, E) y) (ε : ℝ)
    (x₀ : M) : Prop where
  eps : ε = 1 ∨ ε = -1
  phi : ∀ᶠ y in 𝓝 x₀, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ φ y
  smooth : SmoothNear n x₀
  norm : ∀ᶠ y in 𝓝 x₀, g.g y (n y) (n y) = ε
  ker : ∀ᶠ y in 𝓝 x₀, ∀ v : TangentSpace 𝓘(ℝ, E) y,
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) φ y v = 0 ↔ g.g y (n y) v = 0

/-- A field is **tangent** to the level sets of `φ` near `x₀`: `dφ (X) = 0`. -/
def IsTangentNear (φ : M → ℝ) (X : Π y : M, TangentSpace 𝓘(ℝ, E) y) (x₀ : M) : Prop :=
  ∀ᶠ y in 𝓝 x₀, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) φ y (X y) = 0

/-- **The second fundamental form** (extrinsic curvature) `K(v, w) = g(∇_v n, w)`. -/
def secondFF (cov : Connection 𝓘(ℝ, E) M) (g : NondegMetric 𝓘(ℝ, E) M)
    (n : Π y : M, TangentSpace 𝓘(ℝ, E) y) (x : M) (v w : TangentSpace 𝓘(ℝ, E) x) : ℝ :=
  g.g x (cov n x v) w

variable {g : NondegMetric 𝓘(ℝ, E) M} {φ : M → ℝ} {n : Π y : M, TangentSpace 𝓘(ℝ, E) y} {ε : ℝ} {x₀ : M}

/-- A tangent field is `g`-orthogonal to `n` near `x₀`. -/
theorem IsTangentNear.ortho (hn : IsUnitNormal g φ n ε x₀) {X : Π y : M, TangentSpace 𝓘(ℝ, E) y}
    (hX : IsTangentNear φ X x₀) : ∀ᶠ y in 𝓝 x₀, g.g y (n y) (X y) = 0 := by
  filter_upwards [hn.ker, hX] with y hk hy
  exact (hk _).1 hy

/-- **The bracket of two tangent fields is tangent.** -/
theorem lieBracket_isTangentNear (hn : IsUnitNormal g φ n ε x₀) {X Y : Π y : M, TangentSpace 𝓘(ℝ, E) y}
    (hXs : SmoothNear X x₀) (hYs : SmoothNear Y x₀) (hX : IsTangentNear φ X x₀)
    (hY : IsTangentNear φ Y x₀) : IsTangentNear φ (mlieBracket 𝓘(ℝ, E) X Y) x₀ := by
  filter_upwards [eventually_eventually_nhds.2 hn.phi, eventually_eventually_nhds.2 hX,
    eventually_eventually_nhds.2 hY, eventually_eventually_nhds.2 hXs, eventually_eventually_nhds.2 hYs] with
    y hφ hXy hYy hXsy hYsy
  have key := mfderiv_mlieBracket φ X Y y hφ (mdiffAt_of_smoothNear hXsy) (mdiffAt_of_smoothNear hYsy)
  have e1 : dirDeriv φ Y =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
    filter_upwards [hYy] with z hz
    exact hz
  have e2 : dirDeriv φ X =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
    filter_upwards [hXy] with z hz
    exact hz
  show mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) φ y (mlieBracket 𝓘(ℝ, E) X Y y) = 0
  have z1 : (show ℝ from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (dirDeriv φ Y) y (X y)) = 0 := by
    rw [e1.mfderiv_eq]; simp [mfderiv_const]; rfl
  have z2 : (show ℝ from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (dirDeriv φ X) y (Y y)) = 0 := by
    rw [e2.mfderiv_eq]; simp [mfderiv_const]; rfl
  have h1 : (show ℝ from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) φ y (mlieBracket 𝓘(ℝ, E) X Y y)) = 0 := by
    rw [key, z1, z2]; simp
  exact h1

/-- `g(n, Y)` has zero derivative at `x₀` along any vector when `Y` is tangent near `x₀`. -/
theorem IsTangentNear.mvfderiv_gpair (hn : IsUnitNormal g φ n ε x₀) {Y : Π y : M, TangentSpace 𝓘(ℝ, E) y}
    (hY : IsTangentNear φ Y x₀) (u : TangentSpace 𝓘(ℝ, E) x₀) :
    (show ℝ from mvfderiv 𝓘(ℝ, E) (gpair g n Y) x₀ u) = 0 := by
  have e : gpair g n Y =ᶠ[𝓝 x₀] fun _ => (0 : ℝ) := by
    filter_upwards [hY.ortho hn] with z hz using hz
  rw [mvfderiv_congr e]
  simp [mvfderiv, mfderiv_const]

/-- **The second fundamental form is symmetric** on tangent fields, for a torsion-free metric connection:
`g(∇_X n, Y) = g(∇_Y n, X)` at `x₀`. -/
theorem secondFF_symm_fields {cov : Connection 𝓘(ℝ, E) M} (h : cov.IsLeviCivita g)
    (hn : IsUnitNormal g φ n ε x₀) {X Y : Π y : M, TangentSpace 𝓘(ℝ, E) y}
    (hXs : SmoothNear X x₀) (hYs : SmoothNear Y x₀) (hX : IsTangentNear φ X x₀)
    (hY : IsTangentNear φ Y x₀) :
    secondFF cov g n x₀ (X x₀) (Y x₀) = secondFF cov g n x₀ (Y x₀) (X x₀) := by
  have mX := mdiffAt_of_smoothNear hXs
  have mY := mdiffAt_of_smoothNear hYs
  have mn := mdiffAt_of_smoothNear hn.smooth
  have cA := h.2 Y n X x₀ mY mn mX
  have cB := h.2 X n Y x₀ mX mn mY
  have zA := hX.mvfderiv_gpair hn (Y x₀)
  have zB := hY.mvfderiv_gpair hn (X x₀)
  have tor := ((CovariantDerivative.torsion_eq_zero_iff cov).1 h.1) mX mY
  have hbr : IsTangentNear φ (mlieBracket 𝓘(ℝ, E) X Y) x₀ := lieBracket_isTangentNear hn hXs hYs hX hY
  have o := (hbr.ortho hn).self_of_nhds
  have hsA : mvfderiv 𝓘(ℝ, E) (gpair g n X) x₀ (Y x₀) =
      g.g x₀ (cov n x₀ (Y x₀)) (X x₀) + g.g x₀ (n x₀) (cov X x₀ (Y x₀)) := cA
  have hsB : mvfderiv 𝓘(ℝ, E) (gpair g n Y) x₀ (X x₀) =
      g.g x₀ (cov n x₀ (X x₀)) (Y x₀) + g.g x₀ (n x₀) (cov Y x₀ (X x₀)) := cB
  unfold secondFF
  have t2 : g.g x₀ (n x₀) (cov Y x₀ (X x₀)) - g.g x₀ (n x₀) (cov X x₀ (Y x₀)) = 0 := by
    rw [← map_sub, tor]; exact o
  have := zA; have := zB
  linarith

/-- **A tangent vector extends to a smooth tangent field**: the tangential part `V - ε g(V, n) n` of an extension `V`. -/
theorem exists_tangent_extension (hn : IsUnitNormal g φ n ε x₀) (v : TangentSpace 𝓘(ℝ, E) x₀)
    (hv : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) φ x₀ v = 0) :
    ∃ X : Π y : M, TangentSpace 𝓘(ℝ, E) y, SmoothNear X x₀ ∧ IsTangentNear φ X x₀ ∧ X x₀ = v := by
  set V := FiberBundle.extend E v with hV
  have hVs : SmoothNear V x₀ := eventually_extend x₀ v
  have hVx : V x₀ = v := FiberBundle.extend_apply_self E v
  refine ⟨fun y => V y - (ε * g.g y (V y) (n y)) • n y, ?_, ?_, ?_⟩
  · filter_upwards [hVs, hn.smooth] with y hVy hny
    exact hVy.sub_section ((contMDiffAt_const.mul (contMDiffAt_gpair g hVy hny)).smul_section hny)
  · filter_upwards [hn.ker, hn.norm] with y hk hnorm
    refine (hk _).2 ?_
    have hε : ε * ε = 1 := by rcases hn.eps with h | h <;> rw [h] <;> norm_num
    have := g.symm y (V y) (n y)
    simp only [map_sub, map_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hnorm]
    rw [this]
    linear_combination (-(g.g y (n y) (V y))) * hε
  · have hk := hn.ker.self_of_nhds
    have h0 : g.g x₀ (n x₀) v = 0 := (hk v).1 hv
    simp only [hVx]
    rw [g.symm x₀ v (n x₀), h0]
    simp


/-- The unit normal data persists near `x₀`. -/
theorem IsUnitNormal.eventually (hn : IsUnitNormal g φ n ε x₀) : ∀ᶠ y in 𝓝 x₀, IsUnitNormal g φ n ε y := by
  filter_upwards [eventually_eventually_nhds.2 hn.phi, eventually_eventually_nhds.2 hn.smooth,
    eventually_eventually_nhds.2 hn.norm, eventually_eventually_nhds.2 hn.ker] with y h1 h2 h3 h4
  exact ⟨hn.eps, h1, h2, h3, h4⟩

theorem IsTangentNear.eventually {X : Π y : M, TangentSpace 𝓘(ℝ, E) y} (hX : IsTangentNear φ X x₀) :
    ∀ᶠ y in 𝓝 x₀, IsTangentNear φ X y := eventually_eventually_nhds.2 hX

/-- The tangential projection `v - ε g(v, n) n`. -/
def tanProj (g : NondegMetric 𝓘(ℝ, E) M) (n : Π y : M, TangentSpace 𝓘(ℝ, E) y) (ε : ℝ) (y : M)
    (v : TangentSpace 𝓘(ℝ, E) y) : TangentSpace 𝓘(ℝ, E) y :=
  v - (ε * g.g y v (n y)) • n y

variable (cov : Connection 𝓘(ℝ, E) M) [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]

/-- The derivative of the second fundamental form pairing `y ↦ g(∇_Y n, Z)`. -/
def Kf (g : NondegMetric 𝓘(ℝ, E) M) (n Y Z : Π y : M, TangentSpace 𝓘(ℝ, E) y) : M → ℝ :=
  gpair g (dd cov Y n) Z

/-- The tangential connection `D_Y Z = (∇_Y Z)^T` as a field. -/
def Dfield (g : NondegMetric 𝓘(ℝ, E) M) (n : Π y : M, TangentSpace 𝓘(ℝ, E) y) (ε : ℝ)
    (Y Z : Π y : M, TangentSpace 𝓘(ℝ, E) y) : Π y : M, TangentSpace 𝓘(ℝ, E) y :=
  fun y => tanProj g n ε y (dd cov Y Z y)

/-- `∇_Y Z = D_Y Z - ε K(Y, Z) n` near `x₀`, for tangent fields and a metric connection. -/
theorem dd_eq_Dfield (hC : cov.IsMetricCompatible g) (hn : IsUnitNormal g φ n ε x₀)
    {Y Z : Π y : M, TangentSpace 𝓘(ℝ, E) y} (hYs : SmoothNear Y x₀) (hZs : SmoothNear Z x₀)
    (hZ : IsTangentNear φ Z x₀) :
    dd cov Y Z =ᶠ[𝓝 x₀] fun y => Dfield cov g n ε Y Z y + (-(ε * Kf cov g n Y Z y)) • n y := by
  filter_upwards [hn.eventually, hZ.eventually, hYs, hZs, hn.smooth] with y hny hZy hYy hZsy hnsy
  have mY := hYy.mdifferentiableAt (by simp)
  have mZ := hZsy.mdifferentiableAt (by simp)
  have mn := hnsy.mdifferentiableAt (by simp)
  have c := hC Y n Z y mY mn mZ
  have z := hZy.mvfderiv_gpair hny (Y y)
  have hsy : mvfderiv 𝓘(ℝ, E) (gpair g n Z) y (Y y) =
      g.g y (cov n y (Y y)) (Z y) + g.g y (n y) (cov Z y (Y y)) := c
  have key : g.g y (dd cov Y Z y) (n y) = - Kf cov g n Y Z y := by
    have := g.symm y (n y) (dd cov Y Z y)
    simp only [Kf, gpair, dd] at this ⊢
    linarith
  show dd cov Y Z y = tanProj g n ε y (dd cov Y Z y) + (-(ε * Kf cov g n Y Z y)) • n y
  unfold tanProj
  rw [key]
  module

theorem smoothNear_Dfield (hn : IsUnitNormal g φ n ε x₀) {Y Z : Π y : M, TangentSpace 𝓘(ℝ, E) y}
    (hYs : SmoothNear Y x₀) (hZs : SmoothNear Z x₀) : SmoothNear (Dfield cov g n ε Y Z) x₀ := by
  filter_upwards [smoothNear_dd cov hYs hZs, hn.smooth] with y hd hny
  exact hd.sub_section ((contMDiffAt_const.mul (contMDiffAt_gpair g hd hny)).smul_section hny)

theorem contMDiffAt_Kf {Y Z n : Π y : M, TangentSpace 𝓘(ℝ, E) y} {x₀ : M}
    (hYs : SmoothNear Y x₀) (hZs : SmoothNear Z x₀) (hn : SmoothNear n x₀) :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (Kf cov g n Y Z) x₀ :=
  contMDiffAt_gpair g (smoothNear_dd cov hYs hn).self_of_nhds hZs.self_of_nhds

/-- **The normal component of `∇_u (∇_Y Z)`** against a tangent vector `w`:
`g(∇_u ∇_Y Z, w) = g(∇_u D_Y Z, w) - ε K(Y, Z) K(u, w)`. -/
theorem gauss_term (hC : cov.IsMetricCompatible g) (hn : IsUnitNormal g φ n ε x₀)
    {Y Z : Π y : M, TangentSpace 𝓘(ℝ, E) y} (hYs : SmoothNear Y x₀) (hZs : SmoothNear Z x₀)
    (hZ : IsTangentNear φ Z x₀) (u w : TangentSpace 𝓘(ℝ, E) x₀) (hw : g.g x₀ (n x₀) w = 0) :
    g.g x₀ (cov (dd cov Y Z) x₀ u) w =
      g.g x₀ (cov (Dfield cov g n ε Y Z) x₀ u) w - ε * Kf cov g n Y Z x₀ * secondFF cov g n x₀ u w := by
  have hDs := smoothNear_Dfield cov hn hYs hZs
  have hKs := contMDiffAt_Kf cov (g := g) hYs hZs hn.smooth
  have hgs : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun y => -(ε * Kf cov g n Y Z y)) x₀ :=
    (contMDiffAt_const.mul hKs).neg
  have mD := mdiffAt_of_smoothNear hDs
  have mn := mdiffAt_of_smoothNear hn.smooth
  have mgn : MDiffAt (T% ((fun y => -(ε * Kf cov g n Y Z y)) • n)) x₀ :=
    MDifferentiableAt.smul_section (hgs.mdifferentiableAt (by simp)) mn
  have hcov := cov.isCovariantDerivativeOn (s := Set.univ)
  have e := dd_eq_Dfield cov hC hn hYs hZs hZ
  have mdd := mdiffAt_of_smoothNear (smoothNear_dd cov hYs hZs)
  have e' : dd cov Y Z =ᶠ[𝓝 x₀] (Dfield cov g n ε Y Z + (fun y => -(ε * Kf cov g n Y Z y)) • n) := by
    filter_upwards [e] with y hy using hy
  have step1 : cov (dd cov Y Z) x₀ = cov (Dfield cov g n ε Y Z + (fun y => -(ε * Kf cov g n Y Z y)) • n) x₀ :=
    hcov.congr_of_eventuallyEq mdd (mdifferentiableAt_add_section mD mgn) Filter.univ_mem e'
  rw [step1, hcov.add mD mgn, hcov.leibniz mn (hgs.mdifferentiableAt (by simp))]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, map_add,
    map_smul, smul_eq_mul, hw, mul_zero, add_zero]
  unfold secondFF
  ring

/-- The curvature of the tangential connection `D` of the leaves:
`R^D(X, Y) Z = D_X D_Y Z - D_Y D_X Z - D_{[X,Y]} Z` at `x`, with `D_u U = (∇_u U)^T`. -/
def gaussCurv (g : NondegMetric 𝓘(ℝ, E) M) (n : Π y : M, TangentSpace 𝓘(ℝ, E) y) (ε : ℝ)
    (X Y Z : Π y : M, TangentSpace 𝓘(ℝ, E) y) (x : M) : TangentSpace 𝓘(ℝ, E) x :=
  tanProj g n ε x (cov (Dfield cov g n ε Y Z) x (X x)) - tanProj g n ε x (cov (Dfield cov g n ε X Z) x (Y x)) -
    tanProj g n ε x (cov Z x (mlieBracket 𝓘(ℝ, E) X Y x))

/-- **The Gauss relation**: for tangent fields `X, Y, Z, W` and a metric connection,
`g(R(X, Y) Z, W) = g(R^D(X, Y) Z, W) - ε (K(Y, Z) K(X, W) - K(X, Z) K(Y, W))` at `x₀`. -/
theorem gauss_relation (hC : cov.IsMetricCompatible g) (hn : IsUnitNormal g φ n ε x₀)
    {X Y Z W : Π y : M, TangentSpace 𝓘(ℝ, E) y}
    (hXs : SmoothNear X x₀) (hYs : SmoothNear Y x₀) (hZs : SmoothNear Z x₀)
    (hX : IsTangentNear φ X x₀) (hY : IsTangentNear φ Y x₀) (hZ : IsTangentNear φ Z x₀)
    (hW : IsTangentNear φ W x₀) :
    g.g x₀ (cov.curvatureAt x₀ (X x₀) (Y x₀) (Z x₀)) (W x₀) =
      g.g x₀ (gaussCurv cov g n ε X Y Z x₀) (W x₀) -
        ε * (secondFF cov g n x₀ (Y x₀) (Z x₀) * secondFF cov g n x₀ (X x₀) (W x₀) -
          secondFF cov g n x₀ (X x₀) (Z x₀) * secondFF cov g n x₀ (Y x₀) (W x₀)) := by
  have hw : g.g x₀ (n x₀) (W x₀) = 0 := (hW.ortho hn).self_of_nhds
  have hproj : ∀ v : TangentSpace 𝓘(ℝ, E) x₀, g.g x₀ (tanProj g n ε x₀ v) (W x₀) = g.g x₀ v (W x₀) := by
    intro v
    unfold tanProj
    simp only [map_sub, map_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hw]
    ring
  have hR := curvatureAt_apply_eventually cov X Y Z x₀ hXs hYs hZs
  have t1 := gauss_term cov hC hn hYs hZs hZ (X x₀) (W x₀) hw
  have t2 := gauss_term cov hC hn hXs hZs hZ (Y x₀) (W x₀) hw
  unfold gaussCurv
  simp only [map_sub, ContinuousLinearMap.sub_apply, hproj]
  rw [hR]
  simp only [map_sub, ContinuousLinearMap.sub_apply]
  have k1 : Kf cov g n Y Z x₀ = secondFF cov g n x₀ (Y x₀) (Z x₀) := rfl
  have k2 : Kf cov g n X Z x₀ = secondFF cov g n x₀ (X x₀) (Z x₀) := rfl
  rw [← k1, ← k2]
  have := t1; have := t2
  change g.g x₀ (cov (dd cov Y Z) x₀ (X x₀)) (W x₀) - g.g x₀ (cov (dd cov X Z) x₀ (Y x₀)) (W x₀) -
    g.g x₀ (cov Z x₀ (mlieBracket 𝓘(ℝ, E) X Y x₀)) (W x₀) = _
  rw [t1, t2]
  ring

theorem mvfderiv_negEps {f : M → ℝ} {x : M} (ε : ℝ) (hf : MDiffAt f x) (u : TangentSpace 𝓘(ℝ, E) x) :
    (show ℝ from mvfderiv 𝓘(ℝ, E) (fun y => -(ε * f y)) x u) = -(ε * (show ℝ from mvfderiv 𝓘(ℝ, E) f x u)) := by
  have h1 : MDiffAt (fun y => ε * f y) x := mdifferentiableAt_const.mul hf
  have h2 := congrArg (fun L => L u) (mvfderiv_fun_neg (I := 𝓘(ℝ, E)) (g := fun y => ε * f y) (x := x))
  have h3 := congrArg (fun L => L u) (mvfderiv_fun_mul (I := 𝓘(ℝ, E)) (f := fun _ : M => ε) (g := f) (x := x)
    mdifferentiableAt_const hf)
  simp only [mvfderiv_const, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.neg_apply, smul_eq_mul, smul_zero, add_zero] at h2 h3
  exact h2.trans (congrArg Neg.neg h3)

/-- **The splitting of `∇_u (∇_Y Z)`** into the tangential part, the normal part along `∇_u n` and the derivative of the
coefficient. -/
theorem cov_dd_split (hC : cov.IsMetricCompatible g) (hn : IsUnitNormal g φ n ε x₀)
    {Y Z : Π y : M, TangentSpace 𝓘(ℝ, E) y} (hYs : SmoothNear Y x₀) (hZs : SmoothNear Z x₀)
    (hZ : IsTangentNear φ Z x₀) (u : TangentSpace 𝓘(ℝ, E) x₀) :
    cov (dd cov Y Z) x₀ u = cov (Dfield cov g n ε Y Z) x₀ u +
      (-(ε * Kf cov g n Y Z x₀)) • cov n x₀ u + (-(ε * (show ℝ from mvfderiv 𝓘(ℝ, E) (Kf cov g n Y Z) x₀ u))) • n x₀ := by
  have hDs := smoothNear_Dfield cov hn hYs hZs
  have hKs := contMDiffAt_Kf cov (g := g) hYs hZs hn.smooth
  have hgs : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun y => -(ε * Kf cov g n Y Z y)) x₀ :=
    (contMDiffAt_const.mul hKs).neg
  have mD := mdiffAt_of_smoothNear hDs
  have mn := mdiffAt_of_smoothNear hn.smooth
  have hgd := hgs.mdifferentiableAt (by simp)
  have mgn : MDiffAt (T% ((fun y => -(ε * Kf cov g n Y Z y)) • n)) x₀ :=
    MDifferentiableAt.smul_section hgd mn
  have hcov := cov.isCovariantDerivativeOn (s := Set.univ)
  have e := dd_eq_Dfield cov hC hn hYs hZs hZ
  have mdd := mdiffAt_of_smoothNear (smoothNear_dd cov hYs hZs)
  have e' : dd cov Y Z =ᶠ[𝓝 x₀] (Dfield cov g n ε Y Z + (fun y => -(ε * Kf cov g n Y Z y)) • n) := by
    filter_upwards [e] with y hy using hy
  have step1 : cov (dd cov Y Z) x₀ = cov (Dfield cov g n ε Y Z + (fun y => -(ε * Kf cov g n Y Z y)) • n) x₀ :=
    hcov.congr_of_eventuallyEq mdd (mdifferentiableAt_add_section mD mgn) Filter.univ_mem e'
  rw [step1, hcov.add mD mgn, hcov.leibniz mn hgd]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply]
  rw [add_assoc]
  congr 2
  exact congrArg (fun r => r • n x₀) (mvfderiv_negEps ε (hKs.mdifferentiableAt (by simp)) u)

/-- `g(∇_u n, n) = 0` since `g(n, n)` is constant. -/
theorem cov_n_ortho (hC : cov.IsMetricCompatible g) (hn : IsUnitNormal g φ n ε x₀) (u : TangentSpace 𝓘(ℝ, E) x₀) :
    g.g x₀ (cov n x₀ u) (n x₀) = 0 := by
  set X := FiberBundle.extend E u with hX
  have hXs : SmoothNear X x₀ := eventually_extend x₀ u
  have hXx : X x₀ = u := FiberBundle.extend_apply_self E u
  have mn := mdiffAt_of_smoothNear hn.smooth
  have c := hC X n n x₀ (mdiffAt_of_smoothNear hXs) mn mn
  have e : gpair g n n =ᶠ[𝓝 x₀] fun _ => ε := by
    filter_upwards [hn.norm] with y hy using hy
  have z : (show ℝ from mvfderiv 𝓘(ℝ, E) (gpair g n n) x₀ (X x₀)) = 0 := by
    rw [mvfderiv_congr e]; simp [mvfderiv, mfderiv_const]
  have hs : mvfderiv 𝓘(ℝ, E) (gpair g n n) x₀ (X x₀) =
      g.g x₀ (cov n x₀ (X x₀)) (n x₀) + g.g x₀ (n x₀) (cov n x₀ (X x₀)) := c
  rw [hXx] at z hs
  have := g.symm x₀ (n x₀) (cov n x₀ u)
  linarith

/-- For a tangent field `U`: `g(∇_u U, n) = - g(∇_u n, U)`. -/
theorem cov_tangent_ortho (hC : cov.IsMetricCompatible g) (hn : IsUnitNormal g φ n ε x₀)
    {U : Π y : M, TangentSpace 𝓘(ℝ, E) y} (hUs : SmoothNear U x₀) (hU : IsTangentNear φ U x₀)
    (u : TangentSpace 𝓘(ℝ, E) x₀) :
    g.g x₀ (cov U x₀ u) (n x₀) = - g.g x₀ (cov n x₀ u) (U x₀) := by
  set X := FiberBundle.extend E u with hX
  have hXs : SmoothNear X x₀ := eventually_extend x₀ u
  have hXx : X x₀ = u := FiberBundle.extend_apply_self E u
  have c := hC X n U x₀ (mdiffAt_of_smoothNear hXs) (mdiffAt_of_smoothNear hn.smooth) (mdiffAt_of_smoothNear hUs)
  have z := hU.mvfderiv_gpair hn (X x₀)
  have hs : mvfderiv 𝓘(ℝ, E) (gpair g n U) x₀ (X x₀) =
      g.g x₀ (cov n x₀ (X x₀)) (U x₀) + g.g x₀ (n x₀) (cov U x₀ (X x₀)) := c
  rw [hXx] at z hs
  have := g.symm x₀ (n x₀) (cov U x₀ u)
  linarith

theorem Dfield_isTangentNear (hn : IsUnitNormal g φ n ε x₀) (Y Z : Π y : M, TangentSpace 𝓘(ℝ, E) y) :
    IsTangentNear φ (Dfield cov g n ε Y Z) x₀ := by
  filter_upwards [hn.ker, hn.norm] with y hk hnorm
  refine (hk _).2 ?_
  have hε : ε * ε = 1 := by rcases hn.eps with h | h <;> rw [h] <;> norm_num
  unfold Dfield tanProj
  have := g.symm y (dd cov Y Z y) (n y)
  simp only [map_sub, map_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hnorm]
  linear_combination (-(g.g y (n y) (dd cov Y Z y))) * hε + (-(ε * ε)) * this

/-- The covariant derivative of the second fundamental form along `X`, in the leaf connection `D`:
`(D_X K)(Y, Z) = X (K(Y, Z)) - K(D_X Y, Z) - K(Y, D_X Z)`. -/
def covK (g : NondegMetric 𝓘(ℝ, E) M) (n : Π y : M, TangentSpace 𝓘(ℝ, E) y) (ε : ℝ)
    (X Y Z : Π y : M, TangentSpace 𝓘(ℝ, E) y) (x : M) : ℝ :=
  (show ℝ from mvfderiv 𝓘(ℝ, E) (Kf cov g n Y Z) x (X x)) -
    secondFF cov g n x (Dfield cov g n ε X Y x) (Z x) - secondFF cov g n x (Y x) (Dfield cov g n ε X Z x)

/-- The normal-direction term of `∇_u (∇_Y Z)`: `g(∇_u ∇_Y Z, n) = - K(u, D_Y Z) - u (K(Y, Z))`. -/
theorem codazzi_term (hC : cov.IsMetricCompatible g) (hn : IsUnitNormal g φ n ε x₀)
    {Y Z : Π y : M, TangentSpace 𝓘(ℝ, E) y} (hYs : SmoothNear Y x₀) (hZs : SmoothNear Z x₀)
    (hZ : IsTangentNear φ Z x₀) (u : TangentSpace 𝓘(ℝ, E) x₀) :
    g.g x₀ (cov (dd cov Y Z) x₀ u) (n x₀) =
      - secondFF cov g n x₀ u (Dfield cov g n ε Y Z x₀) - (show ℝ from mvfderiv 𝓘(ℝ, E) (Kf cov g n Y Z) x₀ u) := by
  have hε : ε * ε = 1 := by rcases hn.eps with h | h <;> rw [h] <;> norm_num
  have hnn : g.g x₀ (n x₀) (n x₀) = ε := hn.norm.self_of_nhds
  have hDs := smoothNear_Dfield cov hn hYs hZs
  have a := cov_tangent_ortho cov hC hn hDs (Dfield_isTangentNear cov hn Y Z) u
  have b := cov_n_ortho cov hC hn u
  rw [cov_dd_split cov hC hn hYs hZs hZ u]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, b, hnn, a, mul_zero, add_zero]
  unfold secondFF
  linear_combination (-(show ℝ from mvfderiv 𝓘(ℝ, E) (Kf cov g n Y Z) x₀ u)) * hε

/-- **The Codazzi relation**: for tangent fields and the Levi-Civita connection,
`g(R(X, Y) Z, n) = - ((D_X K)(Y, Z) - (D_Y K)(X, Z))` at `x₀`. -/
theorem codazzi_relation (h : cov.IsLeviCivita g) (hn : IsUnitNormal g φ n ε x₀)
    {X Y Z : Π y : M, TangentSpace 𝓘(ℝ, E) y}
    (hXs : SmoothNear X x₀) (hYs : SmoothNear Y x₀) (hZs : SmoothNear Z x₀)
    (hX : IsTangentNear φ X x₀) (hY : IsTangentNear φ Y x₀) (hZ : IsTangentNear φ Z x₀) :
    g.g x₀ (cov.curvatureAt x₀ (X x₀) (Y x₀) (Z x₀)) (n x₀) =
      -(covK cov g n ε X Y Z x₀ - covK cov g n ε Y X Z x₀) := by
  have hC := h.2
  have hR := curvatureAt_apply_eventually cov X Y Z x₀ hXs hYs hZs
  have t1 := codazzi_term cov hC hn hYs hZs hZ (X x₀)
  have t2 := codazzi_term cov hC hn hXs hZs hZ (Y x₀)
  have t3 := cov_tangent_ortho cov hC hn hZs hZ (mlieBracket 𝓘(ℝ, E) X Y x₀)
  have tor := ((CovariantDerivative.torsion_eq_zero_iff cov).1 h.1) (mdiffAt_of_smoothNear hXs) (mdiffAt_of_smoothNear hYs)
  have hbr : IsTangentNear φ (mlieBracket 𝓘(ℝ, E) X Y) x₀ := lieBracket_isTangentNear hn hXs hYs hX hY
  have o := (hbr.ortho hn).self_of_nhds
  -- `D_X Y - D_Y X = [X, Y]`
  have hgb : g.g x₀ (cov Y x₀ (X x₀)) (n x₀) = g.g x₀ (cov X x₀ (Y x₀)) (n x₀) := by
    have h1 : g.g x₀ (cov Y x₀ (X x₀) - cov X x₀ (Y x₀)) (n x₀) = 0 := by
      rw [tor, g.symm]; exact o
    simp only [map_sub, ContinuousLinearMap.sub_apply] at h1
    linarith
  have hD : Dfield cov g n ε X Y x₀ - Dfield cov g n ε Y X x₀ = mlieBracket 𝓘(ℝ, E) X Y x₀ := by
    unfold Dfield tanProj dd
    rw [← tor, hgb]
    abel
  have hK : secondFF cov g n x₀ (mlieBracket 𝓘(ℝ, E) X Y x₀) (Z x₀) =
      secondFF cov g n x₀ (Dfield cov g n ε X Y x₀) (Z x₀) - secondFF cov g n x₀ (Dfield cov g n ε Y X x₀) (Z x₀) := by
    rw [← hD]; unfold secondFF
    simp only [map_sub, ContinuousLinearMap.sub_apply]
  have hg : g.g x₀ (cov.curvatureAt x₀ (X x₀) (Y x₀) (Z x₀)) (n x₀) =
      g.g x₀ (cov (dd cov Y Z) x₀ (X x₀)) (n x₀) - g.g x₀ (cov (dd cov X Z) x₀ (Y x₀)) (n x₀) -
        g.g x₀ (cov Z x₀ (mlieBracket 𝓘(ℝ, E) X Y x₀)) (n x₀) := by
    rw [hR]; simp only [map_sub, ContinuousLinearMap.sub_apply]; rfl
  rw [hg, t1, t2, t3]
  unfold covK
  unfold secondFF at hK ⊢
  linarith

end Hypersurface

end Lightlike
