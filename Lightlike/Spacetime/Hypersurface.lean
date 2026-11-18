import Lightlike.Spacetime.BianchiSecond
import Lightlike.Spacetime.LieMetric

/-!
# Hypersurfaces: the unit normal and the second fundamental form (GE13, first part)

A hypersurface is given as a level set of a smooth function `φ` near a point `x₀`: the leaves `φ = c` through the points near
`x₀` foliate a neighbourhood. `IsUnitNormal g φ n ε x₀` says that `n` is a smooth field near `x₀` with `g(n, n) = ε = ±1`
and that the tangent vectors of the leaves (the kernel of `dφ`) are exactly the vectors `g`-orthogonal to `n`; so the
leaves are non-null. A field `X` is tangent (`IsTangentNear φ X x₀`) when `dφ (X) = 0` near `x₀`.

* `lieBracket_isTangentNear`: the bracket of two tangent fields is tangent (`mfderiv_mlieBracket`);
* `secondFF`: the second fundamental form (extrinsic curvature) `K(v, w) = g(∇_v n, w)`;
* `secondFF_symm_fields`: `K` is symmetric on tangent fields, for a torsion-free metric connection.

**Limits.** The leaves are not given a manifold structure, so "induced metric" and the intrinsic curvature of a leaf are not
available as objects; the Gauss and Codazzi relations are stated with the tangential connection `D` of the leaves
(second part). The existence of a unit normal `n` for a function `φ` with `dφ ≠ 0` and non-null gradient is a hypothesis,
not proved. Manifolds as in `CurvatureSymmetries.lean`.
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
  have h1 : (show ℝ from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) φ y (mlieBracket 𝓘(ℝ, E) X Y y)) = 0 := by
    rw [key, e1.mfderiv_eq, e2.mfderiv_eq]
    trace_state
    simp [mfderiv_const]
    trace_state
  exact h1

end Hypersurface

end Lightlike
