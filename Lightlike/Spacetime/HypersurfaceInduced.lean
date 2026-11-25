import Lightlike.Spacetime.HypersurfaceNormal

/-!
# The induced metric of a level set, pointwise

For a smooth function `φ` on a manifold `M` with a pseudo-Riemannian metric `g`, the level set of `φ` through a point
`p` has the tangent space `ker dφ(p)`, a subspace of the ambient tangent space. The leaves are not given a manifold
structure here (see `Hypersurface.lean`), so the **induced metric** is defined pointwise: it is the restriction of
`g_p` to that subspace, a bilinear form on it.

* `levelTangent φ p`: the subspace `ker dφ(p)` of the tangent space at `p`;
* `inducedMetric g φ p`: the bilinear form `g_p` restricted to `levelTangent φ p`;
* `inducedMetric_apply`: its value on two vectors is `g_p` of their images;
* `inducedMetric_symm`: it is symmetric;
* `inducedMetric_separating_of_isUnitNormal`: if the level set has a unit normal at `p` (`g(n, n) = ±1`, the normal is
  not null), the induced metric at `p` is nondegenerate: a tangent vector orthogonal to every tangent vector is zero;
* `inducedMetric_separating_of_nonnull`: the same for a function with non-null gradient at `p`, using
  `exists_isUnitNormal`.
-/

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace Lightlike

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [IsManifold 𝓘(ℝ, E) 2 M] [CompleteSpace E]

namespace Hypersurface

/-- **The tangent space of the level set of `φ` through `p`**: the kernel of the differential `dφ(p)`, as a subspace
of the tangent space of `M` at `p`. -/
def levelTangent (φ : M → ℝ) (p : M) : Submodule ℝ (TangentSpace 𝓘(ℝ, E) p) :=
  LinearMap.ker (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) φ p).toLinearMap

/-- A vector lies in `levelTangent φ p` exactly when `dφ(p)` kills it. -/
theorem mem_levelTangent {φ : M → ℝ} {p : M} {v : TangentSpace 𝓘(ℝ, E) p} :
    v ∈ levelTangent φ p ↔ mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) φ p v = 0 :=
  Iff.rfl

/-- The metric `g_p` as a bilinear form on the tangent space at `p`. -/
def metricForm (g : NondegMetric 𝓘(ℝ, E) M) (p : M) : LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, E) p) :=
  (ContinuousLinearMap.coeLM ℝ).comp (g.g p).toLinearMap

@[simp] theorem metricForm_apply (g : NondegMetric 𝓘(ℝ, E) M) (p : M) (v w : TangentSpace 𝓘(ℝ, E) p) :
    metricForm g p v w = g.g p v w :=
  rfl

/-- **The induced metric of the level set of `φ` through `p`**: `g_p` restricted to the tangent space
`ker dφ(p)` of the level set, a bilinear form on it. No manifold structure on the leaf is used. -/
def inducedMetric (g : NondegMetric 𝓘(ℝ, E) M) (φ : M → ℝ) (p : M) :
    LinearMap.BilinForm ℝ (levelTangent (E := E) φ p) :=
  (metricForm g p).restrict (levelTangent φ p)

/-- The induced metric of two tangent vectors is `g_p` of them. -/
@[simp] theorem inducedMetric_apply (g : NondegMetric 𝓘(ℝ, E) M) (φ : M → ℝ) (p : M)
    (v w : levelTangent (E := E) φ p) :
    inducedMetric g φ p v w = g.g p (v : TangentSpace 𝓘(ℝ, E) p) (w : TangentSpace 𝓘(ℝ, E) p) :=
  rfl

/-- **The induced metric is symmetric.** -/
theorem inducedMetric_symm (g : NondegMetric 𝓘(ℝ, E) M) (φ : M → ℝ) (p : M)
    (v w : levelTangent (E := E) φ p) : inducedMetric g φ p v w = inducedMetric g φ p w v := by
  simp only [inducedMetric_apply]
  exact g.symm p _ _

/-- **The induced metric is nondegenerate where the level set has a unit normal** (the normal is not null):
if `n` is a unit normal to the level sets of `φ` near `p` with `g(n, n) = ε = ±1`, a tangent vector `v` with
`g_p(v, w) = 0` for every tangent vector `w` is zero. -/
theorem inducedMetric_separating_of_isUnitNormal (g : NondegMetric 𝓘(ℝ, E) M) {φ : M → ℝ}
    {n : Π y : M, TangentSpace 𝓘(ℝ, E) y} {ε : ℝ} {p : M} (hn : IsUnitNormal g φ n ε p)
    (v : levelTangent (E := E) φ p) (hv : ∀ w : levelTangent (E := E) φ p, inducedMetric g φ p v w = 0) :
    v = 0 := by
  have hnorm : g.g p (n p) (n p) = ε := hn.norm.self_of_nhds
  have hker : ∀ u : TangentSpace 𝓘(ℝ, E) p,
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) φ p u = 0 ↔ g.g p (n p) u = 0 := hn.ker.self_of_nhds
  have hε2 : ε * ε = 1 := by rcases hn.eps with h | h <;> rw [h] <;> norm_num
  have hvN : g.g p (n p) (v : TangentSpace 𝓘(ℝ, E) p) = 0 := (hker _).1 v.2
  -- every vector splits into a tangent part and a multiple of the normal
  have hv0 : (v : TangentSpace 𝓘(ℝ, E) p) = 0 := by
    apply g.nondegenerate p
    intro u
    set c : ℝ := ε * g.g p (n p) u with hc
    have hw : (u - c • n p) ∈ levelTangent (E := E) φ p := by
      rw [mem_levelTangent, hker]
      simp only [map_sub, map_smul, smul_eq_mul,
        hnorm, hc]
      linear_combination (-(g.g p (n p) u)) * hε2
    have h1 : g.g p (v : TangentSpace 𝓘(ℝ, E) p) (u - c • n p) = 0 := hv ⟨_, hw⟩
    have h2 : g.g p (v : TangentSpace 𝓘(ℝ, E) p) (n p) = 0 := by rw [g.symm]; exact hvN
    have h3 : u = (u - c • n p) + c • n p := by abel
    rw [h3, map_add, map_smul, h1, h2]
    simp
  exact Subtype.ext hv0

/-- **The induced metric is nondegenerate where the gradient is not null**: for `φ` smooth near `p` whose gradient at
`p` is not null, a tangent vector of the level set orthogonal to all tangent vectors is zero. The unit normal is
supplied by `exists_isUnitNormal`. -/
theorem inducedMetric_separating_of_nonnull (g : NondegMetric 𝓘(ℝ, E) M) {φ : M → ℝ} {p : M}
    (hφ : ∀ᶠ y in 𝓝 p, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ φ y)
    (hnn : ∀ ξ : TangentSpace 𝓘(ℝ, E) p, (∀ v, g.g p ξ v = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) φ p v) → g.g p ξ ξ ≠ 0)
    (v : levelTangent (E := E) φ p) (hv : ∀ w : levelTangent (E := E) φ p, inducedMetric g φ p v w = 0) :
    v = 0 := by
  obtain ⟨n, ε, hn⟩ := exists_isUnitNormal g hφ hnn
  exact inducedMetric_separating_of_isUnitNormal g hn v hv

end Hypersurface

end Lightlike
