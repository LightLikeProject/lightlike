import Mathlib
import Lightlike.Canonical.ADM
import Lightlike.Canonical.LieDeriv
import Lightlike.Spacetime.VolumeMeasure

/-!
# The ADM constraints on a hypersurface

The constraints `D[ξ] = ∫ π^{ij} (ℒ_ξ h)_ij` and `H[N] = ∫ N ℋ` of `Lightlike/Canonical/ADM.lean` on a second countable
Hausdorff manifold `M` (the hypersurface `Σ`) modelled on `ℝᵈ`, without a global chart.

**Data model.** Tensor fields are given by their components in the chart at every point `x₀ : M` (a *chart family*,
`ChartFam M α := M → (Fin d → ℝ) → α`), as `Lightlike.NondegMetric.coordMetric`. A chart family is a genuine tensor field
when it satisfies the change law of the chart changes `chgL` of `Lightlike/Spacetime/VolumeMeasure.lean`
(`IsCovTensor`, `IsVec`, `IsDensity`). The metric `h` is the coordinate metric of a Mathlib
`Bundle.ContMDiffRiemannianMetric` (`NondegMetric.ofRiemannian`); the momentum `π` is a symmetric contravariant tensor
density of weight one, a chart family with `π₀ = |det C| C⁻¹ π₁ C⁻ᵀ` (`IsDensity`).

**The smeared constraints** are sums over the atlas pieces of `VolumeMeasure.lean` (`atlasPiece`, disjoint, measurable, covering
`M`) of the chart integrals of the chart integrands (`momentumDensity`, `hamiltonianDensity`); for compactly supported
test fields the sum is finite. Their independence of the atlas is the covariance of the integrands under a chart change.

**The bracket** is `admBracketM`, the Gateaux derivative along a chart family, as `admBracket`.

**Limits.** No boundary, `C^∞` data; the chart changes use the preferred chart `chartAt` of every point as in
`VolumeMeasure.lean`; the Gateaux variations are chart families (symmetric, compactly supported), the change law of a
variation is not part of the definition of `admBracketM`.
-/

open MeasureTheory Set Manifold Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike.Canonical

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin d → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin d → ℝ) 2 M]

/-- A family of chart components: for every point `x₀` the components in the chart at `x₀`. -/
abbrev ChartFam (M : Type*) (d : ℕ) (α : Type*) := M → (Fin d → ℝ) → α

/-- The chart-change matrix at the point `p` from the chart at `x₀` to the chart at `x₁`. -/
def chgMat (x₀ x₁ p : M) : Matrix (Fin d) (Fin d) ℝ := LinearMap.toMatrix' (chgL (n := d) x₀ x₁ p).toLinearMap

/-- The function `N` on `M` in the chart at `x₀`. -/
def chartScalar (N : M → ℝ) (x₀ : M) : (Fin d → ℝ) → ℝ :=
  fun y => N ((extChartAt 𝓘(ℝ, Fin d → ℝ) x₀).symm y)

/-- **A symmetric covariant 2-tensor field** (the metric, the variations of the metric): chart components, smooth on the
chart targets, symmetric, with the change law `T₀ = Cᵀ T₁ C`. -/
def IsCovTensor (T : ChartFam M d (Matrix (Fin d) (Fin d) ℝ)) : Prop :=
  (∀ x₀ a b, ContDiffOn ℝ ∞ (fun y => T x₀ y a b) (extChartAt 𝓘(ℝ, Fin d → ℝ) x₀).target) ∧
    (∀ x₀ y, (T x₀ y)ᵀ = T x₀ y) ∧
    ∀ x₀ x₁ p, p ∈ (extChartAt 𝓘(ℝ, Fin d → ℝ) x₀).source → p ∈ (extChartAt 𝓘(ℝ, Fin d → ℝ) x₁).source →
      T x₀ (extChartAt 𝓘(ℝ, Fin d → ℝ) x₀ p) =
        (chgMat x₀ x₁ p)ᵀ * T x₁ (extChartAt 𝓘(ℝ, Fin d → ℝ) x₁ p) * chgMat x₀ x₁ p

/-- **A vector field**: chart components, smooth on the chart targets, with the change law `V₀ = C⁻¹ V₁`. -/
def IsVec (V : ChartFam M d (Fin d → ℝ)) : Prop :=
  (∀ x₀ k, ContDiffOn ℝ ∞ (fun y => V x₀ y k) (extChartAt 𝓘(ℝ, Fin d → ℝ) x₀).target) ∧
    ∀ x₀ x₁ p, p ∈ (extChartAt 𝓘(ℝ, Fin d → ℝ) x₀).source → p ∈ (extChartAt 𝓘(ℝ, Fin d → ℝ) x₁).source →
      V x₀ (extChartAt 𝓘(ℝ, Fin d → ℝ) x₀ p) =
        (chgMat x₀ x₁ p)⁻¹ *ᵥ V x₁ (extChartAt 𝓘(ℝ, Fin d → ℝ) x₁ p)

/-- **A symmetric contravariant tensor density of weight one** (the momentum): chart components, smooth on the chart
targets, symmetric, with the change law `π₀ = |det C| C⁻¹ π₁ C⁻ᵀ`. -/
def IsDensity (T : ChartFam M d (Matrix (Fin d) (Fin d) ℝ)) : Prop :=
  (∀ x₀ a b, ContDiffOn ℝ ∞ (fun y => T x₀ y a b) (extChartAt 𝓘(ℝ, Fin d → ℝ) x₀).target) ∧
    (∀ x₀ y, (T x₀ y)ᵀ = T x₀ y) ∧
    ∀ x₀ x₁ p, p ∈ (extChartAt 𝓘(ℝ, Fin d → ℝ) x₀).source → p ∈ (extChartAt 𝓘(ℝ, Fin d → ℝ) x₁).source →
      T x₀ (extChartAt 𝓘(ℝ, Fin d → ℝ) x₀ p) =
        |(chgMat (d := d) x₀ x₁ p).det| • ((chgMat x₀ x₁ p)⁻¹ * T x₁ (extChartAt 𝓘(ℝ, Fin d → ℝ) x₁ p) *
          ((chgMat x₀ x₁ p)⁻¹)ᵀ)

/-- A chart family supported in a compact set of `M`: the components vanish at the chart images of the points outside. -/
def HasCompactSupportFam {α : Type*} [Zero α] (T : ChartFam M d α) : Prop :=
  ∃ K : Set M, IsCompact K ∧ ∀ x₀ y, y ∈ (extChartAt 𝓘(ℝ, Fin d → ℝ) x₀).target →
    (extChartAt 𝓘(ℝ, Fin d → ℝ) x₀).symm y ∉ K → T x₀ y = 0

variable [MeasurableSpace M] [BorelSpace M]

/-- The image under the chart of the atlas piece `i`. -/
def pieceImage (i : AtlasIdx (n := d) M) : Set (Fin d → ℝ) :=
  extChartAt 𝓘(ℝ, Fin d → ℝ) i.1 '' atlasPiece i

/-- The sum over the atlas pieces of the chart integrals of a chart density `f`. -/
def chartSum (f : ChartFam M d ℝ) : ℝ := ∑' i : AtlasIdx (n := d) M, ∫ y in pieceImage i, f i.1 y

/-- **The smeared momentum constraint on `M`**: `D[ξ] = ∫ π^{ij} (ℒ_ξ h)_ij`. -/
def momentumConstraintM (ξ : ChartFam M d (Fin d → ℝ)) (h π : ChartFam M d (Matrix (Fin d) (Fin d) ℝ)) : ℝ :=
  chartSum fun x₀ y => momentumDensity (ξ x₀) (h x₀) (π x₀) y

/-- **The smeared Hamiltonian constraint on `M`**: `H[N] = ∫ N ℋ`. -/
def hamiltonianConstraintM (N : M → ℝ) (h π : ChartFam M d (Matrix (Fin d) (Fin d) ℝ)) : ℝ :=
  chartSum fun x₀ y => chartScalar N x₀ y * hamiltonianDensity (h x₀) (π x₀) y

/-- The Gateaux derivative of a functional of chart families. -/
def dirDerivM (F : ChartFam M d (Matrix (Fin d) (Fin d) ℝ) → ChartFam M d (Matrix (Fin d) (Fin d) ℝ) → ℝ)
    (h π k p : ChartFam M d (Matrix (Fin d) (Fin d) ℝ)) : ℝ :=
  deriv (fun t : ℝ => F (h + t • k) (π + t • p)) 0

/-- **The bracket on `M`**, as `admBracket`. -/
def admBracketM (F G : ChartFam M d (Matrix (Fin d) (Fin d) ℝ) → ChartFam M d (Matrix (Fin d) (Fin d) ℝ) → ℝ)
    (Fπ Gπ : ChartFam M d (Matrix (Fin d) (Fin d) ℝ) → ChartFam M d (Matrix (Fin d) (Fin d) ℝ) →
      ChartFam M d (Matrix (Fin d) (Fin d) ℝ))
    (h π : ChartFam M d (Matrix (Fin d) (Fin d) ℝ)) : ℝ :=
  dirDerivM F h π (Gπ h π) 0 - dirDerivM G h π (Fπ h π) 0

/-- The `π`-gradient of `D[ξ]`: the chart components of `ℒ_ξ h`. -/
def momentumPiGradM (ξ : ChartFam M d (Fin d → ℝ)) (h : ChartFam M d (Matrix (Fin d) (Fin d) ℝ)) :
    ChartFam M d (Matrix (Fin d) (Fin d) ℝ) :=
  fun x₀ => lieTensor (ξ x₀) (h x₀)

/-- The `π`-gradient of `H[N]`. -/
def hamiltonianPiGradM (N : M → ℝ) (h π : ChartFam M d (Matrix (Fin d) (Fin d) ℝ)) :
    ChartFam M d (Matrix (Fin d) (Fin d) ℝ) :=
  fun x₀ => hamiltonianPiGradient (chartScalar N x₀) (h x₀) (π x₀)

/-- The Lie bracket of two vector fields, chart by chart. -/
def lieBracketM (ξ η : ChartFam M d (Fin d → ℝ)) : ChartFam M d (Fin d → ℝ) :=
  fun x₀ y k => lieBracket (ξ x₀) (η x₀) y k

/-- The derivative of the lapse along the shift, `ξ^k ∂_k N`, a function on `M` (computed in the chart at the point). -/
def shiftLapse (ξ : ChartFam M d (Fin d → ℝ)) (N : M → ℝ) : M → ℝ :=
  fun p => ∑ k, ξ p (extChartAt 𝓘(ℝ, Fin d → ℝ) p p) k *
    Lightlike.pd k (chartScalar N p) (extChartAt 𝓘(ℝ, Fin d → ℝ) p p)

/-- The shift of the bracket of two Hamiltonian constraints, `Y^i = h^{ij} (N ∂_j M − M ∂_j N)`, chart by chart. -/
def structureShift (h : ChartFam M d (Matrix (Fin d) (Fin d) ℝ)) (N M' : M → ℝ) : ChartFam M d (Fin d → ℝ) :=
  fun x₀ y i => ∑ j, (h x₀ y)⁻¹ i j *
    (chartScalar N x₀ y * Lightlike.pd j (chartScalar M' x₀) y - chartScalar M' x₀ y * Lightlike.pd j (chartScalar N x₀) y)

end Lightlike.Canonical

end
