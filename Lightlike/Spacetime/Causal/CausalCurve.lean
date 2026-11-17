import Lightlike.Spacetime.Causal.TimeOrientation

/-!
# Causal curves

A *causal curve* is a locally Lipschitz curve `γ : s → M`, `s ⊆ ℝ` an interval, whose tangent
vector, which exists almost everywhere by Rademacher's theorem, is future-directed causal almost
everywhere. Timelike curves are the same with future-directed timelike tangents. Locally Lipschitz
is the weakest regularity under which the tangent exists almost everywhere and the usual causal
theory holds (it is the regularity of the limit curve theorems); piecewise smooth curves are
included.

A curve is a map `γ : ℝ → M` together with its domain `s : Set ℝ` with `s.OrdConnected`, so that
only the values on `s` matter. *Locally Lipschitz* is stated in charts: around each `t ∈ s` the
curve stays in the chart at `γ t` and its chart image is Lipschitz.

## Main definitions

* `Causal.IsLocallyLipschitzOn`: the chart-wise Lipschitz condition on a set.
* `Causal.IsCurveWith P γ s`: locally Lipschitz and `P` holds almost everywhere on the velocity.
* `Causal.IsFutureCausalCurve`, `IsFutureTimelikeCurve`: the two cases of interest, for a time
  orientation `T`; `IsPastCausalCurve`, `IsPastTimelikeCurve`.
* `Causal.IsInextendibleWith P`: a curve with velocity in `P` and no proper extension to a larger
  interval.

## References

* E. Minguzzi, *Lorentzian causality theory*, Living Reviews in Relativity 22 (2019), Section 2
  (causal curves as locally Lipschitz curves).
* S. W. Hawking and G. F. R. Ellis, *The Large Scale Structure of Space-Time*, Cambridge University
  Press (1973), Section 6.2.
-/

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike

namespace Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A curve `γ : ℝ → M` is **locally Lipschitz on `s`** if around every `t ∈ s` it stays, on a
neighbourhood of `t` in `s`, inside the chart at `γ t` and has a Lipschitz image there. -/
def IsLocallyLipschitzOn (γ : ℝ → M) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, ∃ (K : NNReal) (U : Set ℝ), U ∈ nhdsWithin t s ∧
    MapsTo γ U (extChartAt I (γ t)).source ∧
    LipschitzOnWith K ((extChartAt I (γ t)) ∘ γ) U

/-- The velocity `γ'(t)` of a curve `γ : ℝ → M` along `s` (a junk value where the curve is not
differentiable within `s`). -/
def velocity (I : ModelWithCorners ℝ E H) (γ : ℝ → M) (s : Set ℝ) (t : ℝ) : TangentSpace I (γ t) :=
  mfderivWithin 𝓘(ℝ, ℝ) I γ s t (1 : ℝ)

/-- A **curve whose velocity satisfies `P`**: locally Lipschitz on `s`, and for almost every
`t ∈ s` differentiable within `s` with velocity satisfying `P`. `s` is an interval. -/
structure IsCurveWith (P : ∀ x : M, TangentSpace I x → Prop) (γ : ℝ → M) (s : Set ℝ) : Prop where
  /-- The domain is an interval. -/
  ordConnected : s.OrdConnected
  /-- The curve is locally Lipschitz. -/
  lipschitz : IsLocallyLipschitzOn (I := I) γ s
  /-- The velocity exists and satisfies `P` almost everywhere on `s`. -/
  ae_velocity : ∀ᵐ t ∂(volume.restrict s),
    MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t ∧ P (γ t) (velocity I γ s t)

variable {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- A **future-directed causal curve** on the interval `s`. -/
def IsFutureCausalCurve (γ : ℝ → M) (s : Set ℝ) : Prop :=
  IsCurveWith (I := I) (fun _ v ↦ T.IsFutureCausal v) γ s

/-- A **future-directed timelike curve** on the interval `s`. -/
def IsFutureTimelikeCurve (γ : ℝ → M) (s : Set ℝ) : Prop :=
  IsCurveWith (I := I) (fun _ v ↦ T.IsFutureTimelike v) γ s

/-- A **past-directed causal curve** on the interval `s`. -/
def IsPastCausalCurve (γ : ℝ → M) (s : Set ℝ) : Prop :=
  IsCurveWith (I := I) (fun _ v ↦ T.IsPastCausal v) γ s

/-- A **past-directed timelike curve** on the interval `s`. -/
def IsPastTimelikeCurve (γ : ℝ → M) (s : Set ℝ) : Prop :=
  IsCurveWith (I := I) (fun _ v ↦ T.IsPastTimelike v) γ s

/-- A curve with velocity in `P` is **inextendible** if no curve with velocity in `P` agrees with it
on `s` and has a strictly larger interval domain. -/
def IsInextendibleWith (P : ∀ x : M, TangentSpace I x → Prop) (γ : ℝ → M) (s : Set ℝ) : Prop :=
  IsCurveWith (I := I) P γ s ∧
    ∀ (γ' : ℝ → M) (s' : Set ℝ), s ⊆ s' → IsCurveWith (I := I) P γ' s' → EqOn γ γ' s → s' = s

end Causal

end Lightlike
