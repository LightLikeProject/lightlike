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
* `Causal.HasFutureEndpoint`, `HasPastEndpoint`, `NoEndpoints`: endpoints of a curve.
* `Causal.IsInextendibleWith P`: a curve with velocity in `P` and no endpoint;
  `IsInextendibleFutureTimelike`: the same for future timelike curves.

## References

* E. Minguzzi, *Lorentzian causality theory*, Living Reviews in Relativity 22 (2019), Section 2
  (causal curves as locally Lipschitz curves).
* R. M. Wald, *General Relativity*, University of Chicago Press (1984), Section 8.1
  (inextendible curves: curves without endpoint).
* S. W. Hawking and G. F. R. Ellis, *The Large Scale Structure of Space-Time*, Cambridge University
  Press (1973), Section 6.2.
-/

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology

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

/-- A tangent vector is **future-directed timelike with margin `ε`** if `g(v, X) < 0` and
`g(v, v) ≤ -ε g(v, X)²`. The set of such vectors is a closed cone strictly inside the future
timelike cone (in Minkowski space with `X = ∂ₜ`: `|v⃗| ≤ √(1 - ε) v⁰`); every closed cone strictly
inside the future timelike cone, near a point, lies in one of them. -/
def TimeOrientation.IsFutureTimelikeWith (ε : ℝ) {x : M} (v : TangentSpace I x) : Prop :=
  g.g x v v ≤ -ε * (g.g x v (T.X x)) ^ 2 ∧ g.g x v (T.X x) < 0

/-- A tangent vector is **past-directed timelike with margin `ε`**: `0 < g(v, X)` and
`g(v, v) ≤ -ε g(v, X)²`. -/
def TimeOrientation.IsPastTimelikeWith (ε : ℝ) {x : M} (v : TangentSpace I x) : Prop :=
  g.g x v v ≤ -ε * (g.g x v (T.X x)) ^ 2 ∧ 0 < g.g x v (T.X x)

/-- **Future-directed causal curve** on the interval `s`. -/
def IsFutureCausalCurve (γ : ℝ → M) (s : Set ℝ) : Prop :=
  IsCurveWith (I := I) (fun _ v ↦ T.IsFutureCausal v) γ s

/-- A **future-directed timelike curve** on the interval `s`: a curve with future-directed timelike
velocity almost everywhere, with a *margin* on every compact subinterval: on `[a, b] ⊆ s` there is
`ε > 0` with `g(γ', γ') ≤ -ε g(γ', X)²` almost everywhere, i.e. the velocity stays in a closed
cone strictly inside the future timelike cone.

**Difference of form from the textbooks** (Hawking–Ellis, Section 6.2; Wald, Section 8.1), who ask
only for a timelike velocity: the margin is an added hypothesis. For the curve classes of the
textbooks (piecewise `C¹`) it holds (`isFutureTimelikeCurve_of_contMDiffOn`). It is approved by the
project owner on 17 November 2026. Whether the two definitions give the same `I⁺` for smooth
metrics is open (task T-GE2-OPEN-MARGIN), not claimed. -/
def IsFutureTimelikeCurve (γ : ℝ → M) (s : Set ℝ) : Prop :=
  IsCurveWith (I := I) (fun _ v ↦ T.IsFutureTimelike v) γ s ∧
    ∀ a b : ℝ, a < b → Icc a b ⊆ s →
      ∃ ε : ℝ, 0 < ε ∧ IsCurveWith (I := I) (fun _ v ↦ T.IsFutureTimelikeWith ε v) γ (Icc a b)

/-- A **past-directed causal curve** on the interval `s`. -/
def IsPastCausalCurve (γ : ℝ → M) (s : Set ℝ) : Prop :=
  IsCurveWith (I := I) (fun _ v ↦ T.IsPastCausal v) γ s

/-- A **past-directed timelike curve** on the interval `s`, with a margin on compact
subintervals as for `IsFutureTimelikeCurve`. -/
def IsPastTimelikeCurve (γ : ℝ → M) (s : Set ℝ) : Prop :=
  IsCurveWith (I := I) (fun _ v ↦ T.IsPastTimelike v) γ s ∧
    ∀ a b : ℝ, a < b → Icc a b ⊆ s →
      ∃ ε : ℝ, 0 < ε ∧ IsCurveWith (I := I) (fun _ v ↦ T.IsPastTimelikeWith ε v) γ (Icc a b)

/-- `p` is a **future endpoint** of `γ` on `s`: every neighbourhood of `p` contains `γ t` for all
`t ∈ s` from some `c ∈ s` on (Wald, Section 8.1). The parameter interval may be unbounded; if it
has a last point `b`, the curve ends in `γ b`. -/
def HasFutureEndpoint (γ : ℝ → M) (s : Set ℝ) (p : M) : Prop :=
  ∀ U ∈ 𝓝 p, ∃ c ∈ s, ∀ t ∈ s, c ≤ t → γ t ∈ U

/-- `p` is a **past endpoint** of `γ` on `s`: every neighbourhood of `p` contains `γ t` for all
`t ∈ s` up to some `c ∈ s`. -/
def HasPastEndpoint (γ : ℝ → M) (s : Set ℝ) (p : M) : Prop :=
  ∀ U ∈ 𝓝 p, ∃ c ∈ s, ∀ t ∈ s, t ≤ c → γ t ∈ U

/-- A curve has **no endpoint** if its domain is nonempty and it has neither a future nor a past
endpoint. -/
def NoEndpoints (γ : ℝ → M) (s : Set ℝ) : Prop :=
  s.Nonempty ∧ (∀ p, ¬ HasFutureEndpoint γ s p) ∧ ∀ p, ¬ HasPastEndpoint γ s p

/-- A curve with velocity in `P` is **inextendible** if it has neither a future nor a past
endpoint (Wald, Section 8.1; Hawking–Ellis, Section 6.2: a causal curve is inextendible if it has
no endpoint). -/
def IsInextendibleWith (P : ∀ x : M, TangentSpace I x → Prop) (γ : ℝ → M) (s : Set ℝ) : Prop :=
  IsCurveWith (I := I) P γ s ∧ NoEndpoints γ s

/-- An **inextendible future-directed timelike curve**. -/
def IsInextendibleFutureTimelike (γ : ℝ → M) (s : Set ℝ) : Prop :=
  IsFutureTimelikeCurve T γ s ∧ NoEndpoints γ s

end Causal

end Lightlike
