import Lightlike.Spacetime.Lorentzian

/-!
# Time orientation of a Lorentzian manifold

A *time orientation* of a Lorentzian manifold `(M, g)` is the continuous choice, at every point, of
one of the two halves of the light cone. It is given here as data: a continuous timelike vector
field `X`; a tangent vector `v` is then *future directed* when `g(v, X) < 0`. A manifold is
time orientable if such a field exists. (That a continuous time orientation can be replaced by a
smooth one is stated as a task, not used.)

Conventions: signature `(−,+,…,+)` as in `Lightlike/Spacetime/Lorentzian.lean`, which defines the
metric; no metric is defined here.

## Main definitions

* `Causal.TimeOrientation g`: a continuous timelike vector field.
* `Causal.TimeOrientation.IsFutureCausal`, `IsFutureTimelike`, `IsFutureNull`: future-directed
  causal, timelike and null tangent vectors; the `IsPast…` versions are the same with `X` reversed.

## References

* S. W. Hawking and G. F. R. Ellis, *The Large Scale Structure of Space-Time*, Cambridge University
  Press (1973), Section 6.2 (time orientation).
* R. M. Wald, *General Relativity*, University of Chicago Press (1984), Section 8.1.
-/

open Bundle Manifold
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike

namespace Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A **time orientation** of a Lorentzian metric `g`: a continuous vector field `X` with
`g(X, X) < 0` everywhere. The future light cone at `x` is the half of the cone of timelike vectors
containing `X x`. -/
structure TimeOrientation {n : ℕ} (g : LorentzianMetric I M n) where
  /-- The timelike vector field pointing to the future. -/
  X : (x : M) → TangentSpace I x
  /-- Continuity of `X` as a section of the tangent bundle. -/
  contMDiff : ContMDiff I (I.prod 𝓘(ℝ, E)) 0
    (fun x ↦ TotalSpace.mk' E (E := fun x : M ↦ TangentSpace I x) x (X x))
  /-- The field is timelike. -/
  timelike : ∀ x, g.g x (X x) (X x) < 0

/-- A Lorentzian manifold is **time orientable** if it admits a time orientation. -/
def TimeOrientable {n : ℕ} (g : LorentzianMetric I M n) : Prop := Nonempty (TimeOrientation g)

namespace TimeOrientation

variable {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- A tangent vector is **future-directed causal** if it is nonzero, `g(v, v) ≤ 0` and
`g(v, X) < 0`. -/
def IsFutureCausal {x : M} (v : TangentSpace I x) : Prop :=
  v ≠ 0 ∧ g.g x v v ≤ 0 ∧ g.g x v (T.X x) < 0

/-- A tangent vector is **future-directed timelike** if `g(v, v) < 0` and `g(v, X) < 0`. -/
def IsFutureTimelike {x : M} (v : TangentSpace I x) : Prop :=
  g.g x v v < 0 ∧ g.g x v (T.X x) < 0

/-- A tangent vector is **future-directed null** if it is future-directed causal with
`g(v, v) = 0`. -/
def IsFutureNull {x : M} (v : TangentSpace I x) : Prop :=
  T.IsFutureCausal v ∧ g.g x v v = 0

/-- A tangent vector is **past-directed causal** if it is nonzero, `g(v, v) ≤ 0` and
`g(v, X) > 0`. -/
def IsPastCausal {x : M} (v : TangentSpace I x) : Prop :=
  v ≠ 0 ∧ g.g x v v ≤ 0 ∧ 0 < g.g x v (T.X x)

/-- A tangent vector is **past-directed timelike** if `g(v, v) < 0` and `g(v, X) > 0`. -/
def IsPastTimelike {x : M} (v : TangentSpace I x) : Prop :=
  g.g x v v < 0 ∧ 0 < g.g x v (T.X x)

end TimeOrientation

end Causal

end Lightlike
