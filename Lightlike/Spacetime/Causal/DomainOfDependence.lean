import Lightlike.Spacetime.Causal.Ladder

/-!
# Domains of dependence

The *future domain of dependence* `D⁺(S)` of a set `S` is the set of points `p` such that every
past-inextendible causal curve through `p` meets `S`; `D⁻(S)` is the time dual, and
`D(S) = D⁺(S) ∪ D⁻(S)`.

Formulation. A past-inextendible causal curve through `p` is the part, up to `p`, of an
inextendible future-directed causal curve through `p`. So `p ∈ D⁺(S)` is stated as: for every
inextendible future-directed causal curve `γ` and every parameter `t` with `γ t = p`, the curve
meets `S` at some parameter `t' ≤ t`. `D⁻(S)` is the same with `t ≤ t'`. This avoids a separate
notion of one-sided inextendibility and agrees with the usual definition because every causal
curve extends to an inextendible one.

## Main definitions

* `Causal.domainDepFuture`, `Causal.domainDepPast`, `Causal.domainDep`: `D⁺(S)`, `D⁻(S)`, `D(S)`.

## References

* R. Geroch, *Domain of dependence*, J. Math. Phys. 11 (1970) 437.
* S. W. Hawking and G. F. R. Ellis, *The Large Scale Structure of Space-Time*, Cambridge University
  Press (1973), Section 6.5.
-/

open Bundle Manifold Set
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike

namespace Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- The **future domain of dependence** `D⁺(S)`: the points `p` such that every inextendible
future-directed causal curve through `p` meets `S` at or before `p`. -/
def domainDepFuture (S : Set M) : Set M :=
  {p | ∀ (γ : ℝ → M) (s : Set ℝ),
    IsInextendibleWith (I := I) (fun _ v ↦ T.IsFutureCausal v) γ s →
      ∀ t ∈ s, γ t = p → ∃ t' ∈ s, t' ≤ t ∧ γ t' ∈ S}

/-- The **past domain of dependence** `D⁻(S)`: the points `p` such that every inextendible
future-directed causal curve through `p` meets `S` at or after `p`. -/
def domainDepPast (S : Set M) : Set M :=
  {p | ∀ (γ : ℝ → M) (s : Set ℝ),
    IsInextendibleWith (I := I) (fun _ v ↦ T.IsFutureCausal v) γ s →
      ∀ t ∈ s, γ t = p → ∃ t' ∈ s, t ≤ t' ∧ γ t' ∈ S}

/-- The **domain of dependence** `D(S) = D⁺(S) ∪ D⁻(S)`. -/
def domainDep (S : Set M) : Set M := domainDepFuture T S ∪ domainDepPast T S

end Causal

end Lightlike
