import Lightlike.Spacetime.Causal.CausalCurve

/-!
# Task T-GE2-P20

A limit curve through an accumulation point of inextendible causal curves is an inextendible causal
curve.

The statement is `Lightlike.Causal.exists_inextendible_limit_curve`, at the end of this file. Replace
its `sorry` by a proof and change nothing else in the file: the proof-task check rejects any other
change (CONTRIBUTING.md).

Hint. The one-chart endpoint form is `Lightlike.Causal.exists_limit_curve` (`LL-0151`,
`Lightlike/Spacetime/CausalLadder/LimitCurve.lean`); cover by charts and diagonalise.

Source: S. W. Hawking and G. F. R. Ellis, The Large Scale Structure of Space-Time, Cambridge
University Press (1973), Chapter: Causal structure (`hawking-ellis-1973` in
docs/tasks/sources.yaml).
Lock and dependencies: `docs/tasks/tasks.yaml`. This header is written by `scripts/tasks.py deps`
from the plan, the sources and the library.
-/

open Bundle Manifold Set Filter Topology
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- **Limit-curve theorem** (Hawking–Ellis, Lemma 6.2.1). If `p` is an accumulation point of a
sequence of inextendible future-directed causal curves (every neighbourhood of `p` meets infinitely
many of them), there is an inextendible future-directed causal curve through `p`, each of whose points
is an accumulation point of the sequence. The hypothesis `[BoundarylessManifold I M]` matches the
source (space-time has no boundary); the comparison with the source at a location is pending. The
one-chart endpoint form is `exists_limit_curve` (`LL-0151`). -/
theorem exists_inextendible_limit_curve [T2Space M] [SecondCountableTopology M]
    [BoundarylessManifold I M] (γ : ℕ → ℝ → M) (s : ℕ → Set ℝ)
    (hγ : ∀ k, IsInextendibleWith (I := I) (fun _ v ↦ T.IsFutureCausal v) (γ k) (s k)) (p : M)
    (hp : ∀ U ∈ 𝓝 p, ∃ᶠ k in atTop, ∃ t ∈ s k, γ k t ∈ U) :
    ∃ (σ : ℝ → M) (r : Set ℝ),
      IsInextendibleWith (I := I) (fun _ v ↦ T.IsFutureCausal v) σ r ∧ p ∈ σ '' r ∧
        ∀ q ∈ σ '' r, ∀ U ∈ 𝓝 q, ∃ᶠ k in atTop, ∃ t ∈ s k, γ k t ∈ U := by
  sorry

end Lightlike.Causal
