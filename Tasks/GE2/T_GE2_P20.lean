import Lightlike.Spacetime.Causal.CausalCurve

/-!
# Task T-GE2-P20

A limit curve through a limit point of future-inextendible causal curves is a future-inextendible
causal curve.

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

/-- **Limit-curve theorem** (Hawking–Ellis, Lemma 6.2.1; the comparison with the source at a
location is pending). Let `γ k` be future-inextendible future-directed causal curves, on the intervals
`s k`: curves of the library's class (`IsFutureCausalCurve`) with no future endpoint (they do not
converge to a point of `M` as the parameter tends to the top of `s k`). If `p` is a limit point of the
sequence (every neighbourhood of `p` meets infinitely many of the curves), there is a future-inextendible
future-directed causal curve `σ` through `p` that is a limit curve of one subsequence: for every point `q`
of `σ` and every neighbourhood `U` of `q`, all but finitely many curves of the subsequence meet `U`.

Differences from the source, all representation: the open set `O` of the source is taken to be the
whole manifold (an open subset of a space-time is a space-time with the restricted metric, so the source's
`O` is covered by applying the statement to it); `[T2Space M]`, `[SecondCountableTopology M]` and
`[BoundarylessManifold I M]` are the conventions on space-time (Hawking–Ellis: a connected paracompact
Hausdorff manifold without boundary); the curves are the library's causal curves (locally Lipschitz, with
velocity in the future causal cone almost everywhere). Only the future end is asked to be inextendible, as
in the source. The one-chart endpoint form is `exists_limit_curve` (`LL-0151`). -/
theorem exists_inextendible_limit_curve [T2Space M] [SecondCountableTopology M]
    [BoundarylessManifold I M] (γ : ℕ → ℝ → M) (s : ℕ → Set ℝ)
    (hγ : ∀ k, IsFutureCausalCurve T (γ k) (s k) ∧
      ∀ q : M, ¬ Tendsto (fun t : s k => γ k t) atTop (𝓝 q))
    (p : M) (hp : ∀ U ∈ 𝓝 p, ∃ᶠ k in atTop, ∃ t ∈ s k, γ k t ∈ U) :
    ∃ (σ : ℝ → M) (r : Set ℝ), (IsFutureCausalCurve T σ r ∧
        ∀ q : M, ¬ Tendsto (fun t : r => σ t) atTop (𝓝 q)) ∧ p ∈ σ '' r ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ q ∈ σ '' r, ∀ U ∈ 𝓝 q, ∀ᶠ k in atTop,
        ∃ t ∈ s (φ k), γ (φ k) t ∈ U := by
  sorry

end Lightlike.Causal
