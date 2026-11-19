import Lightlike.Asymptotics.Tauberian.Ingham

/-!
# Task T-SP3-P1

A logarithmic Tauberian theorem of Ingham type: if the Laplace transform of a positive measure grows
like `e^{a/β}` in the logarithmic sense, then its counting function grows like `e^{2 √(a X)}` in the
logarithmic sense.

The statement is `Lightlike.Tauberian.ingham_logarithmic`, at the end of this file. Replace its
`sorry` by a proof and change nothing else in the file: the proof-task check rejects any other change
(CONTRIBUTING.md).

Hint. Upper bound: `ρ [0, X] ≤ e^{β X} L(β)` with `β = √(a / X)`. Lower bound: split `L(β)` into the
windows `[0, (1 - η) a / β²]`, `((1 - η) a / β², (1 + η) a / β²]` and `((1 + η) a / β², ∞)`; the outer
two are bounded by `e^{(β'' - β) Y} L(β'')` and `e^{-(β - β') Y} L(β')` with `β'' = β (1 + η/2)`,
`β' = β / (1 + η/2)`, hence at most `L(β) / 4` each.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/Asymptotics/Tauberian/Window.lean`: `Tauberian.laplace`, `Tauberian.counting`

## References

Milestone SP3 (Tauberian theorems for Laplace transforms), ROADMAP section "Asymptotics".
Source: B. Mukhametzhanov and A. Zhiboedov, Modular invariance, tauberian theorems and microcanonical
entropy, arXiv:1904.06359 (`mukhametzhanov-zhiboedov-2019` in docs/tasks/sources.yaml), Section 1.
Lock and dependencies: `docs/tasks/tasks.yaml`. This header is written by `scripts/tasks.py deps`
from the plan, the sources and the library.
-/

open MeasureTheory Set Filter Topology

namespace Lightlike.Tauberian

/-- **A logarithmic Tauberian theorem of Ingham type.** Let `ρ` be a measure on `[0, ∞)`, finite on
compact sets, with `exp (-β x)` integrable for every `β > 0`, and suppose
`β log (∫ exp (-β x) dρ) → a > 0` as `β → 0⁺`. Then `log (ρ [0, X]) / (2 √(a X)) → 1` as `X → ∞`.

Difference from the source (kind: weaker): Ingham's theorem, as cited in Mukhametzhanov–Zhiboedov,
Section 1, gives the asymptotics of `ρ [0, X]` itself (eq. (1.8) with an error term, under modular
invariance), not only of its logarithm; here only the logarithmic asymptotics is proved. The part of the
milestone SP3 given by Ingham's full asymptotics, and by Karamata's theorem, is still open. -/
theorem ingham_logarithmic {ρ : Measure ℝ} [IsFiniteMeasureOnCompacts ρ] (hρ : ρ (Iio 0) = 0)
    (hint : ∀ β : ℝ, 0 < β → Integrable (fun x : ℝ => Real.exp (-β * x)) ρ) {a : ℝ} (ha : 0 < a)
    (hL : Tendsto (fun β : ℝ => β * Real.log (laplace ρ β)) (𝓝[>] 0) (𝓝 a)) :
    Tendsto (fun X : ℝ => Real.log (counting ρ X) / (2 * Real.sqrt (a * X))) atTop (𝓝 1) := by
  exact ingham_log hρ hint ha hL

end Lightlike.Tauberian
