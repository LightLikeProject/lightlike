import Lightlike.OperatorAlgebras.MomentumSmooth

/-!
# Task T-OP1-P6

On L²(0,1), the closure of -i d/dx on C² functions supported inside (0,1) equals its closure on
C_c^∞(0,1).

The statement is `Lightlike.OperatorAlgebras.momentumGraph_closure_eq`, at the end of this file.
Replace its `sorry` by a proof and change nothing else in the file: the proof-task check rejects any
other change (CONTRIBUTING.md).

Hint. Mollification: for f in C²_c(0,1), f * ρ_ε is C_c^∞(0,1) for small ε, and f * ρ_ε → f and (f *
ρ_ε)' = f' * ρ_ε → f' in L²(0,1), so every graph point of the C² operator is a limit of graph points
of the C_c^∞ operator; the other inclusion is monotonicity (momentumGraphSmooth_le). Needs:
convolution with a mollifier commutes with the derivative and converges in L² (Mathlib:
ContDiffBump, convolution approximation of the identity).

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/OperatorAlgebras/MomentumInterval.lean`: `OperatorAlgebras.L2I`,
  `OperatorAlgebras.momentumGraph`
* `Lightlike/OperatorAlgebras/MomentumSmooth.lean`: `OperatorAlgebras.momentumGraphSmooth`

Lemmas about them, which a proof may use:

* `OperatorAlgebras.momentumGraphSmooth_le` (`Lightlike/OperatorAlgebras/MomentumSmooth.lean`)
* `OperatorAlgebras.momentumMin_graph` (`Lightlike/OperatorAlgebras/MomentumInterval.lean`)
* `OperatorAlgebras.momentumGraph_fun` (`Lightlike/OperatorAlgebras/MomentumInterval.lean`)
* `OperatorAlgebras.momentumGraph_eq_map` (`Lightlike/OperatorAlgebras/MomentumSmooth.lean`)
* `OperatorAlgebras.momentumGraphSmooth_ne_bot` (`Lightlike/OperatorAlgebras/TestsMomentumSmooth.lean`)
* `OperatorAlgebras.classI_add` (`Lightlike/OperatorAlgebras/MomentumInterval.lean`)
* `OperatorAlgebras.classI_zero` (`Lightlike/OperatorAlgebras/MomentumInterval.lean`)
* `OperatorAlgebras.classI_smul` (`Lightlike/OperatorAlgebras/MomentumInterval.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.OperatorAlgebras.momentumGraph_closure_eq

## References

Milestone OP1 (Unbounded self-adjoint operators), ROADMAP section "Operator algebras and quantum
information".
Source: B. C. Hall, Quantum Theory for Mathematicians, Graduate Texts in Mathematics 267, Springer
(2013), Chapter: Unbounded Self-Adjoint Operators; B. C. Hall, Quantum Theory for Mathematicians,
Graduate Texts in Mathematics 267, Springer (2013), Chapter: The Spectral Theorem for Unbounded
Self-Adjoint Operators (`hall-2013`, `hall-2013` in docs/tasks/sources.yaml).
Lock and dependencies: `docs/tasks/tasks.yaml`. This header is written by `scripts/tasks.py deps`
from the plan, the sources and the library.
-/

namespace Lightlike.OperatorAlgebras

/-- **The closure of `-i d/dx` on `L²(0, 1)` does not depend on the class of test functions**: the closure of
the graph of `-i d/dx` on `C²` functions supported inside `(0, 1)` (`momentumGraph`) equals the closure of
its graph on `C_c^∞(0, 1)` (`momentumGraphSmooth`). With this, `momentumMin_deficiency` (`T-OP1-P5`), stated
for the `C²` functions, is the textbook statement for `C_c^∞(0, 1)`.

**Differences from the source** (not yet read at the cited location; the comparison is pending): the source
(Reed-Simon, vol. II, Section X.1, Example 1, the deficiency indices of `-i d/dx` on `[0, 1]`; the exact
location is not verified) takes `C_c^∞(0, 1)` as the domain and does not state this equality; it is the
bridge between the `C²` operator of this library and the textbook operator (kind: representation). -/
theorem momentumGraph_closure_eq :
    momentumGraphSmooth.topologicalClosure = momentumGraph.topologicalClosure := by
  sorry

end Lightlike.OperatorAlgebras
