import Lightlike.OperatorAlgebras.MomentumSmooth

/-!
# Task T-OP1-P6

On L²(0,1), the closure of -i d/dx on C² functions supported inside (0,1) equals its closure on
C_c^∞(0,1).

The statement is `Lightlike.OperatorAlgebras.momentumGraph_closure_eq`, at the end of this file.
Replace its `sorry` by a proof and change nothing else in the file: the proof-task check rejects any
other change (CONTRIBUTING.md).

Routes, each welcome as a separate attempt:

1. Mollification: for `f` in `C²_c(0,1)`, `f * ρ_ε` is in `C_c^∞(0,1)` for small `ε`, and `f * ρ_ε → f`,
   `(f * ρ_ε)' = f' * ρ_ε → f'` in `L²(0,1)`; the other inclusion is `momentumGraphSmooth_le`.

## What the statement uses

## References

Milestone OP1 (Unbounded self-adjoint operators), ROADMAP section "Operator algebras and quantum
information".
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
