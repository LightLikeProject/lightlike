import Lightlike.Upstream.SU2Spin.Completeness

/-!
# Axiom checks for the SU(2) spin-representation files

`#print axioms` of the two main results: each depends only on `propext`, `Classical.choice` and
`Quot.sound`.
-/

#print axioms SU2Spin.spinRepresentation_isIrreducible
#print axioms SU2Spin.spinRep_complete
