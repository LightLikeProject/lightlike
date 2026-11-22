import Lightlike.HarmonicAnalysis.PeterWeylRow.Acceptance

/-!
# Axiom check for milestone HA5 (the Peter–Weyl theorem)

Each declaration that states the done-when or a trust check of HA5 depends only on Lean's standard axioms
`propext`, `Classical.choice` and `Quot.sound`. Test file; no catalogue entry.
-/

#print axioms Lightlike.HarmonicAnalysis.peterWeyl_dense_continuous
#print axioms Lightlike.HarmonicAnalysis.peterWeyl_dense_L2
#print axioms Lightlike.HarmonicAnalysis.peterWeyl_isHilbertSum
#print axioms Lightlike.HarmonicAnalysis.finrank_isotypic
#print axioms Lightlike.HarmonicAnalysis.circle_hilbertBasis
#print axioms Lightlike.HarmonicAnalysis.su2_character_orthogonality
#print axioms Lightlike.HarmonicAnalysis.real_not_forall_memLp_two
