import Lightlike.Upstream.SpinReps2.Intertwiner
import Lightlike.Upstream.SpinReps2.LieBridge

/-!
# Axiom checks for the upstream 3j/6j files (`SpinReps2`)

`#print axioms` of the main results: each depends only on `propext`, `Classical.choice` and
`Quot.sound`.
-/

#print axioms PhyslibAlpha.Sl2.sum_threeJ_mul_threeJ
#print axioms PhyslibAlpha.Sl2.sixJSym_zero_left
#print axioms PhyslibAlpha.Sl2.sixJSym_orth_all
#print axioms PhyslibAlpha.Sl2.sum_fourJ_mul_fourJ
#print axioms SU2Spin.isSl2Triple_mat
#print axioms SU2Spin.dSpin_E
#print axioms SU2Spin.dSpin_F
#print axioms SU2Spin.dSpin_H
