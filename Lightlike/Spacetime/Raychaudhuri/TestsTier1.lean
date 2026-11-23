import Lightlike.Spacetime.Raychaudhuri.RicciBound
import Lightlike.Spacetime.Raychaudhuri.RicciManifold
import Lightlike.Spacetime.Raychaudhuri.RicciSharp
import Lightlike.Spacetime.Raychaudhuri.Shifted
import Lightlike.Spacetime.Raychaudhuri.Twist
import Lightlike.Spacetime.Raychaudhuri.TwistFocusing
import Lightlike.Spacetime.Raychaudhuri.FocusingSECMargin
import Lightlike.Spacetime.Raychaudhuri.FluidRicci
import Lightlike.Spacetime.Raychaudhuri.CollapseRicci

/-!
# Axiom checks for the generalisations of the focusing theorem

Each `#print axioms` below must list only `propext`, `Classical.choice`, `Quot.sound`.
The results: the Riccati bound with a Ricci lower bound (`focusing_ricci_bound`, `focusing_ricci_pi`), its manifold
form, its sharpness, the shifted and backward versions, the twisted (non-focusing) case, the margin version under
the strong energy condition, the perfect-fluid Ricci identity and focusing, and the Ricci curvature of the collapse.
-/

#print axioms Lightlike.focusing_ricci_bound
#print axioms Lightlike.focusing_ricci_pi
#print axioms Lightlike.raychaudhuri_focusing_ricci_manifold
#print axioms Lightlike.focusing_ricci_sharp
#print axioms Lightlike.focusing_shifted
#print axioms Lightlike.focusing_backward
#print axioms Lightlike.twisted_no_focusing
#print axioms Lightlike.focusing_twisted
#print axioms Lightlike.ricci_ge_of_strongEC_margin
#print axioms Lightlike.raychaudhuri_focusing_strongEC_margin
#print axioms Lightlike.ricci_fluid_comoving
#print axioms Lightlike.raychaudhuri_focusing_fluid
#print axioms Lightlike.collapse_ricci_comoving
