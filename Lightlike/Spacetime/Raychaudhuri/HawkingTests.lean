import Lightlike.Spacetime.Raychaudhuri.Hawking
import Lightlike.Spacetime.Raychaudhuri.HawkingManifold
import Lightlike.Spacetime.Raychaudhuri.HawkingSEC

/-!
# Axiom checks for the Hawking-type lifetime bounds (Tier 2, milestone CO3 analytic core)

`#print axioms` for the Tier 2 results: the real-line focusing bounds, the sharpness profile,
the manifold bound under `Ric(V,V) ≥ 0`, and the strong-energy-condition version in dimension 4.
Each must depend only on `propext`, `Classical.choice`, `Quot.sound`.
-/

open Lightlike

#print axioms focusing_hawking
#print axioms focusing_hawking_shifted
#print axioms focusing_hawking_backward
#print axioms hawking_profile_hasDerivAt
#print axioms hawking_profile_zero
#print axioms hawking_profile_tendsto
#print axioms hawking_bound_manifold
#print axioms hawking_bound_strongEC
