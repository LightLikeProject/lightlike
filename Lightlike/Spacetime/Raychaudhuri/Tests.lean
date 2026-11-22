import Lightlike.Spacetime.Raychaudhuri.FocusingSEC
import Lightlike.Cosmology.Raychaudhuri

/-!
# Checks for the focusing theorem under the strong energy condition

* the axioms of `raychaudhuri_focusing_strongEC` are the three standard ones;
* the coordinate-stage trust checks (comoving congruences in Minkowski and FLRW, and a de Sitter congruence that
  does not focus) are those of `Lightlike/Cosmology/Raychaudhuri.lean`, which this file only re-exports as
  axiom checks.
-/

#print axioms Lightlike.raychaudhuri_focusing_strongEC
#print axioms Lightlike.Cosmology.minkowski_comoving_expansion
#print axioms Lightlike.Cosmology.flrw_comoving_expansion
#print axioms Lightlike.Cosmology.deSitter_no_focusing
