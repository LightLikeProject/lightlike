import Lightlike.Spacetime.Raychaudhuri.FocusingSEC
import Lightlike.Spacetime.Raychaudhuri.Examples
import Lightlike.Spacetime.Raychaudhuri.DustField
import Lightlike.Cosmology.Raychaudhuri

/-!
# Checks for the focusing theorem under the strong energy condition

* the axioms of `raychaudhuri_focusing_strongEC` are the three standard ones;
* the coordinate-stage trust checks (comoving congruences in Minkowski and FLRW, and a de Sitter congruence that
  does not focus) are those of `Lightlike/Cosmology/Raychaudhuri.lean`;
* the manifold-stage trust checks (`Examples.lean`): the manifold expansion `expansionM` of the comoving field on
  the FLRW, Minkowski and de Sitter manifolds, linked to the coordinate stage by `expansionM_constField`.
-/

#print axioms Lightlike.raychaudhuri_focusing_strongEC
#print axioms Lightlike.flrwManifold_dust_strongEC
#print axioms Lightlike.matForm_perfectFluid
#print axioms Lightlike.Cosmology.minkowski_comoving_expansion
#print axioms Lightlike.Cosmology.flrw_comoving_expansion
#print axioms Lightlike.Cosmology.deSitter_no_focusing
#print axioms Lightlike.expansionM_constField
#print axioms Lightlike.flrwManifold_comoving_expansion
#print axioms Lightlike.minkowskiManifold_comoving_expansion
#print axioms Lightlike.deSitterManifold_no_focusing
