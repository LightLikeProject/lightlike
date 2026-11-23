import Lightlike.Upstream.GeodesicExpansion.Limits
import Mathlib

/-!
# Axiom checks for the Tier 1 consequences of the fifth-order expansion

Prints the axioms of the third-order, two-sided, square-root and directional-limit corollaries
(chart and Mathlib `riemannianEDist` forms). Only `propext`, `Classical.choice`, `Quot.sound`
are expected.
-/

namespace Lightlike.Upstream.GeodesicExpansion

#print axioms IsRiemMetric.chartDist_sq_third
#print axioms IsRiemMetric.riemannianEDist_sq_third
#print axioms IsRiemMetric.chartDist_sq_two_sided
#print axioms IsRiemMetric.riemannianEDist_sq_two_sided
#print axioms IsRiemMetric.chartDist_sub_sqrt_le
#print axioms IsRiemMetric.riemannianEDist_sub_sqrt_le
#print axioms IsRiemMetric.tendsto_chartDist_sq_div
#print axioms IsRiemMetric.tendsto_riemannianEDist_sq_div

end Lightlike.Upstream.GeodesicExpansion
