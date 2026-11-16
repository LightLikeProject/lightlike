import Lightlike.TuraevViro.Reflect.RacahPoint

/-!
# The recurrence coefficients do not involve `Z`

Kernel checks (`decide +kernel`) that the polynomials `Dc`, `N1`, `N3`, `N5` and the factors `fQ0`,
`fQ1`, `fQ2`, `fNa`, `fNc`, `fbn`, `fCq` have no monomial containing `Z`, so that `eval_noZ` of
`RacahPoint` applies to them (used in `RacahRec`). Written by hand, not generated.

## Main results

* `noZ_Dc`, `noZ_N1`, `noZ_N3`, `noZ_N5`: `noZ` holds for the four coefficient polynomials.
* `noZ_Q0`, `noZ_Q1`, `noZ_Q2`, `noZ_Na`, `noZ_Nc`, `noZ_bn`, `noZ_Cq`: the same for the factors.
-/

set_option maxRecDepth 100000

namespace Lightlike.TV.Refl

theorem noZ_Dc : noZ Dc = true := by unfold Dc; decide +kernel
theorem noZ_N1 : noZ N1 = true := by unfold N1; decide +kernel
theorem noZ_N3 : noZ N3 = true := by unfold N3; decide +kernel
theorem noZ_N5 : noZ N5 = true := by unfold N5; decide +kernel

theorem noZ_Q0 : noZ fQ0 = true := by unfold fQ0; decide +kernel
theorem noZ_Q1 : noZ fQ1 = true := by unfold fQ1; decide +kernel
theorem noZ_Q2 : noZ fQ2 = true := by unfold fQ2; decide +kernel
theorem noZ_Na : noZ fNa = true := by unfold fNa; decide +kernel
theorem noZ_Nc : noZ fNc = true := by unfold fNc; decide +kernel
theorem noZ_bn : noZ fbn = true := by unfold fbn; decide +kernel
theorem noZ_Cq : noZ fCq = true := by unfold fCq; decide +kernel

end Lightlike.TV.Refl
