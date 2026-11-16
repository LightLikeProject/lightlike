import Lightlike.SpinFoam.Ooguri

/-!
# Independence of the gauge set for forcing gauge sets

For the gauge-fixed Ooguri state sum `amplitudeGF K T cut`, the choice of the gauge set `T` does not
matter when the sets in question *force* every triangle of `K` (`Forces K K.tris T`): then only the
zero colouring has nonzero weight, and the state sum is `1` at every cutoff
(`amplitudeGF_eq_one_of_forces`).

## Main results

* `amplitudeGF_eq_of_forces`: two forcing sets give the same state sum, at every cutoff and every
  pair of cutoffs.
* `amplitudeGF_eq_of_isGauge_forces`: the same for two gauge sets (`IsGauge`) that force.

This is a sufficient criterion and not a theorem about all gauge sets: for a complex where a gauge
set does not force every triangle, the state sum at a finite cutoff can depend on the gauge set
(numerical evidence: `scripts/spinfoam/gauge_independence_check.py`, five 4-simplices glued
non-manifold-wise, four gauge sets, four different values at cutoff `1/2`;
`scripts/spinfoam/gauge_manifold_check.py`, a 4-sphere triangulation with 24 4-simplices and a gauge
set whose state sum is `1` at cutoff `1/2` and `7/2` at cutoff `1`, against `1` for a forcing gauge
set). `IsGauge` does not imply `Forces`, and independence for all gauge sets is not claimed.
-/

namespace Lightlike.SpinFoam

open Finset Lightlike.FourD

variable {V : Type*} [LinearOrder V]

/-- **Independence of the gauge set, forcing case.** If two sets of triangles each force every
triangle of `K`, they give the same gauge-fixed state sum, for any cutoffs. -/
theorem amplitudeGF_eq_of_forces {K : Complex4 V} {T T' : Finset (Finset V)}
    (h : Forces K K.tris T) (h' : Forces K K.tris T') (cut cut' : Finset V → ℕ) :
    amplitudeGF K T cut = amplitudeGF K T' cut' := by
  rw [amplitudeGF_eq_one_of_forces h, amplitudeGF_eq_one_of_forces h']

/-- The same for two gauge sets (`IsGauge`) that force every triangle. -/
theorem amplitudeGF_eq_of_isGauge_forces {K : Complex4 V} {T T' : Finset (Finset V)}
    (_ : IsGauge K T) (_ : IsGauge K T') (h : Forces K K.tris T) (h' : Forces K K.tris T')
    (cut cut' : Finset V → ℕ) : amplitudeGF K T cut = amplitudeGF K T' cut' :=
  amplitudeGF_eq_of_forces h h' cut cut'

end Lightlike.SpinFoam
