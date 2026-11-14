module

public import Lightlike.PonzanoRegge.Forcing
public import Lightlike.Tests.Manifold

/-!
# Tests for forced edges

* `forcesAll_S3`: on the boundary of the 4-simplex `01234`, the star tree at `0` forces every
  other edge `ij` through the triangle `0ij`.
* `amplitudeGF_S3_star`: hence the gauge-fixed amplitude of this 3-sphere is `1` for **every**
  cutoff; the cutoff can be removed.
-/

@[expose] public section

open Finset

namespace Lightlike.PR.Test.Manifold

/-- The star tree at `0` forces every edge of the boundary of the 4-simplex. -/
theorem forcesAll_S3 : ForcesAll S3 {{0, 1}, {0, 2}, {0, 3}, {0, 4}} := by
  refine .step (p := 1) (q := 2) (r := 0) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) ?_
  refine .step (p := 1) (q := 3) (r := 0) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) ?_
  refine .step (p := 1) (q := 4) (r := 0) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) ?_
  refine .step (p := 2) (q := 3) (r := 0) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) ?_
  refine .step (p := 2) (q := 4) (r := 0) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) ?_
  refine .step (p := 3) (q := 4) (r := 0) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) ?_
  exact .done (by decide)

/-- **The gauge-fixed amplitude of the boundary of the 4-simplex, with the star tree at `0`, is `1`
for every cutoff.** -/
theorem amplitudeGF_S3_star (cut : Finset (Fin 6) → ℕ) :
    amplitudeGF S3 {{0, 1}, {0, 2}, {0, 3}, {0, 4}} cut = 1 :=
  amplitudeGF_of_forcesAll S3 (by decide) forcesAll_S3 cut

end Lightlike.PR.Test.Manifold
