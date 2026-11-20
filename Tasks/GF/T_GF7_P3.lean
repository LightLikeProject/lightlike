import Lightlike.FieldTheory.Borel.Strip

/-!
# Task T-GF7-P3

Nevanlinna–Sokal, eq. (B.7): the local Borel transform B_x(t) = ∑ b_m(x) (t - x)^m/m! is analytic
for |t - x| < ρ.

The statement is `Lightlike.FieldTheory.Borel.SokalHyp.analyticOnNhd_borelLocal`, at the end of this
file. Replace its `sorry` by a proof and change nothing else in the file: the proof-task check
rejects any other change (CONTRIBUTING.md).

Hint. By T-GF7-P2 the coefficients b_m(x)/m! are at most C (m+1) ρ^{-m-1}, so the power series
FormalMultilinearSeries.ofScalars of b_m(x)/m! has radius at least ρ; its sum is analytic on the
ball (HasFPowerSeriesOnBall.analyticAt), and borelLocal is that sum at t - x.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/FieldTheory/Borel/Transform.lean`: `FieldTheory.Borel.SokalHyp`
* `Lightlike/FieldTheory/Borel/Strip.lean`: `FieldTheory.Borel.borelLocal`

Lemmas about them, which a proof may use:

* `FieldTheory.Borel.SokalHyp.rem` (`Lightlike/FieldTheory/Borel/Transform.lean`)
* `FieldTheory.Borel.SokalHyp.R_pos` (`Lightlike/FieldTheory/Borel/Transform.lean`)
* `FieldTheory.Borel.sokalHyp_const` (`Lightlike/FieldTheory/Borel/Strip.lean`)
* `FieldTheory.Borel.SokalHyp.ρ_pos` (`Lightlike/FieldTheory/Borel/Transform.lean`)
* `FieldTheory.Borel.SokalHyp.analytic` (`Lightlike/FieldTheory/Borel/Transform.lean`)
* `FieldTheory.Borel.SokalHyp.K_nonneg` (`Lightlike/FieldTheory/Borel/Transform.lean`)
* `FieldTheory.Borel.SokalHyp.norm_term_le` (`Lightlike/FieldTheory/Borel/Transform.lean`)
* `FieldTheory.Borel.SokalHyp.norm_coeff_le` (`Lightlike/FieldTheory/Borel/Transform.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.FieldTheory.Borel.SokalHyp.analyticOnNhd_borelLocal

## References

Milestone GF7 (Borel summability), ROADMAP section "Group field theory and tensor models".
Source: Laurent Freidel and David Louapre, Non-perturbative summation over 3D discrete topologies,
Phys.Rev. D68 (2003) 104004; Thibault Delepouve, Razvan Gurau and Vincent Rivasseau, Universality
and Borel Summability of Arbitrary Quartic Tensor Models, Annales de l'Institut Henri Poincaré -
Probabilités et Statistiques 2016, Vol. 52, No. 2, 821-848; D. Benedetti, R. Gurau, H. Keppler, D.
Lettera, The small-N series in the zero-dimensional O(N) model: constructive expansions and
transseries (2022), Theorem 1; V. Rivasseau, Z. Wang, Loop Vertex Expansion for Phi^2k Theory in
Zero Dimension (2010), Theorem IV.1; R. Gurau, V. Rivasseau, A. Sfondrini, Renormalization: an
advanced overview (2014), Section 2.1.2 (`freidel-louapre-2002`, `delepouve-gurau-rivasseau-2016`,
`benedetti-gurau-keppler-lettera-2022`, `rivasseau-wang-2010`, `gurau-rivasseau-sfondrini-2014` in
docs/tasks/sources.yaml).
Lock and dependencies: `docs/tasks/tasks.yaml`. This header is written by `scripts/tasks.py deps`
from the plan, the sources and the library.
-/

open MeasureTheory Set Filter Complex Finset
open scoped Topology Real Nat

namespace Lightlike.FieldTheory.Borel

/-- **The local Borel transform `B_x` is analytic in the disk of radius `ρ` about `x`** (Benedetti–Gurau–Keppler–
Lettera, arXiv:2210.14776v2, Appendix B, eq. (B.7), p. 25): under the hypotheses of the Nevanlinna–Sokal theorem,
for `x > 0` and any line `Re w = c > 1/R`, `B_x(t) = ∑_m b_m(x) (t - x)^m/m!` is analytic for `|t - x| < ρ`.

Non-vacuous: `sokalHyp_const`. -/
theorem SokalHyp.analyticOnNhd_borelLocal {f : ℂ → ℂ} {a : ℕ → ℂ} {R K ρ : ℝ} (h : SokalHyp f a R K ρ) {c : ℝ}
    (hc : 1 / R < c) {x : ℝ} (hx : 0 < x) :
    AnalyticOnNhd ℂ (borelLocal f a x c) (Metric.ball (x : ℂ) ρ) := by
  sorry

end Lightlike.FieldTheory.Borel
