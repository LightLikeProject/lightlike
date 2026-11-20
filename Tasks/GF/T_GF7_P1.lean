import Lightlike.FieldTheory.Borel.Strip

/-!
# Task T-GF7-P1

Nevanlinna–Sokal, eq. (B.6): the functions b_m along a vertical line are the successive derivatives
of b_0.

The statement is `Lightlike.FieldTheory.Borel.SokalHyp.hasDerivAt_borelDeriv`, at the end of this
file. Replace its `sorry` by a proof and change nothing else in the file: the proof-task check
rejects any other change (CONTRIBUTING.md).

Hint. Write R_{m+1}(z) = a_{m+1} z^{m+1} + R_{m+2}(z): then b_m(x) = a_m + a_{m+1} x + (1/2π) ∫
e^{xw} w^{m-1} R_{m+2}(w⁻¹) dy by Hankel's formula with k = 1 (hankel_vertical_y), and differentiate
the last integral under the integral sign (hasDerivAt_integral_of_dominated_loc_of_deriv_le): |w^m
R_{m+2}(w⁻¹)| ≤ K (m+2)! ρ^{-m-2} |w|^{-2} is integrable along the line (integrable_inv_sq_add).

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/FieldTheory/Borel/Transform.lean`: `FieldTheory.Borel.SokalHyp`
* `Lightlike/FieldTheory/Borel/Strip.lean`: `FieldTheory.Borel.borelDeriv`

Lemmas about them, which a proof may use:

* `FieldTheory.Borel.SokalHyp.rem` (`Lightlike/FieldTheory/Borel/Transform.lean`)
* `FieldTheory.Borel.SokalHyp.R_pos` (`Lightlike/FieldTheory/Borel/Transform.lean`)
* `FieldTheory.Borel.sokalHyp_const` (`Lightlike/FieldTheory/Borel/Strip.lean`)
* `FieldTheory.Borel.SokalHyp.ρ_pos` (`Lightlike/FieldTheory/Borel/Transform.lean`)
* `FieldTheory.Borel.borelDeriv_zero` (`Lightlike/FieldTheory/Borel/Strip.lean`)
* `FieldTheory.Borel.SokalHyp.analytic` (`Lightlike/FieldTheory/Borel/Transform.lean`)
* `FieldTheory.Borel.SokalHyp.K_nonneg` (`Lightlike/FieldTheory/Borel/Transform.lean`)
* `FieldTheory.Borel.SokalHyp.norm_term_le` (`Lightlike/FieldTheory/Borel/Transform.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.FieldTheory.Borel.SokalHyp.hasDerivAt_borelDeriv

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

/-- **The functions `b_m` are the successive derivatives of `b_0`** (Benedetti–Gurau–Keppler–Lettera,
arXiv:2210.14776v2, Appendix B, eq. (B.6), p. 25): under the hypotheses of the Nevanlinna–Sokal theorem,
along any line `Re w = c > 1/R`, `b_m'(x) = b_{m+1}(x)` for `x > 0`.

The source defines `b_m(x) = d^m b_0(x)/dx^m` and derives the formula (B.6); here `b_m` is defined by the formula
(`borelDeriv`, with `b_0 = borelZero` by `borelDeriv_zero`) and the statement is that these are the derivatives
(kind: representation). Non-vacuous: `sokalHyp_const`. -/
theorem SokalHyp.hasDerivAt_borelDeriv {f : ℂ → ℂ} {a : ℕ → ℂ} {R K ρ : ℝ} (h : SokalHyp f a R K ρ) {c : ℝ}
    (hc : 1 / R < c) (m : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => borelDeriv f a m x c) (borelDeriv f a (m + 1) x c) x := by
  sorry

end Lightlike.FieldTheory.Borel
