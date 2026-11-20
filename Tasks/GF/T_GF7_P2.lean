import Lightlike.FieldTheory.Borel.Strip

/-!
# Task T-GF7-P2

Nevanlinna–Sokal, after eq. (B.6): |b_m(x)| ≤ K (ρ + 1/(2c)) (m+1)! ρ^{-m-1} e^{cx} for x ≥ 0.

The statement is `Lightlike.FieldTheory.Borel.SokalHyp.norm_borelDeriv_le`, at the end of this file.
Replace its `sorry` by a proof and change nothing else in the file: the proof-task check rejects any
other change (CONTRIBUTING.md).

Hint. |a_m| ≤ K m! ρ^{-m} (SokalHyp.norm_coeff_le) and, by the rest-term bound with q = m + 1 at z =
w⁻¹, the integrand is at most e^{cx} K (m+1)! ρ^{-m-1} (c² + y²)⁻¹, whose integral is π/c
(integral_inv_sq_add); then m! ρ^{-m} ≤ ρ (m+1)! ρ^{-m-1} e^{cx}.

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

    scripts/context-pack Lightlike.FieldTheory.Borel.SokalHyp.norm_borelDeriv_le

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

/-- **The bound on `b_m`** (Benedetti–Gurau–Keppler–Lettera, arXiv:2210.14776v2, Appendix B, after eq. (B.6),
p. 25, with `β = 0`): under the hypotheses of the Nevanlinna–Sokal theorem, along the line `Re w = c > 1/R`,
`|b_m(x)| ≤ K (ρ + 1/(2c)) (m+1)! ρ^{-m-1} e^{cx}` for all `m` and `x ≥ 0`.

The source writes `|b_m(x)| ≤ K (m+1)! (m+1)^β ρ^{-m-1} e^{x/r}` with `r = 1/c` and the constant absorbed in `K`;
here the constant is explicit (kind: representation). Non-vacuous: `sokalHyp_const`. -/
theorem SokalHyp.norm_borelDeriv_le {f : ℂ → ℂ} {a : ℕ → ℂ} {R K ρ : ℝ} (h : SokalHyp f a R K ρ) {c : ℝ}
    (hc : 1 / R < c) (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ‖borelDeriv f a m x c‖ ≤ K * (ρ + 1 / (2 * c)) * (m + 1) ! / ρ ^ (m + 1) * Real.exp (c * x) := by
  sorry

end Lightlike.FieldTheory.Borel
