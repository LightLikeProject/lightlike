import Lightlike.FieldTheory.Borel.Strip

/-!
# Task T-GF7-P4

Nevanlinna–Sokal, Theorem 1 (second item): the Borel transform continues analytically to the strip
dist(t, ℝ₊) < ρ, equal to b_0 on (0, ∞), with |B(t)| ≤ C e^{|t|/R} on smaller strips.

The statement is `Lightlike.FieldTheory.Borel.SokalHyp.exists_continuation`, at the end of this
file. Replace its `sorry` by a proof and change nothing else in the file: the proof-task check
rejects any other change (CONTRIBUTING.md). It builds on T-GF7-P1
(`FieldTheory.Borel.SokalHyp.hasDerivAt_borelDeriv`), T-GF7-P2
(`FieldTheory.Borel.SokalHyp.norm_borelDeriv_le`) and T-GF7-P3
(`FieldTheory.Borel.SokalHyp.analyticOnNhd_borelLocal`): a proof may use their statements.

Hint. On the real axis b_0(s) = ∑ b_m(x) (s - x)^m/m! for s > 0, |s - x| < ρ (Taylor's formula with
integral remainder, T-GF7-P1 and T-GF7-P2), so B_x = B_{x'} on the intersection of their disks
(identity theorem, AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq, T-GF7-P3) and B_x = borelT
on |t| < ρ (SokalHyp.borelZero_eq_borelT); glue: B(t) = borelT a t for |t| < ρ, else B_{Re t}(t).
The bound follows from T-GF7-P2 with c ↓ 1/R.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/FieldTheory/Borel/Transform.lean`: `FieldTheory.Borel.SokalHyp`,
  `FieldTheory.Borel.borelT`
* `Lightlike/FieldTheory/Borel/Strip.lean`: `FieldTheory.Borel.sokalStrip`
* `Lightlike/FieldTheory/Borel/Contour.lean`: `FieldTheory.Borel.borelZero`

Lemmas about them, which a proof may use:

* `FieldTheory.Borel.SokalHyp.hasDerivAt_borelDeriv` (`Tasks/GF/T_GF7_P1.lean`)
* `FieldTheory.Borel.SokalHyp.norm_borelDeriv_le` (`Tasks/GF/T_GF7_P2.lean`)
* `FieldTheory.Borel.SokalHyp.analyticOnNhd_borelLocal` (`Tasks/GF/T_GF7_P3.lean`)
* `FieldTheory.Borel.SokalHyp.borelZero_eq_borelT` (`Lightlike/FieldTheory/Borel/Transform.lean`)
* `FieldTheory.Borel.borelDeriv_zero` (`Lightlike/FieldTheory/Borel/Strip.lean`)
* `FieldTheory.Borel.SokalHyp.hasSum_borelT` (`Lightlike/FieldTheory/Borel/Transform.lean`)
* `FieldTheory.Borel.SokalHyp.norm_borelZero_sub_sum_le` (`Lightlike/FieldTheory/Borel/Transform.lean`)
* `FieldTheory.Borel.SokalHyp.rem` (`Lightlike/FieldTheory/Borel/Transform.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.FieldTheory.Borel.SokalHyp.exists_continuation

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

/-- **The Borel transform continues to the strip** (Benedetti–Gurau–Keppler–Lettera, arXiv:2210.14776v2, Theorem 1,
second item, p. 6, and its proof, Appendix B, p. 25): under the hypotheses of the Nevanlinna–Sokal theorem there
is a function `B` analytic on the strip `{dist(t, ℝ₊) < ρ}`, equal to the Borel transform `∑ a_k t^k/k!` for
`|t| < ρ` and to `b_0(x)` for `x > 0` (on every line `Re w = c > 1/R`), with `|B(t)| ≤ C e^{|t|/R}` on every
strip `{dist(t, ℝ₊) < ρ'}`, `ρ' < ρ`.

Difference from the source (kind: weaker): the source states the exponential bound `|B(t)| < K e^{|t|/R}` in the
strip; here it is uniform on every smaller strip `dist(t, ℝ₊) < ρ' < ρ`. Non-vacuous: `sokalHyp_const`. -/
theorem SokalHyp.exists_continuation {f : ℂ → ℂ} {a : ℕ → ℂ} {R K ρ : ℝ} (h : SokalHyp f a R K ρ) :
    ∃ B : ℂ → ℂ, AnalyticOnNhd ℂ B (sokalStrip ρ) ∧ (∀ t : ℂ, ‖t‖ < ρ → B t = borelT a t) ∧
      (∀ c : ℝ, 1 / R < c → ∀ x : ℝ, 0 < x → B x = borelZero f (a 0) x c) ∧
      ∀ ρ' : ℝ, ρ' < ρ → ∃ C : ℝ, ∀ t ∈ sokalStrip ρ', ‖B t‖ ≤ C * Real.exp (‖t‖ / R) := by
  sorry

end Lightlike.FieldTheory.Borel
