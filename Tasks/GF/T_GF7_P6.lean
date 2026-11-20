import Lightlike.FieldTheory.Borel.Strip

/-!
# Task T-GF7-P6

The Nevanlinna–Sokal theorem (Theorem 1 of Benedetti–Gurau–Keppler–Lettera with β = 0): the Borel
transform converges near 0, continues to the strip, and its Laplace transform is f on C_R.

The statement is `Lightlike.FieldTheory.Borel.SokalHyp.nevanlinna_sokal`, at the end of this file.
Replace its `sorry` by a proof and change nothing else in the file: the proof-task check rejects any
other change (CONTRIBUTING.md). It builds on T-GF7-P4
(`FieldTheory.Borel.SokalHyp.exists_continuation`) and T-GF7-P5
(`FieldTheory.Borel.SokalHyp.eq_laplace_borelZero`): a proof may use their statements.

Hint. SokalHyp.hasSum_borelT for the first item; T-GF7-P4 for the continuation and the bound;
T-GF7-P5 with B = b_0 on (0, ∞) for the Laplace representation, and the integrability from |b_0(x)|
≤ |a_0| + M e^{c'x}/(2c') with 1/R < c' < Re z⁻¹.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/FieldTheory/Borel/Transform.lean`: `FieldTheory.Borel.SokalHyp`,
  `FieldTheory.Borel.borelT`
* `Lightlike/FieldTheory/Borel/Strip.lean`: `FieldTheory.Borel.sokalStrip`
* `Lightlike/FieldTheory/ZeroDim/QuarticComplex.lean`: `FieldTheory.diskC`

Lemmas about them, which a proof may use:

* `FieldTheory.Borel.SokalHyp.exists_continuation` (`Tasks/GF/T_GF7_P4.lean`)
* `FieldTheory.Borel.SokalHyp.eq_laplace_borelZero` (`Tasks/GF/T_GF7_P5.lean`)
* `FieldTheory.Borel.SokalHyp.borelZero_eq_borelT` (`Lightlike/FieldTheory/Borel/Transform.lean`)
* `FieldTheory.Borel.SokalHyp.rem` (`Lightlike/FieldTheory/Borel/Transform.lean`)
* `FieldTheory.Borel.borelZero_indep` (`Lightlike/FieldTheory/Borel/Contour.lean`)
* `FieldTheory.Borel.SokalHyp.analytic` (`Lightlike/FieldTheory/Borel/Transform.lean`)
* `FieldTheory.Borel.SokalHyp.hasSum_borelT` (`Lightlike/FieldTheory/Borel/Transform.lean`)
* `FieldTheory.Borel.SokalHyp.norm_borelZero_sub_sum_le` (`Lightlike/FieldTheory/Borel/Transform.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.FieldTheory.Borel.SokalHyp.nevanlinna_sokal

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

/-- **The Nevanlinna–Sokal theorem** (Benedetti–Gurau–Keppler–Lettera, arXiv:2210.14776v2, Theorem 1, eqs. (2.4)-
(2.6), pp. 5-6, with `β = 0`): let `f` be analytic in `C_R = {Re z⁻¹ > 1/R}` with
`|f(z) - ∑_{k<q} a_k z^k| ≤ K q! ρ^{-q} |z|^q` there. Then the Borel transform `B(t) = ∑ a_k t^k/k!` converges
for `|t| < ρ`, continues analytically to the strip `{dist(t, ℝ₊) < ρ}` with `|B(t)| ≤ C e^{|t|/R}` on every
smaller strip, and `f(z) = (1/z) ∫_0^∞ e^{-t/z} B(t) dt` (absolutely convergent) for `z ∈ C_R`.

Difference from the source (kind: weaker): the exponential bound is uniform on every strip `dist(t, ℝ₊) < ρ'`,
`ρ' < ρ`, not on the whole strip, as in T-GF7-P4. Non-vacuous: `sokalHyp_const`. -/
theorem SokalHyp.nevanlinna_sokal {f : ℂ → ℂ} {a : ℕ → ℂ} {R K ρ : ℝ} (h : SokalHyp f a R K ρ) :
    (∀ t : ℂ, ‖t‖ < ρ → HasSum (fun k => a k * t ^ k / (k ! : ℂ)) (borelT a t)) ∧
      ∃ B : ℂ → ℂ, AnalyticOnNhd ℂ B (sokalStrip ρ) ∧ (∀ t : ℂ, ‖t‖ < ρ → B t = borelT a t) ∧
        (∀ ρ' : ℝ, ρ' < ρ → ∃ C : ℝ, ∀ t ∈ sokalStrip ρ', ‖B t‖ ≤ C * Real.exp (‖t‖ / R)) ∧
        ∀ z ∈ diskC R, IntegrableOn (fun x : ℝ => cexp (-(x / z)) * B x) (Ioi 0) ∧
          f z = z⁻¹ * ∫ x in Ioi (0 : ℝ), cexp (-(x / z)) * B x := by
  sorry

end Lightlike.FieldTheory.Borel
