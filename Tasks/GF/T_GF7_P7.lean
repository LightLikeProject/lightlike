import Lightlike.FieldTheory.Borel.Strip

/-!
# Task T-GF7-P7

The partition function of the zero-dimensional λφ⁴ theory is Borel summable (Rivasseau–Wang Theorem
IV.1 with k = 2).

The statement is `Lightlike.FieldTheory.quarticZ_borel_summable`, at the end of this file. Replace
its `sorry` by a proof and change nothing else in the file: the proof-task check rejects any other
change (CONTRIBUTING.md). It builds on T-GF7-P6 (`FieldTheory.Borel.SokalHyp.nevanlinna_sokal`): a
proof may use their statements.

Hint. quarticZ_nevanlinna gives |R_N Z| ≤ 16√(2π) 32^N N! |λ|^{N+1} on every C_R; turn it into
SokalHyp quarticZ quarticCoeff R K ρ with ρ = 1/32 (the case q = 0 from q = 1 and |a_0|) and apply
T-GF7-P6; B does not depend on R because it is determined by its values near 0.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/FieldTheory/Borel/Strip.lean`: `FieldTheory.Borel.sokalStrip`
* `Lightlike/FieldTheory/ZeroDim/QuarticComplex.lean`: `FieldTheory.quarticCoeff`,
  `FieldTheory.diskC`, `FieldTheory.quarticZ`

Lemmas about them, which a proof may use:

* `FieldTheory.Borel.SokalHyp.nevanlinna_sokal` (`Tasks/GF/T_GF7_P6.lean`)
* `FieldTheory.quarticZ_nevanlinna` (`Lightlike/FieldTheory/ZeroDim/QuarticComplex.lean`)
* `FieldTheory.Borel.SokalHyp.rem` (`Lightlike/FieldTheory/Borel/Transform.lean`)
* `FieldTheory.norm_quarticZ_sub_le` (`Lightlike/FieldTheory/ZeroDim/QuarticComplex.lean`)
* `FieldTheory.Borel.SokalHyp.analytic` (`Lightlike/FieldTheory/Borel/Transform.lean`)
* `FieldTheory.Borel.SokalHyp.hasSum_borelT` (`Lightlike/FieldTheory/Borel/Transform.lean`)
* `FieldTheory.Borel.SokalHyp.borelZero_eq_borelT` (`Lightlike/FieldTheory/Borel/Transform.lean`)
* `FieldTheory.Borel.isOpen_diskC` (`Lightlike/FieldTheory/Borel/Contour.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.FieldTheory.quarticZ_borel_summable

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

namespace Lightlike.FieldTheory

open Borel

/-- **The quartic partition function is Borel summable** (Rivasseau–Wang, arXiv:1003.1037, Theorem IV.1 with
`k = 2`, p. 17, through Theorem III.2 with order `1`, eqs. (III-36), (III-37), p. 9): the Borel transform
`B(t) = ∑ a_n t^n/n!` of the Taylor coefficients `a_n = (-1)^n √(2π) (4n - 1)!!/n!` of
`Z(λ) = ∫ e^{-λφ⁴ - φ²/2} dφ` converges near `0`, continues analytically to a strip `{dist(t, ℝ₊) < ρ}`, and
`Z(λ) = (1/λ) ∫_0^∞ e^{-t/λ} B(t) dt` for `λ` in every disk `C_R = {Re λ⁻¹ > 1/R}`.

The statement is unconditional (`quarticZ_nevanlinna` gives the hypotheses of the Nevanlinna–Sokal theorem). -/
theorem quarticZ_borel_summable :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ B : ℂ → ℂ, AnalyticOnNhd ℂ B (sokalStrip ρ) ∧
      (∀ t : ℂ, ‖t‖ < ρ → HasSum (fun n => quarticCoeff n * t ^ n / (n ! : ℂ)) (B t)) ∧
      ∀ R : ℝ, 0 < R → ∀ z ∈ diskC R, quarticZ z = z⁻¹ * ∫ x in Ioi (0 : ℝ), cexp (-(x / z)) * B x := by
  sorry

end Lightlike.FieldTheory
