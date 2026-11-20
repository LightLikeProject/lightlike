import Lightlike.FieldTheory.Borel.Strip

/-!
# Task T-GF7-P5

Nevanlinna–Sokal, eq. (B.8): f(z) = (1/z) ∫_0^∞ e^{-x/z} b_0(x) dx for z in the disk C_R.

The statement is `Lightlike.FieldTheory.Borel.SokalHyp.eq_laplace_borelZero`, at the end of this
file. Replace its `sorry` by a proof and change nothing else in the file: the proof-task check
rejects any other change (CONTRIBUTING.md).

Hint. Without a half-plane Cauchy formula: b_0(x) - a_0 = 0 for x ≤ 0 (move the line to Re w = c' →
∞ with borelZero_indep and the bound M e^{xc'}/(2c')); then φ(x) = (b_0(x) - a_0) e^{-cx} is
integrable and is the inverse Fourier transform of ξ ↦ (f(w⁻¹) - a_0)/w at w = c + 2πiξ, so Fourier
inversion (Continuous.fourier_fourierInv_eq) gives ∫_0^∞ e^{-xw} (b_0(x) - a_0) dx = (f(w⁻¹) -
a_0)/w for Re w > 1/R; take w = z⁻¹ and add ∫_0^∞ e^{-x/z} a_0 dx = a_0 z
(integral_pow_mul_cexp_neg).

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/FieldTheory/Borel/Transform.lean`: `FieldTheory.Borel.SokalHyp`
* `Lightlike/FieldTheory/ZeroDim/QuarticComplex.lean`: `FieldTheory.diskC`
* `Lightlike/FieldTheory/Borel/Contour.lean`: `FieldTheory.Borel.borelZero`

Lemmas about them, which a proof may use:

* `FieldTheory.Borel.SokalHyp.rem` (`Lightlike/FieldTheory/Borel/Transform.lean`)
* `FieldTheory.Borel.borelZero_indep` (`Lightlike/FieldTheory/Borel/Contour.lean`)
* `FieldTheory.Borel.SokalHyp.analytic` (`Lightlike/FieldTheory/Borel/Transform.lean`)
* `FieldTheory.Borel.SokalHyp.borelZero_eq_borelT` (`Lightlike/FieldTheory/Borel/Transform.lean`)
* `FieldTheory.Borel.SokalHyp.norm_borelZero_sub_sum_le` (`Lightlike/FieldTheory/Borel/Transform.lean`)
* `FieldTheory.Borel.isOpen_diskC` (`Lightlike/FieldTheory/Borel/Contour.lean`)
* `FieldTheory.quarticZ_nevanlinna` (`Lightlike/FieldTheory/ZeroDim/QuarticComplex.lean`)
* `FieldTheory.re_pos_of_mem_diskC` (`Lightlike/FieldTheory/ZeroDim/QuarticComplex.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.FieldTheory.Borel.SokalHyp.eq_laplace_borelZero

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

/-- **`f` is the Laplace transform of `b_0`** (Benedetti–Gurau–Keppler–Lettera, arXiv:2210.14776v2, Appendix B,
eq. (B.8), p. 25): under the hypotheses of the Nevanlinna–Sokal theorem, for `z` in the disk `C_R` and any line
`Re w = c > 1/R`, `f(z) = (1/z) ∫_0^∞ e^{-x/z} b_0(x) dx`.

The source takes the line `Re w = c` with `Re z⁻¹ > c`; here any `c > 1/R` is allowed, `b_0` not depending on the
line (`borelZero_indep`) (kind: representation). Non-vacuous: `sokalHyp_const`. -/
theorem SokalHyp.eq_laplace_borelZero {f : ℂ → ℂ} {a : ℕ → ℂ} {R K ρ : ℝ} (h : SokalHyp f a R K ρ) {c : ℝ}
    (hc : 1 / R < c) {z : ℂ} (hz : z ∈ diskC R) :
    f z = z⁻¹ * ∫ x in Ioi (0 : ℝ), cexp (-(x / z)) * borelZero f (a 0) x c := by
  sorry

end Lightlike.FieldTheory.Borel
