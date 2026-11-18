# T-SF10-P3: assessment of `lorVertex_farRemainder` (18 November 2026)

Statement: `Lightlike.Asymptotics.Lorentzian.lorVertex_farRemainder` (Tasks/SF/T_SF10_P3.lean) concludes
`FarRemainderBound j p g e χ`: for every `λ ∈ ℕ` the function `(1 − χ) A e^{λ S}` is integrable on `ℝ⁴⁴` and
`∫ (1 − χ) A e^{λ S} = O(λ^{-23})`.

## Finding 1: the hypotheses do not exclude critical points in the support of `1 − χ`

`hK : CriticalSetIs j p g e χ K` constrains only the points of `tsupport (χ · A)`: inside it, `Re S = 0 ∧ dS = 0` iff `x ∈ K`.
`hχ1` says `χ = 1` near `K`. Nothing is said about a point `x₁ ∉ tsupport χ` with `A(x₁) ≠ 0`, `Re S(x₁) = 0` and `dS(x₁) = 0`
(for Lorentzian data BDFHP eq. (53) has two parity-related critical points; a cutoff around one of them leaves the other
outside `tsupport χ`). If the Hessian at `x₁` is nondegenerate, stationary phase gives
`∫ (1 − χ) A e^{λ S} ~ c λ^{-22}` with `c ≠ 0`, contradicting `O(λ^{-23})`. So the statement is false for such `χ` unless the
hypothesis is strengthened to: every point of `tsupport A` with `Re S = 0 ∧ dS = 0` lies in `K`.
(MEASURED: not computed; PROXY, from the stationary-phase lemmas of `Lightlike/Oscillatory` and eq. (53)'s two critical points.)

## Finding 2: the tail is non-compact and no gap estimate exists

`expPhase_suppressed` (`Suppression.lean`) needs a compactly supported amplitude and `Re S < 0 ∨ dS ≠ 0` on its support. The
integrand `(1 − χ) A` is not compactly supported (`e : ℝ⁴⁴ ≃ᵐ SL(2,ℂ)⁴ × ℂ¹⁰`-coordinates). A proof needs (i) an integrable
majorant of `‖A‖ e^{λ Re S}` uniform in `λ ≥ 1` (this is `‖A‖ e^{Re S} ≤ ∏ρ_e` from `re_lorAction_le_zero` for one `λ`, and
monotonicity in `λ` for `Re S ≤ 0` gives uniformity once the `λ = 1` integrand is integrable), and (ii) a quantitative gap
`Re S ≤ −δ` on the part of the support of `1 − χ` outside a compact set, plus non-stationary phase on the compact part.
(ii) is the new estimate; it is not in BDFHP (the docstring of `lorVertex_farRemainder` says so).

## What was done (integrator's decision, 18 November 2026)

1. The critical-set hypothesis of `lorVertex_farRemainder` is now `CriticalSetIs j p g e (fun _ => 1) K`: every point of
   `tsupport A` with `Re S = 0 ∧ dS = 0` lies in `K`; the chart hypotheses of `lorVertex_asymptotics_fixChart` (`U`, `hP`,
   `hA`, `tsupport χ ⊆ U`) are added. LL-0135 is unchanged (it only assumes `FarRemainderBound`).
2. Split: T-SF10-P5 (`lorVertex_farRemainder_compact`): `∫ (ψ − χ) A e^{λ S} = O(λ^{-N})` for every `N`, provable from
   `expPhase_suppressed`; T-SF10-P6 (`lorVertex_farRemainder_tail`): the integrability and `O(λ^{-23})` of the non-compact tail
   `(1 − ψ) A e^{λ S}`, the new uniform estimate, with no decay hypothesis. T-SF10-P3 is the sum.
   If P6 is false, report a counterexample.

## Reuse check

Mathlib: no stationary-phase or oscillatory-integral estimate. Library: `nonstationary_phase`, `exists_bound_noncritical`
(`Lightlike/Oscillatory/Localisation.lean`), `expPhase_suppressed`, `weighted_suppressed` (`Suppression.lean`),
`re_lorAction_le_zero` (`Action.lean`). Physlib and Tau Ceti: not searched.
