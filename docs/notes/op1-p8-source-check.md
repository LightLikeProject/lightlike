# T-OP1-P8: source check of the statement

Source read: G. Teschl, *Mathematical Methods in Quantum Mechanics*, Graduate Studies in Mathematics 99, AMS (online
edition posted with the permission of the AMS, `https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf`),
Chapter 3, Section 3.1 "The spectral theorem". Each item below was read at its location in that text.

| Statement in the task | Location in the source | Match |
|---|---|---|
| A projection-valued measure on the Borel sets of `ℝ`: orthogonal projections `P(Ω)`, `P(ℝ) = I`, strong `σ`-additivity | Section 3.1, definition (3.5), printed page 88 | Same fields in `ProjectionValuedMeasure ℝ H` (star projection for every set, `0` on non-measurable sets, `univ`, `hasSum'`). The product rule `P(Ω₁ ∩ Ω₂) = P(Ω₁)P(Ω₂)` is not an axiom, as in the source. |
| Domain of the integral of a Borel function `f`: `D_f = {ψ ∣ ∫ ‖f‖² dμ_ψ < ∞}` | (3.25), page 91 | `integralDomain μ f = {ψ ∣ MemLp f 2 (μ.assoc ψ)}`; for measurable `f` this is the same condition. |
| The value `P(f)ψ = lim P(f_n)ψ`, `f_n = χ_{|f| ≤ n} f` | (3.26), (3.27), page 91 | `pmapIntegral` is defined by the polarized form of the quadratic form `ψ ↦ ∫ f dμ_ψ`; the identity with the limit of the truncated integrals is the theorem `tendsto_integral_trunc_apply` (`Lightlike/OperatorAlgebras/Spectral/Unbounded/Integral.lean`). Truncation by `|f| < n` instead of `|f| ≤ n`: no difference in the limit. A difference of representation. |
| Spectral theorem: to every self-adjoint operator `A` there corresponds a unique projection-valued measure `P_A` with `A = ∫ λ dP_A(λ)` | Theorem 3.7, equation (3.49), page 96 | `∃! μ : ProjectionValuedMeasure ℝ H, pmapIntegral μ (fun x : ℝ => (x : ℂ)) = A` for `A : H →ₗ.[ℂ] H` with `IsSelfAdjoint A` (equal domains for `A` and its adjoint, the definition in the source). Existence and uniqueness are both stated. |

The Lean proof is ported from physicslib4 (`Spectral/Unbounded/Cayley.lean`, `existsUnique_spectralMeasure_unbounded`);
the route there is the Cayley transform, not the resolvent and Stieltjes inversion of the source. The statement is the
source's; the proof route is not.

Not checked: B. C. Hall, *Quantum Theory for Mathematicians*, Chapter 10, was not read. The comments "Blueprint: thrm:hall-10.x" in the ported files are the original author's tags and are not verified here; only the match with Teschl above counts. A comparison with Hall is pending.
