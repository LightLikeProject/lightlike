# Karamata's Tauberian theorem and Ingham's theorem: sources read and proof route

Started 18 November 2026.

## Sources read

* M. Herdegen, G. Liang, O. Shelley, "A continuity theorem for generalised signed measures with an application
  to Karamata's Tauberian theorem", arXiv:2205.13075v2 (29 March 2023). Read: Section 1 and Section 3 up to
  Theorem 3.2 (PDF text, pages 1 and 6). **Theorem 3.1** (p. 6): for a positive measure `μ` on `[0, ∞)` with
  finite Laplace transform `Ψ_μ(τ) = ∫ e^{-τx} dμ(x)` for all `τ > 0`, distribution function
  `F_μ(x) = μ[0, x]`, and `ρ ≥ 0`, the statements
  (3.1) `lim_{τ↓0} Ψ_μ(τλ)/Ψ_μ(τ) = λ^{-ρ}` for all `λ > 0` and
  (3.2) `lim_{t↑∞} F_μ(tx)/F_μ(t) = x^ρ` for all `x > 0`
  imply each other, and in either case (3.3) `Ψ_μ(t⁻¹) ~ F_μ(t) Γ(ρ + 1)` as `t → ∞`.
  The paper states the theorem and refers for its proof to Feller (Vol. II, XIII.5, Theorem 1),
  Bingham–Goldie–Teugels (Theorem 1.7.1) and König (1960); those were NOT read. The proof below is Karamata's
  method (polynomial approximation), written out independently.
* B. Mukhametzhanov, A. Zhiboedov, "Modular invariance, tauberian theorems and microcanonical entropy",
  arXiv:1904.06359. Read: Section 1.1 (the theorem with eq. (1.8), p. 7) and Section 1.2 (p. 8). Their theorem
  assumes modular invariance and an estimate for complex `β`; Section 1.2 says that (1.8) without the error
  term "is known as Ingham's tauberian theorem for large Laplace transform [23]" (A. E. Ingham, "A Tauberian
  theorem for partitions", Ann. of Math. 42 (1941)), with an exposition in their [12], Section IV.21.
  Ingham's paper and [12] were NOT read: the hypotheses of Ingham's theorem are not recorded here.

Mathlib (pinned tree, grep on 18 November 2026) and Physlib: no Tauberian theorem, no Karamata theorem, no
regularly or slowly varying functions. Mathlib master and open pull requests were not searched (no GitHub
calls allowed tonight).

## Target statements

(a) Karamata, Tauberian direction, in the form of the assignment: `ρ ≥ 0` on `[0, ∞)`,
`∫ e^{-βx} dρ ~ C β^{-α}` as `β → 0⁺` (`C > 0`, `α ≥ 0`) implies `ρ[0, X] ~ C X^α / Γ(α + 1)` as `X → ∞`.
It is the special case of Theorem 3.1 in which (3.1) holds because the transform is asymptotic to a power.
The general Tauberian direction ((3.1) implies (3.3) and (3.2)) is proved by the same argument.

## Proof route (Karamata's method)

For `β > 0` put `A_β(h) = (∫ e^{-βx} h(e^{-βx}) dρ) / L(β)`. Then `A_β(u^k) = L((k+1)β)/L(β) → (k+1)^{-α}`,
the `k`-th moment of the image under `t ↦ e^{-t}` of the Gamma distribution with shape `α` (the unit mass at
`t = 0` if `α = 0`). So `A_β(P) → ∫ P(e^{-t}) dγ_α(t)` for polynomials, then for continuous `h` on `[0, 1]`
(Weierstrass), then for `g(u) = u⁻¹ 1_{u ≥ 1/e}` by a sandwich between continuous functions and dominated
convergence (`γ_α` has no atom at `t = 1`). Finally `A_β(g) = ρ[0, 1/β] / L(β)` and
`∫ g(e^{-t}) dγ_α = 1/Γ(α + 1)`.

## Ingham's theorem: the source read (18 November 2026)

K. Bringmann, C. Jennings-Shaffer, K. Mahlburg, "On a Tauberian theorem of Ingham and Euler–Maclaurin
summation", arXiv:1910.03036v3 (24 November 2020). Read: Section 1 up to Theorem 1.1 and its remarks (pp. 1 to
2) and the start of Section 4, Theorems 4.1 and 4.2 (pp. 11 to 12) (PDF text).

* **Theorem 4.1** (p. 11; "due to Ingham [13, Theorem 1]", [13] = A. E. Ingham, *A Tauberian theorem for
  partitions*, Ann. of Math. 42 (1941)). `D ⊆ ℂ` connected open containing `(0, h]`, `δ(t)` the distance from
  `t` to the complement of `D`; `φ`, `χ` on `D` with (a) holomorphic on `D`, positive on `(0, h]`;
  (b) `−t φ′(t) → ∞` as `t → 0⁺`; (c) `−δ(t) φ′(t) / (t √(φ″(t))) → ∞`; (d) `φ″(t + z) = O(φ″(t))` and
  `χ(t + z) = O(χ(t))` uniformly for `|z| < δ(t)`. `A : [0, ∞) → ℝ` weakly increasing, `A(0) = 0`,
  `f(z) = ∫₀^∞ e^{−zu} dA(u)` existing for `Re z > 0`, with (i) `f(z) ~ χ(z) e^{φ(z)}` as `z → 0` in `D`;
  (ii) for each fixed `Δ > 0`, `f(z) = O(χ(|z|) e^{φ(|z|)})` as `z → 0` with `|Im z| ≤ Δ Re z`. Then
  `A(x) ~ χ(ψ(x)) e^{φ(ψ(x)) + xψ(x)} / (ψ(x) √(2π φ″(ψ(x))))` as `x → ∞`, `ψ` the inverse function of `−φ′`.
* **Theorem 4.2** (p. 12; "[13, Theorem 1′]"): under (a) to (d) and `−t^k φ′(t)` decreasing to `0` for some
  fixed real `k`, condition (i) may be replaced by (i′) `f(t) ~ χ(t) e^{φ(t)}` as `t → 0⁺` (real `t`).
* **Theorem 1.1** (p. 2), the form for power series: `B(q) = ∑ b_n qⁿ` with `b_n ≥ 0`, radius of convergence
  at least one, `γ > 0`, and (1.2): `B(e^{−t}) ~ λ log(1/t)^α t^β e^{γ/t}` as `t → 0⁺` together with
  `B(e^{−z}) ≪ log(1/|z|)^α |z|^β e^{γ/|z|}` as `z → 0` in each region `|y| ≤ Δx` (`z = x + iy`, `x > 0`).
  Then (1.3) `∑_{n ≤ N} b_n ~ λ γ^{β/2 − 1/4} log(N)^α e^{2√(γN)} / (2^{α+1} √π N^{β/2 + 1/4})`, and (1.4) for
  weakly increasing `b_n`.
* The paper stresses (p. 2, and Section 3.2) that the bound for complex `z` in the angles `|y| ≤ Δx` is an
  essential hypothesis: "the analytic behavior of `B(e^{−z})` for `z → 0⁺` along the real axis is not
  sufficient in general to determine the asymptotic behavior of the coefficients", with counterexamples in its
  Section 3.2 (NOT read yet).

Consequence for the formalisation. The full Ingham theorem is NOT a statement about a measure and its real
Laplace transform alone: `laplace ρ β ~ λ β^b e^{a/β}` for real `β → 0⁺` does not imply the asymptotics of
`ρ[0, X]` (only the logarithmic asymptotics, pl's `ingham_logarithmic`). The source's hypotheses need the
Laplace transform at complex arguments and the bound (ii). Ingham's proof was not read (the paper cites it,
does not reproduce it).

## Search for a readable proof of Ingham's theorem (19 November 2026, bounded search)

Looked for an open-access proof of Ingham's Theorem 1 / 1′ (Ann. of Math. 42 (1941)) or of
Bringmann–Jennings-Shaffer–Mahlburg, Theorem 1.1, under the complex (angle) hypotheses. Result: none found.

* Bringmann–Jennings-Shaffer–Mahlburg (arXiv:1910.03036v3), Section 4 (read, pp. 11 to 12): states Ingham's
  Theorems 1 and 1′ as Theorems 4.1 and 4.2 with the attribution "[13, Theorem 1]", "[13, Theorem 1′]" and
  uses them to prove Theorem 1.1; it does not reproduce Ingham's proof.
* Two web searches (19 November 2026) returned, besides that paper, only texts on a different theorem with
  Ingham's name (the Ingham–Karamata / Ingham–Fatou–Riesz theorem for Laplace transforms bounded near the
  imaginary axis: arXiv:1705.00667, arXiv:1604.05069, arXiv:2411.03809, arXiv:2007.04284), and papers that
  quote the partition theorem without proof (for example arXiv:1905.06304, Theorem 4.1). None of these was
  read beyond the search summary, and none is cited as a source here.
* Ingham's paper and Korevaar's *Tauberian Theory* (Section IV.21, the exposition named by
  Mukhametzhanov–Zhiboedov) are not open access; they were not read.

So the full Ingham theorem is blocked on a readable proof. Nothing is formalised for it.

## Status (19 November 2026): Karamata's theorem is proved

All files of `Lightlike/Asymptotics/Karamata/` compile, with no `sorry`.

| Formal statement (Lean) | Source (Herdegen–Liang–Shelley, arXiv:2205.13075v2) | Match |
| --- | --- | --- |
| `karamata_iff` (`Abelian.lean`): for a measure `ρ` on `[0, ∞)`, finite on compact sets, with finite Laplace transform `L`, and `α ≥ 0`: (`∀ λ > 0`, `L(τλ)/L(τ) → λ^{-α}` as `τ → 0⁺`) if and only if (`∀ x > 0`, `ρ[0, tx]/ρ[0, t] → x^α` as `t → ∞`); and then `L(1/t)/ρ[0, t] → Γ(α + 1)` | Theorem 3.1, p. 6: (3.1) ⇔ (3.2), and (3.3) | match. Representation: the measure lives on `ℝ` with `ρ(Iio 0) = 0`, with pl's `laplace` and `counting`; "`∼`" in (3.3) is written as the limit of the quotient; the limits `τ ↓ 0`, `t ↑ ∞` are along `𝓝[>] 0` and `atTop` |
| `karamata_counting_regularlyVarying`, `karamata_laplace_div_counting` (`RegularVariation.lean`) | Theorem 3.1: (3.1) ⇒ (3.2), (3.3) (the Tauberian direction) | match |
| `karamata_abelian`, `tendsto_laplace_div_counting_of_counting_rv` (`Abelian.lean`) | Theorem 3.1: (3.2) ⇒ (3.1), (3.3) (the Abelian direction) | match |
| `karamata_tauberian`, `karamata_tauberian_zero` (`Karamata.lean`): `L(β) β^α → C > 0` implies `ρ[0, X]/X^α → C/Γ(α + 1)` | the case of Theorem 3.1 in which `L` is asymptotic to a power (the form of the assignment) | corollary of the Tauberian direction; proved directly |

Non-vacuity: `karamata_lebesgue` (`Tests.lean`), Lebesgue measure on `[0, ∞)` with `L(β) = 1/β`.
The source cites the proof (Feller, Bingham–Goldie–Teugels, König: not read); the proof here is Karamata's
method (moments, Weierstrass approximation, a sandwich for the step function) for the Tauberian direction,
and the layer-cake formula with a doubling bound and dominated convergence for the Abelian direction.
Ingham's theorem: not formalised (see above).
