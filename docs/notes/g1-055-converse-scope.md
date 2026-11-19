# G1-055: scope of the converse of the Wigner classification

The converse: every irreducible positive-energy unitary representation of `ℝ⁴ ⋊ SL(2,ℂ)` (orbits other than
`p = 0`) is one of the induced representations, and the little-group representations include the continuous-spin
series of the double cover of `ISO(2)`.

## Source read

E. Freitag, *Unitary representations of the Poincaré group, Wigner classification* (lecture notes, Heidelberg),
pages located by their printed page headers:

| Statement | Location |
| --- | --- |
| Stone's theorem for `ℝⁿ` (multiplication form) | Chapter V, §5, Theorem 5.1, p. 146 |
| projection-valued measure; support on a locally closed set | §5, Definition 5.5, Lemma 5.6, p. 147 |
| imprimitivity theorem (transitive cyclic systems are induced) | §4, Theorem 4.10, p. 143, proof pp. 143–145 |
| Mackey's assumption and theorem | §6, Assumption 6.1, Theorem 6.2, p. 149 |
| the irreducible unitary representations of `Iso(2)` | §6, Theorem 6.4, p. 150 |
| ergodicity; concentration on one orbit | §7, Lemma 7.1, p. 150; Proposition 7.2, p. 151 |
| the spectral theorem for `ℝ` (cyclic vectors, the functional `I_h(g) = ∫ h ĝ`) | Appendix VI.1, Theorem 1.2, Proposition 1.3, pp. 152–153 |

Freitag proves Theorem 5.1 by the route of Appendix VI.1 (positive-definite functions, a positive functional on
test functions, a decomposition into cyclic subspaces), and Theorem 4.10 through pseudomeasures of positive type on
the `∗`-algebra `C_c(Y × G)` (§3, Lemma 3.1, Remark 3.3; §4, Lemmas 4.5, 4.6, Remark 4.7, Lemma 4.9), with the
Haar measures and modular functions of `G` and of the stabiliser `L`.

## Part A: the joint spectral measure of the translations

The question: do Stone's theorem for the four commuting generators and a product of commuting projection-valued
measures give the joint spectral measure faster than the general theorem?

Available in the library: Stone's theorem (`Lightlike/OperatorAlgebras/Spectral/Stone/Theorem.lean`, `stone`: the
generator is self-adjoint, `U(t) = e^{itA}`, and it is unique); the spectral measure of one unbounded self-adjoint
operator, obtained from the Cayley transform and an abstract continuous calculus
(`Lightlike/OperatorAlgebras/Spectral/Unbounded/Cayley.lean`, `existsUnique_spectralMeasure_unbounded`);
`abstractPVM`, a projection-valued measure on a compact metric space `X` built from any isometric unital
`∗`-homomorphism `C(X, ℂ) → B(H)` (`Lightlike/OperatorAlgebras/Spectral/Unbounded/AbstractCalculus.lean`,
`IsAbstractCalculus`). Mathlib has Gelfand duality for commutative C*-algebras (`gelfandStarTransform`) and the
commutativity of the closure of a commutative star subalgebra (`isMulCommutative_topologicalClosure`).

Three routes:

1. **The general theorem along Freitag** (positive-definite functions on `ℝⁿ`, a positive functional on
   `C_c^∞(ℝⁿ)`, the Riesz–Markov theorem, a decomposition into cyclic subspaces by Zorn's lemma, direct sums of Radon
   measures). It reproves the one-variable spectral theorem in `n` variables; the cyclic decomposition and the direct
   sums are not in the library.
2. **The product of the four spectral measures, taken directly.** Once the `E_k` commute,
   `E(S₁ × ⋯ × S₄) = E₁(S₁) ⋯ E₄(S₄)` on rectangles is immediate, but extending it to all Borel sets of `ℝ⁴` is the
   whole difficulty. For each `ψ` the rectangle function is positive and σ-additive in each variable separately. The
   extension needs either an extension theorem for positive bimeasures, which is not in Mathlib, or a positive
   functional on `C_c(ℝ⁴)`. Positivity of that functional on functions that are not sums of products is the joint
   spectral theorem itself. No shortcut.
3. **The product at the level of the Cayley transforms (Gelfand).** The generators commute, so their Cayley
   transforms `C_k = (P_k − i)(P_k + i)⁻¹` are commuting unitaries. The C*-algebra they generate is commutative, and
   Gelfand duality gives an isometric unital `∗`-homomorphism from the continuous functions on the joint spectrum (a
   compact subset of the torus, via `χ ↦ (χ(C_k))_k`) to `B(H)`. `abstractPVM` turns it into a projection-valued
   measure, and the inverse Cayley map pushes that forward to `ℝⁿ` coordinatewise. The set where a coordinate equals
   `1` is null, because `1` is not an eigenvalue of `C_k`. By uniqueness the marginals are the spectral measures of the
   generators, and `U(a) = ∏ e^{i a_k P_k} = ∫ e^{i⟨p, a⟩} dE(p)` by multiplicativity of the integral.

Answer: yes. Route 3 is the four-generators-plus-product approach in a form that works: the product is taken over
the commuting unitaries, where Gelfand duality supplies the extension that route 2 lacks, and it is shorter than
route 1. Pieces, written for `ℝⁿ` so that they serve `ℝ⁴` and the `ℝ²` of `Iso(2)` (line counts are estimates):

| Piece | Lines |
| --- | --- |
| a bounded operator commuting with `U(t)` for all `t` commutes with the generator and its Cayley transform | 150 |
| commuting one-parameter groups have commuting Cayley transforms | 50 |
| the commutative C*-algebra generated by finitely many commuting unitaries, its Gelfand transform, the joint spectrum in the torus, the abstract calculus on it | 400 |
| the projection-valued measure on `ℝⁿ` (push-forward by the inverse Cayley map, the null set) | 250 |
| marginals, `U(a) = ∫ e^{i⟨p, a⟩} dE(p)`, uniqueness | 300 |

About 1150 lines, 3–4 days.

## Part B: imprimitivity implies induced

1. Covariance `U(A) E(S) U(A)⁻¹ = E(A · S)`, from the uniqueness in Part A (150 lines).
2. Ergodicity (Lemma 7.1): for an irreducible representation, `E(S) ∈ {0, 1}` for every invariant Borel set `S`
   (50 lines).
3. Concentration on one orbit (Proposition 7.2) under positive energy: `S ↦ E(p² ∈ S)` takes only the values
   `0, 1`, so it is concentrated at one value `m²` (countable basis of `ℝ`); then `E` is supported on one shell
   (`m > 0`), on the cone, or on `{0}` (300 lines).
4. **The imprimitivity theorem for the orbit (Theorem 4.10)**, the core of the converse. Freitag's route needs the
   `∗`-algebra `C_c(Y × G)`, pseudomeasures of positive type, Haar measures and modular functions of `G` and `L`,
   his model of the induced representation, and the reduction to cyclic systems; none of this machinery is in the
   library (the quotient integration over `G/L` is used here only through images of the Haar measure). The
   alternative uses the explicit sections of the orbits (the standard lifts; continuous on the shell, Borel on the
   cone). It identifies `H` with `L²(orbit, μ; M)` for a Hilbert space `M`, which needs the multiplicity theory of
   the projection-valued measure `E`, also not in the library; a cocycle argument then turns the covariant operators
   into a unitary representation of the stabiliser. Both routes are multi-week. Attempt 1: Freitag's route,
   specialised to `G = ℝ⁴ ⋊ SL(2,ℂ)` acting on one orbit with `L = SU(2)` or the `Iso(2)` cover. Attempt 2: the
   multiplicity route.
5. Identifying the little-group representation. Massive orbit: an irreducible unitary representation of `SU(2)` is
   finite-dimensional (to check in the library), hence a spin representation by `spinRep_complete`
   (`Lightlike/SU2/Completeness.lean`). Massless orbit: an irreducible unitary representation of the `Iso(2)` cover,
   classified by Theorem 6.4, that is Part A for `ℝ²` and steps 1–4 for `Iso(2)`.

## Part C: the continuous-spin series

The infinite-dimensional irreducible unitary representations of the `Iso(2)` cover (Theorem 6.4: induced from a
character `ε` of `{1, −1}` with the character `z ↦ e^{i(r, z)}`, `r > 0`, on `L²` of a circle), and the induced
Poincaré representations on `L²(cone; L²(circle))`: the representations, strong continuity, and irreducibility by the
methods of the helicity case (the commutant of the translations, now with infinite-dimensional fibres). About 1500
lines, 3–5 days, independent of step B4.

## Order

Part A (3–4 days), then B1–B3 (1–2 days), then Part C (3–5 days), so that the list of representations is complete
before the converse, then B4–B5, the long part.
