# Statement card: the Ponzano–Regge asymptotic formula for the 6j symbol (LL-0030)

| | |
|---|---|
| Result | `Lightlike.Asymptotics.ponzanoReggeFormula : PR.PonzanoReggeFormula`, entry LL-0030 (`main: true`) |
| Files | statement `Lightlike/PonzanoRegge/Asymptotics.lean` (`PonzanoReggeFormula`, line 100); proof `Lightlike/Asymptotics/SaddleAssembly.lean`, line 751 (main at `eeba9873b`) |
| Source | J. Roberts, *Classical 6j–symbols and the tetrahedron*, Geometry & Topology 3 (1999) 21–66, arXiv:math-ph/9812013, Theorem 1 (p. 23) and Section 6.1 (pp. 61–62) |
| Card written | 27 Nov 2026, from the paper (Theorem 1 and Section 6.1 read from the page images; Definitions 2 and 3, the Cayley-polynomial passage and the dihedral-angle definition read in the text) and the Lean files named below (read) |

## 1. The source theorem, word for word

> **Theorem 1** (Asymptotic formula) *Suppose a tetrahedron is admissibly labelled by the numbers a, b, c, d, e, f. Let k be a natural number. As k → ∞, there is an asymptotic formula*
>
> { ka kb kc ; kd ke kf } ∼ √( 2 / (3πV k³) ) · cos { Σ (ka + 1) θ_a / 2 + π/4 }  *if τ is Euclidean*, and *exponentially decaying if τ is Minkowskian* (2)
>
> *(where the sum is over the six edges of the tetrahedron).*

(The formula is a display with a brace: top line for the Euclidean case, bottom line for the Minkowskian case. In the Euclidean case the three symbols after `cos` are `Σ (ka+1)·θ_a/2` and `+ π/4`; the `π/4` is outside the sum.)

The text before and after it that the statement depends on, verbatim:

> "A classical 6j–symbol is a real number which can be associated to a labelling of the six edges of a tetrahedron by irreducible representations of SU(2), in other words by natural numbers. … Let V_a (a = 0, 1, 2, …) denote the (a + 1)–dimensional irreducible representation."

> "The SU(2)–invariant part of the triple tensor product V_a ⊗ V_b ⊗ V_c is non-zero if and only if a ≤ b + c, b ≤ c + a, c ≤ a + b, a + b + c is even (1)"

> "Suppose we have a tetrahedron, labelled so that the three labels around each face satisfy these conditions: we will call this an admissible labelling."

> "To an admissibly-labelled tetrahedron we may associate a metric tetrahedron τ whose side lengths are the six numbers a, b, …, f. Its individual faces may be realised in Euclidean 2–space, by the admissibility condition (1). As a whole, τ is either Euclidean, Minkowskian or flat (in other words has either a non-degenerate isometric embedding in Euclidean or Minkowskian 3–space, or has an isometric embedding in Euclidean 2–space), according to the sign of a certain polynomial in its edge-lengths. If τ is Euclidean, let θ_a, θ_b, …, θ_f be its corresponding exterior dihedral angles and V be its volume."

> "If the i-th and j-th faces meet in an edge u, oriented along the direction of v_i × v_j, then the exterior dihedral angle, written θ_u or θ_ij, is defined (in the range (0, π)) by u sin(θ_ij) = [u.v_i.v_j], cos(θ_ij) = v_i.v_j." (Section 5.8, with v_i the face normals.)

> "The sign of the Cayley polynomial V²(a², b², …, f²) (whose explicit form is irrelevant here) is the remaining piece of information needed to determine whether τ is Euclidean, flat or Minkowskian." (Section 5.4)

> **Definition 3** "Given six irreducibles V_a, V_b, …, V_f, one can form ε_abc ⊗ ε_cde ⊗ ε_efa ⊗ ε_fdb … Then the hermitian pairing of these two vectors … defines the associated 6j–symbol by { a b c ; d e f } = (−1)^(Σ a) ( ⊗⁶ ε^aa , ⊗⁴ ε^abc ) where Σ a is simply the sum of the six labels." (page 26, read from the page image; ε^aa has norm √(a+1) and ε^abc norm 1, by the text above Definition 3.) The text after it says: "It is standard to extend the definition to all such sextuples by setting the 6j–symbol to zero elsewhere." and, in a remark, "It does depend on the sign conventions, but these can be seen to be sensible (in that the resulting 6j–symbol is S₄–invariant) using the lemma" (Lemma 4: Definitions 2 and 3 agree).

> "Varshalovich et al [15] … Their definition coincides with the two given here, and with the one in Ponzano and Regge (though in these physics-oriented papers, half-integer spins are used)."

Section 6.1, which relates the theorem to the Ponzano–Regge formula, verbatim:

> "It is important to note that the formula (2) is not the same as the original Ponzano–Regge formula. There are two main differences, apart from the trivial fact that they label their representations by half-integers instead of integers. Their claim, in our integer-labelling notation, is that for large a, b, c, d, e, f: { a b c ; d e f } ≈ √(2/(3πV′)) cos{ Σ (a + 1) θ′_a / 2 + π/4 } if τ′ is Euclidean, exponentially decaying if τ′ is Minkowskian (14), where τ′ is a tetrahedron whose edges are a+1, b+1, …, f+1 and whose dihedral angles θ′_a and volume V′ are therefore slightly different from those of our τ."

> "The second difference explains this. The Ponzano–Regge formula (14) is only claimed as an *approximation* for large irreducibles, rather than an asymptotic expansion in a strict sense as in theorem 1. Therefore the only meaningful comparison between the two formulae is to examine how their function behaves as we rescale a, b, c, d, e, f by k → ∞ in the precise sense of our theorem."

> "As for comparing the actual formulae, the asymptotic behaviour of the Ponzano–Regge function is √(2/(3πk³V)) cos{ Σ (ka + 1) θ′_a / 2 + π/4 } (15), because V and V′ agree to leading order in k. The only problem is the dihedral angles relating to slightly different tetrahedra. Fortunately we may easily show that e^{ik Σ (a+1) θ′_a} ∼ e^{ik Σ (a+1) θ_a} by applying the *Schläfli identity* (see Milnor [11]), which says that the differential form Σ a dθ_a vanishes identically on the space of Euclidean tetrahedra. Therefore there is no inconsistency."

> **Remark** "The case of a flat tetrahedron is not covered by either formula."

Also: "Throughout the paper, the symbol '∼' denotes an asymptotic formula, whereas '≈' denotes merely an approximation." (Section 1.) The paper does not define "∼" for a right-hand side that has zeros; see difference 7.

## 2. The Lean statement, verbatim

From `Lightlike/PonzanoRegge/Asymptotics.lean` (the docstring is part of the file):

```lean
/-- **The Ponzano–Regge asymptotic formula**, in the Ponzano–Regge form (edge lengths `j + ½`): for
spins `j` whose four faces satisfy the triangle inequalities and that form a non-degenerate
Euclidean tetrahedron (`vol2 > 0`), `√(12πV) {6j}(λj) - cos(S_Regge + π/4) → 0`. Proven as
`Lightlike.Asymptotics.ponzanoReggeFormula`. Roberts' Theorem 1 uses the unshifted tetrahedron; the
two forms agree by his §6.1 (the Schläfli identity), but that equivalence is not proven here, and
Roberts' Minkowskian case (`vol2 < 0`) is not stated.
... (counterexample paragraph and integer-base-spin paragraph, see the file) -/
def PonzanoReggeFormula : Prop :=
  ∀ j : Fin 6 → ℕ,
    IsTriad (j 0) (j 1) (j 2) → IsTriad (j 0) (j 4) (j 5) → IsTriad (j 3) (j 1) (j 5) →
    IsTriad (j 3) (j 4) (j 2) →
    0 < vol2 (j 0) (j 1) (j 2) (j 3) (j 4) (j 5) →
    Tendsto (fun lam : ℕ =>
      Real.sqrt (12 * π * Real.sqrt (vol2 (lengths j lam 0) (lengths j lam 1) (lengths j lam 2)
          (lengths j lam 3) (lengths j lam 4) (lengths j lam 5))) * sixJScaled j lam -
        Real.cos (reggeAction (lengths j lam) + π / 4)) atTop (𝓝 0)
```

and the proof, `Lightlike/Asymptotics/SaddleAssembly.lean:751`:

```lean
theorem ponzanoReggeFormula : PR.PonzanoReggeFormula :=
  ponzanoReggeFormula_of_racahSumAsymptotics racahSumAsymptotics
```

The definitions it uses, verbatim (same file, lines 61–97):

```lean
noncomputable def vol2 (a b c d e f : ℝ) : ℝ :=
  (a^2*d^2*(-a^2 - d^2 + b^2 + e^2 + c^2 + f^2) + b^2*e^2*(a^2 + d^2 - b^2 - e^2 + c^2 + f^2)
    + c^2*f^2*(a^2 + d^2 + b^2 + e^2 - c^2 - f^2)
    - a^2*b^2*c^2 - a^2*e^2*f^2 - d^2*b^2*f^2 - d^2*e^2*c^2) / 144

noncomputable def cosDihedral (pq pr qr ps qs rs : ℝ) : ℝ :=
  let ru := (pr^2 + pq^2 - qr^2) / (2 * pq)
  let su := (ps^2 + pq^2 - qs^2) / (2 * pq)
  ((pr^2 + ps^2 - rs^2) / 2 - ru * su) / Real.sqrt ((pr^2 - ru^2) * (ps^2 - su^2))

noncomputable def dihedral (pq pr qr ps qs rs : ℝ) : ℝ := Real.arccos (cosDihedral pq pr qr ps qs rs)

noncomputable def extAngles (l : Fin 6 → ℝ) : Fin 6 → ℝ :=      -- the six π − dihedral
  ... ![π - dihedral AB CA BC AD BD CD, π - dihedral BC AB CA BD CD AD, π - dihedral CA BC AB CD AD BD,
        π - dihedral CD CA AD BC BD AB, π - dihedral AD AB BD CA CD BC, π - dihedral BD AB AD BC CD CA]

noncomputable def lengths (j : Fin 6 → ℕ) (lam : ℕ) : Fin 6 → ℝ := fun e => lam * j e + 1 / 2
noncomputable def reggeAction (l : Fin 6 → ℝ) : ℝ := ∑ e, l e * extAngles l e
noncomputable def sixJScaled (j : Fin 6 → ℕ) (lam : ℕ) : ℝ :=
  sixJSym (2 * lam * j 0) (2 * lam * j 1) (2 * lam * j 2) (2 * lam * j 3) (2 * lam * j 4)
    (2 * lam * j 5)
def IsTriad (a b c : ℕ) : Prop := c ≤ a + b ∧ a ≤ b + c ∧ b ≤ a + c
```

`sixJSym` is Physlib's (`PhyslibAlpha/QuantumMechanics/AngularMomentum/SixJSymmetry.lean:233`), in doubled units: `sixJSym j₁ … j₆ = ∑ m ∈ sixJBox j₁ … j₆, sixJTerm j₁ … j₆ m`, where `sixJTerm` is `(−1)^(Σ (jᵢ − mᵢ) / 2) · (3j)(3j)(3j)(3j)` with the four 3j symbols `(j₁ j₂ j₃; −m₁ −m₂ −m₃)`, `(j₁ j₅ j₆; m₁ −m₅ m₆)`, `(j₄ j₂ j₆; m₄ m₂ −m₆)`, `(j₄ j₅ j₃; −m₄ m₅ m₃)`: the standard sum of four 3j symbols over the projections. The labelling in `PonzanoRegge/` is `j₁ = AB, j₂ = BC, j₃ = CA, j₄ = CD, j₅ = AD, j₆ = BD`; the triads are the faces and the columns of the 6j symbol pair opposite edges.

## 3. Dictionary

| Roberts | Lean | Remark |
|---|---|---|
| labels a, b, c, d, e, f (natural numbers, "twice the spin") | `2 * lam * j e`, the doubled labels handed to `sixJSym` | Roberts' k·a is the Lean's 2λ·j_e: **k = 2λ, a = j_e**. So Lean's k is always even, and its base labels j_e need only satisfy the triangle inequalities. |
| { ka kb kc ; kd ke kf } | `sixJScaled j lam` = `sixJSym (2λj₁) … (2λj₆)` | Physlib's 6j symbol by the sum over four 3j symbols; Roberts' Definitions 2 and 3 are different formulations (spin-network evaluation, hermitian pairing). He says they agree with Varshalovich et al. and Ponzano–Regge. |
| admissible: (1) for the four faces | `IsTriad` for the four faces | Parity is not required of j: the doubled labels 2λj_e have even face sums automatically. |
| τ, side lengths a…f | the tetrahedron with `vol2 (j 0) … (j 5)`, in the hypothesis only | Euclidean iff the squared volume is positive. |
| V² (Cayley polynomial) | `vol2` (Euler–Tartaglia form, divided by 144) | The explicit Cayley polynomial is not written in Roberts ("irrelevant here"). Audit in the file: `vol2_regular` (`V² = ℓ⁶/72`). |
| θ_a, exterior dihedral angles of τ | `extAngles l e = π − dihedral …` | Roberts defines θ through face normals (cos θ_ij = v_i · v_j); the Lean takes `π − interior angle`, the interior angle being the arccos of `cosDihedral`. Audit: `cos_dihedral_regular` (`cos φ = 1/3`). |
| Σ (ka+1) θ_a/2 | `reggeAction l = ∑ e, l e * extAngles l e` at `l = lengths j lam`, `lengths = λ j_e + ½` | (ka+1)/2 = (2λj+1)/2 = λj + ½: see difference 1. |
| √(2/(3π V k³)) | `Real.sqrt (12 π · √vol2 (lengths))` multiplying the 6j symbol | Reciprocal and a different unit of length; see below. |
| ∼ | `Tendsto (…) atTop (𝓝 0)` on the difference of the normalised 6j symbol and the cosine | See difference 7. |
| Minkowskian ("exponentially decaying"), flat | not stated | See differences 3 and 4. |

The prefactor, by hand (PROXY: this card's computation, not a Lean theorem). Roberts' tetrahedron has edge lengths equal to the labels, so scaling a label by ½ to spin units divides edge lengths by 2 and the volume by 8. Then `√(2/(3π · 8 V_spin))= √(1/(12π V_spin))`, which is the reciprocal of the Lean prefactor `√(12π V)`. Phase: `(ka+1)θ/2 = (2λj+1)θ/2 = (λj+½)θ`, the Lean's phase term. So the two statements have the same shape once Roberts' tetrahedron is read in spin units and shifted by ½.

## 4. Differences from the source

1. **Shifted tetrahedron (the Ponzano–Regge form), not Roberts' form.** The Lean volume, angles and phase use the edge lengths `λ j_e + ½`. Roberts' Theorem 1 uses the tetrahedron with lengths `ka` and the phase `Σ (ka+1) θ_a / 2` with the angles of the *unshifted* τ. This is the "(slightly different) version" of Roberts' Section 6.1, his (14)/(15). He argues the two forms agree via the Schläfli identity (a two-line argument, quoted above, that is not worked out in detail). The Lean theorem is therefore the Ponzano–Regge form, with Roberts' Theorem 1 as a sibling statement; the equivalence between the two is not formalised (the docstring and the catalogue entry say so). Kind: **FORM**.
2. **Euclidean hypothesis is on the unshifted spins.** `0 < vol2 (j 0) … (j 5)` is Roberts' hypothesis ("τ is Euclidean"). The shifted tetrahedra are Euclidean for large λ (PROXY: `vol2` is a continuous function, homogeneous of degree 6 in the lengths, so the sign at `λj + ½` agrees with the sign at `j` for large λ; the card does not prove it) and the statement is a limit, so only large λ matters.
3. **Minkowskian case not stated.** Roberts' Theorem 1 has the case "exponentially decaying" when τ is Minkowskian (`vol2 < 0`); the Lean statement has no such case. Kind: **COVERAGE**.
4. **Flat case.** `vol2 = 0` is covered by neither (Roberts' own Remark); the Lean hypothesis is strict `0 < vol2`.
5. **Integer spins only.** In the Lean every spin λ·j_e is an integer (the doubled labels 2λj_e are all even), and j needs only the triangle inequalities, no parity condition. Roberts: any admissible base labels a…f and any k → ∞, so the spins ka/2 can be half-integers. By the dictionary (k = 2λ, a = j), the Lean covers every admissible base a along the even-k subsequence, and every base with all labels even along all k (a = 2j, k = λ). It does not cover the sequences with k odd and some base label odd. Kind: **COVERAGE**, noted in the catalogue entry ("the base spins are integers").
6. **6j symbol.** Roberts' Definition 3 carries the sign (−1)^(Σ labels); the Lean uses the standard 3j-sum definition. The card has not compared them symbol by symbol. Roberts says his definition agrees with Varshalovich et al. and with Ponzano–Regge (quoted above), and the numerical check (section 6) agrees with the standard Wigner 6j for the three tetrahedra tested; neither is a proof that the two conventions agree for all labels. Kind: **CONVENTION**, one reviewer question below.
7. **Meaning of "∼".** Roberts writes `∼` between a 6j symbol and a function with zeros (a cosine) and does not define it further than "asymptotic formula", and "≈" for approximation. The Lean statement fixes one reading: the difference between the normalised 6j symbol `√(12πV)·{6j}` and `cos(S + π/4)` tends to 0, an *absolute* error statement after normalisation; a ratio statement (6j / RHS → 1) is false at zeros of the cosine and is not what the Lean says. ASSUMPTION: this is what Roberts intends (his proof is a stationary-phase evaluation to leading order; the error rate is not stated in Theorem 1). The Lean statement is also weaker than an error bound such as O(1/λ): it says only that the difference tends to 0.
8. **Triangle inequalities are an explicit hypothesis.** Roberts has them inside "admissibly labelled"; the Lean includes the four `IsTriad` hypotheses and the docstring proves that `vol2 > 0` does not imply them (counterexample `j = (1, 1, 3, 1, 5, 3)`, `vol2 = 1.625`, the 6j symbol vanishes identically).
9. **Proof shape.** Roberts: geometric quantization and stationary phase on the moduli of SU(2) representations. Lean: Racah's alternating sum (`racahFormula` converts `sixJScaled` to `racahSum`), then a saddle-point contour estimate for the sum (`racahSumAsymptotics`). The two proofs share nothing but the statement.

## 5. Why each hypothesis is needed

- **The four `IsTriad` hypotheses.** If a face violates the triangle inequality, the 6j symbol is zero for every λ (Roberts: "otherwise the 6j–symbol is simply zero"), while the cosine need not tend to 0. The file has a counterexample for `vol2 > 0` alone: `j = (1, 1, 3, 1, 5, 3)`, `vol2 = 1.625 > 0`, face `(1, 1, 3)` is not a triangle (the file's docstring states it; the `vol2` formula above, evaluated in Python at this sextuple on 27 Nov 2026, gives 1.625; the 6j symbol vanishing follows from the triangle condition, and neither was re-checked in Lean). The docstring also says an exhaustive search over `j ∈ {0, …, 6}⁶` found no tuple with the weak triangle inequalities and `vol2 > 0` that needs more (a finite search, so it says nothing about larger j).
- **`0 < vol2 (j 0) … (j 5)`.** Without it the tetrahedron is Minkowskian or flat; for the Minkowskian case Roberts' statement is a different one (exponential decay), and a cosine with a real volume and angles is not defined (the Lean `Real.sqrt` of a negative number is 0, so the statement would be about a different, meaningless object there; the card has not tested what happens at those inputs).
- **`j : Fin 6 → ℕ` and `lam : ℕ`.** The sequence `λ j` must consist of natural numbers because `sixJSym` takes natural doubled labels. Taking doubled labels `2λj` makes all face sums even automatically.
- **The `+ π/4`.** The tests (section 6) prove the formula with phase offset 0 or −π/4 is false, so the constant is pinned down by the theorem itself.

## 6. Trust checks

- **Axioms** (MEASURED, `lake env lean` on the seed build of `eeba9873b`, `#print axioms`): `ponzanoReggeFormula`, `ponzanoReggeFormula_regular`, `not_ponzanoReggeFormulaWith_zero`, `not_ponzanoReggeFormulaWith_neg_quarter` and `PR.vol2_regular` each depend only on `[propext, Classical.choice, Quot.sound]`.
- **Tests in `Lightlike/Asymptotics/SaddleAssemblyTests.lean` and `PhaseTests.lean`** (read): `ponzanoReggeFormula_regular` gives the limit at the regular tetrahedron `j = (1,…,1)` (the hypotheses are met there: four triangular faces, `V² = ℓ⁶/72 > 0`), so the statement is not vacuous; `racahSumAsymptotics_regular` gives the explicit limit at the same tetrahedron with `θ = π − arccos ⅓`; `not_ponzanoReggeFormulaWith_zero` and `not_ponzanoReggeFormulaWith_neg_quarter` show the formula with the phase 0 or −π/4 in place of π/4 is false; `ponzanoReggeFormulaWith_add_two_pi` is the positive control (offsets differing by 2π give the same statement); `kernelRegion_one_zero`, `kernelRegion_zero_four` and `not_kernelRegion_one_four` document the junk-value behaviour at λ = 0.
- **Numerical evidence** (MEASURED, `python3 scripts/pr_asymptotics.py`, run on 27 Nov 2026, exit 0, "OK"): the normalised error `|√(12πV)·{6j} − cos(Φ + π/4)|`, maximum over windows of five consecutive λ, falls like 1/λ: regular `(1,1,1,1,1,1)`: 0.0068, 0.0031, 0.0016, 0.0010 at λ in 10–14, 20–24, 40–44, 76–80 (log-log slope −1.05); `(2,2,2,2,2,3)`: 0.0105, 0.0049, 0.0028, 0.0016 (slope −1.00); `(2,3,3,2,3,2)`: 0.0258, 0.0117, 0.0076, 0.0029 (slope −1.17). Control without the ½ shift (`--no-shift`): 0.51, 0.52, 0.52, 0.54 / 0.45–0.46 / 0.34, 0.32, 0.35, 0.28 (slopes 0.03, 0.01, −0.11), i.e. the error does not decay. Three tetrahedra only: this supports the Ponzano–Regge form at those inputs and the sign convention of `sixJSym` there, and proves nothing about others. The 6j values come from Racah's formula in exact integers, "validated against SymPy's wigner_6j in `tv_check.py`" (script docstring; `tv_check.py` was not re-run for this card).
- **Not done by this card:** reading the Lean proof of `racahSumAsymptotics` (about 250 lines of saddle-point estimates) or of `racahFormula`; checking Roberts' proof; the unshifted statement (Roberts' form, difference 1) and the Minkowskian case are not in Lean; no check of the 6j conventions beyond the three tetrahedra above.

## 7. One question for the reviewer

Is Physlib's `sixJSym` (the sum over projections of four 3j symbols with the sign `(−1)^(Σ (jᵢ − mᵢ)/2)`) equal to Roberts' 6j symbol (his Definition 3, with the sign `(−1)^(Σ labels)`) for all admissible labels, or only up to a label-dependent sign? The theorem is stated for the first; Roberts' Theorem 1 and the Ponzano–Regge formula are stated for the second and for Wigner's. The numerics above agree for three tetrahedra, the Lean tests pin the phase constant at π/4, but no one has compared the two definitions symbol by symbol.
