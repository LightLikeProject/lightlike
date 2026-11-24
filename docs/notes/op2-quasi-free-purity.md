# G3-159 (OP2, for CS7): purity of a quasi-free state from a complex structure

Question: when is the quasi-free state `ω_η` (`ω_η(W(φ)) = exp(-¼ η(φ, φ))`) of a finite-dimensional symplectic space
a pure state, in a form CS7 ("the positive part of the Pauli-Jordan matrix defines a pure quasi-free state") can use?

What is proved (MEASURED: the three files compile, no `sorry`):
- `QuasiFreeState/FockEquiv.lean`: `qfKer_eq_fockGram`, `exists_unitary_qf_fock` (the GNS space of `ω_η` is unitarily the
  Fock space, intertwining the Weyl unitaries) and `isPureState_qfState_of_equiv`: if `ω = Im⟨e·, e·⟩` and
  `η = Re⟨e·, e·⟩` for an additive bijection `e` onto a complex inner product space, then `ω_η` is pure (from
  `commutant_scalar`, the irreducibility of the Fock representation, and `isPureState_qfState`).
- `QuasiFreeState/ComplexStructure.lean`: `CompatibleComplexStructure ω η` (`J² = -1`, `η` `J`-invariant and
  positive definite, `ω(x, y) = -η(x, J y)`), `isCovariance` (Cauchy-Schwarz), and
  `isPureState_qfState_of_complexStructure`.
- `QuasiFreeState/TestsComplexStructure.lean`: one mode is pure; the doubled covariance `2η` with the same `ω` has no
  compatible complex structure (the hypothesis fails; no claim about mixedness).

In matrix terms (`Ω` for `ω`, `H` for `η`, `η` positive definite): the condition is `Ω H⁻¹ Ω = -H` (from `Ω = -H J`, so `J = -H⁻¹ Ω`, and `J² = -1`),
with `Ω` antisymmetric and `H` symmetric positive definite.

CS7 step (second commit, branch opalg/op2-sj-pure): `QuasiFreeState/PauliJordan.lean`. For a real antisymmetric `D`
(Pauli-Jordan matrix, normalisation not fixed) and `H = |iD|` given by `PJData D H` (`H` symmetric PSD, `H² = -D²`,
`HD = DH`), `J = -(H|_R)⁻¹ D|_R` on `R = range H` is a compatible complex structure (`pjStructure`), `ℝⁿ = R ⊕ ker H`,
and `isPureState_pauliJordan` says the quasi-free state with `ω = x⬝Dy`, `η = x⬝Hy` is pure (`ker D` is the centre; the
retract form `isPureState_qfState_of_complexStructure_retract` handles the degenerate `ω`). Tests: the 2-chain
(`D = a[[0,-1],[1,0]]`, `H = a·1`), a symmetric matrix rejected, the 1-point chain. Third commit: `QuasiFreeState/SorkinJohnston.lean`: `exists_pjData` (`|iD|` = CFC square root of `-D²`, commutes with `D`),
`causalMatrix`, `pauliJordanMatrix a = a (C - Cᵀ)` (Johnston, arXiv:0909.0944, READ: eq. (1) causal matrix, eq. (10)
`Δ = K_R - K_A`, `K_A = K_Rᵀ`, eq. (16) `K_R = a C (1 - a b C)⁻¹`, `a = 1/2`, `b = -m²/ρ` in `M²`, so the massless case is
`K_R = a C`, eq. (20) `Q = Σ λ_i u_i u_i†`, `iΔ = Q - Qᵀ`, eq. (22) `[φ_x, φ_y] = iΔ_xy`, `Im Q = Δ/2`), and
`isPureState_causalSet`: the Sorkin-Johnston state of every finite causal set is pure. Differences / not claimed: only the
antisymmetrised retarded matrix `a C` (massless `M²`, any `a`) is built; the 4D `K_R = a L (1 - a b L)⁻¹` and the massive
2D case are other antisymmetric matrices and are covered by `isPureState_pauliJordan` once `Δ` is given; the milestone's
second source arXiv:1205.7062 is NOT the Afshordi-Aslanbeigi-Sorkin paper (it is a paper on fluctuations of linear
eigenvalue statistics), so that source is unverified; the identification `Q = Pos(iΔ) = ½ (|iΔ| + iΔ)` with the
two-point function `½ (η + iω)` of `QuasiFreeState` rests on eq. (20) and the stated relation `Im Q = Δ/2` (read), with
`η = |iΔ|` (not itself a displayed formula in the paper). Necessity not proved.

Not proved: the necessity (pure implies a compatible `J`). Source status: Dereziński, arXiv:math-ph/0511030, was read
for the conventions only, eq. (70) p. 38 (`(Ψ|W(y)Ψ) = exp(-¼ yηy)`) and Theorem 39 p. 39; it contains no purity
criterion (the text has no "pure"). The criterion itself is not compared with a published statement (comparison
pending: Bratteli-Robinson 2, Chapter 5, not read). So this has no catalogue entry.

Surprise / backlog: the sufficiency half reduces entirely to the existing Fock irreducibility; the hard half
(necessity, `η` degenerate) and the CS7 specialisation (positive part of the Pauli-Jordan matrix gives `J`) are open.

## Comparison (24 Nov 2026): Gérard, arXiv:1901.10175, Proposition 4.9.1
Read (text extracted from the PDF): a quasi-free state with covariance `η` (there `ω(W(x)) = exp(-½ x·ηx)`, so his `2η` is the `η` here) is pure iff `(2η^cpl, σ^cpl)` is Kähler, i.e. `σ j = 2η` for an anti-involution `j ∈ Sp`; proof cited to Dereziński-Gérard, Theorem 17.13 (not read). Bratteli-Robinson 2 was not available, so the comparison is with Gérard. Our `CompatibleComplexStructure` is this condition with `J = -j`; sufficiency is proved here, necessity is not (it needs the polar-decomposition argument of his Proposition 4.9.2 or a decomposition of a non-extremal state; not formalised).
