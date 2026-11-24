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
(`D = a[[0,-1],[1,0]]`, `H = a·1`), a symmetric matrix rejected, the 1-point chain. NOT done: the existence of `H = |iD|`
from `D` (the matrix square root), the definition of `D` from a causal set (retarded Green function; CS1 `Basic` is on
main, the coefficient is dimension dependent and the sources Johnston 0909.0944 and Afshordi-Aslanbeigi-Sorkin
1205.7062 are unread), and necessity.

Not proved: the necessity (pure implies a compatible `J`). Source status: Dereziński, arXiv:math-ph/0511030, was read
for the conventions only, eq. (70) p. 38 (`(Ψ|W(y)Ψ) = exp(-¼ yηy)`) and Theorem 39 p. 39; it contains no purity
criterion (the text has no "pure"). The criterion itself is not compared with a published statement (comparison
pending: Bratteli-Robinson 2, Chapter 5, not read). So this has no catalogue entry.

Surprise / backlog: the sufficiency half reduces entirely to the existing Fock irreducibility; the hard half
(necessity, `η` degenerate) and the CS7 specialisation (positive part of the Pauli-Jordan matrix gives `J`) are open.
