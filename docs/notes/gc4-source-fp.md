# GC4: the Faddeev-Popov determinant against a source that was read

Source: A. Wipf, "Hamilton's Formalism for Systems with Constraints", lectures, arXiv:hep-th/9312078 (ETH-TH/93-48), read in its arXiv HTML version. Section 5.2, equations (5.29)-(5.30).

What the source says: gauge conditions `F_a = 0` should meet every gauge orbit exactly once; a necessary condition is
(5.29) that some `F_b` varies along every null direction `X_a` (`λ^a {γ_a, F_b} ≠ 0`), hence (5.30) `det {γ_a, F_b} ≠ 0`, the
Faddeev-Popov determinant, which makes the first-class constraints with the gauge conditions a second-class system. The source
cites Gribov and Singer for obstructions to attainability and uniqueness.

Match with the library: `FaddeevPopov.pairing_fpMatrix` identifies `dG_a(X_{φ_b}) = {G_a, φ_b}`;
`FaddeevPopov.exists_ker_of_det_eq_zero` is the contrapositive of (5.29)-(5.30): if the determinant vanishes, some nonzero
combination of the gauge directions is annihilated by every `dG_a` (tangent to the slice); and
`linearIndependent_hamField_of_det_ne_zero`, `eq_zero_of_mem_ker_of_det_ne_zero` state that a nonzero determinant gives
transversality of the orbit to the slice.

The second-class property after (5.30) is `FaddeevPopov.combinedBracket_det_ne_zero_iff`: at a point where the constraints are first class, the
bracket matrix of the combined family `(φ, G)` is nonsingular iff the Faddeev-Popov determinant is nonzero.

Scope: (1) the statements are at a point, as (5.29)-(5.30) are; the global attainability and uniqueness of the gauge (every orbit meets the slice
once) and the Gribov copies, which the source cites (Gribov, Singer) and does not prove, are not claimed; (2) the phase space is Physlib's flat
`X × X`.
