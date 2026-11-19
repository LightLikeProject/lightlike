# G3-072: spinor-helicity variables

Lean: `Lightlike/GR/SpinorHelicity.lean` (on `ComplexMinkowski.lean`, G3-061).

## Physlib, Mathlib and repository check

Physlib: no spinor-helicity, angle/square brackets or little-group scaling (grep for `helicity`, `angleBracket`, `Schouten`,
`littleGroup`; the only "little group" is crystallographic, `CondensedMatter/Crystal/Symmetry/IrreducibleZone.lean`); its
`Fermion.metricRaw = !![0, 1; -1, 0]` is the matrix of Elvang-Huang's `ε^{ab}` (A.3) and is reused. Repository:
`ComplexMinkowski.lean` has `spinorMat` (Adamo's `x^{αα̇}`, signature `(+, −, −, −)`), `qC_eq_two_det`,
`det_eq_zero_iff_vecMulVec` (a `2 × 2` matrix is singular iff it is an outer product), `qC_eq_zero_iff`, `qC_eq_zero_iff_tmul`;
reused through `momBispinor_eq` (Elvang-Huang's bispinor is `−√2` times the adjugate of `spinorMat`). Mathlib: nothing.

## Source read (pdftotext of arXiv:1308.1697v2)

H. Elvang, Y. Huang, *Scattering Amplitudes*, arXiv:1308.1697, chapter 2 and Appendix A:
* p. 244, Appendix A: mostly-plus metric `η = diag(−1, 1, 1, 1)`; `(σ^μ)_{aḃ} = (1, σ^i)` (A.1); `ε^{ab} = ε^{ȧḃ} = [[0, 1], [−1, 0]] =
  −ε_{ab} = −ε_{ȧḃ}` (A.3); `p_{aḃ} = p_μ (σ^μ)_{aḃ}` (A.10) `= [[−p⁰ + p³, p¹ − i p²], [p¹ + i p², −p⁰ − p³]]` (A.11); `det p = −p_μ p^μ`
  (A.12).
* p. 9: (2.6)–(2.8), the same bispinor and determinant.
* p. 10: raising `[p|^a = ε^{ab} |p]_b`, `|p⟩^ȧ = ε^{ȧḃ} ⟨p|_ḃ` (2.13); `p_{aḃ} = −|p]_a ⟨p|_ḃ` (2.16) for massless `p`; pp. 10–11: "if a
  2 × 2 matrix has vanishing determinant, it can be written as a product of two 2-component vectors, say λ_a and λ̃_ḃ: i.e.
  det p = 0 ⇔ p_{aḃ} = −λ_a λ̃_ḃ", with `λ_a → |p]_a`, `λ̃_ȧ → ⟨p|_ȧ`; p. 11: "the angle and square spinors are only defined up to an
  overall scaling that leaves p^μ invariant. This is called the little group scaling".
* p. 12: the brackets `⟨p q⟩ = ⟨p|_ȧ |q⟩^ȧ`, `[p q] = [p|^a |q]_a` (2.22); antisymmetry (2.23); `⟨p q⟩ [p q] = 2 p · q = (p + q)²` (2.24).
* p. 15: Mandelstam variables, all momenta outgoing, `s_{ij} = −(p_i + p_j)²` (2.39).
* p. 16: the Schouten identity (2.46)–(2.48), `⟨r i⟩⟨j k⟩ + ⟨r j⟩⟨k i⟩ + ⟨r k⟩⟨i j⟩ = 0`, and "A similar Schouten identity holds for
  the square spinors: [ri][jk] + [rj][ki] + [rk][ij] = 0".
* p. 27: little group scaling `|p⟩ → t|p⟩`, `|p] → t⁻¹|p]` (2.92) leaves (2.16) invariant; for complex momenta `t` is any nonzero
  complex number; p. 28: an amplitude has little-group weight `−2h_i` (2.93).

Numerical check of the conventions before writing Lean (random complex spinors, `p = −λλ̃` inverted through (A.11)):
`⟨pq⟩[pq] = 2p·q` and `−(p + q)² = ⟨pq⟩[qp]` agree to machine precision, so `s_{ij} = ⟨ij⟩[ji]` in these conventions.

## How each Lean statement matches

* `mdot` (mostly-plus product), `momBispinor` ((A.10)–(A.11), (2.7)), `det_momBispinor` ((A.12), (2.8)), `momOf`, `momEquiv`
  (momenta are bispinors). Bridge to G3-061: `momBispinor_eq_adjugate` (`p_{aḃ} = −√2 adj(spinorMat p)`), `mdot_self_eq_neg_qC`,
  `mdot_self_eq_zero_iff_qC`.
* `mdot_self_eq_zero_iff`: `p · p = 0 ⇔ ∃ λ λ̃, p_{aḃ} = −λ_a λ̃_ḃ` (pp. 10–11, (2.16)), via G3-061's `det_eq_zero_iff_vecMulVec`;
  `nullMom`, `momBispinor_nullMom`, `mdot_nullMom_self` (every pair of spinors gives a null momentum).
* `nullMom_littleGroup`: (2.92) leaves the momentum invariant; `exists_littleGroup_of_eq`: conversely two factorisations of the
  same nonzero momentum differ by a little-group scaling (p. 11).
* `angleBr`, `squareBr` (2.22) with (2.13); `angleBr_eq`, `squareBr_eq` (components); `angleBr_antisymm`, `squareBr_antisymm`
  (2.23); `angleBr_mul_squareBr`: `⟨pq⟩[pq] = 2 p · q` (2.24); `mandelstam`, `mandelstam_nullMom`: `s_{ij} = −(p_i + p_j)² = ⟨ij⟩[ji]`
  ((2.39) with (2.24)).
* `schouten_angleBr` (2.48), `schouten_squareBr` (p. 16), `raise` and `schouten_raise` (2.47).
* `angleBr_smul_left`, `squareBr_smul_left`, `mandelstam_littleGroup`: the little-group weights of the brackets under (2.92) and
  the invariance of `s_{ij}`.
* Trust check: `(E, 0, 0, E) = nullMom (0, 1) (0, 2E)`.

## Differences

1. Representation: momenta are complex 4-vectors `p^μ` (Elvang-Huang allow complex momenta, p. 10 and footnote 2, where the
   angle and square spinors are independent); spinors are `Fin 2 → ℂ` with lower indices, `λ_a = |p]_a` and `λ̃_ȧ = ⟨p|_ȧ`
   (p. 11); the brackets are functions of the spinors, `⟨ij⟩ = angleBr λ̃_i λ̃_j`, `[ij] = squareBr λ_i λ_j`.
