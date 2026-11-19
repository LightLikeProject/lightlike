# G2-004: the canonical transformation ADM ↔ Ashtekar–Barbero (source check)

Lean files: `Lightlike/Canonical/AshtekarCanonical.lean`, `Lightlike/Canonical/SpinVariation.lean`,
`Lightlike/Canonical/AshtekarSymplectic.lean` (in progress).

## Sources read

1. S. Holst, *Barbero's Hamiltonian derived from a generalized Hilbert-Palatini action*, arXiv:gr-qc/9511026, read in full.
2. A. Ashtekar and J. Lewandowski, *Background independent quantum gravity: a status report*, arXiv:gr-qc/0404018, Sec. II,
   read in the arXiv PDF (v2) at pp. 10-11 and 15-17 (printed page numbers, equal to the PDF pages).
3. E. Gourgoulhon, *3+1 Formalism and Bases of Numerical Relativity*, arXiv:gr-qc/0703035, Sec. 4.5, read at
   pp. 66-67 (eqs. (4.95), (4.103)-(4.109)).

## Statements and the locations they rest on

| Lean | Source, location | Match |
|---|---|---|
| `E_dSpin_eq_div`: for a variation `(δe, δΓ)` satisfying the linearised compatibility, `E^a_i δΓ^i_a = −½ ∂_a(ε_abc e^k_c δe^k_b)` | Holst, eqs. (5)–(6), p. 2: the transformation `A ↦ A + γ δf/δE`, `f[E] = ∫ Γ^i_a E^a_i`, "the functional derivative of `f[E]` equals `Γ`"; the compatibility is Ashtekar–Lewandowski (2.17), p. 16 | The pointwise identity is the content of `δf/δE = Γ` (`δ(∫ΓE) = ∫ΓδE` iff `∫EδΓ = 0`); the source states the result, not this identity. |
| `integral_E_dSpin_eq_zero`: `∫ E^a_i δΓ^i_a = 0` for compactly supported variations | Holst (5)–(6), p. 2 | Same content (`δf/δE = Γ`). |
| `linCompat_dSpin`: `δΓ = d/dt Γ(e + t δe)` satisfies the linearised compatibility | the variation of Ashtekar–Lewandowski (2.17), p. 16 | Supporting result (the source does not state it separately). |
| `integral_E_deriv_spinConn_eq_zero`: `∫ E^a_i (d/dt Γ(e + t δe))^i_a = 0` | Holst (5)–(6), p. 2 | Same content, for the actual variation of the spin connection. |

| `triad_potential`: along `(e + t δe, K + t δK)`, `E^a_i δK^i_a = δ(√h K) + ½ π^{ab} δh_ab` with `π = √h (K^{ab} − K h^{ab})`, `K` symmetric, `det e > 0` | Ashtekar–Lewandowski (2.19)–(2.21), p. 17: `Ω = ∫ δ₁P δ₂A − δ₂P δ₁A`, `kγ P = E`, `A = Γ − σγ K`; Gourgoulhon (4.106)–(4.109), p. 67: `π^{ij} = ∂L/∂γ̇_ij = √γ (K γ^{ij} − K^{ij})` conjugate to `γ_ij` (`H = π γ̇ − L`), for the action (4.95) `S = ∫ R √−g` | Representation. (a) It is stated for the potentials `Θ = ∫ E δA` and `∫ π δh`, not for `Ω = dΘ`. AL define `Ω` as the curl of `Θ` (p. 11), so `Θ_AB = c Θ_ADM + δF` gives `Ω_AB = c Ω_ADM`. (b) `E` is used, not `P = E/(kγ)`. (c) `K` has AL's sign, which is minus Gourgoulhon's; with Gourgoulhon's `K`, this `π` is (4.108). (d) The normalisation: with `k = 8πG` (AL p. 10) and Gourgoulhon's action without `1/16πG`, `∫ P δA = (1/k) δ∫√h K + (1/2k) ∫ π δh`, so in the units `16πG = 1` of both `Ω_AB = Ω_ADM`. (e) It holds on the Gauss constraint surface: `K` is symmetric (`gaussK_eq_zero_iff`). |

## Next steps (not yet done)

* the integrated potentials: `∫ E δA = γ ∫ δ(√h K) + (γ/2) ∫ π δh` for `A = Γ + γ K` (`abConn`), from `triad_potential`
  and `integral_E_deriv_spinConn_eq_zero`.
