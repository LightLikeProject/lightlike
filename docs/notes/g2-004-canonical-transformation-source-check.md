# G2-004: the canonical transformation ADM ↔ Ashtekar–Barbero (source check)

Lean file: `Lightlike/Canonical/AshtekarCanonical.lean` (in progress).

## Sources read

1. S. Holst, *Barbero's Hamiltonian derived from a generalized Hilbert-Palatini action*, arXiv:gr-qc/9511026, read in full.
2. A. Ashtekar and J. Lewandowski, *Background independent quantum gravity: a status report*, arXiv:gr-qc/0404018, Sec. II.

## Statements and the locations they rest on

| Lean | Source, location | Match |
|---|---|---|
| `E_dSpin_eq_div`: for a variation `(δe, δΓ)` satisfying the linearised compatibility, `E^a_i δΓ^i_a = −½ ∂_a(ε_abc e^k_c δe^k_b)` | Holst, eqs. (5)–(6), p. 2: the transformation `A ↦ A + γ δf/δE`, `f[E] = ∫ Γ^i_a E^a_i`, "the functional derivative of `f[E]` equals `Γ`"; the compatibility is Ashtekar–Lewandowski (2.17), p. 16 | The pointwise identity is the content of `δf/δE = Γ` (`δ(∫ΓE) = ∫ΓδE` iff `∫EδΓ = 0`); the source states the result, not this identity. |
| `integral_E_dSpin_eq_zero`: `∫ E^a_i δΓ^i_a = 0` for compactly supported variations | Holst (5)–(6), p. 2 | Same content (`δf/δE = Γ`). |

## Next steps (not yet done)

* the variation `δΓ = d/dt Γ(e + t δe)` satisfies the linearised compatibility (so `integral_E_dSpin_eq_zero` applies to it);
* the symplectic potentials: `∫ E δA = γ ∫ E δK` (Ashtekar–Lewandowski (2.19)–(2.20), p. 17), and `∫ E δK` in terms of
  `∫ π δh` on the Gauss constraint surface.
