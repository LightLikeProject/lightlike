# G3-073 (colour-ordered trees): the Parke-Taylor amplitude and its symmetries

Lean: `Lightlike/GR/ColourOrdered.lean` (on G3-072's `SpinorHelicity.lean`).

## Source read (pdftotext of arXiv:1308.1697v2)

H. Elvang, Y. Huang, *Scattering Amplitudes*, §2.5:
* p. 24: (2.79) `A₄[1⁻2⁻3⁺4⁺] = ⟨12⟩⁴/(⟨12⟩⟨23⟩⟨34⟩⟨41⟩)`; the Parke-Taylor amplitude (2.80)
  `A_n[1⁺ ⋯ i⁻ ⋯ j⁻ ⋯ n⁺] = ⟨ij⟩⁴/(⟨12⟩⟨23⟩ ⋯ ⟨n1⟩)`; Exercise 2.24: (2.81) `A₄[1⁻2⁻3⁺4⁺] = [34]⁴/([12][23][34][41])`.
* p. 25: "1) Cyclic: … A_n[12 … n] = A_n[2 … n 1]; 2) Reflection: A_n[12 … n] = (−1)ⁿ A_n[n … 2 … 1]"; the U(1) decoupling
  identity (2.82) `A_n[123 … n] + A_n[213 … n] + A_n[231 … n] + ⋯ + A_n[23 … 1 n] = 0`; the Kleiss-Kuijf relations (2.83)–(2.85);
  Exercise 2.27: "Use the Parke-Taylor formula (2.80) to verify (2.85), (2.86), and (2.87)".
* p. 16, Schouten (2.48); p. 28, little-group weights (2.93).

Checked numerically before writing Lean (random complex spinors): the eikonal sum and (2.85) for Parke-Taylor vanish to
machine precision without momentum conservation.

## How each Lean statement matches

* `cycDen` (`⟨12⟩⟨23⟩ ⋯ ⟨n1⟩`), `parkeTaylor` ((2.80): the numerator spinors of the two negative-helicity gluons passed
  separately, the gluons' angle spinors in colour order).
* `cycDen_rotate`, `parkeTaylor_rotate`: cyclic symmetry. `cycDen_rev`, `parkeTaylor_rev`: reflection with `(−1)ⁿ`
  (index lemmas `rev_finRotate`, `finRotate_succAbove`, `finRotate_succ_eq`, `val_succAbove_succ`).
* `eikonal_sum`, `cycDen_insertNth`, `parkeTaylor_U1_decoupling`: (2.82) for every `n`.
* `cycDen_update_smul`, `parkeTaylor_littleGroup_plus`, `parkeTaylor_littleGroup_minus`: weights `t⁻²` (`h = +1`) and `t²`
  (`h = −1`), i.e. `t^{−2h}` (2.93).
* `parkeTaylor_KK5`: (2.85). `Conserved`, `contract_conserved`, `parkeTaylor_four_eq_square`: (2.79) = (2.81) with momentum
  conservation.

## Differences

1. Representation: gluons in colour order are a function `Fin n → (Fin 2 → ℂ)` of angle spinors (reorderings are composition
   with permutations of `Fin n`, insertions `Fin.insertNth`); the identities are stated for nonvanishing brackets (generic
   kinematics); the Parke-Taylor expression is the MHV sector (2.80), taken as a formula.
