# QU3 (G3-201): the fusion ring of SU(2) at level r - 2; the modular tensor category is not built

Status: partial, conditional where it goes beyond the fusion ring.
Done (`TuraevViro/FusionRing.lean`): the fusion coefficients `fusionN r a b c` (1 if `qAdm r a b c`), their symmetry, the unit object, multiplicativity of the quantum dimension `[a+1]` (`fusion_dim`, from `sum_qAdm_qnum`), and associativity of the fusion ring at the levels `r = 3, 4, 5, 6` (`fusion_assoc_small`, all colour quadruples by `decide`). Associativity for every `r` is not proved: a counting proof (the admissible middle colours form an arithmetic progression) made the omega steps exceed the build memory limit.
Not done: the F-matrices (6j symbols) as isomorphisms of a monoidal category, the pentagon (it is the q-Biedenharn-Elliott identity, `qBiedenharnElliott`, a hypothesis of this library, so any pentagon statement is conditional on it), the braiding and hexagon (R-matrix of `U_q(sl₂)`, G3-200 side), the S and T matrices and modularity (G3-202), and the Reshetikhin-Turaev invariant.
No comparison with a published statement of the SU(2)_k fusion rules is claimed; the rules are the admissibility of `qAdm` already used by the Turaev-Viro code.

## The S matrix (`TuraevViro/SMatrix.lean`, G3-202)
`sMat r a b = √(2/r) sin(π(a+1)(b+1)/r)`: symmetric, unit row `S_{0b} = S_{00}[b+1]_q`, `S_{00} > 0`, and the Verlinde formula for the unit-object row (`verlinde_zero`, which is `fusion_dim`). Missing: the Verlinde formula for the other rows (the generalisation of `sum_qAdm_qnum` to `θ = π(x+1)/r`), the orthogonality `S² = 1`, unitarity, and the T matrix and modularity. No small-`r` check by `decide` because the entries are real sines.

## Orthogonality (`TuraevViro/SOrthogonal.lean`)
`sum_sin_mul_sin_orth` (discrete sine orthogonality, a telescoping cosine sum) and `sMat_mul_self`: `S² = 1`, so `S` is an orthogonal involution. Still missing: the Verlinde formula for the other rows (generalise `sum_qAdm_qnum` to `θ = π(x+1)/r`), the T matrix and modularity.
