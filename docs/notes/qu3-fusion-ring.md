# QU3 (G3-201): the fusion ring of SU(2) at level r - 2; the modular tensor category is not built

Status: partial, conditional where it goes beyond the fusion ring.
Done (`TuraevViro/FusionRing.lean`): the fusion coefficients `fusionN r a b c` (1 if `qAdm r a b c`), their symmetry, the unit object, multiplicativity of the quantum dimension `[a+1]` (`fusion_dim`, from `sum_qAdm_qnum`), and associativity of the fusion ring for every `r ≥ 2` (`fusion_assoc`, by counting the admissible middle colours as an arithmetic progression).
Not done: the F-matrices (6j symbols) as isomorphisms of a monoidal category, the pentagon (it is the q-Biedenharn-Elliott identity, `qBiedenharnElliott`, a hypothesis of this library, so any pentagon statement is conditional on it), the braiding and hexagon (R-matrix of `U_q(sl₂)`, G3-200 side), the S and T matrices and modularity (G3-202), and the Reshetikhin-Turaev invariant.
No comparison with a published statement of the SU(2)_k fusion rules is claimed; the rules are the admissibility of `qAdm` already used by the Turaev-Viro code.
