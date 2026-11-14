# The Turaev–Viro state sum

## Abstract (Alpha)

This API defines quantum integers and quantum 6j symbols at a root of unity `q = e^{iπ/r}` and the
Turaev–Viro state sum of a triangulated 3-manifold built from them. It proves that the normalised
state sum is invariant under the 2-3 and 1-4 Pachner moves, given the quantum Biedenharn–Elliott
and orthogonality identities, and proves both identities, and hence invariance outright, at
level `r = 3`.

## Content (Alpha)

At `q = e^{iπ/r}` with `r ≥ 3`, the quantum integers are positive in the range used by the model
[1], and the quantum 6j symbols have the tetrahedral symmetries [2]. The Turaev–Viro state sum
replaces integers by quantum integers and 6j symbols by quantum 6j symbols in the Ponzano–Regge
sum, cuts spins off at level `r − 2`, and normalises by one factor per vertex {1} [3].

A general state-sum model of this shape is invariant under the 2-3 move when its 6j symbols
satisfy the Biedenharn–Elliott identity, and under the 1-4 move when they also satisfy
orthogonality [4]. For the Turaev–Viro model this gives invariance under both moves, with the
quantum Biedenharn–Elliott and quantum orthogonality identities as explicit hypotheses [3]. At
`r = 3` both identities are proven, so the state sum is invariant without hypotheses [5]. The two
identities for `r ≥ 4` are not yet formalized. [TODO]

## Lean References

1. Lightlike/TuraevViro/QNumber.lean - `TV.qnum`, `TV.qnum_pos`
2. Lightlike/TuraevViro/QSixJ.lean - `TV.qSixJ`, `TV.qSixJ_swap12`
3. Lightlike/TuraevViro/TuraevViro.lean - `TV.turaevViro`, `TV.qBiedenharnElliott`,
   `TV.qOrthogonality`, `TV.turaevViro_move23`, `TV.turaevViro_move14`
4. Lightlike/TuraevViro/Model.lean - `TV.Model.Z_move23`, `TV.Model.Z_move14`
5. Lightlike/TuraevViro/LevelOne.lean - `TV.qBiedenharnElliott_three`,
   `TV.qOrthogonality_three`, `TV.turaevViro3_move23`, `TV.turaevViro3_move14`

## References

1. V. G. Turaev, O. Y. Viro, State sum invariants of 3-manifolds and quantum 6j-symbols,
   *Topology* 31 (1992) 865.
