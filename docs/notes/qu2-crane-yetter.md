# QU2 (G3-199, G2-029): the quantum 15j symbol; the Crane-Yetter state sum is not built

Status: partial.
Done: `qFifteenJ` (TuraevViro/QFifteenJ.lean), the 15j symbol of the first kind with the quantum 6j `qSixJ` and the weight `[x+1]_q` at `q = e^{iπ/r}`, mirroring `Lightlike.Recoupling.fifteenJ`; `qFifteenJ_zero` (all spins zero give 1 for every `r ≥ 2`); the terms vanish unless the triad `(a₀ b₀ x)` is `qAdm`.
Not done: the Crane-Yetter state sum on a 4-complex (colourings of triangles and tetrahedra, the face and edge weights, the vertex amplitude `qFifteenJ` of the 4-simplex contraction), its invariance under the 4D Pachner moves (it needs the q-Biedenharn-Elliott identity, `qBiedenharnElliott`, a hypothesis here, G3-196), and the trust checks for `S⁴` and `CP²` (Gauss sums; a triangulation of `CP²`).
No comparison with Crane-Kauffman-Yetter (1997) is claimed; the vertex weight follows the classical 15j of the first kind and the Turaev-Viro conventions of `QSixJ`.
