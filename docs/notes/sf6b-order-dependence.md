# SF6b: the EPRL state sum at gamma = 1 depends on the vertex order through the sign twist

Milestone: SF6b, item p2 (the stated dependence of the state sum on the vertex order).

## Question

Is `amplitudeI 1` (the EPRL state sum in the sorted tetrahedron basis at the BF point) independent of the order of the
vertices of the 4-complex, as the checklist item p2 words it? If not, what is the dependence?

## Method and evidence (numbers)

`scripts/spinfoam/eprl_order_check.py` models `amplitudeI 1` on the boundary of the 5-simplex (`sphere6`) line by line
from `IntrinsicVertex.lean` (`nodeT`, `nodeI`, `nodeP`, `fifteenJSimplex`) and relabels the vertices by sending the
bone cutoff of the edge `{0, 1}` to the bone cutoff of `{u, w}` (a permutation of the vertices maps `sphere6` to itself,
so order independence would force the same value for all fifteen edges).

- MEASURED (numerical, not a proof): `amplitudeI 1` with the bone cutoff of `{u, w}` is `+5.0` for `w - u` odd and `-3.0`
  for `w - u` even (15 edges: `A(0,1) = 5`, `A(0,2) = -3`, `A(0,3) = 5`, `A(0,4) = -3`, ...). It depends on the vertex
  order, and by a different magnitude, not only by a global sign.
- MEASURED, control 1 (pure Ooguri `Ooguri.amplitudeGF` model with `ampP`, same relabellings): `5.0` for all fifteen
  edges, i.e. the Ooguri amplitude `1 + 4` (zero colouring plus bone colouring, `weight_col0 = 4`) is invariant. So the
  face and edge amplitudes `(J+1)`, `1` are not the cause.
- MEASURED, control 2 (wrong-input): gluing the positional labels directly (`EPRL.amplitude` of
  `Lightlike/SpinFoam/EPRL.lean`) gives `1.0` where the intrinsic sum gives `5.0` / `-3.0`: the script distinguishes the two.
- PROVED (Lean): `amplitudeI 1 sphere6 col0 = weight 0 + weight col0 = 1 + 4 = 5` (`amplitudeI_sphere6_low_spin`, the
  value for the edge `{0, 1}`: only the zero colouring and the bone colouring survive the triangle constraints, both with
  sign `+1`); with the face amplitude `(J+1)^2` the same sum is `65` (`amplitudeI_wrong_face`).
- PROVED (Lean): for the bone colouring of any edge `{u, w}`, `u < w`, with the virtual spins forced by the triangle
  constraints (`bone_admitted`), the global sign of the signed Ooguri sum is `(-1)^(w - u - 1)`
  (`eprlGlobalSign_bone`): `+1` for `{0, 1}`, `-1` for `{0, 2}`, ... This is the swap phase: it reproduces the pattern
  `5` / `-3` of the numerical model, given that the Ooguri weight of the bone colouring of every edge is `4`.
- PROXY / not proved in Lean: the Ooguri weight `4` of the bone colourings of the edges other than `{0, 1}`, hence the
  values `-3` for `w - u` even in Lean (they need the vertex amplitude `ampP` of four 4-simplices with the edge at
  positions other than `{0, 1}`, i.e. new 15j evaluations); and the invariance of `amplitudeI` under order isomorphisms.

## Interpretation

The dependence of `amplitudeI 1` on the vertex order is exactly the dependence of the explicit sign `eprlGlobalSign` (the
triangle part and the tetrahedron swap signs, which depend on the positions of the omitted vertices of the two simplices
of every tetrahedron). The relative sign between the colouring terms changes with the order, so the magnitude of the sum
changes. The checklist wording "independent of the vertex order" over-states what the definition gives; the milestone row
asks for the stated dependence. There are two statements the item can carry: (a) the item is worded "dependence stated"
(this note and `eprlGlobalSign_bone`); (b) a compensating vertex-type sign in the definition so that the twist is
trivial, which changes `eprlGlobalSign`, `sgnU`, `sgnV` and the chain `ComplexSign*` (about ten files).

## Limitations

The model script is a numerical re-implementation, not the Lean definition; Lean confirms it for the edge `{0, 1}`
(`5`) and for the sign of every bone colouring, but not the `-3` values.
