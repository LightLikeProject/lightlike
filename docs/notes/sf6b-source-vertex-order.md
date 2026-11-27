# SF6b: what the source says about the vertex order

Milestone: SF6b, item p2 (the stated dependence of the state sum on the vertex order).

## Question

Does the state sum of the source of the EPRL model (arXiv:0711.0146v2, Engle, Pereira, Rovelli, Livine, "LQG vertex
with finite Immirzi parameter") depend on an order of the vertices of the 4-simplices, an order of their tetrahedra,
or an orientation convention? If the source states independence, or fixes a sign convention, the library's convention
(`eprlGlobalSign`, increasing vertex order) can be compared with it.

## What was read

The PDF of arXiv:0711.0146v2: 8 pages, Sections I to VI and the references; there are no appendices and no footnotes.
Pages 3 to 7 (Section II.B to the Conclusion) were read on the PDF itself; the page numbers below are those of the PDF.

## What the PDF says (MEASURED: read on the page)

- p. 3, Sec. II.B, after Eq. (15): "The orientation of the triangulation selects one of the two boundary tetrahedra
  separated by f: call it t." This chooses a tetrahedron for a face; it is the only orientation statement of the paper.
- p. 4, Sec. III, Eq. (27): the SU(2) spin `k` of the constrained subspace is `j+ + j-` for `0 < γ < 1` and `j+ - j-`
  for `γ > 1`; the text before Eq. (25) restricts to `γ > 0`. This selects a spin, not a sign or an order.
- p. 5, Sec. III, Eqs. (31) and (32): the vertex amplitude is
  `A(j_ab, i_a) = Σ_{i_a^+, i_a^-} 15j((1+γ) j_ab / 2; i_a^+) 15j(|1-γ| j_ab / 2; i_a^-) ⊗_a f^{i_a}_{i_a^+ i_a^-}(j_ab)`,
  "where the 15j are the standard SU(2) Wigner symbols", and `f^i_{i+ i-}` is built from the normalized intertwiner `C` of a
  virtual link and the Clebsch-Gordan coefficients `c`. No order of the five tetrahedra, no order of the legs of a
  tetrahedron and no sign convention for the 15j symbol or for `C`, `c` is stated.
- p. 5, Eqs. (33) and (34): `Z = Σ_{j_f, i_e} Π_f d_f Π_v A(j_f, i_e)` and `d_f = (|1-γ| j_f + 1)((1+γ) j_f + 1)`.
  The text says the amplitudes are glued "together with suitable edge and face amplitudes"; the edge amplitude is not
  written.
- p. 5 to 6, Sec. IV, Eqs. (35) to (42): the Lorentzian vertex (40), `A(j_ab, i_a) = Σ_{n_a} ∫ dρ_a (n_a² + ρ_a²) (⊗_a f^{i_a}_{n_a ρ_a}(j_ab)) 15j_{SL(2,C)}((2 j_ab, 2 j_ab γ); (n_a, ρ_a))`,
  with the same structure, and the partition function (42) with face weight `(2 j_f)² (1 + γ²)`. Again no order, orientation
  or sign convention is stated.
- p. 6, Sec. V (area spectra) contains no amplitude; p. 7, Sec. VI (Conclusion) lists open problems and does not mention an order.
- p. 3, Sec. II.B: `γ` is "assumed finite and ≠ 0, 1". The paper does not relate its amplitude to the Barrett-Crane or
  Ooguri amplitude at `γ = 1`, and states no factor `(-1)^…` for it.

## Result

The source is silent on the dependence of its state sum on the vertex order: it neither states independence nor fixes a
sign or a phase. It defines the vertex through 15j symbols of a 4-simplex, which depend on an order of the five tetrahedra
and of the legs of each of them; the paper fixes none.

- A formalization must choose such orders. The library takes the increasing order of the vertices and writes the sign
  twist `eprlGlobalSign` explicitly (`amplitudeI_one_eq_signed_ooguri`); its sorted-basis amplitude depends on the order
  (`docs/notes/sf6b-order-dependence.md`; the Lean counterexample is in a branch that is not on main).
- The source does not contradict this choice and does not support independence either; a comparison of the sign
  convention with the source cannot be made from the paper.

## Limits

- The quotes above are from the PDF; the equations are not re-derived here.
- Whether a different convention (a canonical order of the tetrahedra fixed by the geometry) would make the sum
  independent of the vertex order is not decided by the source.
