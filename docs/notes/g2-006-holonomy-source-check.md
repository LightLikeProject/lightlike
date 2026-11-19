# G2-006: paths, holonomy and gauge action (source check)

Lean files: `Lightlike/ODE/GlobalLipschitz.lean`, `Lightlike/Canonical/Holonomy.lean`,
`Lightlike/Canonical/HolonomyPaths.lean` (in progress).

## Source read

A. Ashtekar and J. Lewandowski, *Background independent quantum gravity: a status report*, arXiv:gr-qc/0404018 (v2),
read in the arXiv PDF at pp. 27-29 (Sec. IV B, eqs. (4.14)-(4.18), footnotes 13-15), p. 33 (eqs. (4.35)-(4.37),
footnote 17) and p. 35 (the common graph `α₃` of two graphs). Printed page numbers equal the PDF pages.

## Statements and the locations they rest on

| Lean | Source, location | Match |
|---|---|---|
| `MatConn`: a connection as matrix-valued components `A_a(x)` on the chart `ℝ³` | p. 28, footnote 14: "Throughout this paper, we will work with a fixed trivialization" | Representation: AL's local trivialisation, with `G ⊂ GL(n, ℂ)` a matrix group. |
| `exists_transport`, `transport_unique`, `transport`, `hasDerivWithinAt_transport`: `d/dt U(t) = −A_a(e(t)) ė^a(t) U(t)`, `U(t₁) = 1` | eq. (4.35), p. 33 | Same equation; existence and uniqueness are not stated in the source and are proved here (`Lightlike/ODE/GlobalLipschitz.lean`). |
| `transport_trans`: `U(u, s) = U(u, t) U(t, s)` | eq. (4.35) (the parallel transport from `e(t₁)` to `e(t)`) | Supporting result. |
| `holonomy`: `A(e) = U(t₂, t₁)` | eq. (4.36), p. 33 | Same. The edges are `C¹` on `ℝ`, where AL use closed-piecewise analytic edges. Representation: footnote 17, p. 33: "These assumptions can be relaxed and one can work with just smooth structures". |
| `holonomy_mem_specialUnitaryGroup`: for `su(2)`-valued `A`, `A(e) ∈ SU(2)` (`transport_conjTranspose_mul_self`: unitary for `u(n)`; `transport_det_two`: `det = 1` for traceless `A` in dimension two) | p. 33, after (4.36): "Thus, `A(e) ∈ G`" | Same for `G = SU(2)`. |
| `holonomy_comp_reparam`: `A(e ∘ φ) = A(e)` for `C¹` `φ` monotone on the parameter interval | p. 33, after (4.36): `A(e)` "is unchanged under orientation-preserving re-parameterizations of `e`" | Same, for `C¹` reparametrisations that are monotone (not necessarily strictly). |
| `transport_isUnit`, `Edge.isUnit_hol`: the transport is invertible | p. 33: `A(e) ∈ G` | Supporting result (a left inverse solves `Y' = Y A_a ė^a`). |
| `holonomy_revPath`, `Edge.hol_rev`, `PwPath.hol_rev`: `A(e⁻¹) = A(e)⁻¹` | eq. (4.37), p. 33, with "`e⁻¹` is obtained from `e` by simply reversing the orientation" | Same; for a piecewise path `p⁻¹` reverses the pieces and their order. |
| `Edge`, `PwPath`, `PwPath.hol`, `PwPath.hol_trans`, `PwPath.hol_comp₂`: `A(e₂ ∘ e₁) = A(e₂) A(e₁)` | eq. (4.37), p. 33 | Same, for piecewise `C¹` paths (lists of `C¹` edges, each starting where the previous one ends), the class closed under composition; AL's edges are closed-piecewise analytic (footnote 17), the representation line above. |
| `Edge.hol_split`: splitting an edge does not change its holonomy | p. 33: "introducing suitable new vertices on `e`" (before (4.39)) | Supporting result: the holonomy of a piecewise path does not depend on the subdivision of a `C¹` piece. |

## Trust checks

* `holonomy_u1Conn`: the constant `u(1)` connection `A₀ = i` along `e(t) = t e₀` has holonomy `exp(−iπ) = −1` over
  `[0, π]`.

## Open (the rest of G2-006)

* the gauge action (4.14), p. 28, on holonomies, and the maps `I_E`, `I_V` of (4.16)-(4.17);
* graphs and the order `α ≤ α′` (p. 27, footnote 13), and the common graph `α₃` of two graphs (p. 35).
