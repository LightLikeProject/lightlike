# G2-006: paths, holonomy and gauge action (source check)

Lean files: `Lightlike/ODE/GlobalLipschitz.lean`, `Lightlike/Canonical/Holonomy.lean`,
`Lightlike/Canonical/HolonomyPaths.lean`, `Lightlike/Canonical/HolonomyGauge.lean`,
`Lightlike/Canonical/HolonomyGraph.lean` (in progress).

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
| `gaugeConn`: `A^g_a = g⁻¹ A_a g + g⁻¹ ∂_a g` for `C¹` `g` with unitary values (`g⁻¹ = gᴴ`) | eq. (4.14), p. 28: `A_α ↦ g_α⁻¹ A_α g_α + g_α⁻¹ d_α g_α` | Same on the chart; `G` unitary, as `SU(2)`. |
| `holonomy_gaugeConn`: `A^g(e) = g(e(t₂))⁻¹ A(e) g(e(t₁))`; `holonomy_gaugeConn_of_endpoints`: unchanged when `g = 1` at the end points | eq. (4.14) with (4.15)-(4.16), p. 28: the holonomies identify `Ā_α = A_α / G⁰_α`, `G⁰_α` the gauge transformations that are the identity at the vertices | Same content (the transformation law of `A(e)` is used, not displayed, in the source; cf. (4.18), p. 29, `(U_1, …) ↦ (g⁻¹ U_1 g, …)` for loops). |
| `holonomy_zero`: the zero connection has holonomy `1` | eq. (4.35) | Supporting result. |
| `transportM`, `exists_transportM`, `transportM_unique`, `transportM_trans`, `transportM_mem_specialUnitaryGroup`: the transport equation `U' = −M(t) U` for a coefficient continuous on the edge | eq. (4.35), p. 33, with `M(t) = A_a(e(t)) ė^a(t)` | Supporting generalisation: `transport` is `transportM` of `A_a(e(t)) ė^a(t)`. |
| `Graph`: finitely many edges, each embedded on `[t₀, t₁)` and on `(t₀, t₁]` (an embedded interval or a circle with a marked point), two edges meeting only at end points | p. 27, footnote 13; p. 28, footnote 15: "For simplicity, in the main body of the paper we will discuss the case where every edge of `α` has two vertices" | Same, with `C¹` edges (the representation line above); loops without a marked point are left out, as in AL's main text. |
| `Graph.Conn`, `Graph.restrict`: a connection on the graph, an `su(2)`-valued 1-form along each edge (its component in the edge parameter) | p. 28: "A `G` connection `A_α` on a graph `α` is the set of `g` valued 1-forms `A_e` defined on each edge `e` of `α`"; "for concreteness" pull-backs of smooth 1-forms on `M`, "not essential in this section" | Representation: the components are continuous on the edge, not necessarily pull-backs of a smooth form on `M`; `restrict` gives the pull-back of a connection of the chart. |
| `Graph.Gauge`, `Graph.Gauge.TrivialAtVertices`, `Graph.actCoeff`: `G_α`, `G⁰_α` and the action (4.14) | p. 28: "A gauge transformation `g_α` in `G_α` is a map `g_α : x_α → G` from all points `x_α` on `α`", eq. (4.14), and `G⁰_α` "all local gauge transformations `g_α` which are identity on the vertices" | Representation: a `C¹` map along each edge, the maps agreeing at common end points (edges meet only there). |
| `Graph.IE`, `Graph.IE_mem`, `Graph.IE_restrict` | eq. (4.16), p. 28: `I_E(Ā_α) = (Ā_α(e_1), …, Ā_α(e_n))` | Same. |
| `Graph.IE_actCoeff`, `Graph.transportM_actCoeff_of_trivial`: `I_E(M^γ)_e = I_V(γ)(t(e))⁻¹ I_E(M)_e I_V(γ)(s(e))`; constant on `G⁰_α`-orbits | eqs. (4.14)-(4.17), p. 28 | Same content. |
| `Graph.IE_injective_mod`, `Graph.IE_surjective`: `I_E` is one-to-one on `A_α / G⁰_α` and onto `SU(2)ⁿ` | p. 28: "natural 1-1 maps between `Ā_α` and `Gⁿ`" (4.16) | Same, for `G = SU(2)`. |
| `Graph.IV`, `Graph.IV_eq_iff`, `Graph.IV_surjective`: `I_V` is one-to-one on `G_α / G⁰_α` and onto `SU(2)^m` | eq. (4.17), p. 28 | Same, for `G = SU(2)`. |
| `su2_exp_form`, `transportM_const_exp`, `exists_su2_coeff`, `transportM_gaugeCoeff` | — | Supporting results: `h = cos θ · 1 + sin θ · K`, the transport of a constant `su(2)` coefficient, gauge covariance along one edge. |

## Trust checks

* `segmentGraph_IE_surjective`: the one-edge graph `t e₀`, `t ∈ [0, 1]`, satisfies the hypotheses of a graph, and every
  element of `SU(2)` is the holonomy of a connection on it.

* `holonomy_pureGauge`: the pure gauge connection `g⁻¹ dg` has holonomy `g(e(t₂))⁻¹ g(e(t₁))`, which depends only on the
  end points.
* `holonomy_u1Conn`: the constant `u(1)` connection `A₀ = i` along `e(t) = t e₀` has holonomy `exp(−iπ) = −1` over
  `[0, π]`.

## Open (the rest of G2-006)

* graphs and the order `α ≤ α′` (p. 27, footnote 13), and the common graph `α₃` of two graphs (p. 35).
