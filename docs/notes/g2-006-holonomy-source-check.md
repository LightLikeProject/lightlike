# G2-006: paths, holonomy and gauge action (source check)

Lean files: `Lightlike/ODE/GlobalLipschitz.lean`, `Lightlike/Canonical/Holonomy.lean`,
`Lightlike/Canonical/HolonomyPaths.lean`, `Lightlike/Canonical/HolonomyGauge.lean`,
`Lightlike/Canonical/HolonomyGraph.lean`, `Lightlike/Canonical/HolonomyALGraph.lean`, `Lightlike/Canonical/HolonomyAnalytic.lean`, `Lightlike/Canonical/HolonomyALOrder.lean`,
`Lightlike/Canonical/HolonomyCommon.lean`.

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
| `Graph`: finitely many edges, each embedded on `[t₀, t₁)` and on `(t₀, t₁]` (an embedded interval or a circle with a marked point), two edges meeting only at end points | p. 27, footnote 13; p. 28, footnote 15: "For simplicity, in the main body of the paper we will discuss the case where every edge of `α` has two vertices" | Tool: the same statement for graphs with `C¹` edges, used for the analytic pieces of the edges of `ALGraph` (next rows). |
| `Graph.Conn`, `Graph.restrict`: a connection on the graph, an `su(2)`-valued 1-form along each edge (its component in the edge parameter) | p. 28: "A `G` connection `A_α` on a graph `α` is the set of `g` valued 1-forms `A_e` defined on each edge `e` of `α`"; "for concreteness" pull-backs of smooth 1-forms on `M`, "not essential in this section" | Tool: the same statement for graphs with `C¹` edges, used for the analytic pieces of the edges of `ALGraph` (next rows). |
| `Graph.Gauge`, `Graph.Gauge.TrivialAtVertices`, `Graph.actCoeff`: `G_α`, `G⁰_α` and the action (4.14) | p. 28: "A gauge transformation `g_α` in `G_α` is a map `g_α : x_α → G` from all points `x_α` on `α`", eq. (4.14), and `G⁰_α` "all local gauge transformations `g_α` which are identity on the vertices" | Tool: the same statement for graphs with `C¹` edges, used for the analytic pieces of the edges of `ALGraph` (next rows). |
| `Graph.IE`, `Graph.IE_mem`, `Graph.IE_restrict` | eq. (4.16), p. 28: `I_E(Ā_α) = (Ā_α(e_1), …, Ā_α(e_n))` | Tool: the same statement for graphs with `C¹` edges, used for the analytic pieces of the edges of `ALGraph` (next rows). |
| `Graph.IE_actCoeff`, `Graph.transportM_actCoeff_of_trivial`: `I_E(M^γ)_e = I_V(γ)(t(e))⁻¹ I_E(M)_e I_V(γ)(s(e))`; constant on `G⁰_α`-orbits | eqs. (4.14)-(4.17), p. 28 | Tool: the same statement for graphs with `C¹` edges, used for the analytic pieces of the edges of `ALGraph` (next rows). |
| `Graph.IE_injective_mod`, `Graph.IE_surjective`: `I_E` is one-to-one on `A_α / G⁰_α` and onto `SU(2)ⁿ` | p. 28: "natural 1-1 maps between `Ā_α` and `Gⁿ`" (4.16) | Tool: the same statement for graphs with `C¹` edges, used for the analytic pieces of the edges of `ALGraph` (next rows). |
| `Graph.IV`, `Graph.IV_eq_iff`, `Graph.IV_surjective`: `I_V` is one-to-one on `G_α / G⁰_α` and onto `SU(2)^m` | eq. (4.17), p. 28 | Tool: the same statement for graphs with `C¹` edges, used for the analytic pieces of the edges of `ALGraph` (next rows). |
| `su2_exp_form`, `transportM_const_exp`, `exists_su2_coeff`, `transportM_gaugeCoeff` | — | Supporting results: `h = cos θ · 1 + sin θ · K`, the transport of a constant `su(2)` coefficient, gauge covariance along one edge. |
| `ALEdge`: a path with a subdivision `τ₀ < ⋯ < τ_k` of `[t₀, t₁]` such that on each `[τ_{j−1}, τ_j]` it agrees with an analytic arc of nonzero velocity | footnote 17, p. 33: "for each edge `e : [tn, t1] → M`, the interval `[tn, t1]` admits a covering by closed intervals `[tn, tn−1], … [t2, t1]` such that the image of each of these closed intervals in `M` is analytic" | Same, reading "embedded" (footnote 13) as an immersion that is a homeomorphism onto its image, so each analytic piece has a nonzero velocity; the arc of a piece is given as a `C¹` map on `ℝ` agreeing with the edge on the piece. |
| `ALGraph`: edges embedded on `[t₀, t₁)` and `(t₀, t₁]`, two edges meeting only at end points | footnote 13, p. 27 (quoted above) | Same. |
| `ALEdge.hol`, `ALGraph.IE`, `ALGraph.IE_restrict`: the holonomy along an edge, the ordered product of the holonomies of its pieces | eqs. (4.36)-(4.37), p. 33 | Same: `A(e₂ ∘ e₁) = A(e₂) A(e₁)` for the pieces. |
| `ALGraph.pieceGraph`: the analytic pieces of all edges form a graph with `C¹` edges | — | Tool (the bridge to the rows above). |
| `ALEdge.comp`, `ALEdge.hol_comp`: the composite `e₂ ∘ e₁` of two closed-piecewise analytic edges, `e₁` ending where `e₂` starts, and `A(e₂ ∘ e₁) = A(e₂) A(e₁)` | eq. (4.37), p. 33 | Same; the composite runs along `e₁`, then along `e₂` translated to start at `t₁(e₁)`, and its pieces are those of `e₁` followed by those of `e₂`. |
| `ALEdge.hol_mem_specialUnitaryGroup`, `ALGraph.IE_mem`: for `su(2)`-valued connections the holonomy along an edge is in `SU(2)`, so `I_E` takes values in `SU(2)ⁿ` | p. 33, after (4.36): "Thus, `A(e) ∈ G`"; eq. (4.16), p. 28 | Same, for `G = SU(2)`. |
| `ALGraph.Conn`, `ALGraph.Gauge`: `A_α` and `G_α` | p. 28: `A_α` "the set of `g` valued 1-forms `A_e` defined on each edge"; `g_α` "a map `g_α : x_α → G` from all points `x_α` on `α`" | Representation (line (3)): the 1-form continuous on each analytic piece, the gauge transformation `C¹` along each piece. |
| `ALGraph.TrivialAtVertices`: `G⁰_α`, the identity at the end points of the edges only | footnote 13, p. 27: "The end points of an edge are called vertices"; p. 28, after (4.15): `G⁰_α` "all local gauge transformations `g_α` which are identity on the vertices of `α`" | Same: the corners `τ_j`, `0 < j < k`, are interior points of an edge, not vertices. |
| `ALGraph.IE_actCoeff`, `ALGraph.IE_actCoeff_of_trivial`: `I_E(M^γ)_e = γ(t(e))⁻¹ I_E(M)_e γ(s(e))`; constant on `G⁰_α`-orbits | eqs. (4.14)-(4.17), p. 28 | Same (the values at the corners cancel). |
| `ALGraph.IE_injective_mod`, `ALGraph.IE_surjective`: `I_E` one-to-one on `A_α / G⁰_α` and onto `SU(2)ⁿ` | p. 28: "natural 1-1 maps between `Ā_α` and `Gⁿ`" (4.16) | Same, for `G = SU(2)`. |
| `ALGraph.IV`, `ALGraph.IV_eq_iff`, `ALGraph.IV_surjective`: `I_V` one-to-one on `G_α / G⁰_α` and onto `SU(2)^m` | eq. (4.17), p. 28 | Same, for `G = SU(2)`. |
| `Edge.IsAnalytic`: an edge analytic at every parameter, with nonzero velocity (the arcs of `ALEdge`) | footnote 17, p. 33, and footnote 13, p. 27 (quoted above) | As for `ALEdge`. |
| `eventually_eq_comp_of_tendsto`: two analytic arcs meeting at points accumulating at `(s₀, t₀)`, `f'(t₀) ≠ 0`, satisfy `e = f ∘ φ` near `s₀`, `φ` analytic | — | Tool for the common graph (the identity theorem after the analytic local inverse of a coordinate of `f`). |
| `Edge.meetFrontier_finite`: two regular analytic arcs meet in finitely many pieces | p. 35: "we can introduce a third graph `α3` which contains all the edges and vertices of `α1` and `α2`" | Tool: the step behind the common graph, for the analytic arcs of the edges. |
| `IsRightTransport`, `IsRightTransport.unique`, `ALEdge.exists_isRightTransport`: the transport along an edge, by right derivatives, unique, ending at the holonomy | eqs. (4.35)-(4.36), p. 33 | Same; along a closed-piecewise analytic edge the velocity has one-sided limits at the corners. |
| `ALEdge.hol_eq_of_eqOn`: the holonomy along an edge does not depend on its subdivision | p. 33, before (4.39): "(This can be achieved simply by introducing suitable new vertices on `e`.)" | Supporting result. |
| `ALEdge.isRightTransport_comp`, `ALEdge.rightDeriv_of_comp`: invariance under orientation-preserving reparametrisation | p. 33, after (4.36): `A(e)` "is unchanged under orientation-preserving re-parameterizations of `e`" | Same, for continuous monotone reparametrisations between edges (their right derivatives exist automatically). |
| `ALEdge.rev`, `ALEdge.hol_rev`: `A(e⁻¹) = A(e)⁻¹` | eq. (4.37), p. 33: "`e⁻¹` is obtained from `e` by simply reversing the orientation" | Same. |
| `ALGraph.Le`, `ALGraph.le_refl`: `α ≤ α'` | p. 27: "A graph `α′` will be said to be larger than another graph `α` (or contain `α`), `α ≥ α′`, if every edge `e` of `α` can be written as `e = e′₁ ∘ … ∘ e′_k` for some edges `e′₁, …, e′_k` of `α′`"; p. 28: "Let us choose an arbitrary but fixed orientation of each edge of `α`" | Representation: `e = e′₁ ∘ ⋯ ∘ e′_K` read as a subdivision of the parameter interval of `e` into parts on which `e = e′_l ∘ φ_l`, `φ_l` continuous and monotone onto the parameter interval of `e′_l`, with `e′_l` in either orientation. |
| `ALGraph.hol_of_le`: for `α ≤ α'` the holonomy along each edge of `α` is the ordered product of holonomies along edges of `α′` or their inverses | p. 35: functions cylindrical with respect to `α` are cylindrical with respect to every larger graph | Same content, at the level of holonomies. |
| `ALGraph.directed`, `ALGraph.common`, `ALGraph.le_common_left`, `ALGraph.le_common_right`: a graph `α₃` with `α₁ ≤ α₃` and `α₂ ≤ α₃` | p. 35: "we can introduce a third graph `α3` which contains all the edges and vertices of `α1` and `α2`"; p. 27: "larger than another graph `α` (or contain `α`)" | Same, in the order `ALGraph.Le` (the representation line above). |
| `ALGraph.vertices_subset_of_le`: for `α ≤ α′` the vertices of `α` are vertices of `α′` | p. 35 (quoted above): "contains all the edges and vertices" | Same. |
| `ALGraph.exists_common_hol`: the holonomies along the edges of `α₁` and of `α₂` are ordered products of holonomies along edges of `α₃` or their inverses | p. 35: "regard the two functions as cylindrical with respect to `α3`" | Same content, at the level of holonomies. |
| `ALGraph.cutPoints`, `ALGraph.CutData.segment_in_piece`, `ALGraph.CutData.injOn_segment`, `ALGraph.seg_share`, `ALGraph.seg_classify`, `image_Ioo_subset`, `exists_reparam` | — | Tool for `α₃`: the edges are cut at finitely many points (end points and midpoints of the pieces, boundary points of the meeting sets, `Edge.meetFrontier_finite`); each segment of `α₂` meets `α₁` only at its end points or has the open part of a segment of `α₁` (`Edge.meet_dichotomy`), and two such segments differ by a continuous monotone or antitone reparametrisation. |

## Trust checks

* `lineGraph_incomparable`: the straight one-edge graphs on `[0, 2] e₀` and `[1, 3] e₀` overlap on `[1, 2] e₀`; neither
  is below the other (each has a vertex the other lacks, `ALGraph.vertices_subset_of_le`), and `ALGraph.directed` gives
  them a common refinement.

* `lGraph_IE_surjective`: the one-edge graph on the `L`-shaped edge (two analytic pieces, a corner at `e₀`) satisfies the
  hypotheses of a graph of Ashtekar–Lewandowski, and every element of `SU(2)` is the holonomy of a connection along it.

* `segmentGraph_IE_surjective`: the one-edge graph `t e₀`, `t ∈ [0, 1]`, satisfies the hypotheses of a graph, and every
  element of `SU(2)` is the holonomy of a connection on it.

* `holonomy_pureGauge`: the pure gauge connection `g⁻¹ dg` has holonomy `g(e(t₂))⁻¹ g(e(t₁))`, which depends only on the
  end points.
* `holonomy_u1Conn`: the constant `u(1)` connection `A₀ = i` along `e(t) = t e₀` has holonomy `exp(−iπ) = −1` over
  `[0, π]`.

## Open (the rest of G2-006)

* None.
