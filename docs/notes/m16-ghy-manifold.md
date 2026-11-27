# M16: the Gibbons–Hawking–York cancellation on a manifold (plan and attempt record)

## Source read (19 November 2026)

E. Dyer, K. Hinterbichler, *Boundary Terms, Variational Principles and Higher Derivative Modified Gravity*,
arXiv:0809.4033, section 4, p. 20: (4.1) `16πG S = ∫_V dⁿx √-g R + 2 ∮_{∂V} dⁿ⁻¹x √|h| K`; (4.2) its variation, with the
boundary term `-∮ √|h| h^{αβ} n^μ ∂_μ δg_{αβ}` from the Einstein–Hilbert part when `δg = 0` on `∂V`; (4.3)
`δK = ½ h^{αβ} n^μ ∂_μ δg_{αβ}`; (4.4) only the bulk term `∫ √-g (R_{μν} - ½ R g_{μν}) δg^{μν}` remains.

## Starting point

* an earlier branch (queued): `eh_ghy_variation_regular`, the cancellation for a region of `ℝⁿ⁺¹` with regular,
  nowhere null boundary, the metric and the perturbation defined and smooth on all of `ℝⁿ⁺¹` with `det g ≠ 0`
  everywhere; the boundary term in graph charts with a partition of unity. Its weaker line: one coordinate patch, not a
  region of a manifold.
* `regge/ge15-divergence-manifold` (3c396c4): the divergence theorem on a manifold, flux in charts with a partition of
  unity subordinate to charts and graph charts of the boundary in each chart.
* the earlier bulk variation on a manifold for a compactly supported perturbation (`CompactVariation.lean`), with small
  coordinate balls and a retraction (`Retraction.lean`) to apply the `ℝⁿ` statements.

## Plan

1. The boundary vector of the variation intrinsically: `V(h) = div_g(h♯) - grad_g(tr_g h)` (Levi-Civita of `g`), a smooth
   vector field supported in the support of `h`; its components in a chart are the coordinate Palatini vector.
2. The bulk variation on `D`: `d/dt ∫_{D ∩ T} (R(g_t) - 2Λ) dvol_{g_t} = ∫_{D ∩ T} (-⟨E, h⟩ + div_g V(h)) dvol_g`, by the
   pointwise coordinate identity in each chart (partition of unity in the integrand, not in `h`).
3. `∫_D div_g V(h) = flux of V(h)` (the divergence theorem on a manifold).
4. In each chart the derivative of the GHY density in graph charts is minus the flux density of `√|g| V(h)` where `h = 0`
   on the boundary (the pointwise identity behind the earlier `eh_ghy_variation_graph`), with the same partition.
5. Sum: the boundary terms cancel, `d/dt (S_EH + S_GHY) = -∫_D ⟨E, h⟩ dvol_g`.

Why the intrinsic `V` in step 1: with the partition `ψ_a` in the integrand, integrating `ψ_a ∂_j(√|g| V_a^j)` by parts chart
by chart leaves `-Σ_a ∫ (∂_j ψ_a) √|g| V_a^j`, which vanishes only after the sum, and only if the chart vectors `V_a` are the
components of one vector field (`Σ_a dψ_a = 0` on the support of `h`).

## Attempts

* Step 1, part 1 done: `dChristoffel_eq_cov` (`DeltaChristoffel.lean`), `δΓⁱ_{jk} = ½ gⁱˡ (∇ⱼ h_{lk} + ∇ₖ h_{lj} - ∇ₗ h_{jk})`
  in coordinates (`covH`), for `g` symmetric everywhere and `h` symmetric at the point. Next: the intrinsic `V(h)` on `M`
  and the identification of its chart components with `Wvec`.
* Step 1, part 2 done: `Wvec_eq_cov`,
  `W^ρ = g^{ρl} g^{σν} (∇_σ h_{lν} - ∇_l h_{σν})` (`div h♯ - grad tr_g h`), from `dChristoffel_eq_cov`: in
  `g^{σν} δΓ^ρ_{σν}` the first two terms agree (swap `σ ↔ ν`, `g⁻¹` symmetric); in `δΓ^κ_{κσ}` the first and third terms
  cancel (swap `κ ↔ l`), leaving `½ g^{κl} ∇_σ h_{lκ}`; the two trace terms combine by `∇_l h_{σν} = ∇_l h_{νσ}`, which needs
  `h` symmetric everywhere (for `∂h`), not only at the point. Then the intrinsic `V(h)` is
  `(u ↦ tr_g[(v, w) ↦ (∇_v h)(u, w)] - tr_g[(v, w) ↦ (∇_u h)(v, w)])♯` with main's `covDerivBilinAt`, `sharp` and the
  chart components of `covDerivBilinAt` (`ChartTensor.lean`).
* Step 1, part 3 done (`PerturbationCovDeriv.lean`): main's intrinsic `covDerivBilinAt` of `h` has the components `covH` in
  every chart (`covDerivBilinAt_coordField`, `covDerivBilinAt_eq_sum`), and `palatiniField` (the vector with components `W`
  in the chart at each point) has components `W` in every chart (`hv_palatiniField`). The route through charts and the
  Jacobian replaced an intrinsic `♯` of a 1-form, which would have needed the 1-form as a continuous linear map.
* Step 1 done: `palatiniField` is smooth (`contMDiff_palatiniField`, from `contDiffOn_pvec`: the components are smooth on
  each chart target, with main's local `contDiffOn_inv_entry`, `contDiffOn_pd`, `contDiffOn_christoffel` in place of
  PalatiniCoord's global ones) and vanishes outside a compact set outside which `h` vanishes
  (`palatiniField_eq_zero_of_notMem`): the hypotheses `hX`, `hXK` of `divergence_theorem_manifold`.
* Step 2 plan (bulk variation on a region): cut `D ∩ K` into disjoint measurable pieces `A_k ∩ D`, each in a compact set
  of a small chart ball (the cover of the earlier `eh_first_variation_manifold_compact`, intersected with `D`); over a piece
  the earlier `hasDerivAt_ehAction_piece` gives the chart integral `pieceVar` of `-√|g| ⟨E, h⟩ + ∂ⱼ(√|g| Wʲ)` for the metric
  retracted to the ball. On the inner ball the retracted metric agrees with the chart metric near every point, so by the
  germ lemmas (`Locality.lean`, extended to `dChristoffel` and `Wvec`) `pieceVar` is the same integral for the chart
  metric; `ehIntegrand_chart` and `setIntegral_volumeMeasure_chart` turn the first term into `-∫_A ⟨E, h⟩ dV_g`, and
  `sqrt_det_mul_expansion` with `hv_palatiniField` turns the second into `∫_A div_g V(h) dV_g`. Summing over the pieces:
  `d/dt ehAction (g + t h) Λ (D ∩ K) = -∫_{D ∩ K} ⟨E, h⟩ dV_g + ∫_D div_g V(h) dV_g`. No chart-by-chart integration by
  parts is needed: the pieces are disjoint and the divergence is that of one vector field.
* Step 2 done (`RegionVariation.lean`): `eh_variation_region_manifold`, as planned, with `pieceVar_eq_chart` (germ
  lemmas) and `pieceVar_intrinsic`. Next, step 3: apply `divergence_theorem_manifold` to `V(h)` (its hypotheses are
  `contMDiff_palatiniField` and `palatiniField_eq_zero_of_notMem`), giving `∫_D div_g V(h) = -Σ σ_ab graphFlux(...)`; then
  step 4, the GHY term in the same graph charts and the pointwise identity of its derivative with the flux density.
* Step 3a done (`GHYLocal.lean`): `ghyGraph_add_smul_loc`, the affine dependence of the GHY density on `t` for a metric
  and perturbation smooth only on an open set containing the graph point (retract to a ball around that point and
  compare germs). Next, 3b: the atlas of the divergence theorem must also carry, on each graph chart with `σ ≠ 0`,
  "`h` vanishes on the graph" and "the graph is not null"; the faithful hypothesis on `M` is a defining function `u` of
  `∂D` with `g⁻¹(du, du) ≠ 0` and `h = 0` on `{u = 0}`, and on a graph chart from `u`, differentiating `u(graphPt y) = 0`
  gives `du = (∂ᵢu) ν` for the graph conormal `ν`, so the graph is not null where `du` is not.
* Step 3b, design (no atlas with a predicate needed): the GHY term is taken in the graph charts of
  `divergence_theorem_manifold` applied to `V(h)`, each chart integral over the compact set
  `removeNth '' φ_a(K ∩ tsupport ψ_a)` (as `eh_ghy_variation_regular` integrates over the projection of `T`). Where the
  weight `ρ_ab ψ_a` of a graph point is not zero, the point lies in the open support of `ρ_ab`, where `φ_a(D)` is the graph
  region; so the graph near it is the chart image of `∂D`, `h = 0` there (hypothesis `h = 0` on `∂D`), and for the
  defining function `u` of `∂D` at the point, `u ∘ φ⁻¹` vanishes on the graph near it, so `d(u ∘ φ⁻¹) = ∂ᵢ(u ∘ φ⁻¹) ν` and
  the graph is not null where `du(♯du) ≠ 0` (hypothesis: `∂D` nowhere null). Where the weight is zero, the term is `0`
  for every `t`. So each chart integrand is exactly affine in `t`, with slope minus the flux integrand of
  `divergence_theorem_manifold` (`ghyGraph_add_smul_loc`), and the boundary terms cancel.
  Pieces, all done in `GHYBoundary.lean` except the assembly: `pd_of_eventually_vanishing_on_graph_at`,
  `conormal_nonnull_of_defining`, `graphPt_mem_frontier`, `mem_frontier_congr`, `symm_mem_frontier_of_mem_frontier_image`,
  `eq_zero_of_mem_frontier`, `mvfderiv_sharp_chart`. Next: the assembly (step 4).

* Step 4 done (`GHYManifold.lean`): `eh_ghy_variation_manifold`, standard axioms. One change on the way: the divergence
  theorem's graph-chart region description was only given on `tsupport ρ_ab`; at graph points on the edge of that support
  the boundary need not be the graph, the graph could be null there, and the weighted GHY density need not be continuous.
  `exists_graph_atlas_integral_divergence_loc_open`, `exists_chart_flux_open` and `divergence_theorem_manifold_open`
  expose the open sets `U_ab ⊇ tsupport ρ_ab` (from the atlas construction) on which the description holds; the old
  statements are their projections. A smooth cut-off `χ = 1` on `K` makes the chart weights `w_a = χ ψ_a` compactly
  supported; `ψ_a V(h) = w_a V(h)` since `V(h)` vanishes off `K`.

## Differences from the source (Dyer–Hinterbichler (4.1)–(4.4), p. 20)

* representation: the Gibbons–Hawking–York term `2 ∮ √|h| K` is written in graph charts of the boundary with a partition
  of unity (charts at `c a` with weights `w a`, graph charts with cut-offs `ρ a b`, signs `σ a b`), as
  `eh_ghy_variation_regular` does in `ℝⁿ⁺¹`; its density `ghyGraph` is from the earlier branch.
* representation: the action is that of `D ∩ K` for `h` vanishing outside the compact `K` (the action of `D \ K` does not
  depend on `t`), so `D` need not be compact; the variation is `δg = h` along `g + t h`, `δg = 0` on `∂D` as in the source.
* convention: the boundary is given by `C²` defining functions with `du ≠ 0` and `du(♯du) ≠ 0` (nowhere null), the
  source's tacit assumption for `K` to be defined; metric and perturbation are smooth.
