# The exponential map (gap row G1-006): source read, and how the library compares

Files: `Lightlike/Geodesic/` (`ExpSmooth`, `ExpDiffeo`, `Radial`, `GaussAux`, `Gauss`,
`ExpJoint`, `TwoPoint`, `Convex`, `Variation`, `GaussMaximal`, `Tests`), `Lightlike/ODE/FlowAlong.lean`,
`Lightlike/ODE/FlowVariational.lean`, and
`Lightlike/ODE/FlowBoxSmooth.lean` for the regularity of the geodesic flow.

## Source (read at the locations given)

M. Kunzinger and R. Steinbauer, *Riemannian Geometry*, lecture notes, University of Vienna, Fall
term 2020, version of 11 December 2025 (PDF on R. Steinbauer's teaching page). The notes treat
semi-Riemannian manifolds ("SRMF") and follow O'Neill, *Semi-Riemannian Geometry*; O'Neill's book
itself, which the gap row names, was not opened.
- 2.1.13 Definition, page 37: `exp_p : D_p → M`, `exp_p(v) = c_v(1)`, with `D_p` the set of `v`
  whose geodesic `c_v` is defined at least on `[0, 1]`.
- 2.1.14 Theorem, pages 38–39: "Let `p` be a point in a SRMF `M`. Then there exist neighbourhoods
  `Ũ` of `0` in `T_pM` and `U` of `p` in `M` such that the exponential map `exp_p : Ũ → U` is a
  diffeomorphism." Proof: smoothness near `0` from the smoothness of `(w, s) ↦ c_w(s)` and the
  rescaling `c_{tv}(s) = c_v(ts)` (2.1.12); `T_0 exp_p = id` (2.1.14); inverse function theorem.
- Page 39: `U` is a normal neighbourhood of `p` if `Ũ` is star shaped.
- 2.1.15 Proposition (radial geodesics), page 39: "Let `U` be a normal neighbourhood of `p`.
  Then for each `q ∈ U` there exists a unique geodesic `σ : [0, 1] → U` from `p` to `q` ...
  Moreover we have `σ'(0) = exp_p⁻¹(q) ∈ Ũ`."
- 2.1.21 Theorem (Gauss lemma), page 43: "Let `M` be a SRMF and let `p ∈ M`,
  `0 ≠ x ∈ D_p ⊆ T_pM`. Then for any `v_x, w_x ∈ T_x(T_pM)` with `v_x` radial we have
  `⟨(T_x exp_p)(v_x), (T_x exp_p)(w_x)⟩ = ⟨v_x, w_x⟩`" (2.1.24).
- 2.2.4 Definition, page 47: an open `C` is convex if it is a normal neighbourhood of all of its
  points. 2.2.6 Theorem (properties of `E`), pages 47–49. 2.2.7 Theorem, page 49: "Every point
  `p` in a SRMF `M` possesses a basis of neighbourhoods consisting of convex sets."

## What the library proves

- `Lightlike.ODE.IsFlowBox.contDiffOn_uncurry`, `contDiffOn_uncurry_infty`: every flow box of a
  `C^{k+1}` (smooth) field has a `C^{k+1}` (smooth) flow on its whole domain. This is the
  smoothness of the geodesic flow used in the proof of 2.1.14.
- `Lightlike.Geodesic.exists_expMap_smooth`: for a coordinate metric `g` on an open `U ⊆ ℝⁿ`
  (`IsCoordMetric`, any signature) and `x ∈ U`, a smooth map `E` on a ball about `0` with
  `E 0 = x`, derivative the identity at `0`, and `E v` the endpoint at time `1` of a geodesic from
  `x` with initial velocity `v`.
- `Lightlike.Geodesic.exists_expMap_diffeo`: Theorem 2.1.14, with `Ũ` a ball (star shaped, so
  the image is a normal neighbourhood): an open partial homeomorphism with source the ball,
  smooth with smooth inverse, equal to the exponential map there.
- `Lightlike.Geodesic.exists_normal_neighbourhood` (file `Radial`): Proposition 2.1.15. In the
  normal neighbourhood `φ(B(0, ρ))`, `t ↦ φ(t v)` is a geodesic from `x` to `φ(v)` with initial
  velocity `v` (this is (2.1.13), `exp_p(tv) = c_v(t)`), and every geodesic `τ` on `[0, 1]` from
  `x` inside the neighbourhood is `t ↦ φ(t τ'(0))`, with `τ'(0) = φ⁻¹(τ(1))`. It rests on
  `IsGeodesicOn.eqOn_Icc`: geodesics in `U` with the same initial data agree on intervals.
- `Lightlike.Geodesic.IsNormalChart.gauss`, `exists_normal_chart_gauss` (file `Gauss`): the Gauss
  lemma, Theorem 2.1.21: for `v` in the ball of a normal chart `φ` at `x` and every `w`,
  `g(φ v)(Dφ(v) v, Dφ(v) w) = g(x)(v, w)`. `IsNormalChart` bundles the conclusions of 2.1.14.
  Proof as in the source, with the two-parameter map `F(t, s) = φ(t(u + s w))`; the covariant
  calculus is replaced by the lowered geodesic equation (`lowered_accel_add`), the symmetry of
  the second derivative of `φ`, and the constant speed of geodesics.
- `Lightlike.Geodesic.exists_expMap_joint` (file `ExpJoint`) and `exists_twoPoint_diffeo` (file
  `TwoPoint`): `(p, v) ↦ exp_p(v)` is smooth near `(x, 0)`, and `(p, v) ↦ (p, exp_p v)` is a
  diffeomorphism from a neighbourhood of `(x, 0)` onto a neighbourhood of `(x, x)`. This is the
  first step of the proof of Theorem 2.2.6; the theorem itself (a diffeomorphism from a
  neighbourhood of the whole zero section onto a neighbourhood of the diagonal) is not stated.
- `Lightlike.Geodesic.exists_convex_neighbourhood` (file `Convex`): Theorem 2.2.7. Inside every
  ball about `x` there is an open `C ∋ x`, `C ⊆ U`, such that for every `q ∈ C` the exponential
  map at `q` is a diffeomorphism from a star-shaped open set containing `0` onto `C` (`C` is a
  normal neighbourhood of each of its points, Definition 2.2.4). The proof is the source's, with
  the squared distance `∑ (q_i − x_i)²` taken in the given coordinates instead of normal
  coordinates: its second derivative along a geodesic is `2∑ w_i² − 2∑ (q_i − x_i) Γ^i(w, w) ≥ 0`
  near `x` (`IsGeodesicOn.convexOn_sqDist`), so the form (2.2.9) is replaced by the bound on the
  Christoffel symbols, and the maximum argument by convexity on `[0, 1]`.
- `Lightlike.ODE.exists_flow_along` (file `ODE/FlowAlong`): for a smooth field on an open set and
  an integral curve `c` on `[0, T]`, solutions starting near `c(0)` exist on an open interval
  containing `[0, T]` and depend smoothly on time and initial point. For the geodesic field this
  is Proposition 2.2.3 (the domain of `exp` is open) together with the smoothness of `exp` on it.
  `Lightlike.ODE.hasDerivAt_fderiv_flow_of_contDiffOn` (file `ODE/FlowVariational`) is the
  variational equation for such a flow.
- `Lightlike.Geodesic.hasDerivAt_pairing_variation` (file `Variation`): the first variation
  identity `d/dt g(∂_t F, ∂_s F) = ½ ∂_s g(∂_t F, ∂_t F)` for a family of geodesics.
- `Lightlike.Geodesic.exists_expMap_along_gauss` (file `GaussMaximal`): the Gauss lemma at any
  vector of the domain of `exp` (Theorem 2.1.21 as stated, `x ∈ D_p`), not only in a normal
  neighbourhood.
- `Lightlike.Geodesic.expDomain`, `expMap` (file `ExpMap`): the exponential map on its maximal
  domain in the chart, `exp(p, v) = c_v(1)` for the geodesic from `p` with velocity `v` that
  exists on an open set containing `[0, 1]` and stays in `U` on `[0, 1]` (Definition 2.1.13,
  (2.2.5)–(2.2.6)). `isOpen_expDomain`, `smul_mem_expDomain` (Proposition 2.2.3: the domain is
  open and star shaped), `expMap_smul` ((2.1.13)), `contDiffOn_expMap`, `gauss_expMap` (Theorem
  2.1.21 on the whole domain). Known value: for the flat metric `exp_p v = p + v`.
- `Lightlike.Geodesic.Tests.exists_expMap_diffeo_ads`: the hypotheses hold for anti-de Sitter
  space in the Poincaré patch (Lorentzian signature).

## Differences from the source (none accepted)

- representation: a coordinate metric on an open subset of `ℝⁿ` (the library's `IsCoordMetric`),
  not a semi-Riemannian manifold; tangent spaces are `ℝⁿ`.
- representation: the exponential map is not defined as a function on the maximal domain `D_p`;
  the theorem gives a map on a ball with the defining property `E v = c_v(1)` (a geodesic from
  `x` with initial velocity `v`, defined on `(-1, 2)`, reaching `E v` at time `1`). Geodesics with
  given initial data are unique (`IsGeodesicOn.eventuallyEq`), so this determines `E`.

- representation (Gauss lemma on the domain of `exp`): `exists_expMap_along_gauss` takes a
  geodesic `γ` defined on an open set containing `[0, 1]` with values in `U` on `[0, 1]` (so
  `v = γ'(0)` is in the source's `D_p`, with the geodesic inside the chart), gives a smooth `E`
  near `v` with `E(u)` the endpoint of the geodesic with velocity `u`, and proves the Gauss lemma
  at `v`. The source states it for a map `exp_p` on `D_p`; the library has no such global map.

## Still open in the row

Local causality (the reading of "causally convex neighbourhoods" fixed by the integrator:
Chruściel, *Elements of causality theory*, Propositions 2.4.5 and 2.4.7); Theorem 2.2.6 in its
global form.
