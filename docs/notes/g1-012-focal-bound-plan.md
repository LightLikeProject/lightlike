# G1-012: the focal bound for a closed trapped spacelike surface

The one hypothesis of `penrose_of_focal_bound` (Rows/G1_012/PenroseFocal.lean) is
`NormalisedFocalBound T S Λ` (Rows/G1_012/ExpCompact.lean): every future null geodesic `γ` from `s ∈ S` to a
point outside `I⁺(S)` has normalised affine length `-g(γ'(0), X)·L ≤ Λ`. This note records the route to it.

## Statement-level facts

* `IsClosedTrappedSurface` (TrappedSurface.lean) only constrains `g`-orthonormal `(n-2)`-frames of
  `T_x S = ker df_x`, so it is vacuous at points where `T_x S` is not spacelike. The proof needs spacelike
  `S`, so `IsClosedTrappedSpacelikeSurface` (TrappedSpacelike.lean) adds the clause `g(v,v) > 0` on `ker df_x`
  and the old definition stays as it is.
* The hypothesis of the trapped definition is stated for smooth global fields `k` that are future null normals
  along `S`. `exists_null_normal_pair` (TrappedNormals.lean) constructs two such fields from `f`: with
  `Nᵢ = ∇fⁱ`, Gram matrix `G`, `D = -det G > 0` and `Q > 0` (from spacelikeness), the fields
  `k_± = √D·τ' ± Rτ'` in the basis `N₁, N₂` (`kα`, `kβ`), smooth on `{D > 0}`, cut off by a smooth bump. Every
  future null normal at a point of `S` is a positive multiple of one of them.

## The route

1. **Normal null congruence.** The map `F(σ, t) = exp_σ(t k(σ))` is smooth (`sflowGerm_along`, FlowSmooth.lean).
2. **Jacobi matrix focusing.** `jacobi_focusing` (JacobiMatrix.lean): `Y'' = -R Y`, symmetric Wronskian,
   `tr R ≥ 0`, `Y` invertible on `[0, T)`, `θ(0) = tr (Y' Y⁻¹)(0) < 0` give `T ≤ m / |θ(0)|`.
   `trace_sq_ge_of_gram` (JacobiGram.lean): for `Q` positive definite and `Q B` symmetric,
   `(tr B)²/m ≤ tr B²`.
3. **Gram route (no parallel frames).** With `J_i = ∂_{σ_i} F`, `Q_ij = g(J_i, J_j)` (unchanged by adding
   multiples of the null `γ'`), `K_i = D_t J_i`: `D_t J_i = D_{σ_i} γ'`, `D_t γ' = 0`, `g(J_i, γ') = g(K_i, γ') = 0`;
   `K_i = Σ_j B_{ji} J_j + c_i γ'` when `Q` is nondegenerate; `Q' = BᵀQ + Q B`; Jacobi `D_t K_i = -R(J_i, γ')γ'`; pair
   symmetry of Riemann gives `Q B` symmetric; `B' + B² = -R̂` with `tr R̂ = Ric(γ', γ')`; so `θ = tr B` satisfies
   `θ' ≤ -θ²/m` and `focusing` applies.
4. **Chart-level identities.** JacobiIdentity.lean: with Christoffel symbols `Γ` and `∂Γ` symmetric in the
   lower indices, `D²J = (J'' + 2Γ(v, J') + ∂_dΓ J^d v v) - R^a_{σγδ} v^σ J^γ v^δ`.
5. **Initial value.** `θ(0) = frameExpansion` for an orthonormal frame of `T_s S`, with a uniform bound on compact
   `S` from the trapped hypothesis applied to `k₁, k₂`.
6. **Focal point.** A focal point `t₀` of a generator, with `det Q(t₀) = 0`, puts `γ(L)` in `I⁺(S)` for `L > t₀`
   (second variation of the null generator; the first variation is `null_geodesic_orthogonal`).
