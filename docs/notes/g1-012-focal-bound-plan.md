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
3. **Gram route (no parallel frames).** For Jacobi fields `J_i` with covariant derivatives `P_i` along a null
   geodesic (`IsJacobiOn`, GE3Row/Jacobi.lean, which a variation of geodesics produces by
   `exists_isJacobiOn_of_variation`), set `Q = g(J_i, J_j)`, `C = g(P_i, J_j)`, `ρ = g(R(J_i, w)w, J_j)`.
   `jacobi_gram_derivs` (JacobiGeom.lean): `Q' = C + Cᵀ`, `C' = -ρ + g(P_i, P_j)`; `gramP_eq`: for `J_i`, `P_i`
   orthogonal to the null `w` in dimension `m + 2`, `g(P_i, P_j) = C Q⁻¹ Cᵀ` (the span of `J_i` and `w` is
   `w^⊥`, `exists_decomp_perp_null`); `gramC_symm`: `C` stays symmetric along the geodesic; `ρ` is symmetric
   (`gpair_riemannApply_symm`, pair symmetry of Riemann); `trace_gram_rho`: `tr (Q⁻¹ ρ) = Ric(w, w)`
   (a null frame `J`, `w`, `N` and `NullFrame.trace_eq`). `hasDerivAt_gram_expansion` and `gram_focusing`
   (JacobiRiccati.lean): `θ = tr (Q⁻¹ Cᵀ)` has `θ' = -tr (Q⁻¹ ρ) - tr B²` and `focusing` gives
   `T ≤ m / |θ(0)|`. `jacobi_focusing_chart` (JacobiRic.lean) combines these.
4. **Chart-level identity.** JacobiIdentity.lean and JacobiCompat.lean: with Christoffel symbols `Γ` and `∂Γ`
   symmetric in the lower indices, `D²J = (J'' + 2Γ(v, J') + ∂_dΓ J^d v v) - R^a_{σγδ} v^σ J^γ v^δ`, and
   `(g(W₁, W₂))' = g(D W₁, W₂) + g(W₁, D W₂)` along a curve.
5. **Initial value.** `θ(0) = frameExpansion` for an orthonormal frame of `T_s S`, with a uniform bound on compact
   `S` from the trapped hypothesis applied to `k₁, k₂`.
6. **Focal point.** A focal point `t₀` of a generator, with `det Q(t₀) = 0`, puts `γ(L)` in `I⁺(S)` for `L > t₀`
   (second variation of the null generator; the first variation is `null_geodesic_orthogonal`).
