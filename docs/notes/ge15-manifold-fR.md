# GE15: `f(R)` gravity, first variation (source, status, plan)

## Source read (19 November 2026)

T. P. Sotiriou, V. Faraoni, *f(R) theories of gravity*, arXiv:0805.1726, section II.A "Metric formalism",
eqs. (5) to (7), p. 5.

* (5): `S_met = (1/2κ) ∫ d⁴x √−g f(R) + S_M(g_{μν}, ψ)`.
* (6): "Variation with respect to the metric gives, after some manipulations and modulo surface terms,
  `f'(R) R_{μν} − ½ f(R) g_{μν} − [∇_μ ∇_ν − g_{μν} □] f'(R) = κ T_{μν}`".
* (7): `T_{μν} = (−2/√−g) δS_M/δg^{μν}`.

## Status (coordinate metrics on `ℝⁿ`; files in `Lightlike/Spacetime/EHManifold/`)

| Formal statement (Lean) | Source | Match |
| --- | --- | --- |
| `hasDerivAt_scalarCurvature_flux` (`FRVariation.lean`): `d/dt R(g + t h) = −R^{αβ} h_{αβ} + (1/√|g|) ∂_ρ(√|g| W^ρ)` | not stated in the source (a step of "some manipulations") | supporting |
| `hasDerivAt_fRDensity` (`FRVariation.lean`), `fR_variation` (`FRIntegral.lean`): `d/dt ∫_T √|g_t| f(R_t) = ∫_T (−√|g| (f'(R) R^{αβ} − ½ f(R) g^{αβ}) h_{αβ} + f'(R) ∂_ρ(√|g| W^ρ))` | (6), before the integrations by parts | weaker: the terms `−[∇_μ∇_ν − g_{μν}□] f'(R)` appear as `f'(R)` times a divergence |
| `fR_first_variation` (`FRParts.lean`): for `h` supported in `T`, the last term is `−∫_T √|g| W^ρ ∂_ρ(f'(R))` | (6), after one integration by parts | weaker, as above |
| `integral_flux_mul_pd` (`FRSecondParts.lean`), with `Wvec_split` (`WSplit.lean`): `∫_T √|g| W^ρ ∂_ρ φ = ∫_T (√|g| W₀^ρ ∂_ρ φ − ∂_μ(c^{μαβ}) h_{αβ})`, no derivative of `h` on the right | (6), after the second integration by parts, in coordinates | supporting |
| `hess_assemble` (`FRHessianAlg.lean`), `flux_sub_pd_hessCoeff`, `integral_flux_mul_pd_hessian` (`FRHessianForm.lean`): `√|g| W₀^ρ ∂_ρ φ − ∂_μ(c^{μαβ}) h_{αβ} = −√|g| h_{ab} (∇^a∇^b φ − g^{ab} □φ)` pointwise, and its integral over `T` | the bracket `[∇_μ∇_ν − g_{μν}□]` of (6) | supporting |
| **`fR_field_equation_variation`** (`FRHessianForm.lean`): for `f ∈ C¹` with `f' ∈ C²` and `h` supported in the compact set `T`, `d/dt|₀ ∫_T √|g_t| f(R_t) = −∫_T √|g| h_{ab} (f'(R) R^{ab} − ½ f(R) g^{ab} − ∇^a∇^b f'(R) + g^{ab} □f'(R))` | (6), left side | see the differences below |

Tests: `fRDensity_id`, `fR_first_variation_id` (`TestsFR.lean`): for `f(R) = R` the Einstein–Hilbert variation
is recovered.

## Differences between `fR_field_equation_variation` and the source's (6)

* convention: the source varies with respect to `g^{μν}` and writes the tensor with lower indices; here the
  perturbation is `h_{ab} = δg_{ab}` and the tensor has raised indices, with an overall sign `−`.
* convention: no factor `1/2κ` (the source's (5) has it).
* representation: `∇^a∇^b φ` and `□φ` are the coordinate expressions `covHessUp`, `dalembertian`
  (`g^{aα} g^{bβ} (∂_α∂_β φ − Γ^μ_{αβ} ∂_μ φ)` and its trace); "modulo surface terms" is the hypothesis
  that `h` is supported in the compact set `T`.
* the manifold version: see the section "On a manifold" below.
* the matter side: see the next section.

The tensor identity was first checked by hand (19 November 2026) with
`δΓ₀^i_{jk} = −g^{ia} h_{ab} Γ^b_{jk}` (`dChristoffel0_eq`), `∂_ρ g^{σν} = −Γ^σ_{ρα} g^{αν} − Γ^ν_{ρα} g^{σα}`
(regge's `pd_inv_eq`) and `∂_ρ √|g| = √|g| Γ^κ_{κρ}` (regge's `pd_sqrt_abs_det`), then formalised term by term
(`hess_q_contract`, `hess_ds_contract`, `hess_dG1_contract` to `hess_dG4_contract`, `W0_contract`).

Tests (`TestsFRHessian.lean`): `covHessUp_const`, `dalembertian_const`, `fR_field_equation_variation_id`
(for `f(R) = R` the Einstein–Hilbert first variation is recovered).

## Matter (`FRMatter.lean`, 19 November 2026)

| Formal statement (Lean) | Source | Match |
| --- | --- | --- |
| `fRTensorUp g f x a b = f'(R) R^{ab} − ½ f(R) g^{ab} − ∇^a∇^b f'(R) + g^{ab} □f'(R)`; `fR_variation_tensor` | left side of (6) | as above (raised indices) |
| `symm_part_eq_zero_of_forall_integral`: the fundamental lemma for symmetric test tensors on `ℝⁿ` | not in the source | supporting |
| **`fR_matter_stationary_iff`**: for any matter action `S_M` with `d/dt|₀ S_M(g + t h) = ½ ∫_T √|g| h_{ab} T^{ab}` for all smooth symmetric `h` supported in a compact `T`, the total action `(1/2κ) ∫ √|g| f(R) + S_M` is stationary under all such `h` iff `fRTensorUp^{ab} + fRTensorUp^{ba} = κ (T^{ab} + T^{ba})` | (5), (6), (7) | see below |

Differences from the source: convention: (7) is `T_{μν} = (−2/√−g) δS_M/δg^{μν}`, i.e.
`δS_M = −½ ∫ √−g T_{μν} δg^{μν} = +½ ∫ √−g T^{μν} δg_{μν}`, which is the hypothesis on `S_M` with raised
indices. representation: the equation is stated for the symmetric parts (a symmetric `h` only tests the
symmetric part); `T` is assumed continuous, not assumed symmetric. representation: `S_M` is an arbitrary
function of the metric field with the stated first variation; no matter fields. weaker: coordinate patch
`ℝⁿ`, as above.

## On a manifold (19 November 2026)

Files `FRManifoldPiece.lean`, `FRManifoldBall.lean`, `FRPieceLinear.lean`, `FRCover.lean`, `FRCompact.lean`,
`FRStationary.lean`; the route is that of `eh_first_variation_manifold_compact`.

| Formal statement (Lean) | Source | Match |
| --- | --- | --- |
| `fRAction g f K = ∫_K f(R) d vol_g` (scalar curvature of the Levi-Civita connection), `fRAction_chart` | (5) | same, without `1/2κ` |
| `fR_first_variation_manifold`: for `h` supported in a compact set inside a small coordinate ball of one chart, `d/dt|₀ fRAction (g + t h) f K = −∫_{φ(K)} √|g| h_{ab} fRTensorUp^{ab} dy` in the components of that chart | (6) | as in coordinates |
| **`fR_first_variation_manifold_compact`**: for `h` with compact support there are finitely many charts with small balls and a smooth partition of unity `ρ_i` on `K` such that `d/dt|₀ fRAction (g + t h) f K = −∑_i ∫_{φ_i(K ∩ supp ρ_i)} √|g| (ρ_i h)_{ab} fRTensorUp^{ab} dy` | (6) | see below |
| **`fR_matter_stationary_manifold_iff`**: for `S_M` with `d/dt|₀ S_M(g + t h) = ½ ∫ √|g| h_{ab} T^{ab} dy` (chart components) for `h` supported in small coordinate balls: `(1/2κ) fRAction + S_M` is stationary under these `h` iff `fRTensorUp^{ab} + fRTensorUp^{ba} = κ (T^{ab} + T^{ba})` on every small ball of every chart | (5), (6), (7) | see below |
| **`isFRStationary_iff`**: `g` is stationary for all `h` of compact support iff in every chart, on every small coordinate ball, the symmetric part of `fRTensorUp` of the chart components vanishes | (6) with `T = 0` | see below |

Differences from the source: representation: on a manifold the variation and the field equations are written
in charts (with a partition of unity for the variation); an intrinsic tensor field `f'(R) Ric − ½ f g −
∇∇f' + g □f'` on `M` would need the covariance of the Hessian of a scalar under a change of chart, which is
not formalised. representation: the chart components of `g` are continued outside the small ball by the ball
retraction (`coordMetricR`); on the ball they are the components of `g`. representation: with matter on a manifold (`fR_matter_stationary_manifold_iff`, `FRMatterManifold.lean`)
the perturbations are those supported in small coordinate balls, and the energy-momentum tensor is given
chart by chart through the variation of `S_M` under such perturbations; this contains the source's
derivation (stationarity implies the equations). The converse for arbitrary compact support is proved in
the vacuum case (`isFRStationary_iff`). This replaces the earlier line "one chart on `ℝⁿ`, manifold version not
attempted".

## Catalogue entry (draft, for the maintainers)

LL-XXXX: first variation of the metric `f(R)` action on a coordinate patch,
`fR_field_equation_variation` (`Lightlike/Spacetime/EHManifold/FRHessianForm.lean`); source Sotiriou–Faraoni
arXiv:0805.1726 II.A (5)–(6) p. 5; differences as listed above.

Matter (`S_M`, (7)) is not treated for `f(R)`; note that (7) has a factor 2 that Carroll's (4.70) does not,
because (5) has `1/2κ`.
