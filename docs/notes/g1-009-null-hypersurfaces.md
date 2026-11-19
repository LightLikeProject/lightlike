# G1-009, null hypersurfaces: source reading and plan

## Source read (19 November 2026)

E. Gourgoulhon, J. L. Jaramillo, *A 3+1 perspective on null hypersurfaces and isolated horizons*, arXiv:gr-qc/0503113v2,
read in the arXiv PDF:

* Section 2.3, p. 20: the null normal `ℓ` is extended off `H` by a foliation of a neighbourhood by null hypersurfaces
  `H_u`; `ℓ = e^ρ du` (2.14), p. 19, holds on that neighbourhood.
* Section 2.4, p. 21: `dℓ = dρ ∧ ℓ` (2.17), the Frobenius identity.
* Section 2.5, pp. 21–22: `ℓ · dℓ = ⟨dρ, ℓ⟩ ℓ` (2.18), `(ℓ · dℓ)_α = ℓ^μ ∇_μ ℓ_α` (2.19) using
  `ℓ_μ ∇_α ℓ^μ = ½ ∇_α (ℓ_μ ℓ^μ) = 0`, so `∇_ℓ ℓ = κ ℓ` (2.21) with `κ = ∇_ℓ ρ = ⟨dρ, ℓ⟩` (2.22).
* pp. 22–23: `ℓ' = α ℓ` is affinely parametrized iff `∇_ℓ ln α = -κ` ((2.23)–(2.25)); the field lines are null geodesics,
  the null generators of `H`.

## Statement (`Lightlike/Spacetime/NullHypersurfaceCoord.lean`, in coordinates)

`covDMat_gradVec_mulVec`: `ℓᵇ ∇_b ℓᵃ = ½ gᵃᵈ ∂_d (ℓ · ℓ)` for the gradient `ℓ = ∇u` (the step `ℓ_μ ∇_α ℓ^μ = ½ ∇_α(ℓ·ℓ)`
with the symmetric Hessian, which in the source is the Frobenius form (2.17)–(2.19)); `gradVec_geodesic_of_null`: if
`ℓ · ℓ = 0` near a point (the level sets of `u` are null there), `∇_ℓ ℓ = 0`; `covDMat_exp_smul_gradVec_of_null`: for
`ℓ' = e^ρ ℓ`, `∇_{ℓ'} ℓ' = ⟨dρ, ℓ'⟩ ℓ'`, the source's (2.21)–(2.22).

Differences:
* representation: in coordinates for a coordinate metric on an open set, `ℓ = e^ρ ∇u` with the gradient of `u` (the
  source's `ℓ = e^ρ du` with the metric duality).

On a manifold (`Lightlike/Spacetime/NullHypersurface.lean`): `gradField g u = ♯du`, its chart components are `gradVec`
(`hv_gradField`), `g(ℓ, ℓ)` is `gradSq` in a chart (`g_gradField`), `ℓ` is smooth (`contMDiff_gradField`), and
`gradField_geodesic_of_null`: if `g(ℓ, ℓ) = 0` near `p` (the source's null foliation `H_u` near `H`), `∇_ℓ ℓ = 0` at `p`
for the Levi-Civita connection (the source's (2.21) with `ρ = 0`, `κ = 0`).
`smul_gradField_of_null`: for `ℓ' = f ♯du`, `∇_{ℓ'} ℓ' = ⟨df, ♯du⟩ ℓ'` (Leibniz rule of the connection); for `f = e^ρ`
this is `κ = ⟨dρ, ℓ'⟩`, the source's (2.21)–(2.22).

Differences (both forms): representation: the null foliation of a neighbourhood of `H` is the hypothesis
`g(♯du, ♯du) = 0` near the point (the level sets of `u` null there), and `ℓ = f ♯du` for the source's `ℓ = e^ρ du`;
convention: `u`, `g` smooth, a manifold modelled on `ℝⁿ` with a metric of any signature.
