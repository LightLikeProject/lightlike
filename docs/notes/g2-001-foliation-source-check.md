# G2-001: the ADM data of a foliation, chart-free (source check)

Lean files: `Lightlike/Canonical/Foliation.lean`, `Lightlike/Canonical/TestsFoliation.lean`.

## Source read

E. Gourgoulhon, *3+1 Formalism and Bases of Numerical Relativity*, arXiv:gr-qc/0703035 (lecture notes, 2007), read at
the locations below in the arXiv PDF (printed page numbers, equal to the PDF pages).

## Statements and the locations they rest on

| Lean | Source, location | Match |
|---|---|---|
| `IsTimeFunction g τ`: `τ` smooth with a timelike gradient | Sec. 3.2.2, eqs. (3.1)–(3.3), p. 40: a smooth regular scalar field whose level surfaces are spacelike and cover `M` | Same data; "regular" and "spacelike leaves" are both implied by a timelike gradient, and the leaves `{τ = t}` cover `M` for any function. |
| `timeGrad`, `lapse`: `N = (−g(∇τ, ∇τ))^{−1/2}` | eq. (3.5), p. 41 | Same. |
| `unitNormal`: `n = −N ∇τ`; `g_unitNormal_self`: `n · n = −1` | eq. (3.4), p. 41, and the sentence after (3.5) | Same. |
| `lapse_pos`: `N > 0` | eq. (3.6), p. 41 | Same. |
| `g_unitNormal`: `n♭ = −N dτ` | eq. (3.7), p. 41 | Same. |
| `normalEvolution`: `m = N n`; `dTime_normalEvolution`: `dτ(m) = 1` | eqs. (3.8) and (3.10), Sec. 3.3.2, p. 42 | Same: `⟨dt, m⟩ = 1`. |
| `shift`: `β = T − m` for a time vector `T` with `dτ(T) = 1`; `dTime_shift` (tangent), `time_eq_lapse_normal_add_shift` (`T = N n + β`), `g_time_time` (`T · T = −N² + β · β`) | Sec. 4.2, eqs. (4.27)–(4.32), pp. 55-56 | Same, with `T = ∂_t` of coordinates adapted to the foliation; here `T` is any vector field with `dτ(T) = 1`, which is what (4.27) asks of `∂_t`. |
| `spatialProj`, `spatialMetric`: `γ = g + n♭ ⊗ n♭`, `γ(n, ·) = 0`, `γ = g` on tangent vectors | eqs. (2.68), (2.69), p. 30 (and the text after them) | Same. |
| `extrinsicCurvature`: `K(u, v) = −g(P u, ∇_{P v} n)`; vanishes on `n`; symmetric | eq. (2.43), p. 24 (`K(u, v) = −u · ∇_v n` on tangent vectors), eq. (2.70), p. 30 (extension by the projector), and the self-adjointness of the Weingarten map, Sec. 2.3.4, p. 23 | Same; the symmetry is `Hypersurface.secondFF_symm_fields` and needs the unit normal to be smooth near the point. |

## Smoothness of the normal

`FoliationSmooth.lean` (manifolds modelled on `ℝⁿ`): the gradient of a smooth `τ` is a smooth vector field
(`contMDiffAt_timeGrad`: in the chart at a point its components are `g^{ab} ∂_b τ`), so for a time function the lapse and
the unit normal are smooth (`smoothNear_unitNormal`), and `isUnitNormal_of_timeFunction` and
`extrinsicCurvature_symm_of_timeFunction` hold without a smoothness hypothesis. This is Gourgoulhon's construction of
`n` from the smooth scalar field `t` (Sec. 3.3.1, eqs. (3.4)-(3.5), p. 41).

## Adapted coordinates

`FoliationChart.lean`: a chart whose first coordinate is `τ` (`IsAdaptedChart`, Gourgoulhon Sec. 4.2.1, the coordinates
`(t, xⁱ)`, p. 54) has `dτ(∂_a) = δ_{a0}`, and with the shift of the time vector `∂₀`:

| Lean | Source, location | Match |
|---|---|---|
| `coordMetric_adapted_00`: `g₀₀ = −N² + g(β, β)` | eq. (4.43), p. 57 | Same. |
| `g_time_tangent`, `coordMetric_adapted_0i`: `g₀ᵢ = g(β, ∂ᵢ)` | eqs. (4.44)–(4.45), p. 57 | Same (`g(β, ∂ᵢ) = βᵢ`). |
| `coordMetric_adapted_ij`: `gᵢⱼ = γ(∂ᵢ, ∂ⱼ)` | eq. (4.46), p. 58 | Same. |
| `admSliceMetric`: the spatial block of the coordinate metric on `x⁰ = t` | eq. (4.47), p. 58 (the block form of `g_{αβ}`) | `admSliceMetric_eq_spatialMetric`: it is the induced metric of the leaf `τ = t`. |
| `admSliceMomentum`: `π^{ij} = √det h (K h^{ij} − K^{ij})` from the coordinate components `K_ij = K(∂ᵢ, ∂ⱼ)` | eq. (4.108), p. 67 (`π^{ij} = √γ (K γ^{ij} − K^{ij})`) | Same formula; `admSliceMomentum_symm`: symmetric for the Levi-Civita connection. |

## The extrinsic curvature as a Lie derivative

`FoliationLie.lean`, `extrinsicCurvature_eq_neg_half_lieDeriv`: for the Levi-Civita connection and fields `V, W` tangent
to the leaf at `x`, `K(V, W) = −½ (ℒ_n g)(V, W)` at `x`. Source: Gourgoulhon Sec. 3.3.5, eq. (3.27), p. 45,
`K = −½ ℒ_n γ`. Representation: the statement uses the Lie derivative of the metric `g` (`Lightlike.lieDerivMetric`),
which equals that of `γ = g + n♭ ⊗ n♭` on vectors tangent at `x`, since `n♭` vanishes there.

## The leaves are spacelike

`FoliationSpacelike.lean`, `spatialMetric_pos`: for a Lorentzian metric, `γ(w, w) > 0` for nonzero `w` tangent to a leaf.
Gourgoulhon assumes the leaves spacelike (Sec. 3.2.2, p. 40); here it follows from the timelike gradient.

## Trust checks

Minkowski space with `τ = x⁰`: `∇τ = −e₀`, `N = 1`, `n = e₀`, `γ` the Euclidean metric of the spatial coordinates
(`TestsFoliation.lean`); `τ = x¹` (spacelike gradient) is not a time function. The identity chart of Minkowski space is
adapted to `τ = x⁰`, its slice metric is `δ_ij` (`admSliceMetric_minkowski`) and, for the flat connection, its slice
momentum is `0` (`admSliceMomentum_minkowski`).

## Not done here

* the passage from the Einstein equations on the spacetime to the constraints on the slice data (Gourgoulhon
  Sec. 4.2, eqs. (4.19), (4.22), through the Gauss and Codazzi relations of `Lightlike/Spacetime/Hypersurface.lean`).
