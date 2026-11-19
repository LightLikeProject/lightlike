# G1-024, Killing rigidity: source reading and plan

## Source read (19 November 2026)

M. Blau, *Lecture Notes on General Relativity*, version "Last update November 15, 2026",
http://www.blau.itp.unibe.ch/newlecturesGR.pdf, read in the PDF (printed page = PDF page − 1):

* Section 13.2, p. 322: (13.5) `∇_[α ∇_β ξ_γ] = 0` from the first Bianchi identity; for Killing vectors (13.7) the cyclic
  identity and (13.8) `∇_α ∇_β K_γ = Rᵟ_{αβγ} K_δ`.
* Remark 1 after (13.12), pp. 322–323: the second derivatives of a Killing vector at a point are expressed algebraically in
  terms of the vector and its first derivatives there, which bounds the number of independent Killing vectors.
* Section 14.1, p. 337: (14.2) the same identity; "a Killing vector field `K^μ(x)` is completely and uniquely determined
  everywhere by the values of `K_μ(x₀)` and `∇_μ K_ν(x₀)` at a single point `x₀`" ("think of Taylor expansions"); p. 338,
  (14.4): at most `n(n + 1)/2` independent Killing vectors.

## Statements (`Lightlike/Spacetime/KillingRigidityCoord.lean`)

* `covCo2_sub_covCo2`: the Ricci identity for a covector field in coordinates, `[∇_a, ∇_b] θ_c = −Rᵈ_{cab} θ_d` (our
  convention `Rᵖ_{σμν} = ∂_μ Γᵖ_{νσ} − …`, `riemann g ρ σ μ ν`).
* `covCo2_antisymm`, `covCo2_killing`: (13.8) for a covector satisfying Killing's equation near the point, derived from
  the Ricci identity at the three cyclic orderings, the antisymmetry, and the first Bianchi identity
  (`IsCoordMetric.bianchi_first`), rather than from (13.6)–(13.7).

* `rigVec_eq_zero_of_isPreconnected`, `eq_of_rigVec_eq`: the rigidity statement after (14.2), on a connected open set:
  a covector satisfying Killing's equation is determined by `θ` and `∂θ` (equivalently `∇θ`) at one point. Proof: along
  a segment `(θ, ∂θ)` solves a linear ODE with continuous coefficients (`pd_pd_killing`, `rigVec_eq_zero_of_segment`,
  `linear_ode_eq_zero` by Gronwall's inequality), and the zero set is open and relatively closed.

Differences:
* representation: in coordinates for a coordinate metric on an open set, for the covector `θ = K♭`; the index placement
  of (13.8) is that of our Riemann convention.
* representation: "everywhere" is a connected open set of the chart (the source's tacit assumption); the proof is by
  uniqueness for a linear ODE, valid for smooth fields, not the source's Taylor expansion.

## Plan

1. (done) Uniqueness in coordinates, above.
2. (done) On a manifold (`Lightlike/Spacetime/KillingRigidity.lean`): `killing_eq_zero_of_eq_zero`, a smooth Killing
   field of the Levi-Civita connection on a connected manifold with `X(p₀) = 0` and `∇X(p₀) = 0` vanishes everywhere.
   In the chart at any point, `θ_b = g(X, ∂_b)` satisfies Killing's equation (`covCo_chartCovector`: `∇_a θ_b =
   g(∇_{∂_a} X, ∂_b)`), the coordinate rigidity holds in a ball of the chart, and the set where `X` and `∇X` vanish is
   open and closed (closedness also from the ball: a point in its closure has a ball meeting it).
   Difference: representation, a manifold modelled on `Fin n → ℝ` without boundary, metric of any signature, the
   vanishing form (two Killing fields agreeing with their covariant derivatives at a point: the difference, by
   linearity, not stated separately).
3. (done) The bound (14.4), p. 338: `finrank_killingFieldSpace_le`, the smooth Killing fields of the Levi-Civita
   connection on a connected nonempty manifold form a finite-dimensional real vector space of dimension at most
   `n (n + 1) / 2`. The map `X ↦ (g(X, ∂_b), g(∇_{∂_a} X, ∂_b))` at a point is linear (the connection is additive and
   homogeneous on differentiable fields), lands in `ℝⁿ` times the antisymmetric `n × n` matrices (Killing's equation),
   and is injective (rigidity), as in the source's count.
   Difference: representation, "independent Killing vectors" as the finite rank of the vector space of smooth Killing
   fields (the source's linear independence with constant coefficients).
4. The isometry-group form, stage 1 (slices; scope agreed 19 November 2026): six linearly independent Killing fields
   of a 3-metric with isotropy at a point have the space-form structure constants after a change of complement.
   S1 closure (dimension at most 6 and the bracket of Killing fields), S2 evaluation at the point through
   `pd_pd_killing` and rigidity, S3 Jacobi, so(3)-equivariance and the change of complement. First piece (done):
   `KillingAlgebraCoord.lean`, the bridge from the Lie-derivative form of Killing's equation used by
   `isometric_spaceForm` to the covector form of the rigidity (`covCo_lowerVec_add`). Checked numerically before
   writing: Jacobi forces the rotation part of `[J, P]` to vanish, and the translation part of `[P, P]` is removed by
   `P' = P - (β/2) J`.
   Working plan for the next pieces (coordinates on a ball of `Fin 3 → ℝ`, the setting of `isometric_spaceForm`):
   (a) (done: `lieCo_bracketCo`, `lieCo_bracketCo_eq_zero`) `L_{[Y,Z]} T = L_Y (L_Z T) - L_Z (L_Y T)` for the coordinate
       Lie derivative
       `(L_Y T)_{ab} = Yᶜ ∂_c T_{ab} + ∂_a Yˡ T_{lb} + T_{al} ∂_b Yˡ` of a field of bilinear forms (second derivatives
       cancel by `pd_pd_comm`), so brackets of Killing fields are Killing;
   (b) with the normalization at `p` (`P_m(p)` a frame, `R_ab(p) = 0`, `∇R_ab(p)` the so(3) generators), the six values
       `rigVec (lowerVec g Y_e) p` span the Killing data at `p` (value and antisymmetric derivative), so for every
       Killing field `Z` there are constants with `rigVec (lowerVec g Z) p = Σ cₑ rigVec (lowerVec g Y_e) p`, and
       `eq_of_rigVec_eq` gives `Z = Σ cₑ Y_e` on the ball: S1 and S2 together;
   Refinement (19 November 2026, 21:15): normalise the translations as transvections at `p` (`P_m(p) = e_m`,
   `∇P_m(p) = 0`; any frame of Killing fields can be brought to this by subtracting rotations). Then, by
   `covCo2_killing` at `p`: `[P_a, P_b](p) = 0` (no translation part, `β = 0`), `∇[R_ab, P_m](p) = 0` (since
   `∇∇R(p) = Riem · R(p) = 0`; no rotation part, `λ = 0`), and `∇[P_a, P_b](p)` is the curvature at `p`; Jacobi
   (`[R, [P, P]]`) makes that curvature isotropic, `[P_m, P_n] = -k R_mn` in the convention of `SpaceForm.S`.
   (c) the constants of `[Y_i, Y_j]` from their data at `p` (`[R,R]`: so(3); `[R,P]`: translation part from
       `∇R(p)`; the rest unknown), Jacobi on the constants, the equivariance computation, the change of complement, and
       `hS` for `S k`; then `isometric_spaceForm`.
