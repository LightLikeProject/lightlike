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
4. The Killing algebra of the model type (G1-024's isometry-group form).
