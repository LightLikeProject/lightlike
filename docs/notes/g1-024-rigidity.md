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
2. On a manifold: Killing fields in charts satisfy the coordinate Killing equation; a Killing field on a connected manifold
   vanishing with its covariant derivative at one point vanishes.
3. The bound (14.4) and the Killing algebra of the model type (G1-024's isometry-group form).
