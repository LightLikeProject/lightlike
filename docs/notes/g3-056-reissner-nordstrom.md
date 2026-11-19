# G3-056 (partial): Reissner–Nordström and the extremal black hole

Lean: `Lightlike/GR/ReissnerNordstrom.lean`, `Lightlike/Spacetime/MaxwellCoord.lean` (coordinate Maxwell equations), Regge's
electromagnetic stress-energy `emT` (`Lightlike/Spacetime/EnergyConditions.lean`, branch regge/ge14-em) evaluated on the coordinate
tangent space (`coordBil`, `emA_coord`, `emF2_coord`, `emT_coord`).

## Source read (pdftotext of the arXiv PDF)

S. M. Carroll, *Lecture Notes on General Relativity*, arXiv:gr-qc/9712019, chapter 7 "The Schwarzschild solution and black holes":
* p. 201: the electromagnetic stress-energy "T_μν = (1/4π)(F_μρ F_ν^ρ − ¼ g_μν F_ρσ F^ρσ)" (7.107); the spherically symmetric field strength
  "F_tr = f(r, t) = −F_rt, F_θφ = g(r, t) sin θ = −F_φθ" (7.108); "The field equations in this case are both Einstein's equations and Maxwell's
  equations: g^μν ∇_μ F_νσ = 0, ∇_[μ F_νρ] = 0" (7.109).
* p. 202: "The solution is known as the Reissner-Nordstrøm metric, and is given by ds² = −Δ dt² + Δ⁻¹ dr² + r² dΩ² (7.110), where
  Δ = 1 − 2GM/r + G(p² + q²)/r² (7.111) ... q is the total electric charge, and p is the total magnetic charge ... The electromagnetic fields
  associated with this solution are given by F_tr = −q/r², F_θφ = p sin θ (7.112)"; the horizons "r± = GM ± √(G²M² − G(p² + q²))" (7.113).
* p. 206: "Case Three — GM² = p² + q². This case is known as the extreme Reissner-Nordstrøm solution (or simply 'extremal black hole')";
  "The extremal black holes have Δ(r) = 0 at a single radius, r = GM. This does represent an event horizon, but the r coordinate is never timelike".
* p. 112: Einstein's equation "R_μν − ½ R g_μν = 8πG T_μν" (4.52). p. 107: Maxwell in curved space (4.24), (4.25); p. 61: (3.28); p. 62: (3.29).

## How each Lean statement matches

* `rnMetric M (q² + p²)` = (7.110)–(7.111) with `G = 1` (representation: units). `rnField q p` = (7.112).
* `rn_einstein`: `G_μν = 2 emT_μν`, i.e. (4.52) with `G = 1` and `T = emT/4π` (7.107) (Regge's `emT` has no `1/4π`: representation, recorded by Regge).
* `rn_maxwell`: (7.109) in the coordinate form `∂_μ(√|g| F^{μν}) = 0`, cyclic `∂F = 0` (representation; `MaxwellCoord.lean` docstring).
* `rnF_eq_factor`, `rnF_rplus`, `rnF_rminus`: (7.113) with `G = 1` (MATCH).
* `rn_extremal`: "GM² = p² + q² ... Δ(r) = 0 at a single radius, r = GM": the double root `Δ(M) = Δ'(M) = 0`, `Δ = (1 − M/r)²` (MATCH; "single radius"
  is formalized as the coincidence `r₊ = r₋ = M` plus the double root). "the r coordinate is never timelike; it becomes null at r = GM, but is spacelike on either side": `rn_extremal_nonneg` (`Δ ≥ 0`, `Δ > 0` off `r = M`).
* `rn_surfaceGravity` (`Δ'(r₊)/2 = (r₊ − r₋)/(2r₊²)`): supporting lemma, not in the source read.
* Trust checks: `rn_schwarzschild` (`q = p = 0`), `rn_not_vacuum` (`q² + p² ≠ 0`: not Ricci-flat).

## Out of scope (named in the docstring)

The supersymmetric BPS bound (the row's "BPS bounds": `M ≥ |Q|` as a Bogomolny bound in N = 2 supergravity, saturated by the extremal solution)
is not formalized; only the classical extremal Reissner–Nordström solution. Not proved: that `r = M` is an event horizon (causal structure), uniqueness.
