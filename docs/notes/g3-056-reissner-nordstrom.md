# G3-056 (partial): Reissner–Nordström and the extremal black hole

Lean: `Lightlike/GR/ReissnerNordstrom.lean`, `Lightlike/Spacetime/MaxwellCoord.lean` (coordinate Maxwell equations), Regge's
electromagnetic stress-energy `emT` (`Lightlike/Spacetime/EnergyConditions.lean`, branch regge/ge14-em) evaluated on the coordinate
tangent space (the library's `matForm`, `emA_coord`, `emF2_coord`, `emT_coord`).

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

## The bound: what the sources state (checked 19 Nov 2026)

* Row G3-056 names "ST10; F–VP Ch. 11". Strominger–Vafa, arXiv:hep-th/9601029v2, read (pdftotext): §1 p. 1 "BPS saturated states - i.e.
  extremal black holes ... preserve only 1/4 of the N = 4 supersymmetry"; §2 pp. 2–3, the extremal 5D Reissner–Nordström metric (2.8),
  "annihilated by one quarter of the supersymmetries". It states no inequality. Freedman–Van Proeyen, *Supergravity*, Ch. 11: a book,
  **not read** (not accessible here); nothing below is compared with it.
* Carroll gr-qc/9712019 (read): the three cases "GM² < p² + q²: Δ always positive (never zero)", a naked singularity, p. 202;
  "GM² > p² + q²", two horizons, p. 204; "GM² = p² + q²", the extremal hole, p. 206. This is the classical bound `M ≥ |Q|` for a horizon.
* Kallosh–Linde–Ortín–Peet–Van Proeyen, *Supersymmetry as a cosmic censor*, arXiv:hep-th/9205027 (read, pdftotext), §2: the bounds of the
  rest-frame algebra "{S(1), S(1)*} = 2|S(1)|² = M − |z1| ≥ 0" (7), p. 6–7; for asymptotically flat N = 2 supergravity "M ≥ √(Q² + P²) =
  |z1|" (8), p. 7, derived by Gibbons–Hull "by applying the Witten-Nester-Israel construction"; z1 = √(Q² + P²) (9) and the supercovariant
  derivative (10), p. 8: "extreme Reissner-Nordström black holes with M = √(Q² + P²) admit super-covariantly constant spinors ... and saturate
  the bound (8)".
* Bilal, *Introduction to supersymmetry*, arXiv:hep-th/0101055v1 (read): the rest-frame algebra (3.12), the oscillators (3.14)–(3.15) and
  "positivity of the Hilbert space requires that 2m ≥ |q_n|" (3.16), pp. 13–14.

## Proved

* The classical bound: `rn_horizon_iff` (a zero of `Δ` at `r > 0` iff `0 < M ∧ q² + p² ≤ M²`), `rn_horizon_iff_sqrt` (`M ≥ √(q² + p²)`),
  `rnF_pos_of_lt` (Carroll's Case One), `rn_degenerate_iff` (saturation iff the horizon is degenerate, `M² = q² + p²`). MATCH with Carroll
  pp. 202–206 (`G = 1`).
* The algebraic BPS bound (`Lightlike/GR/BPSBound.lean`): `bps_bound`, `bps_bound_restFrame` (`|Z| ≤ 2m` in a unitary representation of the
  rest-frame N = 2 algebra; Bilal (3.16), KLOPV (7) in Bilal's normalization), `bps_saturated` (at `|Z| = 2m` the oscillator `a` vanishes,
  Bilal p. 14). Difference: bounded operators on a Hilbert space; Bilal's `U(N)` rotation to the real form (3.13) is a phase `c` here.

## Not proved: extremal Reissner–Nordström as a BPS state of N = 2 supergravity (KLOPV (8)–(10), Gibbons–Hull)

Attempt 1 (19 Nov 2026), the Witten–Nester–Israel integral of Gibbons–Hull: (a) Dirac spinor fields on a curved Lorentzian manifold, (b) the
supercovariant connection (10) built from the spin connection and `F`, (c) the Nester 2-form and its divergence identity, positive under the
field equations, (d) Stokes on an asymptotically flat slice, the surface integral at infinity giving `M − |z1|`, (e) a solution of Witten's
elliptic equation with constant asymptotic value. Obstruction, checked in the repository: (a) does not exist: Physlib's Dirac spinors are the
flat representation `Module.End ℂ Dirac` (`Relativity/Fermions/Dirac/GammaMatrices.lean:49`), its API map lists "A spinor field on spacetime
is subject to the Dirac equation. [TODO]" (`Relativity/Fermions/Dirac/API-map.md:67`), and Lightlike has no spin structure; (b) needs (a) and a
spin connection, and Lightlike has no tetrad or spin connection (`grep -rli "tetrad|vierbein|spin connection" Lightlike`: no hit); (d) has no
ADM mass or surface integral at spatial infinity (`grep -rli "ADM mass|admMass" Lightlike`: no hit); (e) has no elliptic existence theory.
Stopped at (a): each of (a)–(e) is a library of its own.

Attempt 2 (19 Nov 2026), the superalgebra and the Killing spinor (KLOPV (7) and (10)): (i) the bound from positivity in the rest-frame
algebra: done (`bps_bound_restFrame`); (ii) solve `∇̂_μ ε = 0` (10) on the extremal metric in the static chart, `ε` with values in ℂ⁴ ⊗ ℂ²;
(iii) identify the `m` and `Z` of (i) with the ADM mass and `√(Q² + P²)` of the solution, KLOPV (8)–(9). Obstruction: (ii) needs the
coordinate gamma matrices `γ_μ = e^a_μ γ_a` of the tetrad `diag(√Δ, 1/√Δ, r, r sin θ)` and the spin connection `ω_μ^{ab}`, neither of which the
coordinate framework (`IsCoordMetric`, `christoffel`, `ricci`) provides; it was not started in Lean, because (iii) is the boundary-term
computation of the supercharges (KLOPV p. 6: "construct the supersymmetry charges ... paying attention to boundary terms"), i.e. steps (c)–(d)
of attempt 1, so a Killing spinor alone does not give the BPS property here. The weaker line is therefore the identification (iii) and the
supergravity bound (8).

## Out of scope (named in the docstring)

The supergravity bound (8) and the BPS property of extremal Reissner–Nordström (above). Not proved: that `r = M` is an event horizon (causal
structure), uniqueness.
