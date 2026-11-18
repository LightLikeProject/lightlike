# GE14: energy conditions, compared with the sources read (18 November 2026)

Sources read: E. Curiel, *A Primer on Energy Conditions* (arXiv 1405.0403v1), section 2.1 "Pointilliste Energy Conditions", pp. 5-6 of the arXiv pdf (physical and effective forms of
NEC, WEC, SEC, DEC); the lists of violating matter on pp. 29-31; S. M. Carroll, *Lecture Notes on General Relativity* (1997, arXiv gr-qc/9712019, not the book), eq. (4.72), p. 117 (the weak energy condition).

## Definitions
* NEC: "for any null vector k^a, T_mn k^m k^n >= 0" (Curiel, physical form, p. 5): our `NullEC`. Effective form `ρ + p_μ̂ ≥ 0`.
* WEC: "for any timelike vector ξ^a, T_mn ξ^m ξ^n >= 0" (p. 5); Carroll (4.72): "T_{μν} V^μ V^ν ≥ 0 for all timelike vectors V^μ": our `WeakEC`. Effective form `ρ ≥ 0` and `ρ + p_μ̂ ≥ 0`.
* SEC: "for any timelike vector ξ^a, (T_mn − ½ T g_mn) ξ^m ξ^n >= 0" (p. 5): our `StrongEC` (four dimensions, trace by `traceG`). Effective form `ρ + Σ p_μ̂ ≥ 0` and `ρ + p_μ̂ ≥ 0`.
* DEC (physical form, p. 5): "1. for any timelike vector ξ^a, T_mn ξ^m ξ^n >= 0, and T^a_n ξ^n is causal; 2. for any two co-oriented timelike vectors ξ^a and η^a, T_mn ξ^m η^n >= 0": our `DominantEC`,
  with "co-oriented" as `g(ξ, η) < 0` and "causal" as `g(w, w) <= 0`. Effective form `ρ ≥ 0` and `|p_μ̂| ≤ ρ`.
* For the perfect fluid `(ρ + p) u ⊗ u + p g` (principal pressures all `p`, dimension four) the effective forms of Curiel's table give NEC: `ρ + p ≥ 0`; WEC: `ρ ≥ 0, ρ + p ≥ 0`; SEC: `ρ + 3p ≥ 0, ρ + p ≥ 0`;
  DEC: `ρ ≥ |p|`. These are the theorems `fluid_nullEC_iff`, `fluid_weakEC_iff`, `fluid_strongEC_iff`, `fluid_dominantEC_iff` (proved, not quoted).

Also read: P. Martín-Moruno and M. Visser, *Classical and semi-classical energy conditions* (arXiv 1702.05915), p. 4: for a type I stress-energy tensor (perfect fluids, massive scalar fields and non-null
electromagnetic fields are named as examples) the conditions are equivalent to NEC `ρ + p_i ≥ 0`; WEC `ρ ≥ 0` and `ρ + p_i ≥ 0`; SEC `ρ + Σ p_i ≥ 0` and `ρ + p_i ≥ 0`; DEC `|p_i| ≤ ρ` (and `ρ ≥ 0`): the same effective forms as Curiel's table.
The paper does not state, for the Maxwell field, which conditions hold; p. 5 says non-minimally coupled scalar fields can violate all conditions classically.

## Stress-energy forms (Carroll lecture notes gr-qc/9712019, read)
* Perfect fluid: `T^{μν} = (ρ + p) U^μ U^ν + p η^{μν}`, eq. (1.110), p. 30: our `fluidT`.
* Electromagnetic field: `T^{μν}_{e+m} = (1/4π)(F^{μλ} F^ν{}_λ − ¼ η^{μν} F^{λσ} F_{λσ})`, eq. (8.25), pp. 221-222 (and eq. (1.111), p. 30, printed with the opposite overall sign: an index-order convention for `F^ν{}_λ`;
  not resolved here), with vanishing trace (8.26): our `emT` is `F_ac F_b{}^c − ¼ F² g_ab` (Gaussian factor `1/4π` omitted, the sign of (8.25): `T^{00} = E²/8π … > 0`).
* Scalar field: `T^{μν}_{scalar} = η^{μλ}η^{νσ}∂_λφ ∂_σφ − ½ η^{μν}(η^{λσ}∂_λφ ∂_σφ + m²φ²)`, eq. (1.112), p. 30: our `scalarT` is `dφ ⊗ dφ − (½ |dφ|² + V) g` with `V = ½ m²φ²` for the free massive field, and a general potential
  `V(φ)` as in the standard minimally coupled field (the generalisation to `V(φ)` is not stated in the pages read).

## Trust checks and their sources
* Dust with `ρ ≥ 0` satisfies all four: follows from the effective forms of Curiel's table with `p = 0`; our proof is direct (`dust_energyConditions`).
* A cosmological constant: Curiel lists "a negative cosmological constant, as in de Sitter spacetime" as violating the SEC (p. 29-30) and "a positive cosmological constant (e.g., anti-de Sitter space)" as
  violating the WEC; his sign convention for Λ is the opposite of ours (standard: de Sitter has `Λ > 0`, `G + Λ g = 8πG T`, vacuum energy density `ρ_Λ = Λ/(8πG) > 0`). In our convention a positive vacuum
  energy density violates the SEC and satisfies the WEC (`cosmo_energyConditions`), the same physical content as his statement about de Sitter space.
* A Klein-Gordon field with negative potential violates the weak condition at a point where `dφ = 0` (`scalar_negative_potential_violates_weak`): no read source states this specific computation. What the read sources say:
  Carroll p. 117 "it is straightforward to invent otherwise respectable classical field theories which violate the WEC"; Curiel p. 31-32 "using classical scalar fields alone ... it is relatively easy to engineer violations of
  even the weakest conditions, the NEC and the ANEC" and lists minimally coupled and massive Klein-Gordon fields among possible violators (p. 30-31). Our check is a direct computation from (1.112)
  with a general potential; **open comparison**: no read source states "negative potential at `dφ = 0` violates the WEC".
* Electromagnetic and scalar fields satisfy which conditions? No read source states it (Curiel's lists name "classical Dirac fields" and scalar fields as violators, not the Maxwell field). We therefore do not
  claim the weak, strong and dominant conditions for `emT`; only the null condition is proved (`em_nullEC`), as an own computation.

## Differences
Curiel works on a spacetime with a time orientation; ours is pointwise on a Lorentzian vector space and "co-oriented" is the pointwise notion above.

## Stage 2: stress-energy fields on a manifold and the geometric forms (`EnergyConditionsField.lean`)
* `NullECField`, `WeakECField`, `StrongECField`, `DominantECField`: the stage-1 conditions at every point of a Lorentzian 4-manifold. Curiel's
  conditions in §2.1 are pointwise ("pointilliste": "those ... that constrain behavior at individual points", p. 5), so a field satisfies one
  iff it does at every point: no difference.
* The perfect fluid, dust, Klein–Gordon and electromagnetic fields are the stage-1 forms at every point; the effective forms for a fluid with a
  unit timelike velocity field follow pointwise. The constant Klein–Gordon field with a negative potential value violates the weak condition:
  the same open comparison as in stage 1 (no read source states it).
* Geometric forms. Curiel, §2, p. 5: "In every case, the physical formulation is logically equivalent to the geometric formulation if the
  Einstein field equation is assumed to hold." Table of §2.1, p. 6, geometric column: NEC "for any null vector k^a, R_mn k^m k^n ≥ 0"; WEC
  "for any timelike vector ξ^a, G_mn ξ^m ξ^n ≥ 0"; SEC "for any timelike vector ξ^a, R_mn ξ^m ξ^n ≥ 0"; DEC "1. for any timelike vector
  ξ^a, G_mn ξ^m ξ^n ≥ 0, and G^a_n ξ^n is causal 2. for any two co-oriented timelike vectors ξ^a and η^a, G_mn ξ^m η^n ≥ 0".
  Ours: `nullECField_iff_ricci`, `weakECField_iff_einstein`, `strongECField_iff_ricci`, `dominantECField_iff_einstein` under `G = κ T`, `κ > 0`
  (`EinsteinEq` with `Λ = 0`); `G^a_n ξ^n` is written as the vector `w` with `g(w, ·) = G(ξ, ·)` (index raising); the strong form uses the
  trace `R = −κ tr_g T` (`scalarCurvatureAt_of_einsteinEq`, dimension four). Curiel does not print the field equation in the pages read
  (p. 2 note 1: `T_ab` is "the stress-energy tensor picked out in a spacetime model by the Einstein field equation"; conventions of Malament,
  not read), so a general coupling `κ > 0` and the absorption of a cosmological constant into the source (`einsteinEq_iff_absorb`) are no
  difference from a stated form.
* Non-vacuity: Minkowski space with the flat connection solves `G = κ · 0` (`minkowski_einsteinEq_zero`), and the strong form gives
  `Ric(ξ, ξ) ≥ 0` there (`minkowski_ricci_nonneg`). A non-vacuum check (closed de Sitter or Friedmann dust through the equivalence) waits for
  regge/co30-sphere on main.
* Differences: none found for stage 2.
