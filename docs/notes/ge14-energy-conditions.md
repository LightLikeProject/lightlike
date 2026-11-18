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

## Trust checks and their sources
* Dust with `ρ ≥ 0` satisfies all four: follows from the effective forms of Curiel's table with `p = 0`; our proof is direct (`dust_energyConditions`).
* A cosmological constant: Curiel lists "a negative cosmological constant, as in de Sitter spacetime" as violating the SEC (p. 29-30) and "a positive cosmological constant (e.g., anti-de Sitter space)" as
  violating the WEC; his sign convention for Λ is the opposite of ours (standard: de Sitter has `Λ > 0`, `G + Λ g = 8πG T`, vacuum energy density `ρ_Λ = Λ/(8πG) > 0`). In our convention a positive vacuum
  energy density violates the SEC and satisfies the WEC (`cosmo_energyConditions`), the same physical content as his statement about de Sitter space.
* A Klein-Gordon field with negative potential violates the weak condition at a point where `dφ = 0` (`scalar_negative_potential_violates_weak`): no read source states this; Carroll (p. 117) only says that it is
  "straightforward to invent otherwise respectable classical field theories which violate the WEC", and Curiel lists massive Klein-Gordon fields as possible SEC violators (p. 31). Comparison pending: the
  stress-energy `T = dφ ⊗ dφ − (½ |dφ|² + V) g` is the standard form, not compared with a read source.

## Differences
Curiel works on a spacetime with a time orientation; ours is pointwise on a Lorentzian vector space and "co-oriented" is the pointwise notion above. Electromagnetic fields (named in the task): `emT` is the standard form `F_ac F_b^c − ¼ F² g_ab`, not compared with a read source (comparison pending), and only the null condition is proved (`em_nullEC`).
