# G1-010, conservation of the stress-energy: source reading

## Source read (19 November 2026)

S. M. Carroll, *Lecture Notes on General Relativity*, arXiv gr-qc/9712019, read in the arXiv PDF, chapter 4,
pp. 110–111 (PDF pp. 117–118):

* (4.38): energy-momentum conservation in curved spacetime, `∇^μ T_{μν} = 0`.
* (4.42): the Einstein tensor `G_{μν} = R_{μν} - ½ R g_{μν}`, "which always obeys `∇^μ G_{μν} = 0`".
* (4.43): `G_{μν} = κ T_{μν}`, with "a symmetric and conserved (0, 2) tensor" on both sides.

## Statement (`Lightlike/Spacetime/StressEnergyConservation.lean`)

`divBilinAt_eq_zero_of_einsteinEq`: if `g.EinsteinEq cov Λ κ T` (`cov` the Levi-Civita connection of `g` and
`G + Λ g = κ T`) with `κ ≠ 0`, then `cov.divBilinAt g T x w = 0` at every point and for every vector.

Differences:
* representation: with a cosmological constant, `G + Λ g = κ T` (the source's (4.43) is `Λ = 0`), using that the metric
  is parallel; the divergence is `divBilinAt`, `g^{ij} (∇_i T)(e_j, w)`, for a manifold modelled on `ℝⁿ`.

G1-010 remainder not done: the null energy condition for the Klein–Gordon field (a two-line consequence of `scalarT`
for null `k`) has no read source location yet; Curiel arXiv 1405.0403v1 lists the Klein–Gordon field only among
possible violators of the other conditions (p. 30).
