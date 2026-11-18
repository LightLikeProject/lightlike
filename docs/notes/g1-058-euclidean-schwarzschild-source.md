# G1-058: Euclidean Schwarzschild, source comparison

Lean files: `Lightlike/GR/EuclideanSchwarzschild.lean`, `EuclideanCigar.lean`, `EuclideanCone.lean`.

## Sources read

1. S. Hawking-style statement, smooth period only: D. Harlow, *Jerusalem Lectures on Black Holes and Quantum Information*,
   arXiv:1409.1231, section 4.8 "The Euclidean black hole", eqs (4.42)-(4.44), p. 43 (pdftotext of the arXiv PDF; units r_s = 2M = 1).
   Wording: "if we were to decide to have t_E be an angular variable with period 4π then the apparent singularity at ρ = 0 would be
   resolved by the geometry capping off smoothly." (4π = 8πM.) It says nothing about other periods.
2. I. Kuntz, G. Paci, O. Zanusso, *Euclidean actions and static black hole entropy in teleparallel theories*, arXiv:2410.04510,
   Appendix A "Euclidean Schwarzschild and conical singularity", eqs (A1)-(A6), p. 21 (pdftotext of the arXiv PDF; r_s = 2m).
   Wording: "Close to the Schwarzschild radius, r ≈ 2m, we have ds²|_E ≈ (ρ/4m)² dτ² + dρ² + r² dΩ² (A5). The first two terms are
   understood as the metric of an Euclidean flat 2d space in polar coordinates, where ρ is the radius and τ/4m is the angular
   variable ... In polar coordinates ρ = 0 is an apparent singularity iff the angle is identified with period 2π, implying
   τ ~ τ + 8πm. ... If instead the angle is not identified with period 2π, i.e., β ≠ β_H, the Euclidean manifold will have a conical
   singularity. ... the integral of the scalar curvature, which is proportional to the deficit angle times the area of the
   codimension-two surface ... ∫_sing d⁴x √g R = 4π (1 − β/β_H) A (A6), where A = 16πm²."

## How each Lean statement matches

* `tendsto_cone_ratio`: circumference of the τ-circle over proper radial distance tends to `β/(4M)`. Source (A5): the angular variable is
  `τ/4m` with radius ρ, so the circle has circumference `β ρ/(4m)` and the ratio is `β/(4m)`. MATCH (same quantity).
* `cone_ratio_eq_two_pi_iff`: ratio `= 2π` iff `β = 8πM`. Source: "ρ = 0 is [not] a singularity iff the angle is identified with period 2π,
  implying τ ~ τ + 8πm". MATCH for the smooth period.
* `cone_deficit`: `2π − β/(4M) = 2π(1 − β/(8πM))`. Source (A6) gives the integrated curvature `4π(1 − β/β_H) A`, "proportional to the deficit
  angle times the area". With the standard cone relation `∫√g R = 2 δ A` for deficit angle δ, (A6) is `δ = 2π(1 − β/β_H)`. MATCH up to that
  convention, which the source does not spell out; the Lean statement is the angle deficit itself, not the curvature integral.
* The Lean files do NOT prove that the conical singularity is a curvature singularity, nor (A6), nor that no smooth extension exists for
  `β ≠ 8πM`: the source states the conical singularity for `β ≠ β_H` as a fact of geometry, not as a theorem about extensions.
  Difference kind for those two statements: representation (angle deficit as a limit of a ratio).
* `cig_isVacuumSolution`, `cigChange_periodic`: the smooth cap in Cartesian coordinates; the source says "It is trivial to show that the metric
  is now smooth everywhere". Lean proves it (Ricci-flat through the tip, smooth coordinate metric). Source gives no explicit Cartesian form.
* `hawkingTemperature = 1/(8πM)`: source "β_H = 8πm, is the inverse of Hawking's temperature". MATCH.

Not read: Gibbons-Hawking 1977 (Phys. Rev. D 15, 2752), cited by Kuntz et al. as ref. [2]; no location from it is claimed.
