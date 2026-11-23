# G1-016, conformal compactification of Minkowski space: source reading

## Source read (19 November 2026)

S. M. Carroll, *Lecture Notes on General Relativity*, arXiv gr-qc/9712019, chapter 7, read in the arXiv PDF (printed page =
PDF page − 7):

* p. 192–193: (7.86) `ds² = −dt² + dr² + r² dΩ²`, (7.87) the ranges, (7.88) `u = ½(t + r)`, `v = ½(t − r)`, (7.89),
  (7.90) `ds² = −2(du dv + dv du) + (u − v)² dΩ²`.
* p. 194: (7.91) `U = arctan u`, `V = arctan v`, (7.92) `−π/2 < U, V < π/2`, `V ≤ U`, (7.93)–(7.97) the metric
  `ds² = (cos² U cos² V)⁻¹ [−2(dU dV + dV dU) + sin²(U − V) dΩ²]`.
* p. 195: (7.98) `η = U + V`, `χ = U − V`, (7.99) `−π < η < π`, `0 ≤ χ < π`, (7.100) `ds² = ω⁻² (−dη² + dχ² + sin² χ dΩ²)`,
  (7.101) `ω = cos U cos V = ½ (cos η + cos χ)`, (7.102) the "unphysical" metric `ds̄² = ω² ds²`, the Einstein static
  universe on `ℝ × S³`; "Minkowski space is mapped into the subspace defined by (7.99)".
* p. 196: the Penrose diagram; the boundaries are "conformal infinity".

## Statements (`Lightlike/Spacetime/MinkowskiCompactification.lean`)

* `minkowski_eq_conformal_esu`: (7.100), the Minkowski metric `−dt² + dr² + r² dΩ²` on the image of
  `a ∂_η + b ∂_χ + w` is `ω⁻² (−a² + b² + sin² χ q)` (`q = dΩ²(w, w)`), with the partial derivatives of
  `t = sin η / ω`, `r = sin χ / ω` (`hasDerivAt_compT_eta`, ...).
* `compOmega_eq_cos_mul_cos`: (7.101). `compT_eq_tan_add`, `compR_eq_tan_sub`: `t = tan U + tan V`, `r = tan U − tan V`,
  i.e. (7.88) and (7.91) inverted.
* `bijOn_comp`: the map `(η, χ) ↦ (t, r)` is a bijection from `0 < χ`, `|η| + χ < π` onto `r > 0`.

Differences:
* representation: the region is written `0 < χ`, `|η| + χ < π`, the image of (7.92) `V < U` (the axis `r = 0`, `χ = 0`,
  which the source treats as "well-behaved" after (7.87), is left out, as polar coordinates degenerate there); the
  sphere factor `dΩ²` enters through `q = dΩ²(w, w)`, a statement about the radial part and the warping by `r²`.

* `compOmega_eq_zero_iff`: conformal infinity, p. 196: on the closed region `0 ≤ χ`, `|η| + χ ≤ π` the conformal factor
  `ω` vanishes exactly on the boundary `|η| + χ = π`, where the physical metric `ω⁻² ds̄²` is not defined.

## The axis (`Lightlike/Spacetime/MinkowskiCompactificationAxis.lean`, 24 November 2026)

Source: the same, p. 192-195 (read 19 November), after (7.87) where `r = 0` is called well-behaved. The polar form degenerates at
`χ = 0`; the Cartesian form with `p = (cos χ, sin χ n)` on the unit sphere of `ℝ × ℝ³` does not.

* `minkowski_eq_conformal_esu_cartesian`: on tangent vectors `a ∂_η + v` (`⟨p, v⟩ = 0`), `-dt² + |dx⃗|² = ω⁻² (-a² + |v|²)`
  at every point with `ω ≠ 0`, the axis included. Checked symbolically (sympy) before the Lean proof.
* `cartT_axis`, `cartX_axis`, `cartOmega_axis`: on the axis `t = 2 tan (η/2)`, `x⃗ = 0`, `ω = cos² (η/2)`.

Difference (representation): the source writes the sphere part as `sin² χ dΩ²`; here `|v|²` is the round metric of `S³ ⊂ ℝ⁴`,
the same metric. * `bijOn_cartMap`: `(η, p) ↦ (t, x⃗)` is a bijection from `{|η| < π, p ∈ S³, ω > 0}` onto `ℝ × ℝ³`, axis included
  (the source's (7.92)/(7.99) region, in Cartesian form; the inverse is algebraic, no arctan).

Difference (representation): the source's regions (7.92), (7.99) are in `(U, V)`/`(η, χ)`; ours is `|η| < π` with `ω > 0`
(equivalent to `|η| + χ < π`), and the sphere is `S³ ⊂ ℝ⁴` instead of `(χ, n)`. The AdS part is `AdSCompactification`.
