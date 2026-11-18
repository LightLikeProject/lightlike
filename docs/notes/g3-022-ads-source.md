# G3-022: anti-de Sitter solutions, source comparison

Lean: `Lightlike/GR/AdSPoincare.lean` (Poincaré patch), `Lightlike/GR/StaticSphericalJet.lean`, `StaticSphericalRicci.lean`,
`SAdSVacuum.lean` (Schwarzschild-AdS), `AdSConformal.lean` (global AdS and its conformal boundary).

## Source read (pdftotext of the arXiv PDF)

D. Harlow, *Jerusalem Lectures on Black Holes and Quantum Information*, arXiv:1409.1231:
* section 6.1, eq. (6.4) (global AdS, `r_ads = 1`, `f = 1 + r²`), (6.5): `1/r_ads² = -16πGρ₀/(d(d-1))` (vacuum energy and AdS radius),
  (6.6) `r = tan ρ`, `ds² = (1/cos²ρ)(-dt² + dρ² + sin²ρ dΩ²)`.
* section 6.4, eqs. (6.30)-(6.32), p. 79: "The AdS_{d+1} version of the Schwarzschild geometry, which is the unique spherically symmetric
  solution of Einstein's equation with negative vacuum energy, has (for d ≥ 3) metric (again setting r_ads = 1) `ds² = -f(r) dt² + dr²/f(r) + r² dΩ²_{d-1}`
  (6.30), here `f(r) = r² + 1 - α/r^{d-2}` (6.31), and α is related to the AdS version of the ADM mass M as `α = 16πGM/((d-1)Ω_{d-1})` (6.32)."
  And "The Schwarzschild radius r_s is the unique positive root of f".

## Matches

* `sadsF M L r = 1 - 2M/r + r²/L²`: eq. (6.31) with `d = 3`, `r_ads = L` (restoring the radius), `α = 2M`. MATCH up to the identification of `α` (the source's `α` is
  `16πGM/((d-1)Ω_{d-1})` for the ADM mass; ours is `2 M_Schw`, the Schwarzschild mass parameter).
* `sadsMetric`: eq. (6.30). MATCH.
* `sads_isVacuumSolution` (`G + Λ g = 0`, `Λ = -3/L²`): the source states that this is a solution of Einstein's equation with negative vacuum energy
  (unique among spherically symmetric); we prove that it is a solution (and that the Ricci tensor is `-(3/L²) g`), not uniqueness. The relation between `Λ`
  and `L` in (6.5) for `d = 3`: `1/L² = -16πGρ₀/6`, i.e. `Λ = 8πGρ₀ = -3/L²`: consistent.
* Pure AdS (`M = 0`): `adsGlobal` in `AdSConformal.lean` matches (6.4).
* Poincaré patch (`AdSPoincare.lean`): not stated in the sections read (Harlow mentions "AdS-Poincaré slicing" only in a footnote); its comparison remains with the
  plan row only (Carroll, Spacetime and Geometry ch. 8, not read).
