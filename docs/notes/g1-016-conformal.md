# G1-016, conformal geometry: source reading and plan

## Source read (19 November 2026)

E. Gourgoulhon, *3+1 Formalism and Bases of Numerical Relativity*, arXiv:gr-qc/0703035, read in the arXiv PDF (printed
pages equal PDF pages):

* Section 6.2.4 "Conformal connection", p. 88: (6.28) the Christoffel symbols `Γ̃` of `γ̃`; (6.29) the covariant
  derivatives of `D` and `D̃` differ by the tensor `C`; (6.30) `Cᵏ_{ij} := Γᵏ_{ij} - Γ̃ᵏ_{ij}`; (6.31)
  `Cᵏ_{ij} = ½ γᵏˡ (D̃_i γ_{lj} + D̃_j γ_{il} - D̃_l γ_{ij})`.
* p. 89: (6.33) for `γ = Ψ⁴ γ̃`, `Cᵏ_{ij} = 2 (δᵏ_i D̃_j ln Ψ + δᵏ_j D̃_i ln Ψ - D̃ᵏ ln Ψ γ̃_{ij})`.
* pp. 90–91: (6.44)–(6.48) the Ricci tensor of `γ` from `C`, for a 3-metric (`Cᵏ_{ki} = 6 D̃_i ln Ψ`, (6.46)).

A. Campos, E. Verdaguer, *Semiclassical equations for weakly inhomogeneous cosmologies*, arXiv:gr-qc/9307027v1, read in
the arXiv PDF, Appendix C "Curvature tensors in conformally transformed n dimensional spaces", p. 28 (PDF p. 29): for
`g̃ = e^{2ω} g` (C.1), the Riemann tensor (C.2), the Ricci tensor (C.3)
`R̃_{μα} = R_{μα} - (n - 2) ω_{;μα} - g_{μα} □ω + (n - 2) ω_{;μ} ω_{;α} - (n - 2) g_{μα} ω_{;ρ} ω^{;ρ}` and the scalar
curvature (C.4) `R̃ = e^{-2ω} [R - 2(n - 1) □ω - (n - 1)(n - 2) ω_{;ρ} ω^{;ρ}]`, in any dimension `n`. These are the
general-`n` forms of Gourgoulhon's (6.48)–(6.49); the Ricci and scalar curvature steps cite (C.3) and (C.4).

## Statements (`Lightlike/Spacetime/ConformalCoord.lean`)

* `christoffel_conformal`: for `g̃ = e^{2ψ} g`, `Γ̃ᵃ_{bc} = Γᵃ_{bc} + δᵃ_c ∂_b ψ + δᵃ_b ∂_c ψ - g_{bc} gᵃᵈ ∂_d ψ` at a point
  where the entries of `g` and `ψ` are differentiable, `det g ≠ 0` and `g` is symmetric. This is the source's (6.33)
  with `e^{2ψ} = Ψ⁴` (`ψ = 2 ln Ψ`), the old metric `g = γ̃` and the new `g̃ = γ`.
* `riemann_of_christoffel_add`: the Riemann tensor of a metric whose Christoffel symbols are `Γ + C` near a point
  (the source's (6.29)–(6.30) relation, used for the Ricci tensor (6.44)).

Differences:
* convention: any dimension and signature (the source is a Riemannian 3-metric), the conformal factor `e^{2ψ}` for the
  source's `Ψ⁴`, and partial derivatives of `ψ` for the source's `D̃ ln Ψ` (equal on scalars).

## Statements (`Lightlike/Spacetime/ConformalRicci.lean`)

* `ricci_of_christoffel_add_cov`: Gourgoulhon's (6.44) in any dimension, `R̃_{σν} = R_{σν} + ∇_ρ Cᵖ_{νσ} - ∇_ν Cᵖ_{ρσ} +
  Cᵖ_{νσ} Cˡ_{lρ} - Cᵖ_{νl} Cˡ_{ρσ}` for two metrics whose Christoffel symbols differ by `C` near a point, `∇` that of
  the old metric (`covC`). The source states it for the two connections of a conformal pair and remarks it holds for any
  two; the Lean statement assumes only the Christoffel relation.
* `covC_conformalC`: `∇_k Cᵃ_{bc} = δᵃ_c H_{kb} + δᵃ_b H_{kc} - g_{bc} gᵃᵈ H_{kd}`, with `H` the covariant Hessian of `ψ`
  (`hessC`); `sum_confCAt_quadratic`: the quadratic terms sum to `(n - 2)(∂_ν ψ ∂_σ ψ - g_{νσ} |dψ|²)`.
* `ricci_conformal`: Campos–Verdaguer (C.3) with `ω = ψ`, `ω_{;μα}` the covariant Hessian `hessC`, `□ω` its trace `boxC`
  and `ω_{;ρ} ω^{;ρ}` the square `gradSq` of the gradient.
* `scalarCurvature_conformal`: Campos–Verdaguer (C.4).

These hold for a coordinate metric on an open set `U ⊆ ℝⁿ` and `ψ` smooth on `U`, at every point of `U`.

Differences:
* representation: the statements are in coordinates on an open set of `ℝⁿ` (partial derivatives and the coordinate
  Christoffel symbols of a coordinate metric); the source's covariant derivatives `ω_{;μα}` are the coordinate
  expressions `∂_μ ∂_α ψ - Γᵉ_{μα} ∂_e ψ`.

## Statements (`Lightlike/Spacetime/ConformalWeyl.lean`)

Source read (19 November 2026): S. M. Carroll, *Lecture Notes on General Relativity*, arXiv gr-qc/9712019, chapter 3,
p. 82 (PDF p. 89): (3.97) the Weyl tensor
`C_{ρσμν} = R_{ρσμν} - 2/(n - 2) (g_{ρ[μ} R_{ν]σ} - g_{σ[μ} R_{ν]ρ}) + 2/((n - 1)(n - 2)) R g_{ρ[μ} g_{ν]σ}`, "only
defined in three or more dimensions"; after (3.99): "invariant under conformal transformations. This means that if you
compute C_{ρσμν} for some metric g_{μν}, and then compute it again for a metric given by Ω²(x) g_{μν} ... you get the
same answer" (the indices of `C` in that sentence are all down in the PDF, checked by glyph position).

* `riemann_of_christoffel_add_cov`: the uncontracted form of Gourgoulhon's (6.44).
* `riemann_conformal`, `riemannLow_conformal`: Campos–Verdaguer (C.2), with `ω_{;αρ} - ω_{;α} ω_{;ρ}` the tensor
  `hessC - ∂ψ ∂ψ` and the antisymmetrizations written out.
* `weyl`: (3.97) with the antisymmetrizations written out; `weyl_conformal` (`n ≥ 3`): `C̃_{ρσμν} = e^{2ψ} C_{ρσμν}`;
  `weylUp_conformal` (`n ≥ 3`): `C̃ᵖ_{σμν} = Cᵖ_{σμν}`.

Differences:
* representation: coordinates on an open set of `ℝⁿ`, as for the Ricci tensor above.
* representation: the source states the invariance for `C_{ρσμν}` with all indices down. With all indices down the
  Weyl tensor scales by the conformal factor, `C̃_{ρσμν} = Ω² C_{ρσμν}` (`weyl_conformal`, `Ω² = e^{2ψ}`), and the
  tensor that is unchanged is `Cᵖ_{σμν}` (`weylUp_conformal`). Both are proved.
