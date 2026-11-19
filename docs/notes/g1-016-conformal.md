# G1-016, conformal geometry: source reading and plan

## Source read (19 November 2026)

E. Gourgoulhon, *3+1 Formalism and Bases of Numerical Relativity*, arXiv:gr-qc/0703035, read in the arXiv PDF (printed
pages equal PDF pages):

* Section 6.2.4 "Conformal connection", p. 88: (6.28) the Christoffel symbols `Γ̃` of `γ̃`; (6.29) the covariant
  derivatives of `D` and `D̃` differ by the tensor `C`; (6.30) `Cᵏ_{ij} := Γᵏ_{ij} - Γ̃ᵏ_{ij}`; (6.31)
  `Cᵏ_{ij} = ½ γᵏˡ (D̃_i γ_{lj} + D̃_j γ_{il} - D̃_l γ_{ij})`.
* p. 89: (6.33) for `γ = Ψ⁴ γ̃`, `Cᵏ_{ij} = 2 (δᵏ_i D̃_j ln Ψ + δᵏ_j D̃_i ln Ψ - D̃ᵏ ln Ψ γ̃_{ij})`.
* pp. 90–91: (6.44)–(6.48) the Ricci tensor of `γ` from `C`, for a 3-metric (`Cᵏ_{ki} = 6 D̃_i ln Ψ`, (6.46)).

## Statements (`Lightlike/Spacetime/ConformalCoord.lean`)

* `christoffel_conformal`: for `g̃ = e^{2ψ} g`, `Γ̃ᵃ_{bc} = Γᵃ_{bc} + δᵃ_c ∂_b ψ + δᵃ_b ∂_c ψ - g_{bc} gᵃᵈ ∂_d ψ` at a point
  where the entries of `g` and `ψ` are differentiable, `det g ≠ 0` and `g` is symmetric. This is the source's (6.33)
  with `e^{2ψ} = Ψ⁴` (`ψ = 2 ln Ψ`), the old metric `g = γ̃` and the new `g̃ = γ`.
* `riemann_of_christoffel_add`: the Riemann tensor of a metric whose Christoffel symbols are `Γ + C` near a point
  (the source's (6.29)–(6.30) relation, used for the Ricci tensor (6.44)).

Differences:
* convention: any dimension and signature (the source is a Riemannian 3-metric), the conformal factor `e^{2ψ}` for the
  source's `Ψ⁴`, and partial derivatives of `ψ` for the source's `D̃ ln Ψ` (equal on scalars).

Next, in order: the Riemann, Ricci and scalar curvature of `e^{2ψ} g` in covariant form, then the
Weyl tensor and its conformal invariance (Carroll gr-qc/9712019 (3.97) and the statement after (3.99), p. 82, read).
