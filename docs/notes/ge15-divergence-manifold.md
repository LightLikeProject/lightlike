# GE15: the divergence theorem on a manifold (source, statement, differences)

## Source read (19 November 2026)

L. H. Loomis, S. Sternberg, *Advanced Calculus* (revised edition), chapter 10, read in the PDF of the revised edition:

* Section 3, p. 409: `P` is the space of locally absolutely integrable densities of compact support; Theorem 3.1: the
  integral of `ρ ∈ P` is the unique linear function with `∫ ρ = ∫_{α(U)} ρ_α` when `supp ρ ⊆ U`.
* Section 5, pp. 418–419: `div⟨X, ρ⟩ = D_X ρ`, locally `(div⟨X, ρ⟩)_α = Σ ∂(Xⁱ_α ρ_α)/∂xⁱ`.
* Section 6, Definition, p. 419: `D` is a domain with regular boundary if every `x ∈ M` has a chart with (i) `U ∩ D = ∅`,
  (ii) `U ⊆ D`, or (iii) `α(U ∩ D) = α(U) ∩ {vⁿ ≥ 0}`.
* (6.1)–(6.2), p. 421: the density `ρ_X` on `∂D`, `(ρ_X)_α = |Xⁿ| ρ_α` in a chart of type (iii).
* Theorem 6.1, p. 421: for `D` with regular boundary, `ρ ∈ P` and a smooth `X`, `∫_D div⟨X, ρ⟩ = ∫_{∂D} ε_X ρ_X` (6.3), with
  `ε_X = 1, 0, -1` as `X` points out of `D`, is tangent, points in; (6.4): `ε_X = -sgn Xⁿ` in a chart of type (iii).
* Proof, pp. 422–423: a partition of unity subordinate to an atlas of charts of the three types; Case I, II, III.
* (6.5)–(6.6), p. 424: with a Riemann metric, `ρ = j dV`, `div⟨X, j dV⟩` and the form `∫_D div⟨X, j dV⟩ = ∫_{∂D} j (X, n) dS`.

## Statement (`Lightlike/Spacetime/EHManifold/ManifoldDivergence.lean`)

`divergence_theorem_manifold`: `M` a second countable Hausdorff manifold modelled on `ℝⁿ⁺¹`, `g` a metric of any
signature (`NondegMetric`), `leviCivita g` its Levi-Civita connection, `X` a smooth vector field vanishing outside a
compact `K`, `D` measurable with, near every point of its closure, `D = {u ≥ 0}` for a `C²` function `u` on `M` with
`du ≠ 0` where `u = 0`. Then there are a smooth partition of unity `ψ_a` (finitely many, each supported in the chart domain at
`c_a`, `Σ ψ_a = 1` on `K`) and, in each chart, finitely many graph charts with cut-offs `ρ_{ab}` (as in
`RegularDomainDivergence.lean`, on the chart image of `D`), with

`∫_D div X d vol_g = -Σ_a Σ_b σ_{ab} · graphFlux(γ_{ab}, i_{ab}, ρ_{ab} · √|g_a| (ψ_a X)_a)`,

`div X = tr(u ↦ ∇_u X)` (`expansionM`). `divergence_theorem_manifold_density`: the same for the density `f · dV_g` (a
smooth function `f`), whose divergence is `div_g(f X) dV_g`, i.e. the theorem for the field `f X`.

Proof: the partition of unity splits `X` (`ψ_a X`, supported in a compact subset of a chart domain); the divergence is
additive (`expansionM_sum`); for one piece `∫_D div Y d vol_g = ∫_{φ(D ∩ U)} ∂ⱼ(√|g| Yʲ) dy`
(`integral_expansionM_chart`: the chart formula of the volume measure, `setIntegral_volumeMeasure_chart`, and
`√|g| ∇ₐYᵃ = ∂ⱼ(√|g| Yʲ)`, `sqrt_det_mul_expansion`, from `pd_sqrt_abs_det`); `u ∘ φ⁻¹` is a defining function of the chart
image of `D` (`chart_defining_function`); the divergence theorem in `ℝⁿ⁺¹` with its hypothesis on the support of the field
(`LocalDivergence.lean`, the proof of `RegularDomainDivergence.lean` with the hypothesis localised) gives the flux
(`exists_chart_flux`).

## Differences from Theorem 6.1

* representation: the density is the volume density `√|g|` of a given metric (the form (6.6) of the source); a density
  `ρ = f dV_g` is `divergence_theorem_manifold_density` (`div⟨X, f dV_g⟩ = div_g(f X) dV_g`).
* representation: the domain is given near each point of its closure by a defining function on `M` (`D = {u ≥ 0}`, `du ≠ 0`
  where `u = 0`), equivalent to the charts of types (ii)/(iii) of the Definition p. 419 (a chart of type (iii) gives
  `u = αⁿ`; conversely the inverse function theorem gives a chart from `u`).
* representation: the boundary integral `∫_{∂D} ε_X ρ_X` is written in charts with a partition of unity and, in each
  chart, in graph charts of the boundary, as the source defines the integral of a density over the manifold `∂D`
  (Theorem 3.1); no surface measure or unit normal appears.
* convention: the three cases of the proof pp. 422–423 are encoded by a sign `σ ∈ {1, -1, 0}`.
* stronger: `X` is smooth and the defining functions are `C²`; `D` need not be bounded.

No registry entry: the source is a book whose locations `sources.py` cannot verify (no arXiv text, no chapter DOI in the
recorded edition).
