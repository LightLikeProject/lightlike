# G3-073 (colour algebra): U(N) and SU(N) completeness, structure constants as traces

Lean: `Lightlike/GR/ColourAlgebra.lean` (Mathlib only).

## Mathlib and Physlib check

Mathlib has the Frobenius-type inner product on `EuclideanSpace ℂ (Fin N × Fin N)`, `OrthonormalBasis.mk`, `sum_repr'`,
`LinearIndependent.span_eq_top_of_card_eq_finrank'`, `Matrix.trace_mul_comm`, `Matrix.trace_mul_cycle`; it has no Fierz
identity or colour-ordered trace basis. Physlib: no U(N) colour algebra (its Pauli matrices are not needed; the trust check
writes them out).

## Source read (pdftotext of arXiv:1308.1697v2)

H. Elvang, Y. Huang, *Scattering Amplitudes*, §2.5:
* p. 21: generators "normalized such that Tr TᵃTᵇ = δᵃᵇ and [Tᵃ, Tᵇ] = i f̃ᵃᵇᶜ Tᶜ" (footnote 6: `f̃ᵃᵇᶜ = √2 fᵃᵇᶜ`
  against `Tr TᵃTᵇ = ½δᵃᵇ`); the colour factors `c_s, c_t, c_u` (2.65).
* p. 22: the Jacobi identity `c_s + c_t + c_u = 0` (2.66); `i f̃ᵃᵇᶜ = Tr(TᵃTᵇTᶜ) − Tr(TᵇTᵃTᶜ)` (2.67); the completeness relation
  `(Tᵃ)ᵢʲ (Tᵃ)ₖˡ = δᵢˡ δₖʲ − (1/N) δᵢʲ δₖˡ` (2.68); `f̃^{a₁a₂b} f̃^{ba₃a₄} ∝ Tr(T¹T²T³T⁴) − Tr(T¹T²T⁴T³) − Tr(T¹T³T⁴T²) +
  Tr(T¹T⁴T³T²)` (2.69); the trace basis (2.70)–(2.71).

## How each Lean statement matches

* `IsGenerators`: Hermitian with `Tr(TᵃTᵇ) = δᵃᵇ` (p. 21). `flat`, `inner_flat`, `orthonormal_flat`, `generatorBasis`: `N²` of them
  are an orthonormal basis of `M_N(ℂ)`. `expand_generators`: `X = Σₐ Tr(TᵃX)Tᵃ`.
* `fierz`: the U(N) completeness relation `Σₐ (Tᵃ)ᵢⱼ(Tᵃ)ₖₗ = δᵢₗδₖⱼ`; `fierz_su`: (2.68) with `−(1/N)δᵢⱼδₖₗ` for `N² − 1` traceless
  generators; `fierz_trace_trace`: `Σₐ Tr(XTᵃ)Tr(TᵃY) = Tr(XY)`.
* `structureConst` (`−i Tr([Tᵃ,Tᵇ]Tᶜ)`), `commutator_eq_structureConst` (`[Tᵃ,Tᵇ] = iΣ f̃ᵃᵇᶜTᶜ`), `i_mul_eq_trace_sub` ((2.67)),
  `structureConst_antisymm`, `structureConst_cyclic`.
* `structureConst_mul_sum`: (2.69) with the constant: `Σ_b f̃^{a₁a₂b}f̃^{ba₃a₄} = −(…)`; `jacobi_colour`: (2.66).
* `colourTrace`, `trace_prod_rotate` (cyclicity), `traceBasisAmplitude`: the trace basis (2.71), stated.
* Trust check: `u2Gen` (`σᵃ/√2`), `isGenerators_u2Gen`, and the U(2) completeness relation as an instance of `fierz`.

## Differences

1. Scope: the diagram-by-diagram colour decomposition (2.70)–(2.71) of the full Yang-Mills amplitude needs the Yang-Mills
   Feynman rules, which the library does not have; the trace basis (2.71) is stated (`traceBasisAmplitude`) and not derived.
   The other statements are Elvang-Huang's identities in their normalisation; (2.69)'s `∝` is made exact (factor −1).
