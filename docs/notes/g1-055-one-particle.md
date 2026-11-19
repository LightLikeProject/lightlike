# G1-055: the one-particle Hilbert space of a free field

The gap row: one-particle Hilbert space of a free field, `L²` of the mass shell with a Lorentz-invariant
measure, a positive-energy unitary representation of the Poincaré group, and the Wigner classification.

## Source read

X. Bekaert, N. Boulanger, *The unitary representations of the Poincaré group in any spacetime dimension*,
arXiv:hep-th/0611263v2 (PDF text read):

| Statement in the source | Location | Content as read |
| --- | --- | --- |
| translations on momentum eigenstates | §3.1, page 9 of v2 | `U(1, a) = exp(−i P^μ a_μ)`, `U(1, a) Ψ_{q,σ} = e^{−i q·a} Ψ_{q,σ}` (signature `(−,+,+,+)`) |
| the induced action | §3.1, equations (10)–(13), pages 9–10 | `U(Λ) Ψ_{p,σ} = N(p)/N(Λp) Σ_{σ'} D_{σ'σ}(W(Λ, p)) Ψ_{Λp,σ'}`, `W(Λ, p) = L⁻¹(Λp) Λ L(p)` |
| the invariant scalar product | §3.2, Remarks, page 11 | `⟨Ψ|Φ⟩ = ∫ dᴰp δ(p² + m²) Θ(p⁰) Σ_σ Ψ*_{p,σ} Φ_{p,σ}` for `p² ≤ 0` |
| the orbits | §3.2, page 11 | the mass shell (`p² = −m²`, one sheet) and the light cone (`p² = 0`, one half) |

## Formalised

Momenta are Hermitian matrices `p⁰ + p·σ`, acted on by `SL(2,ℂ)` through `P ↦ A P Aᴴ`; Physlib's
`Lorentz.SL2C.toRestrictedLorentzGroup` identifies this with the restricted Lorentz group, and it is surjective.

1. **Invariant measures** (`Lightlike/Poincare/OneParticle.lean`): `exists_invariant_measure_massShell` and
   `exists_invariant_measure_lightCone`: nonzero measures, finite on compacts, preserved by every restricted
   Lorentz transformation (the image of the Haar measure on the shell, the image of Lebesgue measure on `ℂ²` under
   `v ↦ v vᴴ` on the cone).
2. **The representation** (`OneParticle.lean`, `OneParticleContinuity.lean`, `OneParticleRestricted.lean`):
   for every invariant measure `μ` on the mass shell finite on compacts, `V(a, A) = T(a) U(A)` on
   `L²(μ; ℂ^{n+1})`, with `(T(a) ψ)(p) = e^{i p·a} ψ(p)` and the induced spinor action `U(A)`, is a unitary
   representation of `ℝ⁴ ⋊ SL(2,ℂ)` (`poincareL2_mul`, `poincareL2_one`), strongly continuous
   (`continuous_poincareL2`). For integer spin it descends to the restricted Poincaré group `ℝ⁴ ⋊ SO⁺(1,3)`
   (`poincareR`, `poincareR_mul`), strongly continuous for its own topology (`continuous_poincareR`: the covering
   map is continuous and open by the open mapping theorem), and for spin `0` it is `(V(a, Λ) ψ)(p) =
   e^{i p·a} ψ(Λ⁻¹ p)` (`coeFn_poincareL2_scalar`).
3. **Positive energy** (`OneParticleSpectrum.lean`): the momentum projection-valued measure `E(B) = 1_{p ∈ B}`
   (`momPVM`) satisfies `T(a) = ∫ e^{i p·a} dE(p)` (`translL2_eq_integral`), so it is the joint spectral measure of
   the translation generators, and `E(B) = 0` for `B` disjoint from the closed forward cone
   (`momPVM_eq_zero_of_disjoint`).

Differences from the source (kind: representation): the group is presented through its double cover
`ℝ⁴ ⋊ SL(2,ℂ)` (half-integer spin is a representation of the cover only, as in the source); the sign convention is
`(+,−,−,−)`, so the source's `e^{−i q·a}` is `e^{i p·a}` here; the measure is any invariant measure finite on
compacts (the source's `δ(p² + m²) Θ(p⁰) dᴰp` is one of them; uniqueness up to a scalar is not stated).

## Not formalised: the Wigner classification

The classification says that every irreducible positive-energy unitary representation of the Poincaré group is
one of the induced representations, labelled by the orbit and an irreducible representation of the little group.
What stops it here, concretely:

* the SNAG theorem (a strongly continuous unitary representation of `ℝ⁴` is `∫ e^{i p·a} dE(p)` for a
  projection-valued measure `E` on `ℝ⁴`): the library has Stone's theorem for one-parameter groups and the spectral
  theorem for one self-adjoint operator, not the joint version for `ℝ⁴`; above, `E` is constructed by hand for the
  induced representations only;
* Mackey's imprimitivity theorem (a system of imprimitivity based on a transitive orbit is induced from the little
  group): not in the library;
* irreducibility of the induced representations: it needs the commutant of the translations on
  `L²(μ; ℂ^{n+1})` to be the multiplication operators by bounded matrix functions of the momentum, which is not
  formalised.

The massless representations on `L²` of the light cone are not built here: the standard lift of the cone is not
continuous (no continuous global section exists), so the multiplier is a measurable field of unitaries and the
construction of `mulL2` (which uses a continuous field) does not apply as it stands.
