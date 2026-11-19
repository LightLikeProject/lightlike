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
compacts (the source's `δ(p² + m²) Θ(p⁰) dᴰp` is one of them, `sourceMeasure` below; uniqueness up to a scalar is not
stated).

## Not formalised: the Wigner classification

The classification says that every irreducible positive-energy unitary representation of the Poincaré group is
one of the induced representations, labelled by the orbit and an irreducible representation of the little group.
The first step, the joint spectral measure of the translations (the SNAG theorem), is formalised
(`Lightlike/Poincare/SnagJoint.lean`): a strongly continuous unitary representation of `ℝⁿ` is
`T(a) = ∫ e^{i⟨a, p⟩} dP(p)` for a unique projection-valued measure `P` on `ℝⁿ` (`exists_jointSpectralMeasure`,
`jointSpectralMeasure_unique`; Freitag, Chapter V, §5, Theorem 5.1, p. 146, in the projection-valued-measure form of
Remarks 5.3, 5.4 and Definition 5.5, p. 147). The proof takes the Stone generators of the axis subgroups, their
commuting Cayley transforms (`SnagCommute.lean`), and the joint spectral measure of these through Gelfand duality
(`SnagGelfand.lean`). The second step is formalised as well (`Lightlike/Poincare/OneOrbit.lean`): for a
strongly continuous unitary representation `V(a, A)` of `ℝ⁴ ⋊ SL(2,ℂ)` (`IsPoincareRep`) the momentum measure is
covariant (`covariant_jointSpectralMeasure`, `SnagCovariance.lean`); for an irreducible `V` the projection of an
invariant Borel set of momenta is `0` or `1` (`momPVM_invariant_eq_zero_or_one`; Freitag, Lemma 7.1, p. 150); and
under positive energy (the closed forward cone carries the momentum measure) the measure sits on one orbit: a mass
shell `p² = m²`, `m > 0`, the light cone, or `{0}` (`exists_orbit`; Proposition 7.2, p. 151). What stops the rest,
concretely:

* Mackey's imprimitivity theorem (a system of imprimitivity based on a transitive orbit is induced from the little
  group): not in the library. Its first step is formalised for the mass shells (`OrbitMeasureClass.lean`,
  `momPVM_eq_zero_of_null`): a momentum measure carried by a shell is absolutely continuous with respect to the image
  of the Haar measure; the decomposition of `H` over the orbit and the passage to a representation of the stabiliser
  are not.

The massless representations of helicity `n/2` act on `L²(ν)` of the forward light cone, for every invariant
measure `ν` (`ConeL2.lean`). The standard lift of the cone is discontinuous on the half-line `P₀₀ = 0` (no continuous
global section exists), so the helicity factor is only measurable; that half-line is null for every invariant
s-finite `ν` (`ConeNull.lean`, `measure_alphaC_eq_zero`: such a `ν` has the null sets of the image of the Haar
measure, and `{A : A₀₀ = 0}` is Haar-null because its right translates by the rotations `u_θ`, `0 ≤ θ < π`, are
pairwise disjoint), and the representations are strongly continuous when `ν` is finite on compacts
(`ConeContinuity.lean`, `continuous_poincareCone`). They are irreducible for every invariant σ-finite `ν`
(`IrreducibleMassless.lean`, `irreducible_massless`, `commutant_eq_scalar_cone`): the commutant of the translations
of the cone is the multiplications by measurable functions (`CommutantCone.lean`), the helicity factor is
unimodular, so such a function is invariant, and invariant functions are almost everywhere constant. The source's
measure `δ(p²) Θ(p⁰) d⁴p`, which is `d³p / (2|p|)` in the chart `p ↦ (|p|, p)` (`coneSourceMeasure`), is half the image
of the Lebesgue measure under the light-cone coordinates `(w, t) ↦ [[|w|² e^{-t}, w], [w̄, e^t]]`, hence invariant
(`ConeSourceMeasure.lean`, `measurePreserving_coneSourceMeasure`), and the massless representations on
`L²(d³p / 2|p|)` are irreducible (`irreducible_massless_coneSourceMeasure`).

## Toward the Wigner classification

Source read: E. Freitag, *Unitary representations of the Poincaré group, Wigner classification* (lecture notes,
Heidelberg): Chapter IV, §2, p. 126 (the orbits of `SL(2,ℂ)` on `ℝ⁴` and their little groups; only the orbits of
`(m, 0, 0, 0)`, `m > 0`, with little group `SU(2)`, and of `(1, 1, 0, 0)`, with the double cover of `ISO(2)`, give
the positive-energy representations of physical interest); Chapter V, §4, Definitions 4.1, 4.2, Proposition 4.4
(systems of imprimitivity), pp. 139–140; §5, Theorem 5.1 (Stone's theorem for `ℝⁿ` in multiplication form),
Definition 5.5, Lemma 5.6, pp. 146–147; §6, Assumption 6.1 and Theorem 6.2 (Mackey), p. 149, Theorem 6.4 (the
irreducible unitary representations of `ISO(2)`), p. 150; §7, Lemma 7.1, Proposition 7.2 (ergodicity and concentration on
one orbit), pp. 150–151; Appendix VI.1 (the spectral theorem for `ℝ`), pp. 152–153.

Scope: the orbit `p = 0` (whose representations are those of `SL(2,ℂ)` itself, Bekaert–Boulanger §3.2, Remark,
PDF page 13: "the zero-momentum representations are essentially UIRs of the little group") is not part of this row.

Formalised for the irreducibility of the induced representations (the first half of Freitag's Theorem 6.2 for the
massive orbit):

* the canonical system of imprimitivity (`Imprimitivity.lean`, `isSystemOfImprimitivity_inducedL2`);
* an operator commuting with the translations commutes with every Schwartz function of the momentum
  (`CommutantTranslations.lean`, Fourier inversion and Fubini) and with every momentum projection `E(S)`
  (`CommutantPVM.lean`, smooth approximations of open sets and the `π`-`λ` theorem);
* such an operator is the multiplication by a strongly measurable field of matrices
  (`CommutantDecomposition.lean`, `exists_matField_of_commute_transl`);
* **irreducibility of the massive representations** (`IrreducibleMassive.lean`): for every `SL(2,ℂ)`-invariant
  σ-finite measure `μ` on the shell, every bounded operator commuting with all `T(a)` and `U(A)` is a scalar
  (`commutant_eq_scalar`), and every closed subspace invariant under them is `0` or everything
  (`irreducible_massive`). Every such `μ` has the null sets of the image of the Haar measure
  (`measure_mul_haar_univ`: `μ(S) · haar(SL(2,ℂ)) = shellMeasure(S) · μ(shell)`); the matrix field is covariant, its
  transport to `SL(2,ℂ)` is almost everywhere invariant under left translations and hence almost everywhere constant
  (ergodicity of the left regular action), and right translation by `SU(2)` with Schur's lemma makes it a scalar.

* **the source's measure** (`ShellSourceMeasure.lean`): `δ(p² − m²) Θ(p⁰) d⁴p`, which is `d³p / (2ω_p)` in the chart
  `p ↦ (ω_p, p)` (`sourceMeasure`), is half the image of the Lebesgue measure of `ℂ × ℝ` under the light-cone
  coordinates `(w, t) ↦ [[(m² + |w|²) e^{-t}, w], [w̄, e^t]]` (`sourceMeasure_eq`); upper triangular matrices and the
  Weyl element act on these coordinates by Lebesgue-preserving maps and generate `SL(2,ℂ)` (Bruhat decomposition),
  so `d³p / (2ω_p)` is invariant (`measurePreserving_shellAct_sourceMeasure`) and the massive representations on
  `L²(d³p / 2ω_p)` are irreducible (`irreducible_massive_sourceMeasure`, `commutant_eq_scalar_sourceMeasure`).

Remaining for the converse (every irreducible positive-energy representation is induced): the SNAG theorem for `ℝ⁴` and Mackey's
imprimitivity theorem, and the representations of the `ISO(2)` cover including the continuous-spin series.
