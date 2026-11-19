# G3-064: SU(2, 2) on twistor space and the Poincaré group as the stabilizer of the infinity twistor

Lean: `Lightlike/GR/TwistorConformal.lean` (on `Lightlike/GR/ComplexMinkowski.lean`, G3-061).

## Sources read (pdftotext of the arXiv PDFs)

* T. Adamo, *Lectures on twistor theory*, arXiv:1712.02196:
  * §2.1, p. 13: in Lorentzian signature the incidence relations are modified "by including a factor of 'i'": `μ^α̇ = i x^{αα̇} λ_α` (2.2).
  * p. 14: the inner product `Z · Z̄ = [μ λ̄] + ⟨μ̄ λ⟩` (2.5) "has signature (+2, −2) ... the inner product is an SU(2, 2)-invariant";
    `Z · Z̄ = i (x − x†)^{αα̇} λ_α λ̄_α̇` (2.6); "x ∈ M if and only if x^{αα̇} = (x^{αα̇})†. Therefore, any line X which corresponds to a
    point in real Minkowski space-time must be contained in PN" (2.7).
  * §2.3, pp. 18–21: the linear action of the complexified conformal group SL(4, ℂ) (2.21)–(2.23); "IAB is the ingredient required to break
    conformal invariance on twistor space"; the infinity twistor (2.29) with `I_AB X^AB = ⟨λ₁ λ₂⟩`; `I_AB X^AB = 0` iff the points of `X` have
    `λ = 0`.
* M. Atiyah, M. Dunajski, L. Mason, *Twistor theory at fifty*, arXiv:1704.07464, §2.1, p. 7: the `(+ + − −)` Hermitian form `Σ` on `C⁴`;
  "The orientation–preserving endomorphisms of the twistor space which preserve Σ form a group SU(2, 2) which is locally isomorphic to
  the conformal group SO(4, 2)"; real points give lines in `PN`.
* A. Bette, *Twistors, special relativity, conformal symmetry and minimal coupling — a review*, arXiv:hep-th/0402150, §3: the Lorentz
  group acts block diagonally (3.1), p. 11; the SU(2, 2)-invariant form (3.7) of signature `+ + − −` and the translations (3.10), p. 14;
  "restricting ... the SU(2, 2) matrix group action to its 'Poincaré' subgroup by putting C_{A′B} = 0 and d = 1 in (3.5) ... This defines
  completely (the covering group of the identity connected part of) the Poincaré group", p. 16.
* Not read: Huggett–Tod, *An introduction to twistor theory* (book, the area's canonical source); nothing is compared with it.

## How each Lean statement matches

* `twistorInc X l = (Xᵀ λ, λ)`: Adamo's (1.23) (as in G3-061), not (2.2): representation, see below.
* `twistorNorm`, `twistorHerm = [[0, −i], [i, 0]]`: the form `Σ(Z) = i(λ̄ · μ − μ̄ · λ)`, Hermitian of signature `(2, 2)`; for the twistor
  `(i μ, λ)` of (2.2) it is Adamo's (2.5) with the spinor contractions written in components.
* `twistorNorm_inc`: (2.6) in components. `twistorNorm_inc_eq_zero_iff`, `twistorLine_null_iff`: the twistor line of `x` lies in the null
  twistors iff `x` is real. Adamo states "⇐" (2.7); "⇒" is added.
* `IsSU22`: preserves the form, determinant one (ADM p. 7, Adamo p. 14). `IsSU22.twistorNorm_mulVec`.
* `infinityForm`, `infinityForm_inc`: (2.29) and `I_AB X^AB = ⟨λ₁ λ₂⟩`, p. 21.
* `poincareTwistor L a = [[L̄, aᵀ (Lᵀ)⁻¹], [0, (Lᵀ)⁻¹]]`, `poincareTwistor_inc`: it maps the twistor line of `X` to that of `L X L† + a`;
  `poincare_isHermitian`: on the real slice this is Physlib's `SL2C.toSelfAdjointMap` followed by a real translation (Bette (3.1), (3.10)).
* `isSU22_and_fixesInfinity_iff`: the stabilizer of `I` in SU(2, 2) is exactly `{T(L, a) : L ∈ SL(2, ℂ), a Hermitian}`, Bette's Poincaré
  subgroup (p. 16) in our coordinates.

## Differences

1. Representation: the incidence relation is (1.23) without the factor `i` of (2.2); the form carries the `i` instead.
2. Representation: twistors are `Fin 2 ⊕ Fin 2 → ℂ` (blocks `(μ, λ)`); G3-061's `Fin 4 → ℂ` twistors are related by `finSumFinEquiv`
   (`incidence_comp_finSumFinEquiv`).
3. The equality "stabilizer of `I` in SU(2, 2) = Poincaré group" is proved here in matrix form. Adamo says `I` breaks conformal
   invariance and Bette defines the Poincaré subgroup by the block form; neither source states the equality as a theorem at the
   locations read. The Poincaré group appears as `SL(2, ℂ) ⋉ {Hermitian a}` (the double cover of the restricted Poincaré group);
   the identification with Lorentz matrices is Physlib's `SL2C.toLorentzGroup` and is not restated here.
