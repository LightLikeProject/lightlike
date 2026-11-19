# G1-050: the commutators of `dΓ` for finitely many modes

Source: J. Dereziński, *Introduction to representations of the canonical commutation and anticommutation relations*,
arXiv:math-ph/0511030 (source key `derezinski-2006`).

Read: Section 5.2, p. 19, `dΓₙ(h) = ∑ⱼ 1 ⊗ ⋯ ⊗ h ⊗ ⋯ ⊗ 1` on `⊗ⁿZ`, `dΓ(h) = ⊕ₙ dΓₙ(h)`, and Theorem 13 (1), p. 19,
`[dΓ(h₁), dΓ(h₂)] = dΓ([h₁, h₂])` for `h₁, h₂ ∈ B(Z)`; Section 5.5, p. 21, the restriction of `dΓ(h)` to `Γs/a(Z)`;
Theorem 17, p. 22 (the CCR and the CAR for `a(w)`, `a*(w)`); Theorem 18 (2), (4), p. 22, `[dΓ(h), a(w)] = -a(h* w)`,
`[dΓ(h), a*(w)] = a*(hw)`, in the bosonic and the fermionic case.

| Source | Lean |
|---|---|
| Theorem 17, p. 22: CAR, CCR for `aᵢ = a(eᵢ)`, `aᵢ* = a*(eᵢ)` | `IsModeAlgebra`, `isModeAlgebra_car`, `isModeAlgebra_ccr` |
| `dΓ(h)` for `Z = ℂⁿ` | `dGamma a ad h = ∑ᵢⱼ hᵢⱼ aᵢ* aⱼ` |
| Theorem 18 (4), p. 22 | `dGamma_commutator_creation`: `[dΓ(h), aₖ*] = ∑ᵢ hᵢₖ aᵢ* = a*(h eₖ)` |
| Theorem 18 (2), p. 22 | `dGamma_commutator_annihilation`: `[dΓ(h), aₖ] = -∑ⱼ hₖⱼ aⱼ = -a(h* eₖ)` |
| Theorem 13 (1), p. 19 | `dGamma_commutator`: `[dΓ(h₁), dΓ(h₂)] = dΓ(h₁ h₂ - h₂ h₁)` |

`[dΓ(h₁), dΓ(h₂)]` is computed from Theorem 18 (2), (4) and the Leibniz rule `[D, aₖ* aₗ] = [D, aₖ*] aₗ + aₖ* [D, aₗ]`;
`commutator_number` gives `[aᵢ* aⱼ, aₖ* aₗ] = δⱼₖ aᵢ* aₗ - δᵢₗ aₖ* aⱼ` directly.

Differences:

* representation: `dΓ(h) = ∑ᵢⱼ hᵢⱼ aᵢ* aⱼ` in an algebra whose `aᵢ`, `aᵢ*` satisfy the CAR or the CCR, instead of
  `⊕ₙ dΓₙ(h)` on the Fock space. Both satisfy `[·, a*(w)] = a*(hw)` (Theorem 18 (4); `dGamma_commutator_creation`) and
  annihilate `Ω`, and the vectors `a*(w₁) ⋯ a*(wₙ) Ω` span the finite-particle space, so the two agree there.
  `dGamma_oneMode` checks `dΓ(h) = dΓ₀(h) ⊕ dΓ₁(h) = 0 ⊕ h` on `Λ(ℂ)`.
* weaker: `Z = ℂⁿ` (finitely many modes), where the source allows any Hilbert space `Z` and `h ∈ B(Z)`.

Tests (`TestsSecondQuantFinite.lean`): one fermionic mode on `Λ(ℂ)` is a mode algebra with `ε = -1`;
`dΓ(h) = 0 ⊕ h`; the same operators are not a mode algebra with `ε = 1` (wrong input).

Reused and aligned: Physlib's `LadderSystem ℂ V d` (`PhyslibAlpha.Mathematics.LadderSystem.Basic`) is the bosonic case:
`E i j = acᵢ aⱼ`, `lie_E` (the CCR case of `commutator_number`) and `toGlHomLinear_lie` (the CCR case of
`dGamma_commutator`, on `Module.End ℂ V` with `Fin d` modes). It has no CAR, so `IsModeAlgebra` is kept;
`SecondQuantLadder.lean` aligns the two: `isModeAlgebra_ladderSystem` (a ladder system is a mode algebra with `ε = 1`)
and `dGamma_ladderSystem` (`dΓ(x) = L.toGlHomLinear x`). Mathlib has no second quantization or Fock space.
