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

## Attempts at the full statement (any Hilbert space `Z`, `h ∈ B(Z)`)

Attempt 1, basis-free algebra (`SecondQuantRank.lean`, built). `Z` is any complex inner product space, `a*` linear and
`a` antilinear on `Z` with `a(w) a*(v) = ⟪w, v⟫ + ε a*(v) a(w)` and the (anti)commutation of the `a*` and of the `a`
(`IsFieldAlgebra`). For finite-rank `h = ∑ₖ |uₖ⟩⟨vₖ|`, `dΓ(h) = ∑ₖ a*(uₖ) a(vₖ)` and Theorem 18 (2), (4) and Theorem 13 (1)
hold (`dGammaRank_commutator_creation`, `dGammaRank_commutator_annihilation`, `dGammaRank_commutator`, with
`rankOp_comp`: the product of the two finite-rank operators). This removes the restriction `Z = ℂⁿ`. It stops at
`h` of infinite rank: `dΓ(h)` is then an infinite sum with no limit in an abstract algebra, and no normed completion
helps, because `dΓ(1) = N` has the eigenvalue `n` on the `n`-particle space for every `n ≤ dim Z`, so it is unbounded
and lies in no normed algebra containing the field operators.

Attempt 2, the Fock space in coordinates (`FermiFockGeneral.lean`'s `Γ = ℓ²(Finset ι)` for a Hilbert basis `(eᵢ)` of
`Z`, `B S` the wedge of the `eᵢ`, `i ∈ S`). The coefficient formula `(dΓ(h)ψ)(T) = ∑_{i ∈ T} ∑_{j ∉ T∖{i}} hᵢⱼ s(i, j, T)
ψ(T∖{i} ∪ {j})` (`hᵢⱼ = ⟪eᵢ, h eⱼ⟫`, `s` the sign of the reordering) converges for every `ψ ∈ ℓ²`, since the rows
of a bounded `h` are in `ℓ²`, and is bounded by `|T| ‖h‖ ‖ψ‖`. The commutator needs `dΓ(h)` as an operator on a domain
invariant under `a*(w)`. The algebraic span of the `B S` is not invariant: `a*(w) B ∅` has the coefficients `⟪eⱼ, w⟫`
on all `{j}`, infinitely many nonzero for a general `w`. The natural domain is the finite-particle space `⊕ₙ Γₙ` with
`Γₙ` the closed span of the `B S`, `|S| = n`, and this needs `‖dΓ(h) ψ‖ ≤ n ‖h‖ ‖ψ‖` on `Γₙ`. That is where this attempt
stops. Summing `|(dΓ(h)ψ)(T)|²` over `|T| = n` with Cauchy-Schwarz meets, for fixed `S`, infinitely many `(T, i, j)`
with `T∖{i} ∪ {j} = S`. The estimate closes only with the weights `∑ⱼ |hᵢⱼ|²` summable over `i`, which gives
`‖dΓₙ(h)‖ ≤ n ‖h‖_HS` for Hilbert-Schmidt `h`. The bound `n ‖h‖` for a general bounded `h` comes from
`dΓₙ(h) = ∑ⱼ 1 ⊗ ⋯ ⊗ h ⊗ ⋯ ⊗ 1` on the Hilbert tensor power `Z^{⊗n}`, each term of norm `‖h‖`, and Mathlib has no
completed Hilbert-space tensor product.

Result: the line is "weaker: `h` of finite rank" (attempt 1), in place of "weaker: `Z = ℂⁿ`".
