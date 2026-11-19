# Full dΓ (any Hilbert space Z, h ∈ B(Z)): plan

Domain. The finite-particle space Γ_fin = ⊕ₙ^alg Γₙ, Γₙ = closed span of the wedges B S, |S| = n (FermiFockGeneral's
ℓ²(Finset ι) model). dΓ(h) maps Γₙ → Γₙ; a*(w) maps Γₙ → Γₙ₊₁ and a(w) maps Γₙ → Γₙ₋₁, so Γ_fin is invariant and the
commutators [dΓ(h), a*(w)] = a*(hw), [dΓ(h), a(w)] = -a(h*w), [dΓ(h₁), dΓ(h₂)] = dΓ([h₁, h₂]) make sense on Γ_fin.

The bound ‖dΓₙ(h)‖ ≤ n ‖h‖ without a Hilbert tensor product:
1. Z^⊗n in coordinates: ℓ²(Fin n → ι) for a Hilbert basis b of Z indexed by ι.
2. One slot: ℓ²(ι × M) ≅ ℓ²(M, Z) (Mathlib's lp (fun _ : M => Z) 2), ψ ↦ (m ↦ ∑ₖ ψ(k, m) bₖ), an isometry
   (∑ₘ ‖∑ₖ ψ(k, m) bₖ‖² = ∑ₘ ∑ₖ |ψ(k, m)|²). On ℓ²(M, Z), h ⊗ 1 is ψ ↦ h ∘ ψ, of norm ≤ ‖h‖ (slotMap, norm_slotMap_le).
3. Slot j: conjugate by the permutation unitary of Fin n swapping 0 and j.
4. Antisymmetric vectors: Γₙ ≅ the antisymmetric part of ℓ²(Fin n → ι) (B S ↦ (n!)^{-1/2} ∑_σ sgn σ e_{σ(S)}), and
   Σⱼ hⱼ restricted there is n Pₐ h₀ Pₐ, so ‖dΓₙ(h)‖ ≤ n ‖h‖.

What a genuine Z^⊗n would need instead: the completed Hilbert tensor product (inner product on the algebraic tensor
product, completion, universal property for bounded operators h₁ ⊗ h₂ with ‖h₁ ⊗ h₂‖ = ‖h₁‖ ‖h₂‖). Mathlib has the
algebraic TensorProduct and its inner product for finite-dimensional factors, not the completion; the coordinate model
above sidesteps it at the cost of a fixed Hilbert basis.

Pieces: (D1) slotMap and the isometry ℓ²(ι × M) ≅ ℓ²(M, Z); (D2) slot permutations and the antisymmetrizer on
ℓ²(Fin n → ι), the embedding Γₙ → antisymmetric part; (D3) dΓₙ(h) and the bound; (D4) dΓ(h) on Γ_fin (a LinearPMap)
and the commutators.

Simplification found while drafting D1: on ℓ²(Fin n → ι) each slot operator hⱼ is a reindexing (by the equivalence
(Fin n → ι) ≃ ι × (Fin (n-1) → ι) through slot j) of slotMap h, so ‖hⱼ‖ ≤ ‖h‖ and ‖∑ⱼ hⱼ‖ ≤ n ‖h‖ by the triangle
inequality alone. The antisymmetrizer is needed only to transport ∑ⱼ hⱼ to FermiFockGeneral's Γₙ along the isometric
embedding Eₙ : Γₙ → ℓ²(Fin n → ι) (dΓₙ(h) = Eₙ* (∑ⱼ hⱼ) Eₙ, still ≤ n ‖h‖), and the commutators need Eₙ₊₁ a*(w) Eₙ*
in the same model (D4).

Status: D1 and D3 are built (`SecondQuantSlot.lean`: `slotMap`, `slotOp`, `dGammaTensor`, `norm_dGammaTensor_le`).

D2, design. For `ι` linearly ordered (as in `FermiFockGeneral`) and `f : Fin n → ι` injective, Mathlib's `Tuple.sort f` is the
permutation `σ` with `f ∘ σ` monotone, so `f ∘ σ` is the increasing enumeration of `image f`; the sign of `f` is
`sign (Tuple.sort f)`. The embedding is `Eₙ ψ f = (n!)^{-1/2} sign(f) ψ(image f)` for injective `f` and `0` otherwise. It is
isometric on `Γₙ` because every `n`-element `S` is the image of exactly `n!` injective `f` (the bijections `Fin n ≃ S`), all
with `|sign| = 1`. Pieces: (D2a) `sign` of an injective tuple and its behaviour under a permutation of `Fin n`
(`sign (f ∘ τ) = sign τ · sign f`); (D2b) the fibre count `#{f injective | image f = S} = n!`; (D2c) `Eₙ` as a linear isometry
from the `n`-particle part of `ℓ²(Finset ι)` into `ℓ²(Fin n → ι)`, using the fibre count for the `HasSum` of `‖Eₙ ψ‖²`.

Status: D2 and D3 are built (`SecondQuantWedge.lean`: `tupleSign`, `card_enum`, `embCLM` isometric on the `n`-particle
vectors, `dGammaFock n h = Eₙ₊₁* (∑ⱼ hⱼ) Eₙ₊₁` with `norm_dGammaFock_le`: `‖dΓₙ₊₁(h)‖ ≤ (n + 1) ‖h‖` for every bounded `h`).

D4, design. Approximation by finite-rank `h` does not reach a general bounded `h` (the finite-rank operators are not dense
in `B(Z)` in norm, and the bound gives no strong convergence), so the commutators are proved as operator identities on the
coordinate side: (D4a) the antisymmetrizer `A Φ (f) = (n!)⁻¹ ∑_σ sign σ Φ(f ∘ σ)`, a projection commuting with every
`∑ⱼ hⱼ`; (D4b) `Eₙ Eₙ* = A` and `Eₙ* Eₙ = 1` on the `n`-particle vectors; (D4c) creation on the tensor power,
`C_w Φ (f) = b.repr(w)(f 0) Φ(f ∘ succ)` (`w ⊗ Φ`), with `[∑ⱼ hⱼ, C_w] = C_{hw}` (slot `0` against the others);
(D4d) the core coefficient identity `Eₙ₊₁ a*(w) = √(n+1) A C_w Eₙ` (`FermiFockGeneral.creW` against the signs of the
enumerations); then `[dΓ(h), a*(w)] = √(n+1) Eₙ₊₁* A C_{hw} Eₙ = a*(hw)`, `[dΓ(h), a(w)] = -a(h* w)` by adjoints, and
`[dΓ(h₁), dΓ(h₂)] = dΓ([h₁, h₂])` from `[∑ⱼ h₁ⱼ, ∑ⱼ h₂ⱼ] = ∑ⱼ [h₁, h₂]ⱼ` on the tensor side.

Status: D4 is built. `SecondQuantWedge.lean`, on `FermiFockGeneral`'s `ℓ²(Finset ι)`: the sign of a cons tuple
(`tupleSign_cons`, from the inversion product), the core identity `embL_creW`, `Eₙ Eₙ* = A` (`embCLM_adjoint_apply`),
`Eₙ* Eₙ = 1` on the `n`-particle vectors (`adjoint_embCLM_embCLM`), `dΓ(h)* = dΓ(h*)` (`adjoint_dGammaFock`), different slots
commute (`slotOp_comm`, checked on the basis vectors `clm_ext_single`), and on every particle sector `dGammaFock_creW`,
`dGammaFock_zero_creW`, `annL2_dGammaFock`, `annL2_dGammaFock_zero`, `dGammaFock_comm`.

The source's own form (`SecondQuantFock.lean`). Dereziński defines `Γⁿ_{s/a}(Z) = Θⁿ_{s/a} ⊗ⁿZ` with
`Θⁿ_{s/a} = (n!)⁻¹ ∑_σ χ(σ) Θ(σ)` (Section 5.3, p. 20), `a*(w)Ψ = √(n+1) Θ_{s/a}(w ⊗ Ψ)` on `Γⁿ_{s/a}` and
`a(w) = a*(w)*` (Section 5.7, p. 22). In coordinates `Θ(σ)` is `P_σ Φ (f) = Φ(f ∘ σ)`, since `Θ(σ) e_f = e_{f ∘ σ⁻¹}`.
`theta` is an orthogonal projection (`theta_theta`, `adjoint_theta`); `creF = √(n+1) Θₙ₊₁ (w ⊗ Θₙ ·)` agrees with the
source's `a*(w)` on `Γⁿ` (`creF_of_theta`), and `annF = creF*` maps into `Γⁿ` (`theta_annF`). Because `∑ⱼ hⱼ`
commutes with every `P_σ`, Theorem 18 (4), (2) and Theorem 13 (1) are identities of bounded operators between
consecutive tensor powers, for bosons and fermions alike (`dGammaT_creF`, `dGammaT_annF`, `dGammaT_comm`). In the
bosonic case `a*(w)` is unbounded on `Γ_s(Z)`, but it is bounded from `Γⁿ_s` to `Γⁿ⁺¹_s` (norm at most `√(n+1) ‖w‖`).
So the identities on the finite-particle space `⊕ₙ^alg Γⁿ` are exactly these sector-wise ones. The fermionic case agrees
with `ℓ²(Finset ι)`: `embCLM_creW` and `embCLM_dGammaFock` carry `FermiFockGeneral`'s `a*(w)` and `dGammaFock` to `creF`
and `dGammaT`.

Differences against Theorem 18 (2), (4) and Theorem 13 (1):
* representation: `⊗ⁿZ` is `ℓ²(Fin n → ι)` for a Hilbert basis `(bᵢ)_{i ∈ ι}` of `Z`, with `ι` linearly ordered (every
  Hilbert space has a Hilbert basis, and every index set carries a linear order). The order is used only to compare with
  `ℓ²(Finset ι)`.
* representation: the operators are bounded maps between consecutive tensor powers, and the identities are stated
  sector by sector, not for the closures on `Γ_fin`. `dΓ(h)` keeps the particle number and `a*(w)`, `a(w)` shift it by
  one, so on the algebraic direct sum `Γ_fin` the source's identities are the sums of the sector identities.

