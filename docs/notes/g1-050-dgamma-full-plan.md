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
