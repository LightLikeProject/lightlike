# Fermionic Shale: plan (OP2, infinite modes)

Setting: Fock space `Γ_a(Z)` with creation `creW`, annihilation `annW` and field `fockField` (FermiFockGeneral.lean).
A Bogoliubov map is a real-linear bijection `R` of `Z` with `Re⟪Rw, Rw'⟫ = Re⟪w, w'⟫`, `R = α + β` with `α` linear and
`β` antilinear. It is implemented if a unitary `U` has `U φ(w) = φ(R w) U`.

Sufficiency (β Hilbert-Schmidt implies implemented):

1. Vacuum to implementer. If `w ↦ φ(R w)` has a unit vector `Ω'` killed by every `b(w) = (φ(Rw) + i φ(R(iw)))/2`, then
   the wedge vectors `b*(e_{s1}) ... b*(e_{sp}) Ω'` are orthonormal (CAR induction). By irreducibility (R bijective) they
   span a dense set, which gives a unitary `U` with `U B(S) = b*(e_S) Ω'`, and `U` implements `R`.
2. Existence of `Ω'`. `P_F = ∏_{k∈F} b_k b_k*` are commuting projections, decreasing in `F`, and `b_k` commutes with
   `b_l b_l*` for `k ≠ l`. Bonferroni: `⟨v, P_F v⟩ ≥ ‖v‖² − ∑_{k∈F} ‖b_k v‖²`. For the vacuum, `∑ ‖b_k Ω‖² = ‖β‖²_HS`.
   So `Ω' = lim P_F v` is nonzero when `‖β‖_HS < 1`. For general HS `β`, first compose with a finite product of
   reflections `φ(u)` (each implemented by the field operator), which reduces to the case `‖β‖_HS < 1`.
3. Necessity: `⟨Ω', N Ω'⟩ = ‖β‖²_HS`, with the finiteness of the particle number to be derived from the implementer.

Status:

* Step 1 done: `CARShale.exists_implementer` (vacuum to unitary, every `R` with a unit vacuum).
* Step 2 done for `‖β‖²_HS < 1` only: `CARProjections.norm_sq_PF_ge` (Bonferroni), `CARShale.exists_vacuum_of_small`,
  `CARShale.fermionic_shale_of_small`.
* Step 2 for a general Hilbert-Schmidt `β` is open. The vacuum overlap `⟨Ω₀, P_F Ω₀⟩` can vanish (a particle-hole swap of one
  mode), so a different test vector is needed. The bound `⟨v, P_F v⟩ ≥ ‖P_{F₀} v‖² − ∑_{k∉F₀} ‖b_k v‖²` does not close the
  argument by itself.
* Step 3 (necessity) not started.

## Plan for the general Hilbert-Schmidt case (24 Nov)

Bonferroni alone cannot work (a tail below 1 is needed relative to a vector of norm possibly 2^-n). The route that does:

1. `K = β*β` is a compact positive complex-linear operator when `β` is Hilbert-Schmidt. Take an orthonormal eigenbasis
   `e_k`, `K e_k = λ_k e_k` (`Spectral/Compact.lean`, `exists_hilbertBasis_eigenvectors`). The vectors `β e_k` are orthogonal
   with `‖β e_k‖² = λ_k`; put `f_k = β e_k / √λ_k`.
2. Transformed modes of this basis: `a'_k = a*(β e_k) + a(α e_k)`. R orthogonal gives `⟨α e_k, β e_l⟩ = -⟨α e_l, β e_k⟩`, and since
   `α e_k` lies in the `1 - λ_k` eigenspace of `β β*` the pairing `⟨α e_k, f_l⟩` vanishes unless `λ_l = 1 - λ_k`.
3. `F₀ = {k : λ_k ≥ 1/2}` closed under partners (`λ_l = 1 - λ_k`) is finite. For `k ∉ F₀`, `a*(f_k)` anticommutes with every
   `a'_l` and with every `c'_l` for `l ≠ k`, and `{c'_k, a*(f_k)} = √λ_k`. Hence for `u = P_D P_{F₀} W Ω₀` with `D ∌ k`,
   `‖a'_k u‖² ≤ λ_k ‖u‖²`, so `‖P_{D ∪ k} v‖² ≥ (1 - λ_k) ‖P_D v‖²`: a relative bound.
4. `W` is a product of the fields `φ(R e_l)`, `l ∈ F₀`, chosen so that `‖P_{F₀} W Ω₀‖² ≥ 2^{-|F₀|}` (one mode at a time:
   `‖P_k v‖² + ‖n_k v‖² = ‖v‖²` and `p_k` swaps them).
5. Then `‖P_s W Ω₀‖² ≥ 2^{-|F₀|} ∏ (1 - λ_k) ≥ 2^{-|F₀|} exp(-2 h) > 0` for every finite `s`, `exists_fixed_of_decreasing_projections`
   gives the vacuum, `exists_implementer` the unitary. The mode family must be generalised from the Fock basis `b` to a second
   orthonormal family `e` (the vacuum killed by `a'_{e_k}` for an orthonormal basis is killed for all vectors).
