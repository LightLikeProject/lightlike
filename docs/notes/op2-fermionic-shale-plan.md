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
