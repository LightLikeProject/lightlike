# T-HA6 stage 5: draft of the classification statement (NOT locked; for the owner's agreement)

18 November 2026, branch `spinfoam/ha6-poincare`. Scope (owner, 22:3x): the restricted Poincaré group only; Wigner 1939 and
Mackey 1952 are historical references, not compared sources.

## Compared sources and what each states

| Source (version, location) | What it states | What it does not prove |
| --- | --- | --- |
| Bekaert–Boulanger, arXiv:hep-th/0611263v2 (13 June 2021), §3.3 "Classification", table on page 13, text pages 13–15 | the four orbit types and little groups, the UIRs of `ISO(D−1,1)↑` are induced from the little group; massive `SO(D−1)`, massless `ISO(D−2)`, tachyonic `SO(D−2,1)↑`, zero momentum `SO(D−1,1)↑`; massless split into helicity / infinite-spin by the short little group; finite-component ones have compact (short) little group | a proof of exhaustion: it is a review ("reduced to the classification of the UIRs of the stability subgroup") |
| Sunder, *Notes on the imprimitivity theorem* (draft 8 April 1998), Theorem 5.1, page 21 | for `G = A ⋊ K`, `A` abelian, `K` acting regularly on `Â`: (a) `π_{χ,θ}` induced from `χ ⊗ θ` is irreducible, (b) every irreducible representation is some `π_{χ,θ}` | proofs: (a) "not very difficult", (b) "not hard now to write down"; the "ergodic and regular ⇒ concentrated on one orbit" step is stated as known |
| Landsman, arXiv:math-ph/9807030v1, Theorem 3.12.1, page 82 | Mackey's *transitive* imprimitivity theorem: covariant representations of `(G, C₀(G/H))` are induced from `H` | the non-transitive case; this is exactly the missing step |

## The statement to be formalised (draft)

Let `P̃ = ℝ^{1,3} ⋊ SL(2,ℂ)` be the universal cover of the restricted Poincaré group (`SL(2,ℂ)` acting on `ℝ^{1,3}` through the
covering `SL(2,ℂ) → SO(3,1)↑`; signature `(+,−,−,−)`). Orbits of `SO(3,1)↑` on momentum space: mass shells `H_m` (`p² = m² > 0`,
`p⁰ > 0`; and `p⁰ < 0`), forward and backward light cones, one-sheeted hyperboloids `p² = −κ²`, the origin.

**(A) Construction.** For each orbit type with standard momentum `q`, stabiliser `G_q ⊂ SL(2,ℂ)` and irreducible continuous unitary
representation `θ` of `G_q`, the representation `π_{q,θ}` on `L²(O_q, µ; H_θ)`,
`(π(a, Λ)ψ)(p) = e^{i p·a} θ(W(Λ,p)) ψ(Λ⁻¹p)`, is a continuous unitary representation of `P̃`; it is irreducible, and `π_{q,θ} ≅ π_{q',θ'}`
iff the orbits agree and `θ ≅ θ'`. For the massive orbit `G_q = SU(2)` and `θ = spinRep n` (`Lightlike/SU2`, `spinRep_complete`);
`P² = m²`, `W² = −m² s(s+1)` (`s = n/2`); for the massless orbit `G_q` is the double cover of `E(2)`, the helicity representations
have the translation part acting trivially and `W = h P`.

**(B) Exhaustion (the deep part).** Every strongly continuous irreducible unitary representation of `P̃` on a separable Hilbert
space is equivalent to some `π_{q,θ}`; those with the joint spectrum of the translations contained in the closed forward cone
(positive energy) are exactly the massive (`m > 0`), massless, and zero-momentum ones.

## What (B) needs, and where it is not in a source

1. Spectral measure of the translation group on `ℝ^{1,3}` (SNAG / Stone for `ℝ⁴`): to be checked against what
   `Lightlike/OperatorAlgebras` (the Stone existence pieces) already has.
2. Gap (ii): regularity of the action of `SO(3,1)↑` on momentum space: the Borel map `p ↦ (p², sign p⁰, [p = 0])` separates the
   orbits (to be proved; the integrator's idea).
3. Gap (i): an ergodic quasi-invariant measure of a regular action is concentrated on one orbit (stated without proof in Sunder
   p. 20; a measure-theoretic proof from the Borel cross-section, to be written).
4. The imprimitivity theorem in the form of Sunder Theorem 5.1 (b) (Landsman's 3.12.1 is the transitive case, applied after
   steps 2 and 3 reduce to one orbit `G/H = O_q`).
5. The induced-representation construction on `L²(O_q, µ; H_θ)` with an invariant measure `µ` on the orbit (Lorentz-invariant
   measure on the mass shell / light cone), and the cocycle identity for `W(Λ,p)`.

## Proposal for the lock

Lock (A) as the statement of T-HA6 stage 5 first (construction, unitary, irreducible, inequivalent, Casimirs): all its ingredients are
in Mathlib/Physlib/the repo except the induced-representation machinery. Keep (B) as a separate statement, to be locked only when
items 1–5 are planned; if the owner wants (B) as part of T-HA6, it is a multi-week piece of work and is not a "proof from sources"
(steps 2, 3, parts of 4 and 5 are mine to write). A weaker version needs two recorded full-proof attempts (owner's 17:10 rule).
