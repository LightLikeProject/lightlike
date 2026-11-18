# T-HA6 Wigner classification of the Poincaré group: reuse check and plan

18 November 2026, branch `spinfoam/ha6-poincare` (from main 473d1011). Written before any Lean for HA6.

## HA4 already exists (so HA6's dependency is met)

`Lightlike/SU2/` (API map `Lightlike/SU2/API-map.md`): `SU2.spinRep` (the spin-`n/2` representation, unitary, dimension
`n+1`), `SU2.spinRepresentation_isIrreducible`, `SU2.exists_exp_eq`, `SU2.lie_product`, `SU2.dSpin_E/F/H` (link to
Physlib's `sl₂`-module `V(n)`), and `SU2.spinRep_complete` (`Lightlike/SU2/Completeness.lean`: every continuous irreducible
finite-dimensional representation of SU(2) is equivalent to a spin representation, proved through the Lie algebra, not
through Peter–Weyl). Remaining HA4 gap (not mine to start now): the link to 6j symbols (`Lightlike/Recoupling/`, `Spin4/`).
`docs/tasks/tasks.yaml` T-HA4 has empty `checks`; its source rows are Hall 2015 Ch. 4 / Martin-Dussaud 2019 §4.1 /
Bröcker–tom Dieck Ch. II.

## Reuse check for HA6

* **Physlib** (`.lake/packages/Physlib/PhyslibAlpha/Relativity/`): `PoincareGroup d` (`Poincare/Basic.lean:75`, a structure
  `⟨translation : SpaceTime d, lorentz : LorentzGroup d⟩` with the semidirect-product `Group` instance, `IsOrthochronous`,
  action on `SpaceTime d` and on functions), `LorentzGroup d` (`LorentzGroup/Basic.lean`, boosts, invariants),
  `SL2C/`, `PauliMatrices/`, `MinkowskiMatrix.lean`. Nothing on unitary representations, orbits of momentum space, little
  groups or induced representations (grep for `LittleGroup`, `Wigner`, `massShell`: no hit in Physlib or Mathlib).
* **Mathlib**: no Poincaré group, no Mackey theory, no induced unitary representations.
* **In the repo**: `Lightlike/Lorentz/` (`SL2C`, `SL2R`, `Signature`, `Mobius`, `PrincipalSeries`, Haar measure and Plancherel
  for `SL(2,ℂ)`), `Lightlike/SU2/`, `Lightlike/Spin4/`.
* Tau Ceti and physicslib4: not yet checked (to do before the first Lean file).

## Source read (opened and read, 18 November 2026)

X. Bekaert, N. Boulanger, *The unitary representations of the Poincaré group in any spacetime dimension*, arXiv:hep-th/0611263v2
(13 June 2021), https://arxiv.org/pdf/hep-th/0611263 (text extracted with `pdftotext`; the full text was available).
Read: §3.1 "Induced representations" (equations (10)–(13): standard boost `L(p)`, `Ψ_{p,σ} = N(p) U(L(p)) Ψ_{q,σ}`, Wigner
rotation `W(Λ,p) = L⁻¹(Λp) Λ L(p)`, `U(Λ)Ψ_{p,σ} = (N(p)/N(Λp)) Σ D_{σ'σ}(W(Λ,p)) Ψ_{Λp,σ'}`), §3.2 "Orbits and
stability subgroups" (mass shell, light cone, one-sheeted hyperboloid; stabilisers `SO(D−1)`, `ISO(D−2)` with an algebraic
proof, `SO(D−2,1)↑`; the invariant scalar product on the orbit), §5.2 (quartic Casimir on massive representations; "in four
spacetime dimensions, the square of the Pauli–Lubanski vector acting on a massive field of spin-s is indeed equal to
`m² s(s+1)`"), §5.4 (tachyonic: `C₄ = C₂(iso) C₂(so(D−2,1))`, momentum space-like, non-compact little group), §3.3 and §1.3 only
skimmed. Weinberg Chapter 2 and Wigner 1939 are NOT read.

Convention difference to record in any statement: Bekaert–Boulanger use signature `(−,+,+,+)` (so `p² = −m²` for a massive
state and `W² = +m² s(s+1)`); T-HA6 in `docs/tasks/milestones.md` is in `(+,−,−,−)` with `W² = −m² s(s+1)`. Both give the same
representations; a formal statement has to fix the signature, and Lightlike/Physlib use `(+,−,−,−)`-style `SpaceTime d` (to be
checked against `PhyslibAlpha/Relativity/MinkowskiMatrix.lean`).

## Staged plan (each stage a compiled, committable file)

1. **Orbits and little groups.** On momentum space `ℝ^{1,3}` (signature `(+,−,−,−)`): the invariant `p²` and the sign of `p⁰`
   separate the orthochronous-Lorentz orbits (mass shell `p² = m² > 0, p⁰ > 0`; light cone `p² = 0, p⁰ > 0`; tachyonic
   `p² < 0`); the standard momenta `(m,0,0,0)`, `(1,0,0,1)`, `(0,0,0,κ)`, `0`; their stabilisers. Check statement of the
   milestone: the tachyonic little group (`SO(2,1)`) is non-compact (explicit unbounded boosts fixing `(0,0,0,κ)`).
2. **Massive representations.** For a unitary irreducible representation `D` of `SU(2)` (from `SU2.spinRep`), the induced
   unitary representation of the Poincaré group on `L²(mass shell, dμ_m; ℂ^{2s+1})`
   `(U(a,Λ)ψ)(p) = e^{i p·a} D(W(Λ,p)) ψ(Λ⁻¹p)` with the Wigner rotation `W`; prove it is a unitary representation (cocycle
   identity) and compute `P² = m²`; massive spin-1/2 has two states per momentum.
3. **Massless representations.** Little group `ISO(2)` (double cover `E(2)`), finite-helicity representations (the translation
   part acts trivially), `W = h P`.
4. **Casimir `W²`.** Pauli–Lubanski vector on the induced representations, `W² = −m² s(s+1)`.
5. **Classification (lockable statement).** Every irreducible unitary positive-energy representation is one of these. This
   is the deep part (Mackey machine); in the plan it is last and needs a precise statement agreed with the owner before work
   starts: a *weaker* version needs two recorded full-proof attempts (owner's 17:10 rule).

## Not started

No Lean has been written for HA6. Next: reuse check of Tau Ceti and physicslib4, then stage 1 (definitions of the orbits and little groups
against `PoincareGroup`/`LorentzGroup` of Physlib).
