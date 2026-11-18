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

## Source (not yet read)

Weinberg, *The Quantum Theory of Fields I* (1995), Chapter 2, §2.5 ("One-particle states", the table of standard momenta and
little groups) and Wigner, Ann. Math. 40 (1939) 149; the statement text of T-HA6 in `docs/tasks/milestones.md` names
Weinberg Chapter 2. Per the owner's 19:57 rule nothing below counts as checked until a text has been opened and located.

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

No Lean has been written for HA6. Next: reuse check of Tau Ceti and physicslib4, read Weinberg Chapter 2 (or another open
text) and record its location, then stage 1.
