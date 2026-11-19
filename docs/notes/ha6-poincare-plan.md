# T-HA6 Wigner classification of the Poincaré group: reuse check and plan

18 November 2026. Written before any Lean for HA6.

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
* **Physlib, finer inventory (`.lake/packages/Physlib/Physlib/Relativity/`, signature `(+,−,−,−)`, `Lorentz.Vector d := Fin 1 ⊕ Fin d → ℝ`)**:
  `LorentzGroup d` (a set of matrices with a `Group` instance on the subtype, `LorentzGroup/Basic.lean:48`; defining relation
  `Λᵀ η Λ = η`, `mem_iff_transpose_mul_minkowskiMatrix_mul_self`), the Minkowski product `⟪p, q⟫ₘ` with
  `minkowskiProduct_invariant` (`Tensors/RealTensor/Vector/MinkowskiProduct.lean:147`), causal character (`Causality/`),
  `LorentzGroup.IsOrthochronous`, `IsProper`, the restricted group, axis boosts `boost i β hβ` with
  `Lorentz.Vector.boost_*` action lemmas (`LorentzGroup/Boosts/Basic.lean:89`, `Apply.lean`), and **generalized boosts**
  `generalizedBoost u v : LorentzGroup d` taking a velocity `u` to a velocity `v`, orthochronous, proper, in the restricted
  group (`LorentzGroup/Boosts/Generalized.lean:189,361-366`). So transitivity of the restricted Lorentz group on the mass
  shell and the standard boost `L(p) = generalizedBoost (basis 0) (p/m)` are available; `Rotations.lean` has the rotations.
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
skimmed. Weinberg Chapter 2 §2.5 (pp. 62–66) and Wigner, Ann. Math. 40 (1939) 149: searched for an openable copy on
18 November 2026, none found (no legal PDF of Weinberg Vol. 1; Wigner 1939 is behind JSTOR). NOT read. Bekaert–Boulanger §3.1
reproduces Weinberg's construction (their eqs (10)–(13) are Weinberg's (2.5.x) with the same `L(p)`, `W(Λ,p)`, `N(p)`), and
§3.2 quotes Wigner on the null-vector stabiliser. A copy of Weinberg Chapter 2 or of Wigner 1939 supplied by the maintainers would
close this item.

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
   is the deep part (Mackey machine); in the plan it is last and needs a precise statement agreed with the maintainers before work
   starts: a *weaker* version needs two recorded full-proof attempts (the maintainers' rule of 18 November 2026).

## Not started

No Lean has been written for HA6. Next: reuse check of Tau Ceti and physicslib4, then stage 1 (definitions of the orbits and little groups
against `PoincareGroup`/`LorentzGroup` of Physlib).

## Stage 5 sources read (18 November 2026; decided by the maintainers: Wigner 1939 and Mackey 1952 are historical references only)

Downloaded to scratch directories and extracted with `pdftotext`; read:

* **Sunder, "Notes on the imprimitivity theorem"** (Draft: 8 April 1998, `https://www.imsc.res.in/~sunder/imp.pdf`, as obtained on
  18 November 2026): §5 "semi-direct products", page 20 (document pages 20–21): the induced-by-the-stabiliser setting
  `G = A ⋊_α K`, `A` abelian, `α̂_k(χ) = χ ∘ α_{k⁻¹}`; the unitary representation restricted to `A` gives a spectral measure
  `P(E)`; if `π` is irreducible the measure `µ` is ergodic for `K` on `Â`; **the sentence "it is known — and not hard to
  prove — that if … the action is ergodic and regular (there is a Borel set `C` meeting `µ`-almost every orbit in exactly one
  point), then the measure is concentrated on one orbit" is stated without proof** (this is gap (i)); **Theorem 5.1** (page 21,
  statement): for regular `α̂`, (a) `π_{χ,θ}(a, k_χ) = χ(a) θ(k_χ)` induced up to `G` is irreducible for `θ` irreducible
  representation of the stabiliser `K_χ`, (b) every irreducible representation of `G` is equivalent to some `π_{χ,θ}`; the text
  says that, "putting all the above analysis together, and invoking the imprimitivity theorem, it is not hard now to write
  down a complete proof of part (b)" and that the proof of (a) is "not very difficult": **neither part is proved in the source**.
* **Landsman, *Lecture Notes on C\*-Algebras, Hilbert C\*-modules, and Quantum Mechanics*, arXiv:math-ph/9807030v1**
  (24 July 1998; draft of 8 April 1998): **Theorem 3.12.1, "Mackey's transitive imprimitivity theorem"** (section 3.12, page 82 of the
  printed page numbering; the section's table-of-contents entry is `3.12 … 82`): for a closed subgroup `H ⊂ G` every covariant
  representation `(U(G), π̃(C₀(G/H)))` is unitarily equivalent to one induced from a unitary representation `U_χ(H)`; the
  correspondence is bijective on equivalence classes and preserves direct sums and irreducibility; the proof combines
  Theorems 3.10.1, 3.6.1, 3.7.11, 3.8.7 (stated, with proofs in the notes). **This is the *transitive* theorem (homogeneous
  space `G/H`)**; the non-transitive case needed for the Poincaré group (a measure on momentum space concentrated on one orbit)
  is exactly gap (i), not covered. Also §3.6 (page 67, the quantum imprimitivity theorem) and §3.10 (page 78, the abstract
  transitive imprimitivity theorem) are the ingredients.
* **Bekaert–Boulanger** hep-th/0611263v2 (13 June 2021): read as recorded above (§3.1, §3.2, §5.2, §5.4); §3.3 "Classification"
  (page of v2 around 13–14, `pdftotext` line 598 onwards) to be read before the stage 5 statement is locked.

Scope (decided by the maintainers): the restricted Poincaré group only (no parity, no time reversal, no extended group). Gaps (i) ergodic measure of a
regular action is concentrated on one orbit and (ii) the Lorentz action on momentum space is regular are to be proved in Lean.
