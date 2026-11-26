Verdict: fail
Reviewer: regge
Worked by: no plan recorded
Commit: 76585fffab3958c3df151a62ce9d253a7f07e248

## General findings

The Lean code is sound. There is no `sorry`, and the main declarations use only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`. The statements are typed correctly and, as far as I
can check, true. The source comparison (r1) passes against Wigner (1939), which I read. The
milestone still fails on honesty grounds (checks 2–4):

- The trust check t1 (`lightPL_eq`, `W = (h/2) P`) is true by definition.
- The catalogue note LL-0282 overstates what Lean proves.
- The notes LL-0278, LL-0280 and LL-0313 leave out two differences: the form of `W`, and how weak
  the massless part of `WignerClassification` is.

Every fix is to documentation or the checklist. No new proof is needed, because the stronger
generator-level results already exist in `Lightlike/Poincare/`.

Reviewer checks, compiled against the built library at this commit with `.venv/bin/lake env lean`
on a scratch file (not committed):

```lean
-- compiles: disjunct (c) adds no logical content to WignerClassification
theorem review_wignerClassification_of_weak
    (hweak : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (ρ : ISL2C →* (H ≃ₗᵢ[ℂ] H)), IsStronglyContinuous ρ → HasPositiveEnergy ρ → IsIrreducible ρ →
        (∀ a, ρ (transl a) = 1) ∨ (∃ m (hm : 0 < m) n, EquivMassive ρ hm n) ∨
        SpectrumIn ρ (lightCone ∪ {0})) :
    WignerClassification   -- proof: classical case split on ∃ h, EquivMassless ρ h
-- compiles: stdLightPL h = fun ν => (h/2) * coord (lightMom 1) ν   (by fin_cases; simp; ring)
```

## r1

Result: pass

What was compared:

- **Wigner (1939), Ann. Math. 40, 149–204.** I read the JSTOR scan hosted at
  math.toronto.edu (`Wigner-1939.pdf`) from its text layer:
  - §3, pp. 157–158: four classes (time-like, null ≠ 0, zero, space-like). Only the first two
    are treated, and the restricted group is treated "up to the sign", i.e. the double cover.
  - §2, p. 156, and §3, p. 158: class `0_0` (every translation acts trivially) is "not determined".
  - §6, pp. 186–187: the subclasses `P_±`, `0_±` and `0_0`.
  - §7A, p. 197: for `P > 0` the little-group representations are `D^(0), D^(1/2), D^(1), …`.
  - §7B, p. 198, "The final result":
    - `P_+^j`: `P > 0`, and `j` is zero or a positive integer or half-integer.
    - `0_+` has three kinds: `0_+^s` with `s` an integer or half-integer, positive, negative or
      zero; `0_+(Ξ)`, single-valued, `Ξ > 0`; and `0'_+(Ξ)`, double-valued, `Ξ > 0`.
    - The classes `0_0` and `P < 0` "have not been determined".
- **How the Lean statement matches.** `WignerClassification` (ClassificationStatement.lean:125) lists:
  - (a) translation-trivial, which is Wigner's `0_0`, left unclassified in both;
  - (b) `EquivMassive ρ hm n` with `m > 0` and `n ∈ ℕ`, which is `P_+^j` with `j = n/2` and
    `P = m²`;
  - (c) `EquivMassless ρ h` with `h ∈ ℤ`, which is `0_+^s` with `s = h/2`, covering every sign
    and half-integers;
  - (d) `MasslessNotHelicity`, which is `0_+(Ξ)` and `0'_+(Ξ)` together.

  The negative-energy classes `P_-` and `0_-` and the space-like class `P < 0` are excluded by
  `HasPositiveEnergy`: the spectrum lies in the closed forward cone. The list and the parameter
  ranges match the source.
- **Named weakening.** Wigner gives the continuous-spin classes positively, by `Ξ > 0` and
  single- or double-valuedness. Lean gives (d) only negatively, so (c) ∨ (d) reduces to "the
  spectrum lies in `lightCone ∪ {0}`" (reviewer check above). The massless part of the statement
  therefore asserts only that the spectrum is light-like. The module docstring names this ("only
  characterised negatively … the honest content"); catalogue note LL-0313 does not (see check 2).
- **Only completeness is stated.** The statement does not say that each listed representation is
  irreducible. That is proved separately: `irreducible_massive_sourceMeasure` and
  `irreducible_massless_coneSourceMeasure`, LL-0310 and LL-0311. It also does not say that
  different parameters give inequivalent representations. Wigner states both.
- **Weinberg, QFT I, §2.5: not read.** No legitimate online copy. From memory only: Table 2.1 has
  six classes (a)–(f) with little groups SO(3), ISO(2), SO(2,1) and SO(3,1), and only (a), (c)
  and (f) are physical. The continuous θ of ISO(2) is "not observed", leaving helicity σ, which
  §2.7 allows to be integer or half-integer. This agrees with the list above, but the Weinberg
  half of r1 is still pending.

## Check 1: items ticked

- `stream_status.py show --milestone HA6`: 9 of 10 ticked, all work items ticked, only r1 open,
  `plan: none`.
- The declarations named in the checklist exist: m1–m3, p1, p2, t1–t3 and c1.
- The API map cites them: `Lightlike/Lorentz/API-map.md` items 34, 35, 37, 40 and 41, lines
  178–192.

## Check 2: statements against the done-when and sources

- `wigner_massive` (Classification.lean:156) states five things:
  - the L² norm is preserved for `inducedRep`, on pointwise functions whose norm is measurable;
  - the translations are covariant;
  - `P² = m²`, which is `P.2.1` and so holds by the definition of `massShell`;
  - `W² = −m² s(s+1)` with `s = n/2`, in signature (+,−,−,−);
  - there are `n+1` states per momentum.

  The n/2 spin convention and the signature are named in the docstring and in LL-0278.
- `wigner_massless` (:180) states that the L² norm is preserved, `P² = 0` (by definition of
  `lightCone`), `W = (h/2) P` and `W² = 0`. The h/2 helicity convention is named in the docstring
  and in LL-0279.
- **Difference not named in the catalogue, the form of `W`.** `pauliLubanski` (PauliLubanski.lean:126)
  is the formula `m Σ_k L(A)^μ_k J_k`, indexed by a group element `A`. It is not the operator
  `½ ε^{μνρσ} M_{νρ} P_σ` built from the generators of `poincareRep`. The module docstring says
  "pointwise" and "covariance … not part of this file". LL-0278 and LL-0280 do not say this. The
  generator form exists but is not catalogued: `pauliLubanski_sq_generators` in
  `Lightlike/Poincare/PauliLubanskiGenerators.lean`.
- **Difference not named in the catalogue, the massless sector.** The LL-0313 note says "massless
  of infinite spin (MasslessNotHelicity)" as if that were a positive description. It should say
  that (d) is only negative, that (c) adds no logical content, that Wigner's `0_+(Ξ)` and
  `0'_+(Ξ)` are not identified, and that only the completeness direction is stated.
- Omitted cases (tachyonic, negative energy, a classification of `0_0`, continuous spin) are named
  in the ClassificationStatement.lean docstring. Tachyonic and negative energy are excluded by the
  hypothesis.

## Check 3: trust checks and non-vacuity

- **t1, `lightPL_eq`: true by definition (fail).** `stdLightPL h` is hard-coded as
  `(h/2)·coord(lightMom 1)` (reviewer check above), and `lightPL h A` is defined as `L(A)` applied
  to it. So `W = (h/2) P` reduces to the linearity `coord_smul_eq_sum`. No Lean statement connects
  `stdLightPL` to `lightInducedRep`. The genuine content is in:
  - `helChar_rotZ`, `helChar_upper`;
  - `Lightlike/Poincare/MasslessGenerators.lean`: `hasDerivAt_helicityAct_rot_at` and
    `hasDerivAt_helicityAct_trans_at`, which are derivatives of the representation at every
    light-cone momentum.

  Fix: point t1 at these.
- **t2, `finrank_atMomentum_spinHalf`: weak but acceptable.** The fibre type is
  `Fin (n+1) → ℂ`, so the dimension holds by construction. In Wigner's construction the states per
  momentum are the little-group space by definition, and `atRest_irreducible` shows the fibre is
  one irreducible SU(2) doublet.
- **t3, `not_isCompact_littleGroup_tachyon`: genuine.** The boosts along x¹ fix `(0,0,0,κ)` and
  `γ` is unbounded. It holds for every κ, including the degenerate κ = 0; this is harmless.
- **Non-vacuity of the statement.** `trivialRep_admissible` is real: a Dirac spectral measure at 0
  shows the hypotheses can be satisfied. `trivialRep_classified` is `rfl` and exercises only
  disjunct (a). No check builds an instance of `EquivMassive` or `EquivMassless`.
- **Fourier sign convention: checked by hand.** `translateOp` uses `e^{+iP·a}` and `SpectrumIn` uses
  `e^{+ip·a}` with Mathlib's ⟪·,·⟫, which is conjugate-linear in its first argument. The massive
  spectral measure `|ψ|² shellMeasure` therefore lies in `massShell ⊆ forwardCone`, and the
  convention is consistent. Backlog: a Lean non-vacuity check for case (b).

## Check 4: catalogue honesty

- LL-0278, LL-0279, LL-0280, LL-0282, LL-0312 (`proven`): no unproved hypotheses beyond `0 < m`
  and measurability of the norm.
- LL-0313 (`stated`): stated, as designed. `WignerClassification` is a `def … : Prop`.
- **LL-0282 overstates (fail).** It says "The vector W is computed from the helicity character
  and the rotation generator J_z". In Lean `W` is defined from hand-chosen values (see t1).
  Rewrite the note, or move the entry to the MasslessGenerators theorems.
- LL-0278, LL-0280 and LL-0313: add the differences listed under check 2.
- All the HA6 notes say "Wigner (1939) was not read". Update them with the r1 location (§7B,
  p. 198). There is also no `wigner-1939` key in the reference registry.

## Check 5: planning IDs in names

- Pass. No folder, file or declaration name in `Lightlike/Lorentz/PoincareIrreps/`,
  `Lightlike/Lorentz/WignerOrbits/` or `Lightlike/Poincare/` contains HA6, LL-xxxx, G1-xxx or an
  item ID (grep of declaration heads).
- "HA6" and "T-HA6" still appear in 20 module docstrings, for example Poincare.lean:9 and
  LittleGroups.lean:13. That is outside this check, noted only.

## To pass

1. Fix the LL-0282 note, and point t1 at `helChar_rotZ`/`helChar_upper` or the
   `hasDerivAt_helicityAct_*_at` theorems.
2. In LL-0278 and LL-0280, name that `W` is the little-group formula and not the generator
   operator, citing `pauliLubanski_sq_generators`.
3. In LL-0313, name the negative (d), the redundant (c), and that only completeness is stated.
   Record the Wigner §7B comparison there.
4. Weinberg §2.5 remains pending until it is read.
