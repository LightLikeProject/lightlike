# G3-067: zero-rest-mass fields, the Maxwell and Weyl spinor decompositions

Lean: `Lightlike/GR/ZeroRestMass.lean` (namespace `Lightlike.Spinor`), `Lightlike/GR/WeylSpinor.lean`.

## Mathlib, Physlib and repository check

`ε` is Physlib's `Fermion.metricRaw = !![0, 1; -1, 0]` (`Physlib/Relativity/Fermions/Weyl/Metric.lean`), reused.
Physlib has the Weyl-fermion representations and `metricRaw`'s commutation with `SL(2, ℂ)`, but no z.r.m.
equations and no SD/ASD decomposition of 2-forms or Weyl tensors. The repository's `Spin4/` is
Euclidean representation theory. Mathlib proves "holomorphic implies `C^∞`" only in one variable
(`DifferentiableOn.contDiffOn`, `s : Set ℂ`), so the wave-equation theorems assume `C²`.

## Sources read (rendered PDF pages and pdftotext of arXiv:1712.02196)

T. Adamo, *Lectures on twistor theory*:
* p. 6: `ε_{αβ} = [[0, 1], [−1, 0]] = ε_{α̇β̇}` (1.5); inverses `ε^{αβ} ε_{γβ} = δ^α_γ`, `ε^{αβ} ε_{αβ} = 2` (1.6);
  "lower to the right, raise to the left" `a_α := a^β ε_{βα}`, `b^α := ε^{αβ} b_β` (1.7).
* p. 23 (rendered): (3.1); (3.2) `F_{αα̇ββ̇} = ½ ε_{αβ} F^γ_{α̇γβ̇} + ½ ε_{α̇β̇} F_α^{γ̇}_{βγ̇}`; (3.3) `F̃_{α̇β̇} := ½ F^γ_{α̇γβ̇}`,
  `F_{αβ} := ½ F_α^{γ̇}_{βγ̇}`.
* p. 24: (3.4) `F_{αα̇ββ̇} = ε_{αβ} F̃_{α̇β̇} + ε_{α̇β̇} F_{αβ}`; (3.7) Maxwell, (3.8) Bianchi; (3.9)–(3.10)
  `∂_β^{α̇} F̃_{α̇β̇} = 0`.
* p. 25 (rendered): (3.11) `∂^α_{β̇} F_{αβ} = 0`, "These equations are the spin-1 zero-rest-mass (z.r.m.) equations";
  (3.12) the Riemann decomposition "with Ψ̃_{α̇β̇γ̇δ̇} and Ψ_{αβγδ} totally symmetric, encoding the SD and ASD portions of
  the Weyl curvature"; (3.14); (3.15): `h > 0`: `∂^{βα̇₁} φ̃_{α̇₁⋯α̇_{2|h|}} = 0`, `h = 0`: `□Φ = ∂^{αα̇}∂_{αα̇}Φ = 0`,
  `h < 0`: `∂^{α₁β̇} φ_{α₁⋯α_{2|h|}} = 0`.
* p. 32, Exercise "momentum eigenstates", item 3: the fields `p_{α₁}⋯p_{α_{2|h|}} e^{ik·x}`, `e^{ik·x}`,
  `p̃_{α̇₁}⋯p̃_{α̇_{2h}} e^{ik·x}`, `k_{αα̇} = p_α p̃_α̇`.

## How each Lean statement matches

ZeroRestMass.lean:
* `maxwell_decomposition`, `asdPart_symm`, `sdPart_symm`, `ofParts_antisymm`, `parts_ofParts`, `maxwellEquiv`: (3.2)–(3.4)
  as an equivalence between 2-forms and pairs of symmetric spinors (with the sign of difference 1).
* `ClosedD`, `DivFreeD`, `ZrmASDD`, `ZrmSDD`, `maxwell_iff_zrm_D`: at a point, `dF = 0 ∧ ∂^aF_{ab} = 0` holds iff
  (3.10) and (3.11) hold for the parts, in the first derivatives `D = ∂F`.
* `pd`, `box`, `IsZrmNeg`, `IsZrmPos`, `IsZrmScalar`: (3.15) for every `|h| = (n + 1)/2` and `h = 0`, on an open set.
* `IsZrmNeg.box_eq_zero`, `IsZrmPos.box_eq_zero`: each component of a `C²` z.r.m. field solves `□φ = 0` (added; Adamo
  does not state it), via `wave_algebra`.
* `planeWave_isZrmNeg`, `planeWave_isZrmPos`, `planeWave_isZrmScalar`: p. 32, item 3, all helicities.
* `maxwell_iff_zrm`: for a 2-form field differentiable on an open set, Maxwell's equations hold iff `F.asd` is a z.r.m.
  field of helicity `−1` and `F.sd` one of helicity `+1` (3.7)–(3.11).

WeylSpinor.lean:
* `IsWeyl` (pair antisymmetry, pair exchange, cyclic identity, trace-free with `η^{ac} ↔ ε^{αγ}ε^{α̇γ̇}`),
  `weyl_eq_weylOf`, `weylASD_symm`, `weylSD_symm`, `weylOf_isWeyl`, `weylParts_weylOf`, `weylEquiv`: the Weyl term of (3.12)
  as an equivalence between Weyl tensors and pairs of totally symmetric 4-spinors.

The finite linear identities (`maxwell_iff_zrm_D`, `weyl_eq_weylOf`, `weylASD_symm`, `weylSD_symm`, `wave_algebra`) are
proved by `linear_combination` certificates found by exact linear solves (sympy and exact sparse elimination over the
256 components of a 4-index bispinor tensor; the Weyl constraints have rank 246, leaving 10 = 5 + 5).

## Differences

1. Sign: with (1.5)–(1.7), (3.3)'s parts are `−asdPart F`, `−sdPart F` and the right side of (3.2) is `−F` (checked
   numerically on random symmetric spinors: every component ratio is −1); (3.2)–(3.3) and (3.4) disagree by an overall
   sign. The Lean parts are the ones for which (3.4) holds. The z.r.m. equations are linear and do not see the sign.
2. Misprint: (3.12)'s second term is printed `ε_{αβ} ε_{γδ} Ψ_{αβγδ}` (undotted lower indices repeated, no dotted ones,
   so it has no well-formed reading); the corrected form, used in Lean, is `ε_{α̇β̇} ε_{γ̇δ̇} Ψ_{αβγδ}`, the only reading with
   the free indices of `R_{abcd}`.
3. Scope: this covers the Weyl term of (3.12); the `Φ_{αβγ̇δ̇}` and `R` terms are not claimed.
4. Representation: the raised indices of (3.15) and (3.10)–(3.11) are written out with `ε` (`ε^{αβ}` is the matrix
   (1.5) by (1.6)); fields are families `φ i`, `i : Fin (n + 1) → Fin 2`, on an open `U ⊆ ℂ⁴` in the coordinates `x^{αα̇}`;
   regularity is a hypothesis of the theorems that need it (differentiability for Maxwell; `C²` for the added
   wave-equation theorem, which the source does not state).

## Found while reading (not formalized)

* The scalar bracket of (3.12) as printed, `ε_{αγ}ε_{βδ}ε_{α̇β̇}ε_{γ̇δ̇} + ε_{αβ}ε_{γδ}ε_{α̇γ̇}ε_{β̇δ̇}`, is not antisymmetric
  under `(αα̇) ↔ (ββ̇)`: 16 of its 256 components violate `R_{bacd} = −R_{abcd}`; with `−` between the two terms, none do
  (numerical check of all components). The full (3.12) (the `Φ` and `R` terms) is a follow-up.
