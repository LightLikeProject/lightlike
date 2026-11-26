Verdict: fail
Reviewer: oscillatory
Worked by: lorentz
Commit: 76585fffab3958c3df151a62ce9d253a7f07e248

# Review of SF7: the Lorentzian EPRL vertex amplitude and its finiteness

Done-when (docs/tasks/milestones.md:613): "the Lorentzian EPRL vertex amplitude is defined and its
finiteness proven (Engle–Pereira–Rovelli–Livine 2008; Engle–Pereira 2009 for finiteness)". Row
title (milestones.md:564): labels `ρ = γ(j+1)`, `k = j`.

Bottom line: the finiteness half is proven, and proven more generally than the sources need. The
"defined" half is not met. The sources contract SU(2)-invariant intertwiners, which needs the `ε`
twist (or an equivalent dualisation) on one end of every link. `eprlVertex` leaves the twist out,
and the Lean file says itself that the EPRL amplitude "is not defined here"
(Lightlike/Lorentz/EPRL.lean:206). Its argument for leaving the twist out covers finiteness only,
so r1 fails.

## r1

Result: fail

**Compared.** `Lightlike.Lorentz.eprlVertex` (Lightlike/Lorentz/EPRL.lean:208) together with
`eprlRho`, `eprlVec`, `eprlCoeff`, `eprlLinks` and `magBox` (:145–197), against the following
sources:

- EPRL 2008, arXiv:0711.0146v2, Sec. IV "Lorentzian theory", eqs. (35)–(41);
- Engle–Pereira 2009, arXiv:0805.4696, eqs. (10)–(12), (16), (17)–(23), (24)–(30), Sec. 4 and
  App. A.

The full text of both was read, extracted with pdftotext from the arXiv PDFs. Ding–Rovelli
(arXiv:1006.1294), the source cited for `ρ = γ(j+1)`, was **not** read.

| Point | Source | Library | Verdict |
|---|---|---|---|
| Integral form, gauge fixing | EP (17)→(22): drop the fifth integral after `Ṽ_i = V₅⁻¹V_i`. EP (23) is the regularised vertex | `V₄ = 1` (`gauge`, StarBound.lean:80); integral over SL(2,ℂ)⁴ with `haar4` | match; named (EPRL.lean:19–21) |
| Lowest SU(2) level | EPRL after (37): "k = n/2"; EP (12): `k = N/2 = ρ/(2γ)` | `eprlVec` = `suV J ρ 0`, spin `J/2` | match |
| Link factor | EP (27)–(28): `∏_{t<t'} K_{k m_tt', k' m_t't}(x_t, x_t')`, with `K = D(B(x_t)⁻¹B(x_t'))` | `linkProd` over `a < b` of `⟨Y e_{m a b}, π(V_a⁻¹V_b) Y e_{m b a}⟩` | match, index for index |
| Contraction | EP (30): `[⊗_t i_t] · F{m}`. EP (10): each node tensor is "a tensor in ⊗_{ℓ∈n} H_(N_ℓ,ρ_ℓ)". EPRL (39)–(41): `i ∈ Inv_SU(2)(H_{j1} ⊗ … ⊗ H_{j4})`, vertex = standard 15j of SL(2,ℂ) | `Σ_{m∈magBox} ∏_a ι_a(m_a·) ∫ eprlLinks`: arrays contracted as they stand, with no `ε` and no conjugation | **differs** (see below) |
| Labels | EPRL after (37) and (40): `ρ = γn`, `(2j, 2jγ)`. EP (16), (23): `A_v[2j, 2γj; j, i]`. In the library's normalisation (`n = 2k`, `ρ_EP = 2ρ`, EPRL.lean:25–28) this is `ρ = γj` | `eprlRho γ J = γ(J/2 + 1)` = `γ(j+1)`, as the milestone row prescribes | differs from both sources by the row's choice. The difference is named in the docstring (:23–29), the LL-0046 note and the API map. Finiteness for any labels: `integrable_linkProd_inner`. Acceptable |
| Normalisation | EP (29): `dV = dR dx`, so (30) integrates over hyperboloids | Haar on SL(2,ℂ)⁴ (EP's (22)) | a positive constant; named (:50–51) |
| Finiteness | EP Sec. 4 and App. A: finite for all labels, via the matrix-element bound and Baez–Barrett | `integrable_eprlIntegrand` and `lintegral_enorm_eprlIntegrand_lt_top`, for all `γ`, `J`, `ι`. Route: `|D| ≤ C·I`, then Hölder over the five stars | match, more general |

**The `ε` twist: the source has it, implicitly.**

- **Where the sources need it** (MEASURED from the text). EP's node tensors all live in `⊗ H`
  (EP p. 3, after (10)). EPRL's intertwiners are invariants of `H_{j1} ⊗ … ⊗ H_{j4}` (EPRL (39),
  (41)). In both, all four legs are of the same type. Contracting such a tensor at both ends of a
  link with `D(U_ℓ)`, an operator, needs an identification of `H` with its dual at one end.
- **What the identification is** (PROXY: the standard spin-network and 15j convention, which
  neither paper prints). It is the invariant bilinear form, that is the structure map
  `ε: e_m ↦ ±e_{J−m}`, or equivalently the conjugated intertwiner.
- **Why EP's argument needs it** (PROXY: a short hand calculation, not checked in Lean). EP's step
  (26) drops the rotations "using the SU(2) invariance of the projected spin-network". This holds
  only if the bra legs transform by the conjugate representation `ε D ε⁻¹`, which is what the
  twist provides. The untwisted contraction of an invariant `ι` does not have this property.

So the source amplitude on its natural inputs, SU(2)-invariant intertwiners, is
`eprlVertex γ J (τ ι)`, where `τ` applies `ε`, or conjugation, on the bra legs `b > a` of node
`a`. It is not `eprlVertex γ J ι`.

**What the absence does and does not affect.**

- **Finiteness: justified** (PROXY: a one-line argument, not formalised). `τ` acts leg by leg, so
  `τ ι` is again a family of node arrays. Every theorem of SF7 holds for all `ι`. The source
  amplitude is therefore covered by instantiating at `τ ι`. The docstring gives this argument
  (EPRL.lean:48–49), and it is correct.
- **"Defined": not justified, only disclaimed** (MEASURED from the Lean file). The def docstring
  says: "For SU(2)-invariant intertwiners the EPRL amplitude needs the `ε` twist on the bra legs;
  it is not defined here, and `eprlVertex` is not claimed to equal it" (EPRL.lean:203–207). The
  module docstring says the same (:45–49), as do the LL-0046 note and the checklist hint of m1.
  The disclaimer is honest. But it concedes the first half of the done-when instead of meeting it.
  The ticked m1 text ("The Lorentzian EPRL vertex amplitude … is defined") contradicts the
  library's own docstring.
- **Downstream: exposed.** Callers that feed invariant or coherent arrays into `eprlVertex`
  inherit the missing twist. LL-0087 `eprlVertex_eq_lorVertex` says "no epsilon twist", and SF10
  depends on SF7.

**Missing for r1 to pass** (any one route):

1. **Define the twist.**
   - The structure map `ε_J` on doubled spin `J`, with its sign stated in the basis that
     `eprlVec` uses, and the bra-leg twist of a node array.
   - `eprlVertex γ J (twistBra J ι)` as the EPRL amplitude of SU(2) intertwiners, with its
     finiteness. This is immediate from `integrable_eprlIntegrand`.
   - A check that the twist is the right one: for SU(2)-invariant `ι`, the twisted integrand is
     invariant under `V_a ↦ V_a h`, `h ∈ SU(2)`, for `a = 0, …, 3`, or a known value at a nonzero
     spin.
   - A wrong-model control: the untwisted contraction of an invariant intertwiner fails that check.
2. **Or justify the absence by typing.**
   - State in Lean that `eprlVertex` equals the source amplitude when `ι_a` is typed as an
     invariant of the mixed product: the ket legs in `V`, the bra legs in the conjugate (dual)
     representation.
   - Prove the gauge-invariance check of route 1 for that class.
   - Have the docstring, the LL-0046 note and the API map say so, instead of "not defined here".

Until one of these routes is done, SF7 meets its done-when only in the weaker reading "a
generalisation of the vertex is defined and is finite". A done-when worded with the `ε` twist
would not be met.

## The other checks of the done-when

1. **Non-review items are ticked on main** (MEASURED). the computed milestone status, generated from main 76585ff,
   shows m1, p1, p2 and c1 ticked and r1 open (4 of 5).
2. **Statement against the done-when and the sources.**
   - The finiteness theorems state what EP Sec. 4 states. They hold for every array, which is more
     general than the source.
   - Every difference is named in the module docstring, the def docstrings, the LL-0046 note and
     the API map (Lightlike/Lorentz/API-map.md:61–76): the labels, the gauge fixing, the Haar
     normalisation and the missing twist.
   - The one unmet part is "defined", treated in r1 above.
3. **Trust checks** (MEASURED, read in Lightlike/Lorentz/EPRLTests.lean). They are real, not
   trivially true:
   - `eprlCoeff_spin_zero`: the spin-0 coefficient is the spherical function. This goes through
     Schur (`intertwiner_eq_smul`), not by definition.
   - `eprlVertex_spinZero_ne_zero` and `exists_pos_eprlVertex_spinZero_ne_zero`: positivity at
     `γ = 0`, then dominated convergence in `γ`.
   - `lintegral_linkProd_ungauged_eq_top`: an honest wrong-model check. Its docstring says it
     concerns the dominating kernel, not `|integrand|`.
   - `casimir2_hvec_eq_iff` and `casimir2_wrong_label_ne`: the label check, which separates
     `γ(j+1)` from EP's `γj`.

   Limits: non-vacuity is shown at spin 0 only, where the `ε` twist is trivial. No test exercises
   a nonzero spin or an invariant intertwiner. That gap is exactly the r1 gap.
4. **Catalogue** (MEASURED). LL-0046 (docs/results.yaml:607–621) has status proven, its four
   theorems take no hypotheses, and the axioms are only `propext`, `Classical.choice` and
   `Quot.sound`. This was checked by `#print axioms` through `.venv/bin/lake env lean` on the local
   oleans, which may predate the checkout; the sources are unchanged since f04e4a87. The note
   names the twist, the labels, the gauge fixing, the non-vacuity range and the normalisation. The
   title ("The Lorentzian EPRL vertex amplitude is finite … every coefficient array") says more
   than the note: its subject is the untwisted generalisation. The theorems are cited in the API
   map (API-map.md:148–153). The p1 decls are definitions, so no catalogue entry is needed.
5. **Planning IDs** (MEASURED). There are none in the folder, file or declaration names. A grep of
   Lightlike/Lorentz/*.lean found no `SF7`, `LL-…`, `T-…`, `G…-…` or item IDs. The names are
   subject names: `eprlRho`, `eprlVec`, `eprlCoeff`, `magBox`, `eprlVertex`, `eprlIntegrand`.

## Who worked on it

The files were created in the pre-release repository by the lorentz stream. The commits are
5805a11b ("define the Lorentzian EPRL vertex amplitude and prove it finite", 10 Nov) and
a1893b82 (review fixes that added the `ε` disclaimer, 11 Nov). They reached main squashed in
f04e4a87 (v0.1.0). The LL-0046 note was later extended by the catalogue-honesty commit 2b70ce1e.
The downstream bridge `eprlVertex_eq_lorVertex` (LL-0087) is not an SF7 item and was written by
the reviewing stream; no SF7 declaration was.

## Limits of this review

- Ding–Rovelli's eq. (24), the source of `ρ = γ(j+1)`, was not read.
- That the identification is `ε` or conjugation rests on the standard convention, which neither
  paper prints (PROXY).
- The failure of gauge invariance without the twist is a hand calculation, not a Lean check
  (PROXY).
- The library's normalisation `ρ_EP = 2ρ` is taken from EPRL.lean:25–28. It is consistent with
  EP's Casimirs after (10), but was not independently derived.
