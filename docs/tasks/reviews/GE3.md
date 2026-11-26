Verdict: pass
Reviewer: turaev-viro
Worked by: unknown (no plan); per git log the GE3 commits came from the regge stream (branches `regge/ge3-raychaudhuri`, `regge/g1-009-raychaudhuri`, `regge/g1-009-manifold`; index computation `raychaudhuri_algebra`) and the api-g1-005 session (branch `api-g1-005/ge3-raychaudhuri`, merged in 7736c79f)
Commit: 76585fffab3958c3df151a62ce9d253a7f07e248

# Review of GE3: geodesics, the exponential map and the Raychaudhuri equation on a manifold

Done-when (docs/tasks/milestones.md:57): the Raychaudhuri equation for timelike geodesic congruences, and
focusing under the strong energy condition. Trust checks: comoving expansion in Minkowski and FLRW in closed
form; a congruence in a spacetime violating the energy condition does not focus.

No plan file exists. docs/tasks/checklists.yaml:116-148 has no item of kind `review` for GE3, so this review has
one section per work item (m1, m2, p1, t1, t2, c1).

## Global checks

- **Ticks.** `stream_status.py show --milestone GE3`: "6 of 6 items ticked; work items all ticked: True; review:
  none". The reviewer (turaev-viro) authored none of the GE3 commits.
- **Sources read.** Kar and SenGupta, gr-qc/0611123, fetched from arXiv and read at eqs. (12)-(16) and the
  paragraph after (16) (pp. 10-12). Carroll, gr-qc/9712019, Chapter 4 read (pp. 117-119, eqs. (4.72)-(4.74)).
  Hawking and Ellis 1973, Chapter 4 (DOI 10.1017/CBO9780511524646.005) is paywalled and was not read: **that
  comparison is pending.**
- **Axioms.** `.venv/bin/lake env lean` on a scratch file with `#print axioms` for all 13 checklist
  declarations plus `collapse_focusing_example`: each depends only on `[propext, Classical.choice, Quot.sound]`.
  The .olean files are dated 23-24 Nov; the GE3 sources were last changed on 22 Nov (git log), so the output
  matches main's sources. CI's `scripts/AxiomAudit.lean` checks every declaration in any case.
- **sorry.** None in `Lightlike/Spacetime/Raychaudhuri/`, `RaychaudhuriManifold.lean`, `RaychaudhuriCoord.lean`,
  `RaychaudhuriFocusing.lean`, `RiccatiFocusing.lean`, `EnergyConditionsField.lean` or
  `Cosmology/Raychaudhuri.lean` (grep).
- **Planning IDs.** `python3 -I scripts/planning_ids.py`: "none in Lean folder, file or declaration names".
  Advisory only: the file name `Lightlike/Spacetime/Raychaudhuri/TestsTier1.lean` uses the plan's tier word
  "Tier1" (that is not one of the ID kinds the rule lists). Module docstring headings ("(GE3)", "(GE3, Tier 1)")
  and catalogue notes ("GE3 (G1-005)") carry planning IDs, which the rule allows because they are not names.
- **Sign convention.** The Ricci convention matches the source: `deSitterManifold_no_focusing` gives
  `Ric(∂_t,∂_t) = -3H²` (Examples.lean:84) and `flrw_raychaudhuri` gives `dΘ/dt + Θ²/3 = -R₀₀` with
  `Θ = 3ȧ/a`, so `R₀₀ = -3ä/a` (Cosmology/Raychaudhuri.lean:75-81). Both are the standard values, so
  `Ric(V,V) ≥ 0` is Kar and SenGupta's `R_ab vᵃ vᵇ ≥ 0`.

## m1

Result: pass

`Lightlike.raychaudhuri_leviCivita` (Lightlike/Spacetime/RaychaudhuriManifold.lean:462-472) specializes
`raychaudhuri_manifold` (:377-387) to `leviCivita g`. The instance `LocallySmoothConnection (leviCivita g)`
(LeviCivitaSmooth.lean:184) discharges the connection hypothesis, so the only hypotheses are that `V` is smooth
and `∇_V V = 0` near `x`. The conclusion is `V(Θ) = -tr((∇V)²) - Ric(V,V)` at `x`, with `Θ = tr(u ↦ ∇_u V)`
(`expansionM`, :309-312).

Comparison with Kar and SenGupta: (12) is
`dΘ/dλ + Θ²/3 + σ² - ω² = -R_ab vᵃ vᵇ` for n = 4. The source says it comes from the identity `vᶜ∇_c B_ab`,
traced and then split. The Lean statement is that traced identity before the split, with
`tr(B²) = Θ²/3 + σ² - ω²` for a unit timelike field. It holds in any dimension and signature, for any geodesic
field, with no normalisation. That is a generalization, not a weakening. The split is proven in coordinates
(`raychaudhuri_equation`, LL-0192). The differences are named: the LL-0190 note
(docs/results.yaml:2498-2511) says "any signature", "with no normalisation of V" and "Kar and SenGupta's identity
behind (12)", and the docstrings at :377-378 and :462 say "any signature" and give the formula.

Junk values: the left side is an `mfderiv`, which would be junk 0 if `Θ` were not differentiable. The proof
establishes `MDifferentiableAt` (`hMD`, :437-438), so the equation is not satisfied by a junk value.

Gap, non-blocking: `RaychaudhuriManifold.lean` has no module docstring (lines 1-10 go straight from the imports
to `open`). Nothing in the file is a weakened statement, so definition-of-done item 4 does not require one, but
this is the one GE3 file without a docstring stating its limits.

## m2

Result: pass

`Lightlike.raychaudhuri_focusing_strongEC` (Lightlike/Spacetime/Raychaudhuri/FocusingSEC.lean:26-43):

- Setting: a Lorentzian metric on a 4-manifold, a locally smooth Levi-Civita connection, and
  `EinsteinEq cov 0 κ T` (`G + 0·g = κT`, EinsteinEquations.lean:51-56) with `κ > 0`.
- Hypotheses: `StrongECField T`, which is `(T - ½ tr T g)(ξ,ξ) ≥ 0` for timelike `ξ`
  (EnergyConditionsField.lean:105-107). `V` is smooth, and along an integral curve `γ` on `[0, L)` it is
  geodesic and unit near `γ s` and rotation-free (`g(∇_u V, w)` symmetric, i.e. `ω_ab = 0`). `Θ(γ 0) < 0`.
- Conclusion: `L ≤ 3/|Θ(γ 0)|`.

Comparison with Kar and SenGupta, the paragraph after (16). For zero rotation, `R_ab vᵃ vᵇ ≥ 0` gives geodesic
focusing. With the Einstein equations `R_ab = T_ab - ½ g_ab T`, that condition is the strong energy condition
`(T_ab - ½ g_ab T) vᵃ vᵇ ≥ 0`. The Lean proof makes the same two steps: `strongECField_iff_ricci`
(EnergyConditionsField.lean:279-282, with the factor `κ > 0`) and then `raychaudhuri_focusing_manifold`.

The source says "convergence occurs" without a bound. The Lean gives `3/|Θ₀|`, the standard constant, and it
cannot be improved under these hypotheses: the equality profile `Θ = mC/(m + Cs)` blows up exactly at `m/|C|`
(`hawking_profile_hasDerivAt`, Raychaudhuri/Hawking.lean:49-51). The source's "Θ → -∞ within 3/|Θ₀|" becomes
"a smooth field with these hypotheses has no such integral curve longer than 3/|Θ₀|". The LL-0364 title says
this ("cannot be continued beyond parameter 3/|Θ_0|"), as does the docstring of `raychaudhuri_focusing_manifold`.

Differences from the m2 hint, all named:

- dimension 4: theorem docstring "four-manifold", module docstring line 12, LL-0364 note.
- Λ = 0, absorbed into T: module docstring line 12 cites `einsteinEq_iff_absorb` (EnergyConditionsField.lean:198-201);
  the note says "Λ = 0".
- rotation-free: docstring, module docstring line 13, LL-0364 title and note.
- the bound `L ≤ 3/|Θ|`: the statement itself.

Carroll Ch. 4 (read) also supports moving Λ into T (`T_µν = -Λ g_µν`, text after (4.74)).

Non-vacuity: `collapse_focusing_example` (Raychaudhuri/CollapseExample.lean:56-65) discharges every hypothesis
for the collapsing dust universe `a = (c - t)^{2/3}`, with Einstein equations via Friedmann, dust strong energy
condition, `∂_t` unit, geodesic and rotation-free, `Θ = -2/c < 0` and `L = c/2 > 0`. It assumes a connection
with `IsLeviCivita` and `ContMDiffCovariantDerivative`; `leviCivita g` has both (LeviCivitaSmooth.lean:175, :184),
so the example is not vacuous. The extra `[T2Space M]` (FocusingSEC.lean:24) is the usual Hausdorff assumption
on spacetimes.

## p1

Result: pass

`raychaudhuri_manifold` is m1 above. `raychaudhuri_focusing_manifold_at` (RaychaudhuriManifold.lean:474-484)
gives `V(Θ) ≤ -Θ²/(n-1)` at `x`, for a Lorentzian metric, a unit field geodesic near `x`, rotation-free at `x`,
`Ric(V,V) ≥ 0` and `1 < n`. `raychaudhuri_focusing_manifold` (:535-550) gives `L ≤ (n-1)/|Θ(γ 0)|` along an
integral curve on `[0, L)`.

This is Kar and SenGupta (16) with σ² ≥ 0 and ω = 0 in dimension n; for n = 4 it is `3`, matching the `Θ²/3`
of (12). The division by `n - 1` is guarded by `hn : 1 < n`. `|Θ(γ 0)|` sits under the hypothesis
`Θ(γ 0) < 0`, so no division by 0 occurs. `expansionDeriv` is an `mfderiv`, but the proof shows `HasDerivAt`
along `γ` (:554-563), so it is not a junk value. Non-vacuity comes through m2's collapse example, which applies
this theorem.

The LL-0190 note names the limits: unit and Lorentzian for focusing, rotation-free at the point, and "the null
version (their (17)) is not here" (that version is LL-0212, RaychaudhuriNull.lean and RaychaudhuriNullManifold.lean).

## t1

Result: pass

Coordinates (Lightlike/Cosmology/Raychaudhuri.lean):

- `flrw_comoving_expansion` (:66-68): `Θ = 3·(ȧ/a)` for every `k`, assuming `a(t) ≠ 0`, `a` differentiable and
  `Dn k x ≠ 0`, so the quotient is not a junk value. It is computed from `christoffel_flrw`, not by definition.
- `minkowski_comoving_expansion` (:94-96): `Θ = 0` for `a = 1`, `k = 0`. This is the true value: it comes from
  `ȧ = 0` through the same closed form, not from a junk value.
- `flrw_raychaudhuri` (:74-81): `HasDerivAt` of `3ȧ/a` together with `dΘ/dt + Θ²/3 = -R₀₀`, using `ricci_flrw`.
  This checks the equation, with its sign, on a non-trivial metric.

Manifold layer (Lightlike/Spacetime/Raychaudhuri/Examples.lean):

- `flrwManifold_comoving_expansion` (:38-43): `expansionM cov ∂_t = 3ȧ/a` for every Levi-Civita `cov` of
  `flrwManifoldMetric`, via the bridge `expansionM_constField` (ConstField.lean:53-59).
- `minkowskiManifold_comoving_expansion` (:57-65): `Θ = 0` on `I = ℝ`, `k = 0`.

These are closed forms, as the trust check asks. They are not trivially true: FLRW has non-zero Christoffel
symbols, and the value `3ȧ/a` is derived from them.

## t2

Result: pass

`Cosmology.deSitter_no_focusing` (Cosmology/Raychaudhuri.lean:100-104) and `deSitterManifold_no_focusing`
(Examples.lean:74-84) state, for `a = e^{Ht}`, `k = 0`, at every point of ℝ⁴: `Θ = 3H` and `Ric(∂_t,∂_t) = -3H²`.
So for `H ≠ 0` the timelike convergence condition fails, and through `strongECField_iff_ricci` so does the strong
energy condition. The expansion stays finite on the whole spacetime. Both values are derived (`ricci_flrw`, the
derivative of exp), not definitional.

As the checklist hint says, these theorems state the values of Θ and Ric. They are not a non-blow-up theorem:
"does not focus" is read off the constant finite Θ on all of ℝ⁴.

Observation, non-blocking: the docstring (Examples.lean:74-76) argues from the case `H ≥ 0`, where both
`Θ < 0` and `Ric ≥ 0` fail. The case that isolates the energy condition is `H < 0` (contracting de Sitter).
There `Θ₀ = 3H < 0` and every hypothesis of the focusing theorem holds except `Ric ≥ 0`, yet the comoving curve
exists for every `L > 1/|H| = 3/|Θ₀|`, so the conclusion fails. A short theorem stating that would make the
"wrong input gives a different result" check of definition-of-done item 3 explicit at the level of the theorem.

`twisted_no_focusing` (Raychaudhuri/Twist.lean:26-32) is a genuine counterexample for rotation at the Riccati
level. `¬ ∃ B` is proved by the constant `Θ ≡ -√m ω`, which satisfies `Θ' ≤ -Θ²/m + ω²` with equality; it is not
trivially true. It is an inequality on ℝ, not a spacetime; the hint says so.

## c1

Result: pass

The catalogue entries for the main theorems and the pieces:

- LL-0190 (docs/results.yaml:2498-2511): decls `raychaudhuri_manifold`, `raychaudhuri_leviCivita`,
  `raychaudhuri_focusing_manifold_at`, `raychaudhuri_focusing_manifold`; status `proven`; source
  kar-sengupta-2007, eqs. (12) and (16).
- LL-0364 (docs/results.yaml:4822-4835): decl `raychaudhuri_focusing_strongEC`; status `proven`.
- The trust checks are also catalogued, in LL-0191 (:2512-2525) for the coordinate stage.

Honesty of `proven`:

- No declaration in these entries takes an unproved statement as a hypothesis. Every hypothesis is part of the
  source's setting (smoothness, geodesic, unit, rotation-free, Einstein equations, strong energy condition,
  `Θ₀ < 0`), and each is satisfied in the collapse example.
- `raychaudhuri_leviCivita` carries no hypothesis on the connection.
- Every limit in the notes is consistent with the Lean statements read above.

API map citations exist:

- Lightlike/Spacetime/API-map.md:191 (RaychaudhuriManifold, all four p1/m1 decls).
- Lightlike/Spacetime/API-map.md:257, entry 117 (`raychaudhuri_focusing_strongEC`), and the prose at :105-107.
- Lightlike/Cosmology/API-map.md:55-56 (the coordinate trust checks).

Findings, non-blocking; the maintainers should fix them in the catalogue:

1. **LL-0364 sources do not contain the theorem at the cited place.** Carroll gr-qc/9712019 Chapter 4 was read.
   It has the weak energy condition (4.72) and moves Λ into `T` after (4.74). It says "There are also stronger
   energy conditions ... we won't dwell on them", and it has no strong energy condition, Raychaudhuri equation
   or focusing. `sources-verified.json` records "Chapter 4" as verified only because the chapter exists.
   Hawking and Ellis Ch. 4 was not reachable, so that comparison is pending. The Lean docstring cites
   kar-sengupta-2007, which does support the statement (the paragraph after (16)). Recommended:
   - add `{ref: kar-sengupta-2007, location: "eq. (16)"}` to LL-0364;
   - keep Carroll only for the Λ absorption, at "eq. (4.74)".

   The note already says "comparison with the source is pending", so the entry is not dishonest, only imprecise.
2. The LL-0364 note says "Λ = 0" but not that a cosmological constant is absorbed into `T`
   (`einsteinEq_iff_absorb`); the module docstring says it. Adding it to the note would cover every point of
   the m2 hint there.
3. The manifold trust checks (`flrwManifold_comoving_expansion`, `minkowskiManifold_comoving_expansion`,
   `deSitterManifold_no_focusing`) and `twisted_no_focusing` have no catalogue or API-map entry. c1 does not
   require one (it covers the main theorems and pieces), but definition-of-done item 5 reads "its results".

## Not required by the done-when

The milestone title names "the exponential map", but neither the done-when nor the checklist requires it, and
GE3 does not provide it. `Cosmology/Raychaudhuri.lean:23-24` says so. An exponential map exists in the GE4 work
(`Lightlike/Spacetime/PenroseSingularity/ExpLocal.lean`).
