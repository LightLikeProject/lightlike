# G3-074: the Parke-Taylor formula for the true colour-ordered amplitudes (plan)

State (24 Nov 2026): proved on main or queued: `bgAmplitude` (Berends-Giele recursion of the Feynman rules), Ward
identity, residue factorization (`residue_factorization'`), the recursion `bgAmplitude_eq_sum_channels'` with the large-z
falloff as hypothesis `hinf`, and the three-gluon MHV amplitudes (`bgAmplitude_three_mmp`, `_mpm`, `MHVTrue.lean`).

Design. `IsBCFWFamilyMHV` forgets the square spinors, so it is not discharged. Instead prove by induction on `n` that
for every conserved generic `(l, lt)` the amplitude with `epsMinus` (reference `|qs]`) at legs `0` and `j` and `epsPlus`
(reference `⟨qa|`) elsewhere equals `parkeTaylor`, via the `[0, 1⟩` shift (negative `0`, positive `1`; the adjacent case
`j = 1` by cyclic relabelling so that the other negative gluon is last).

Steps.
1. Falloff (3.6) for the shift `|0̂] = |0] + z|1]`, `|1̂⟩ = |1⟩ − z|0⟩` with constant references: `ε̂₀ = O(1/z)`,
   `ε̂₁ = O(1/z)`, momenta of an interval containing exactly one of the legs `0, 1` are `O(z)`, otherwise `O(1)`, and the
   propagator `1/P̂²` is `O(1/z)` for such an interval (linear `P̂² = P² + z c`, `c ≠ 0`), `O(1)` otherwise. Induction on
   the intervals of `bgCurrent`: a current is `O(1)` if it contains neither leg, `O(1/z)` otherwise. The amputated
   last vertex then gives `Â(z) = O(1/z)`. (The wrong shift `[+, −⟩` fails by the same count.)
2. The channel set is `{(1, d) : 2 ≤ d ≤ m + 1}`. Hypotheses of `bgAmplitude_eq_sum_channels'`: `hlin`, `hP0`, `hzI`,
   `hinj`, `hfix` from generic kinematics.
3. Evaluate `channelTerm` with `residue_factorization'`: every channel except `d = 2` vanishes (an amplitude with at
   most one negative gluon vanishes: all-plus and single-minus, needs the Berends-Giele closed forms of those currents;
   three-point vanishing by special kinematics); for `d = 2` the product is the true `(n−1)`-point amplitude (induction)
   times `antiMHV3`, with the internal leg's references the global `qs`, `qa`.
4. `parkeTaylor_bcfw_far` closes the induction.

Open core: step 1 (formalisable by degree bookkeeping with `IsBigO` along `cocompact ℂ`), and the vanishing theorems of
step 3.


## Progress (24 Nov 2026, evening)

Proved on this branch: three-gluon base cases (`MHVTrue.lean`), the falloff
(`BCFWFalloff.lean`, `BCFWFalloffSpinor.lean`: `tendsto_bgAmplitude_shift`), the vanishing of the all-plus and single-minus
amplitudes and gauge invariance (`MHVVanishing.lean`). Local: `MHVThreeGen.lean` (three-gluon amplitudes for general
conserved kinematics, `bgAmplitude_three_mmp_gen`, `bgAmplitude_three_ppm_gen`).

Remaining work, in order:
* T1 a null vector is `nullMom lP ltP` for some spinors (needed for `hP` of `bgAmplitude_eq_sum_channels'`).
* T2 the setting: `mom0`, `pol0 j`, `mhvTrue m j l lt qs qa`, the zero-shift identities `shiftedMom l lt 0 = mom0`.
* T3 the hypotheses of `bgAmplitude_eq_sum_channels'` for the channel set `C = {(1, d) : 2 ≤ d ≤ m + 1}`: `hlin`
  from `FalloffData.momRange_eq` (the computation inside `FalloffData.ord_prop`), `hcons`, `htr`, `hfix`, `hinj`
  (distinct poles: a genericity hypothesis), `hP` (T1), `hq1`, `hq2` (genericity of `qs`, `qa`).
* T4 channel terms: `bgAmplitude_oneMinus` and `bgAmplitude_allPlus` must be applied to `leftMom`/`leftPol`/`collapse`;
  weaken their hypotheses `∀ t` to `∀ t ≤ m + 2` first. Channels `d ≥ 3` vanish; for `d = 2` the left factor is a
  three-point amplitude at the pole where the angle spinors of `1̂` and `2` are proportional (`ptShift_onshell`).
* T5 three-point amplitudes at anti-MHV kinematics: `[++−]` is `ppm_gen = [01] ⟨q'2⟩²/(⟨q'0⟩⟨q'1⟩) = antiMHV3`
  (angle spinors proportional, `c_i ∝ [jk]`), `[−−+]` vanishes there (factor `⟨01⟩`); the cyclic rotations by
  `bgAmplitude_rotLabels`.
* T6 identify the right factor with the `(n−1)`-point true amplitude (induction hypothesis) and close with
  `parkeTaylor_bcfw_far`; the adjacent case `j = 1` by cyclic relabelling (`bgAmplitude_rotLabels`) so that the other
  negative gluon is last.


## Obstruction found and its resolution (24 Nov, late)

`bgAmplitude_eq_sum_channels'` needs the polarizations to be entire in `z` (`Differentiable ℂ`). With the constant
references `qs`, `qa` of the falloff theorem, `ε̂₀ = √2|q]⟨0|/[q 0̂]` has a spurious pole at `[q 0̂] = 0` and so does `ε̂₁`.
Entire polarizations need the references `|q] = |1]` (so that `[q 0̂] = [1 0]` is constant) and `⟨q'| = ⟨0|`
(`⟨0 1̂⟩ = ⟨0 1⟩`); but then the termwise power counting of `BCFWFalloff.lean` does not give the falloff.
Resolution: (R1) the gauge shift of `ε₋` (conjugate of `epsPlus_sub_epsPlus`); (R2) reference independence of the true
amplitude, by `bgAmplitude_update_add_mom` leg by leg (needs all propagators nonzero); (R3) for large `|z|` the good-gauge
amplitude equals the generic-gauge one, so it also tends to `0`. Then the recursion applies with entire polarizations, and
the induction hypothesis may be used with any references because of (R2).


## State after R3 and the case analysis of the channel terms

Done: R1 (`epsMinus_sub_epsMinus`), R2 (`bgAmplitude_refs`), R3 (`tendsto_goodGauge` in `MHVRecursion.lean`, good gauge
`qs = l 1`, `qa = lt 0`, with polarizations constant in `z`), T1 (`exists_nullMom_of_null`).

Case analysis of `channelTerm` for the channel `(1, d)` at its pole (negative gluons `0`, `j ≥ 2`; left amplitude has legs
`1̂ … d` and the internal leg, right amplitude has `0̂`, `d+1 … m+2` and the internal leg at position 1):
* `j > d`: term A has the left factor `(+…+, −)`, term B the left factor `(+…+, +)` = all-plus = 0. For `d ≥ 3` the left
  factor of term A is single-minus = 0 (`bgAmplitude_oneMinus`, generic angle brackets); for `d = 2` it is the
  three-point `[++−]` in angle-collinear kinematics = `antiMHV3` (`bgAmplitude_three_ppm_gen`), the surviving term.
* `j ≤ d`: term A has the right factor `(0̂⁻, +, …, +)` = single-minus = 0; term B has the left factor
  `(…j⁻…, +)` = single-minus = 0 for `d ≥ 3`; for `d = 2 = j` it is the three-point `[+−+]` (rotate labels), nonzero,
  with the right factor the `(n−1)`-point MHV amplitude with the internal leg negative at position 1 (adjacent case).
* At the `d = 2` pole `⟨2| (lt 1 − z lt 0) = 0`: `z = ⟨12⟩/⟨02⟩`, `lt 1 − z lt 0 = (⟨01⟩/⟨02⟩) lt 2`, so
  `lP = (⟨01⟩/⟨02⟩) l 1 + l 2`, `ltP = lt 2` (the choice of `IsBCFWFamilyMHV`).
Done (T3-T6): the vanishing lemmas applied to the channel factors (`MHVChannels.lean`), the channels `[1,d]`,
`d ≥ 3`, vanish (`MHVChannelZero.lean`, `channelTerm_zero_far`), the channel `[1,2]` evaluated for `j ≥ 3`
(`MHVChannelTwo.lean`, `MHVStepFar.lean`) and for `j = 2` (`MHVChannelTwoJ2.lean`, `MHVStep.lean`; the three-point
`[+−+]` by cyclic rotation of `[++−]`), the reduced kinematics (`MHVReduce.lean`), the propagator sign against
`antiMHV3/(⟨12⟩[12])` (the factor `([12]/c)/(⟨12⟩[12])` of `parkeTaylor_bcfw_far`, `MHVPTStep.lean`), the base
case (`MHVBase.lean`), adjacent negative gluons by `bgAmplitude_rotLabels` (`MHVRotate.lean`) and the induction
(`MHVGood.lean`, `MHVInduction.lean`): `trueAmp_eq_ptN`.

The genericity is a class `G` of kinematics closed under the reduction (`ClosedClass`), because the reduced
kinematics of the channel `[1,2]` must again satisfy the nonvanishing hypotheses of the recursion at every level.
Open: that the class is nonempty and open for `n ≥ 4` (the statement is vacuous for the empty class); an explicit
`n = 4` kinematic point in `G` would be the first check.
