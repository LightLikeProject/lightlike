# HA3: the Plancherel formula of SL(2,R) is proved for radial functions only (G3-145, G3-146)

Met: the principal and discrete series are defined and unitary, the Casimir values (`casimir_principal`, `casimir_discrete`, `casimir_complementary`), the complementary-series wrong-parameter test (`NoInvariantForm`), and the spherical Plancherel identity with density `ρ tanh(πρ)` (`SphericalClean`) for smooth compactly supported `SO(2)`-biinvariant functions.
Missing: the Plancherel formula on all of `L²(SL(2,R))`, which is Harish-Chandra's decomposition: the non-radial and odd principal series contributions and the discrete-series terms (formal degrees `n - 1/2`-type weights), from the Fourier inversion of the orbital integrals.
Only the radial case is proved; a radial function sees none of the discrete series and only the even principal series.
The step beyond the Abel route is an inversion formula for the (non-radial) Fourier transform via characters or orbital integrals, with no upstream support; estimated well above the $40 cap.
Status (24 Nov 2026): HA3 is recorded as met for the spherical Plancherel, full decomposition missing.

## The complementary-series wrong-parameter test is at the Lie-algebra level (G3-145, 26 Nov 2026)

`no_invariant_form` (`Lightlike/Lorentz/SL2RPlancherel/NoInvariantForm.lean`) shows that for `|τ| > 1` no positive definite Hermitian form
on a space of smooth functions with `E, F, H` acting as the derived principal-series action makes `E, F, H` skew; this is the form of
the HA3 trust check "a complementary-series parameter outside `(0, 1/2)` shown to fail" that is proved. A group-level version
(invariance of the form under the group action itself) is not covered, for a concrete reason: the model `|cx+d|^{-τ-1}` is singular at
the pole of `g`, so no space of differentiable functions is stable under the whole group. The `K`-fixed vector `(1+x²)^{-(τ+1)/2}` has the
smooth orbit `((ax+b)² + (cx+d)²)^{-(τ+1)/2}`, but the vectors `E v`, `F v`, `H v` obtained from it by the derived action have singular
orbits; and an abstract Hermitian form has no continuity that would let one differentiate its invariance along one-parameter subgroups.
A group-level statement would need a Hilbert space with a strongly continuous unitary representation and a `K`-fixed unit vector, whose
spherical function `φ(g) = ⟨π(g) v, v⟩` satisfies `|φ| ≤ 1`, against the growth of the spherical function for `|τ| > 1`; this development
is not done.

## K-types `(l, r)`, attempt 1 (25 Nov 2026)

Question: for the ladder images `h_{l,r}[G] = (ladUp (l-1) r ∘ … ∘ ladUp 0 r)(sinh^r G^{(r)}(cosh ξ))` of a smooth compactly supported `G`
(the `K`-type `(l, r)` of the principal-series picture), is `π² ∫ |h_{l,r}[G]|² sinh ξ dξ = ¼ ∫ ρ tanh(πρ) wl(l,ρ) wl(r,ρ) |Ĝ(ρ)|² dρ`?

- MEASURED (sympy/mpmath, `G = exp(-cosh ξ)`, `(l, r) ∈ {(0,0),(1,0),(0,1),(1,1),(0,2),(1,2)}`, relative difference at most `2e-7`,
  of the order of the quadrature error on a trapezoid grid): yes, with `wl(n, ρ) = ∏_{k<n} ((k + ½)² + ρ²)`, also for odd `r`. So the target is the
  right statement and the factor `(l + ½)² + ρ²` of the left recursion does not depend on `r`.
- PROVED (new): `radialCasimir_ladUp` (`LadderCasimir.lean`): `Cas_{l+1,r} ∘ ladUp l r = ladUp l r ∘ Cas_{l,r}` on `ξ > 0` for smooth `F`
  (no shift); `ladUp_profile` (`LadderProfile.lean`): `ladUp k 0 (sinh^k G^{(k)}∘cosh) = sinh^{k+1} G^{(k+1)}∘cosh` on `ξ > 0`, which is
  the base `(0, r) = (r, 0)`: `Cas_{k,0} = Cas_{0,k}` as operators.
- Not proved, with the concrete obstructions: (1) `radialCasimir_ladUp`, `ladder_adjoint`, `ladDown_ladUp` assume a global `ContDiff` of `F`,
  but `ladUp l r F` is only smooth on `ξ > 0` (`ladCoeff` has `1/sinh ξ`), so the recursion needs local (`ContDiffOn` on `Ioi 0`)
  versions; `radialCasimir_ladUp` is now stated for `ContDiffOn ℝ ∞ F (Ioi 0)` (done, with `hasDerivAt_ladUp_at`), `ladder_adjoint`
  and `ladDown_ladUp` are still global (about 100 lines). (2) The boundary term of the adjoint identity at
  `ξ → 0`: `h_{l,r}[G](a) conj(h_{l+1,r}[G'](a)) sinh a → 0` needs `h_{l,r}[G] = O(ξ^{l+r})` with a smooth quotient, a separate induction
  (about 150 lines). (3) The polarised induction of `KClaim_succ` with the weight `wl l · wl r`. Estimated 500 more lines.

### Closed form found in attempt 2 (25 Nov 2026): the whole `(l, r)` recursion lives in `v = cosh ξ`

`ladUp l r (sinh^{l+r} ξ · u(cosh ξ)) = sinh^{l+r+1} ξ · (u' + r u/(v+1))(cosh ξ)` (direct computation:
`(n cosh - l cosh - r) u + sinh² u'` with `n = l + r` equals `r (cosh - 1) u + sinh² u'`). With `w = (v+1)^r u` the step is `w ↦ w'`, hence

`h_{l,r}[G](ξ) = sinh^{l+r} ξ · (v+1)^{-r} (d/dv)^l [ (v+1)^r G^{(r)}(v) ]` at `v = cosh ξ`,

checked symbolically for `(1,1), (2,1), (1,2), (2,2)` (sympy; e.g. `h_{1,1} = (v-1)((v+1) G'' + G')`, `h_{2,2} = (v-1)² ((v+1)² G'''' + 4 (v+1) G''' + 2 G'')`).
Consequences: (i) the boundary term at `ξ → 0` disappears (the weight `(v-1)^{l+r}(v+1)^{l-r}` vanishes at `v = 1` and the factor is a smooth
function of `v`, so no `O(ξ^{l+r})` induction is needed); (ii) the `L²(sinh ξ dξ)` norm is the Jacobi-weighted Sobolev form
`∫_{v>1} (v-1)^{l+r} (v+1)^{l-r} |(v+1)^{-r} ∂^l ((v+1)^r G^{(r)})|² dv`, the exact analogue of `Kform` of `KTypePlancherel.lean`
(which is `r = 0`); (iii) the induction step is integration by parts in `v` against this weight, then the intertwining
`radialCasimir_ladUp` (already proved) in `v`. Remaining plan: define `Wform r l F G` (this form), prove the `v`-variable step
`Wform r (l+1) F F = Wform r l F (radialQ F) + l (l+1) Wform r l F F` with `(v+1)^r` conjugation, base `l = 0` = `Kform r` of
`KTypePlancherel`, then the polarised induction `KClaim_succ` with the weight `wl l · wl r`.

Done after the closed form: `LadderLocal.lean`: `ladder_adjoint_boundary` (adjointness on `[a, b] ⊂ (0, ∞)` for `ContDiffOn ℝ 1` on `(0, ∞)`, with the boundary term `P(b) - P(a)`, `P = F conj(G) sinh`) and `ladDown_ladUp_local` (`ladDown (l+1) r ∘ ladUp l r = Cas + l (l+1)` for `ContDiffOn ℝ 2`). Open: the `a → 0`, `b → ∞` limits (the closed form gives `h_{l,r} = sinh^{l+r} · smooth(cosh)`, so `P(a) → 0`, and compact support kills `P(b)`), the sesquilinear form and the polarised induction with weight `wl l · wl r`.
