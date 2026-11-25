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
