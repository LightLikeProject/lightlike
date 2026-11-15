# Lightlike/Asymptotics/Lorentzian

## Abstract (Alpha)

This API sets up the stationary phase analysis of the Lorentzian EPRL vertex amplitude in
coherent boundary states. For one triangle it gives the action at the level of spinors, shows
that its real part is at most zero with the maximum exactly at proportional spinors, and derives
the first critical relation. At a vertex, stationarity in the group variables is closure of the
normals, and the critical relation for SU(2) group elements holds exactly when two normals agree.
The second variation of the triangle factor is computed along a line and along the group
variation. The classification of the solutions and the asymptotic formula are not covered.

## Content (Alpha)

The setting is that of Barrett, Dowdall, Fairbairn, Hellmann and Pereira {1}, Section 4. For one
triangle, with spinors `Z = X_a† z` and `Z' = X_b† z`, the antilinear structure `jMap`, the
weight `triWeight` (the modulus of `e^S`) and the complex action `triAction` are defined [1].
The weight is at most one, so `Re S ≤ 0`, and it equals one exactly at proportional spinors [1].
Eliminating `z` gives the first critical relation, eq. (20) of {1} [1]. A maximal and a
non-maximal example check the definitions [1].

Stationarity in the group variables uses the triangle factor `triFactor` for a doubled spin
`n = 2k` and its derivative along `X ↦ X exp(tL)` with `L` in `sl₂(ℂ)`, at the source and at the
target end of a triangle [2]. The vertex condition is `Σ n_e n̂_e = 0` and `Σ p_e n̂_e = 0`, and
for `p = γk` it is closure of the normals, with `γ` dropping out [2]. A configuration of two
opposite triangles is stationary, and a single triangle is not [2].

For unit spinors, `2|⟨x,y⟩|² = ‖x‖²‖y‖² + n(x)·n(y)`, so unit spinors with equal normals differ
by a phase [3]. For SU(2) group elements the relation `A⁻¹ξ = c B⁻¹Jξ'` with a unit `c` holds
exactly when the normals of `A⁻¹ξ` and `B⁻¹Jξ'` agree [3].

The second derivative of the triangle factor along `Z + tW` is `triFactor · (ℓ² + H)`, with `ℓ`
the log derivative and `H = -n (⟨W,ξ⟩/⟨Z,ξ⟩)² - (n + 2ip)(‖W‖²/‖Z‖² - 2 (Re⟨Z,W⟩)²/‖Z‖⁴)` [4]. Under
the group variation `X ↦ X exp(tL)` at `Z ∥ ξ`, with `c = β + iα`, this becomes
`-n (½ c·n̂)² - (n + 2ip)(¼(|β|² + |α|² + 2 (β×α)·n̂) - 2 (½ β·n̂)²)`, using
`4‖L†ξ‖² = Σ|c_i|² + 2 (β×α)·n̂` [4]. A rotation and a boost about the axis of a spinor give
`-ip/2` and `+ip/2` [4].

## Lean References

1. Lightlike/Asymptotics/Lorentzian/Action.lean - `Asymptotics.Lorentzian.triWeight_le_one`,
   `Asymptotics.Lorentzian.triWeight_eq_one_iff`, `Asymptotics.Lorentzian.norm_exp_triAction`,
   `Asymptotics.Lorentzian.exists_critical_relation`, `Asymptotics.Lorentzian.jMap_jMap`,
   `Asymptotics.Lorentzian.inner_jMap_self`, `Asymptotics.Lorentzian.triWeight_eq_one_example`,
   `Asymptotics.Lorentzian.triWeight_lt_one_example`
2. Lightlike/Asymptotics/Lorentzian/Stationary.lean -
   `Asymptotics.Lorentzian.hasDerivAt_triFactor_gen`,
   `Asymptotics.Lorentzian.hasDerivAt_triFactor_gen_target`,
   `Asymptotics.Lorentzian.stationary_iff`, `Asymptotics.Lorentzian.stationary_iff_closure`,
   `Asymptotics.Lorentzian.spinVec_jMap`
3. Lightlike/Asymptotics/Lorentzian/Critical.lean - `Asymptotics.Lorentzian.two_norm_inner_sq`,
   `Asymptotics.Lorentzian.phase_iff_spinVec_eq`, `Asymptotics.Lorentzian.su2_relation_iff`

4. Lightlike/Asymptotics/Lorentzian/Hessian.lean - `Asymptotics.Lorentzian.hasDerivAt_lineLogDeriv`,
   `Asymptotics.Lorentzian.hasDerivAt_triFactor_line`,
   `Asymptotics.Lorentzian.hasDerivAt_deriv_triFactor_line`,
   `Asymptotics.Lorentzian.norm_adjoint_gen_sq`, `Asymptotics.Lorentzian.hessLine_group`

## References

1. J. W. Barrett, R. J. Dowdall, W. J. Fairbairn, F. Hellmann, R. Pereira, Lorentzian spin foam
   amplitudes: graphical calculus and asymptotics, *Class. Quantum Grav.* 27 (2010) 165009.
