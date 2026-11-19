# CO1 (G1-024 flat case, G1-025): compared with Carroll's lecture notes (18 November 2026)

Source read: S. M. Carroll, *Lecture Notes on General Relativity* (1997, arXiv gr-qc/9712019, the lecture notes, not the book), chapter 8,
pp. 217-218 (eq. (8.1)) and pp. 223-225 (eqs. (8.35)-(8.38) and the text after (8.41)).

## G1-024 (flat case): `flat_flrw_of_killing` (`Lightlike/Spacetime/HomogeneousIsotropic.lean`)
* Carroll, pp. 217-218: "the universe can be foliated into spacelike slices such that each slice is homogeneous and isotropic";
  "homogeneity and isotropy together imply that a space has its maximum possible number of Killing vectors"; "Therefore we can take
  our metric to be of the form ds² = −dt² + a²(t) γ_ij(u) du^i du^j (8.1)", with `γ` maximally symmetric, "we have scaled t such that g_tt = −1";
  no cross terms `dt du^i` (comoving coordinates).
* Ours: a smooth metric of any signature on `ℝ⁴` for which the three spatial translations `∂_k` and the three rotations
  `x_i ∂_j − x_j ∂_i` are Killing (Lie derivative zero on the coordinate basis fields) has `g_0k = 0`, `g_ij = a(x⁰) δ_ij`, `g_00 = b(x⁰)`.
* Differences:
  - (resolved, 19 November 2026 ~04:00) every curvature: `curved_flrw_of_killing` (`HomogeneousIsotropicCurved.lean`) gives, for every `k`,
    `g_{ij} = a(t) δ_{ij}/(1 + k|x|²/4)²` (the maximally symmetric 3-metric of curvature `k` in isotropic coordinates) from the rotations and the
    curved translations `Pₘ = (1 − k|x|²/4)∂ₘ + (k/2)xₘ(x · ∂)` as Killing fields on `1 + k|x|²/4 > 0`. Carroll's (8.7) writes `γ` in the
    radial coordinate `dr²/(1 − kr²) + r²dΩ²`; ours is the isotropic form (representation, as for LL-0133).
  - weaker: the Killing fields are given as the standard coordinate fields of `ℝ⁴`; the passage from a foliation by homogeneous and
    isotropic slices to such adapted coordinates is not proved (Carroll states it as following from maximal symmetry).
    Route (A), 19 November 2026: for each slice the passage is proved in orbit charts (`isometric_spaceForm`, LL-XXXX-g): a 3-metric with a
    Killing algebra of the space-form type (structure constants `S_k`), isotropic at `p`, is there `c · δ/(1 + k|x|²/4)²`. Still weaker
    than Carroll: (i) Killing algebra of the model type, not the isometry group (the structure constants are hypotheses; the classification
    of six-dimensional Killing algebras with `so(3)` isotropy and the step from a group action are not proved); (ii) (resolved, 19 November
    2026 ~05:30) the assembly into four dimensions: `flrw_of_killing_algebra` (LL-XXXX-h) gives `b(t) dt² + a(t) δ/(1 + k|x|²/4)²` in the
    chart `Φ(t, ξ) = exp(∑ ξₑ Yₑ)(c t)` when the rotations vanish along a worldline `c` (no cross terms, `g₀₀ = g(c', c')`).
    Attempts at line (i), the step from an isometry group to the Killing algebra of the model type (17:10 rule):
    (A1) Carroll's group route: homogeneity and isotropy as an isometry group acting transitively with isotropy `SO(3)`; its one-parameter
    subgroups give Killing fields with the Lie algebra's brackets. Fails at two named missing pieces: the Myers–Steenrod theorem (isometries
    are smooth and the isometry group is a Lie group acting smoothly) and the exponential map / one-parameter subgroups of a Lie group; neither
    is in Mathlib or Physlib (grep 19 November 2026: no `Myers`-`Steenrod` result, no `IsometryGroup`, no exponential in
    `Geometry/Manifold/GroupLieAlgebra.lean` or `Geometry/Manifold/Algebra/LieGroup.lean`, no `OneParameter` subgroup of a Lie group).
    (A2) Infinitesimal route, bypassing Lie groups: smooth one-parameter families of isometries realising homogeneity and isotropy; their
    generators are Killing, the brackets of Killing fields are Killing (`KillingAlgebra.lean`), and the so(3)-equivariance of the brackets
    `[𝔪, 𝔪] → 𝔨 ⊕ 𝔪` fixes them to `S_k` after a change of complement. Fails at: (a) rigidity, a Killing field is determined by `(X, ∇X)` at a
    point (`∇∇X = R(·, X)·` and uniqueness along curves), needed for the algebra to be six-dimensional and closed: absent from Mathlib, and
    in-house only for the flat case (`eq_affine_of_skew_deriv`, `KillingMinkowski.lean`); (b) Schur's lemma over `ℝ` for the vector
    representation of `so(3)`: Mathlib's (`RepresentationTheory/FDRep.lean`, `AlgebraRepresentation/Basic.lean`) needs an algebraically closed
    field.
    Route (B) (constant curvature, normal coordinates) needs the curvature's naturality under pullback and the exponential map, absent.
  - representation: `g_00 = b(t)` is not normalised to `−1` (Carroll rescales `t`), and the spatial factor is `a(t)` for Carroll's `a²(t)`.
  - representation: the slices of curvature `k` in isotropic coordinates `δ/(1 + k|x|²/4)²` for Carroll's radial form (8.7), `dr²/(1 − kr²) + r²dΩ²`.

## G1-025: `bigBang_age_le`, `bigBang_density_tendsto_atTop` (`Lightlike/Cosmology/BigBang.lean`)
* Carroll, p. 224: "set Λ = 0, and consider the behavior of universes filled with fluids of positive energy (ρ > 0) and nonnegative
  pressure (p ≥ 0). Then by (8.35) we must have ä < 0. ... if we trace the evolution backwards in time, we necessarily reach a singularity
  at a = 0. Notice that if ä were exactly zero, a(t) would be a straight line, and the age of the universe would be H0⁻¹. Since ä is
  actually negative, the universe must be somewhat younger than that." p. 225: "the energy density becomes arbitrarily high as a → 0".
* Ours: with Friedmann's second equation, `Λ = 0` and `ρ + 3p ≥ 0` (which Carroll's `ρ > 0, p ≥ 0` implies), `ä ≤ 0`; on an interval
  `(t₁, t₂)` where `a > 0` and with `ȧ(t₀) > 0`, `t₀ − t₁ ≤ a(t₀)/ȧ(t₀) = 1/H(t₀)`; with Friedmann's first equation and `k ≥ 0`, if `a → 0`
  as `t ↓ t₁` then `ρ → ∞`.
* Differences:
  - (resolved with a difference, 19 November 2026 ~06:00) the singularity itself: `bigBang_singularity` (`BigBangSingularity.lean`,
    LL-XXXX-i) proves that with `ρ + 3p ≥ 0` **and `p ≤ ρ`**, either `a → 0` at the left end of the interval or `a'`, `a''`, `ρ`, `p` stay
    bounded there (`(ρ a⁶)' = 3a⁵a'(ρ − p) ≥ 0`, from Carroll's (8.34)). Differences:
    - weaker: the extra hypothesis `p ≤ ρ`. Carroll's claim under `ρ > 0`, `p ≥ 0` alone is false: `a = 1 + √t`, `k = 0`, has `ρ > 0`,
      `p > 0`, `ȧ > 0`, `ä < 0` on `(0, ∞)`, and `ȧ → ∞` as `t ↓ 0` while `a → 1` (`onePlusSqrt_friedmann`; the density diverges, at
      `a = 1`, and `p > ρ` there, `onePlusSqrt_not_dominant`).
    - representation: "the maximal interval" as the dichotomy (`a → 0`, or no blow-up of `a'`, `a''`, `ρ`, `p`): without an equation of
      state the Friedmann equations do not determine a continuation, so maximality is not a property of `a` alone.
    Two readings of p. 224 ("universes filled with fluids of positive energy (ρ > 0) and nonnegative pressure (p ≥ 0)"; the equation of
    state `p = wρ`, `w` constant, is introduced at (8.21)-(8.23) as what "essentially all of the perfect fluids relevant to cosmology
    obey" and not restated there): (a) as printed, for any `ρ > 0`, `p ≥ 0`: false by `onePlusSqrt_friedmann`, true with `p ≤ ρ`
    (`bigBang_singularity`); (b) in the (8.21) setting, `p = wρ` with constant `w > -1/3` (Carroll's `w ≥ 0`): proved,
    `bigBang_singularity_of_eos` (`BigBangEOS.lean`, LL-XXXX-j), no further hypothesis.
    The gap row's three parts: finite age (`bigBang_age_le`, strict `bigBang_age_lt_of_pos_density`) and `ρ → ∞` as `a → 0`
    (`bigBang_density_tendsto_atTop_of_pos`, every `k`, `ρ(t₀) > 0`) are in the CO1 branch (regge/co1-homogeneous); `a → 0` at a singular left end is
    `bigBang_singularity` (with `p ≤ ρ`) and `bigBang_singularity_of_eos` (with `p = wρ`).
  - (resolved, 18 November 2026 ~23:30) the strict bound: `bigBang_age_lt_of_pos_density` proves `t₀ − t₁ < a(t₀)/ȧ(t₀)` under Carroll's
    `ρ > 0`, `p ≥ 0` (`ä < 0`; the bound at an earlier time `s` and the strict tangent inequality at `t₀`). No difference left.
  - (resolved, same time) the density for every `k`: `bigBang_density_tendsto_atTop_of_pos` proves `ρ → ∞` as `a → 0` for every `k` when
    `ρ(t₀) > 0` (Carroll's `ρ > 0`), from `ρ(t) a(t)² = (ȧ(t)² + k)/(8πG/3) ≥ ρ(t₀) a(t₀)²`. The hypothesis `ρ > 0` is needed:
    the Milne universe `a = t`, `k = −1`, `ρ = p = 0` (`milne_friedmann`) solves the equations with `a → 0` and bounded density. No difference left.
