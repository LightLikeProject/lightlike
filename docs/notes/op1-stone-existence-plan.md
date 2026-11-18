# T-OP1-P2 (Stone's theorem, existence): plan

Statement: for a self-adjoint `A : H →ₗ.[ℂ] H` there is a strongly continuous unitary group `U` with
`U.generator = A` (`Tasks/OP/T_OP1_P2.lean`). Route: the Yosida approximation, without the spectral theorem
(`docs/tasks/decomposition.yaml`, route 2).

## Check before build (17-18 November 2026)

* Mathlib: `LinearPMap` has the adjoint, `IsSelfAdjoint`, `IsClosed`, `closure`; an open pull request adds a
  resolvent (`LinearPMap` resolvent and resolvent identities); there is no resolvent in the pinned checkout,
  and no Hille-Yosida, no strongly continuous semigroup. For a bounded operator `B` there is `NormedSpace.exp`
  on `H →L[ℂ] H` with `hasDerivAt_exp_smul_const` and `exp_add_of_commute`. Used: those; the resolvent is
  written here (`resolventCLM`), with the names of the pull request kept where possible.
* Physlib: `LinearPMap.IsUnbounded` and closure/adjoint algebra; no resolvent or semigroup.
* Tau Ceti: no unbounded operators, semigroups or Stone's theorem on its roadmap.
* Lightlike: self-adjointness is Mathlib's `A† = A`, which gives a dense domain, closedness, symmetry
  (`generator_isFormalAdjoint`-style) and trivial deficiency spaces at non-real `z`
  (`deficiencySpace_of_isSelfAdjoint`). No blocker.

## Pieces

1. Resolvent of a self-adjoint operator at a non-real `z`: `‖(A - z) x‖² = ‖(A - Re z) x‖² + (Im z)² ‖x‖²`,
   range closed (A closed), range dense (trivial kernel of `A† - conj z`), so `(A - z)⁻¹` is a bounded operator
   `R z` of norm at most `1 / |Im z|`, with `R z (A - z) x = x`, `(A - z) R z y = y`, `(R z)† = R (conj z)`.
2. Strong limit `n R (± i n) y → ± i y` for all `y` (dense domain, uniform bound).
3. Bounded self-adjoint approximants `A_n = (n² / 2) (R (i n) + R (-i n))`, `A_n x → A x` on the domain.
4. Unitary groups `U_n t = exp (i t A_n)` (Mathlib bounded exponential); the Cauchy estimate
   `‖U_n t x - U_m t x‖ ≤ |t| ‖A_n x - A_m x‖` from the derivative of `s ↦ U_n s U_m (t - s) x`.
5. The limit `U t x = lim U_n t x` (dense domain, isometries): unitary, group law, strong continuity
   (locally uniform limit).
6. Generator: `A ≤ U.generator` (the integral identity `U t x - x = i ∫₀ᵗ U s A x ds`, limit of the same for
   `U_n`), both self-adjoint, hence equal (P1 gives that `U.generator` is self-adjoint; maximality).

## Estimate

Pieces 1-3: about 400 lines, pieces 4-5: about 400, piece 6: about 150. Several sessions of work; each piece
is a library file that gates on its own. No catalogue entry until `T-OP1-P2` is proved.
