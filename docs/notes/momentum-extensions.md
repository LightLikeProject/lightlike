# The self-adjoint extensions of the momentum on `L²(0, 1)`

Source read: G. Bonneau, J. Faraut, G. Valent, "Self-adjoint extensions of operators and the teaching of quantum mechanics",
arXiv:quant-ph/0103153 (read in its arXiv HTML version):
- Appendix A.3 (finite interval): `D(P†) = D_max(0, L)`, where `D_max(a, b)` (Appendix A) is the set of `ψ` absolutely
  continuous on `[a, b]` with `ψ, ψ' ∈ L²(a, b)`; `D₀(P) = {ψ ∈ D_max(0, L) : ψ(0) = ψ(L) = 0}`.
- Section 5.3, eq. (14): the momentum on `[0, L]` has deficiency indices `(1, 1)`, and its self-adjoint extensions are the `P_θ` with domain
  `D_θ = {ψ ∈ D_max(0, L) : ψ(L) = e^{iθ} ψ(0)}`, `θ ∈ [0, 2π]`.

Library statements (files `MomentumAdjoint`, `MomentumBoundary`, `MomentumTheta`, checks in `TestsMomentumTheta`), for `momentumMin = -i d/dx` on the `C²` functions with compact support
in `(0, 1)`, and `L = 1`:

| Source | Library | Check |
|---|---|---|
| A.3, `D(P†) = D_max(0, L)` | `mem_adjoint_iff_ac`: `y ∈ D(A†)` iff `y` agrees a.e. with an absolutely continuous `f` on `[0, 1]` with `f' ∈ L²(0, 1)`; `mem_adjoint_iff_primitive` (the same through primitives `c + ∫₀ˣ g`), `A† y = -i g` | matches, `L = 1` |
| A.3, `D₀(P)` | `domZero` (`y(0) = y(1) = 0` for the continuous representative), `momentumZero` (`A†` on `D₀`); `momentumZero_eq_closure`: `momentumZero` is the closure of `momentumMin` | matches, `L = 1` |
| (14), `D_θ` | `domTheta θ`: `y ∈ D(A†)` with `y(1) = e^{iθ} y(0)`; `momentumTheta θ` = `A†` on `D_θ` | matches, `L = 1`, `θ ∈ ℝ` |
| (14), "these are the self-adjoint extensions" | `selfAdjoint_extensions_momentumZero`: `B ⊇ P` (on `D₀`) is self-adjoint iff `B = P_θ` for some real `θ`; also for the closure of `momentumMin` (`selfAdjoint_extensions_eq_momentumTheta`) | matches |

Supporting: `momentumZero_eq_closure` (via Physlib's `adjoint_adjoint_eq_closure`), `boundary_form_momentum` (`⟪A† y, z⟫ - ⟪y, A† z⟫ = i (conj y(1) z(1) - conj y(0) z(0))`, by Mathlib's integration by parts for absolutely
continuous functions), `bv_closure`, `momentumMin_symm`.

Differences from the source, kind convention: (a) the interval is `[0, 1]`, `L = 1` (the general `L` is the unitary rescaling
`ψ(x) ↦ √L ψ(L x)`, not stated); (b) `θ` ranges over `ℝ` instead of `[0, 2π]` (the same set of operators; `θ` and `θ + 2π` give the same
`P_θ`). Neither changes the statement for the interval `[0, 1]`; (a) is a special case, so for a general `L` the statements are not made here.
Not stated (and not claimed): the spectrum, eq. (15).
