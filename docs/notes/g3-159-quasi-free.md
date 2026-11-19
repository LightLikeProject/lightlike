# G3-159 / G2-077: quasi-free vectors of a representation of the CCR (Dereziński, Section 9.1)

Source read: J. Dereziński, arXiv:math-ph/0511030 (key `derezinski-2006`): Section 3.1, pp. 9-10 (eq. (8)-(9), a
representation of the CCR; Theorem 2, eq. (11)-(12); a representation is *regular* if `t ↦ W(ty)` is strongly continuous
for each `y`, p. 10); Section 9.1, pp. 38-39 (eq. (70), quasi-free vectors; Theorems 37, 38 and 39).

| Source | Library | Check |
|---|---|---|
| (8)-(9), p. 9: `y ↦ W(y)` unitary with `W(y₁)W(y₂) = e^{-i y₁ωy₂/2} W(y₁ + y₂)` | `WeylSystem h K` (`QuasiFree`) | (representation) `(Y, ω)` is a complex inner product space `h` with `ω = σ = Im⟪·,·⟫`, as in the repository's `CCRRep`; the continuity condition of `CCRRep` is dropped |
| Theorem 2, (11)-(12), p. 9: `W(0) = 1`, `W(t₁y)W(t₂y) = W((t₁ + t₂)y)` | `WeylSystem.W_zero`, `WeylSystem.W_line_add` | matches |
| p. 10: regular representations | `CCRRep` (strongly continuous along every real line), `WeylSystem.toCCRRep` | matches |
| (70), p. 38: `(Ψ|W(y)Ψ) = exp(-¼ yηy)` for a quadratic form `η` | `CCRRep.IsQuasiFree R Ψ η` | (representation) `η` is a symmetric real bilinear form on `h` and `yηy = η(y, y)` |
| p. 38: "`η` is necessarily positive" | `CCRRep.IsQuasiFree.nonneg` | matches |
| Theorem 37, p. 38: a quasi-free representation (one with a cyclic quasi-free vector) is regular | `WeylSystem.continuous_line_of_quasiFree` | matches; proof: `‖W(ty)W(x)Ψ - W(x)Ψ‖² = 2 - 2 Re(e^{itσ(x,y)} e^{-t²η(y,y)/4}) → 0`, the vectors with `W(ty)u → u` form a closed subspace, and the group law gives continuity at every `t` |
| p. 38: the field operators `φ(y)` of a quasi-free representation, `W(ty) = e^{itφ(y)}` | `CCRRep.field R y`, the generator of `t ↦ W(ty)` (`CCRRep.lineGroup`; self-adjoint by Stone's theorem, `UnitaryGroup.generator_isSelfAdjoint`); `CCRRep.IsQuasiFree.mem_domain`: `Ψ ∈ Dom φ(y)` | matches; proof: `‖W(ty)Ψ - Ψ‖ ≤ (η(y,y)/2)^{1/2} |t|` and the adjoint-domain criterion |
| Theorem 39 (1), p. 39: `y₁(η + 2iω)y₂ = (Ψ|φ(y₁)φ(y₂)Ψ)` | `CCRRep.IsQuasiFree.inner_field_field`: `(φ(y₁)Ψ|φ(y₂)Ψ) = ½(η(y₁,y₂) + iσ(y₁,y₂))`; `norm_field_sq`: `‖φ(y)Ψ‖² = ½ η(y,y)` | (representation) `(Ψ|φ(y₁)φ(y₂)Ψ)` is read as `(φ(y₁)Ψ|φ(y₂)Ψ)`, equal to it whenever `φ(y₂)Ψ ∈ Dom φ(y₁)` since `φ(y₁)` is symmetric. Source error: the printed `η + 2iω` does not follow from (70); the expansion of `exp(-¼ t²yηy)` to second order gives `(Ψ|φ(y)²Ψ) = ½ yηy` (not `yηy` as in the proof), and the commutation relation gives the imaginary part `½ y₁ωy₂`; check: the Fock vacuum is quasi-free with `η = Re⟪·,·⟫` (`FockRep.isQuasiFree_vacuum`) and its two-point function is `½⟪f, g⟫` (`FockRep.inner_field_field_vacuum`, `TestsQuasiFree`) |
| Theorem 39 (2), p. 39: `|y₁ωy₂| ≤ 2 |y₁ηy₁|^{1/2} |y₂ηy₂|^{1/2}` | `CCRRep.IsQuasiFree.abs_symp_le_two_mul` (as printed), from `abs_symp_le`: `|σ(y₁,y₂)| ≤ η(y₁,y₁)^{1/2} η(y₂,y₂)^{1/2}` | matches; the constant `1` of `abs_symp_le` is sharp (the Fock vacuum with `y₂ = i y₁`) |

Not stated (open): Theorem 38 (Wick's theorem in the operator form: `Ψ ∈ Dom(φ(y₁)⋯φ(yₙ))` and the pairing formula for
`(Ψ|φ(y₁)⋯φ(yₙ)Ψ)`, and the converse).
