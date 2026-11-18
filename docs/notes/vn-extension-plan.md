# Von Neumann's extension theory: plan and sources

Gap row: "Operator algebras and quantum information: Deficiency indices; von Neumann extension theory; example `-i d/dx` on `[0,1]`" (partial).

Source read: G. Bonneau, J. Faraut, G. Valent, "Self-adjoint extensions of operators and the teaching of quantum mechanics",
arXiv:quant-ph/0103153, Section 4, Theorem 1 (von Neumann 1929): for a closed symmetric densely defined operator with deficiency indices
`n₊, n₋` (dimensions of `ker (A† - z₊)`, `ker (A† - z₋)`, `Im z₊ > 0 > Im z₋`): (i) `n₊ = n₋ = 0` iff `A` is self-adjoint; (ii) `n₊ = n₋ = n ≥ 1`:
infinitely many self-adjoint extensions, parametrised by a unitary `n × n` matrix; (iii) `n₊ ≠ n₋`: no self-adjoint extension. Section 5.3,
eqs (14)-(15): the momentum on `[0, L]` has deficiency indices `(1, 1)` and the extensions `P_θ` with `ψ(L) = e^{iθ} ψ(0)`.

Done (`VonNeumann.lean`, branch `opalg/vn-ext`): case (i) as an equivalence, `isSelfAdjoint_iff_deficiency_bot` (closed symmetric `A`, at `z = ± i`),
with the closed-range and lower-bound lemmas for closed symmetric operators. Earlier on main: the deficiency spaces of `-i d/dx` on `L²(0, 1)`
(`T-OP1-P5`).

Next bricks (estimates): (1) von Neumann's decomposition `D(A†) = D(A) ⊕ N₊ ⊕ N₋` for closed symmetric `A` (not stated in the source read: our own
lemma, marked so); (2) for a unitary `U : N₊ → N₋`, the extension `A_U` on `D(A) + (1 + U) N₊` is self-adjoint (case (ii), existence; the domain
formula is our own, not in the source read); (3) a self-adjoint extension `B ⊇ A` gives a unitary `N₊ → N₋` (case (iii) by contraposition,
`n₊ = n₋` as cardinals); (4) the interval: `P_θ` self-adjoint, from (2) with `U = e^{iθ}`-type maps on the one-dimensional `N_{± i}`, or from a
twisted translation group and Stone's theorem.

## Done (update)

Bricks (1)-(3) are proved (`VonNeumannDecomp`, `VonNeumannBoundary`, `VonNeumannExt`, `VonNeumannClassify`): the decomposition
`D(A†) = D(A) + N_i + N_{-i}` with uniqueness; the boundary form `⟪A† y, y'⟫ - ⟪y, A† y'⟫ = 2 i (⟪q, q'⟫ - ⟪p, p'⟫)`; for a unitary
`U : N_i → N_{-i}` the extension `A_U` on `D(A) + {p + U p}` is self-adjoint (`extU_isSelfAdjoint`); every self-adjoint `B ⊇ A` is `A_{U_B}`
(`eq_extU_of_selfAdjoint`), so a self-adjoint extension forces `deficiencyDim A i = deficiencyDim A (-i)` (`deficiencyDim_eq_of_selfAdjoint_ext`).

Comparison with the source read (Theorem 1 of Section 4): case (i) matches (`isSelfAdjoint_iff_deficiency_bot`); case (iii) matches in contrapositive
form; case (ii) "parametrised by a unitary `n × n` matrix" is matched by the bijection `U ↦ A_U` onto the self-adjoint extensions, with two
differences, both to report: (a) representation: unitaries `N_i ≃ₗᵢ N_{-i}` instead of `n × n` matrices (equivalent for finite `n` after choosing
bases); (b) representation: "n₊ = n₋" is read as "the deficiency spaces have Hilbert bases indexed by the same set" (`VonNeumannDim.exists_selfAdjoint_ext_iff`:
a self-adjoint extension exists iff this holds; the deficiency spaces are closed, `deficiencySpace_eq_orthogonal`), the Hilbert-dimension reading of the
source's "dimension"; the algebraic `deficiencyDim` equality is also derived (`deficiencyDim_eq_of_selfAdjoint_ext`). The invariance of the Hilbert
dimension is not needed and not proved. The domain formula `D(A_U) = D(A) + (1 + U) N_i` and the decomposition are the library's own,
not in the source read. Open: (4) the interval example (`P_θ`).
