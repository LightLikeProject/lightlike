# SF1 m1: uniqueness of the Barrett–Crane intertwiner (Reisenberger 1999)

Status: proved, for four legs, as `Lightlike.SpinFoam.BC.bcNode_unique`
(`Lightlike/SpinFoam/BarrettCraneUnique.lean`), by a route that needs neither the operators `G²` nor
`β_J`; see the last section. This note records the statement and the hypotheses as printed, read on
26 Nov 2026 in the arXiv version gr-qc/9809067v1 (*On relativistic spin network vertices*).

## What the paper states (§2 Definition 1 and §3 Theorem, pp. 2–7)

A **relativistic spin network** is a Spin(4) spin network such that (1) on each edge the left and
right spins agree, `j_L = j_R`, and (2) in any expansion of an `n`-valent vertex into a sum of
trivalent trees, only trees with `j_L = j_R` on every internal edge appear.

**Theorem** (§3, p. 7): the intertwiner of any vertex in a relativistic spin network is determined,
up to a numerical factor, by the irreps on the incident edges. With `j = j_L = j_R` and `H(j)` the
space of tensors with the SU(2) irreps of spins `j`: (1) the intertwiner, as a tensor of
`H(j) ⊗ H(j)*`, is a linear map of `H(j)` to itself; (2) it is proportional to the orthogonal
projector of `H(j)` onto the invariant tensors `Inv_SU(2)(j)`.

## The proof, and its one external input (§3, pp. 7–10)

For four edges: the intertwiner is `Φ = X P` with `P` the projector and `X` a linear map of
`Inv(j)`; condition (2) makes `X` diagonal in the trivalent tree bases of the three pairings. Those
bases are the eigenbases of `G₁₂²`, `G₁₃²`, `G₁₄²` (eigenvalues `J(J+1)`, pairwise distinct), so `X`
commutes with all three. The paper writes `X` as a polynomial in `G₁₂²` and uses the matrix elements
`β_J = ⟨J|[G₁₃², G₁₂²]|J−1⟩`, given by equation (13) (Lévy-Leblond and Lévy-Nahas 1965, eq. (2.17)),
which are non-zero for all but the smallest `J`, to conclude `X = b₀·1`.

## In Lean

`Lightlike/SpinFoam/ReisenbergerCore.lean`, `scalar_of_commute_chain`: the last step as a statement
about matrices. If `c` is injective, `X` commutes with `diagonal c` and with a matrix `M` whose
entries `M (k+1) k` are non-zero, then `X` is a scalar. (A direct argument: `X` is diagonal, and
`(X_{k+1,k+1} − X_{k,k}) M_{k+1,k} = 0`.)

Still missing, in order: (a) the operators `G₁₂²` and `G₁₃²` on the intertwiner space of four spins,
in the library's channel basis `fourJNode` (the second pairing needs the 6j change of basis of
`Lightlike/SU2/Recoupling6j.lean`); (b) the non-vanishing of `β_J`, equation (13), which is the
input quoted from Lévy-Leblond–Lévy-Nahas and has not been read at its source or proved here; (c)
the statement that a relativistic intertwiner is of the form `X P`, with the condition (2) of the
definition as a hypothesis, and the conclusion that `bcNode` is the projector.

## The proof in Lean (27 Nov 2026)

`bcNode_unique` assumes condition (2) for the pairings `(01)(23)` and `(02)(13)` only, which is a
weaker hypothesis than the paper's (all three pairings). The components of `Φ` are diagonal in
both tree bases, and the two bases are related by the orthogonal 6j recoupling matrix
(`sum_basisB_mul_basisA`). Its column at the extreme channel `l₀ = min(j₀ + j₂, j₁ + j₃)` is a
stretched 6j symbol, whose Racah sum has one term, so it is nonzero for every admissible `k`
(`sixJSym_extreme_ne_zero`). Hence every diagonal entry equals `M_{l₀ l₀}`, so `Φ = c · bcNode`.
The missing items (a)–(c) above are therefore not needed. `scalar_of_commute_chain` stays as the
matrix form of Reisenberger's own last step.
