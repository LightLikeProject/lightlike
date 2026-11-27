# Statement card: uniqueness of the Barrett–Crane intertwiner (SF1 m1, draft entry LL-XXXX-u)

| | |
|---|---|
| Result | `Lightlike.SpinFoam.BC.bcNode_unique`, draft entry LL-XXXX-u (`docs/results.d/spinfoam-barrett-crane-unique.yaml`) |
| Files | statement and proof `Lightlike/SpinFoam/BarrettCraneUnique.lean`; `bcNode` in `Lightlike/SpinFoam/BarrettCrane.lean` |
| Source | M. P. Reisenberger, *On relativistic spin network vertices*, J. Math. Phys. 40 (1999) 2046–2054, arXiv:gr-qc/9809067, §2 Definition 1 and §3 Theorem |
| Card written | 27 Nov 2026, from the arXiv HTML rendering of gr-qc/9809067v1 (Definition 1, the Theorem and its proof, eqs. (6)–(16) read; the printed J. Math. Phys. version not compared) and the Lean file above (read) |

## 1. The source theorem, word for word

Definition 1 (§2), the two conditions defining a relativistic spin network:

> 1. "On each edge the left handed spin, j_L, and the right handed spin, j_R, are equal."
> 2. "In any expansion of an n-valent vertex into a sum of trivalent trees only trivalent trees with j_L=j_R on each of the internal (virtual) edges appear."

Theorem (§3, unnumbered):

> "The intertwiner of any vertex in a relativistic spin network is uniquely determined, up to a numerical factor, by the irreps on the incident edges."

The proof writes the intertwiner as Φ = X P, with P the projector onto Inv_SU(2)(j), and eq. (6) "furthermore requires that X is diagonal in each of the trivalent tree bases of Inv_SU(2)(j)". For four legs: "There are three (unoriented) trivalent trees matching the four incident edges", and after eq. (7): "it commutes with G_12^2, G_13^2, and G_14^2". Eqs. (8)–(16) use only G_12² and G_13² (through β_J, eq. (13)).

## 2. The Lean statement, verbatim

```lean
theorem bcNode_unique {j : Fin 4 → ℕ} {Φ : (Fin 4 → ℤ) → (Fin 4 → ℤ) → ℂ}
    (hμ : ∀ ν, IsInv (legs j) ![false, false, false, false] (fun μ => (Φ μ ν).re) ∧
      IsInv (legs j) ![false, false, false, false] (fun μ => (Φ μ ν).im))
    (hν : ∀ μ, IsInv (legs j) ![false, false, false, false] (fun ν => (Φ μ ν).re) ∧
      IsInv (legs j) ![false, false, false, false] (fun ν => (Φ μ ν).im))
    (hA : ∀ k k', k ≠ k' →
      ∑ μ ∈ boxJ j, ∑ ν ∈ boxJ j, ((basisA j k μ * basisA j k' ν : ℝ) : ℂ) * Φ μ ν = 0)
    (hB : ∀ l l', l ≠ l' →
      ∑ μ ∈ boxJ j, ∑ ν ∈ boxJ j, ((basisB j l μ * basisB j l' ν : ℝ) : ℂ) * Φ μ ν = 0) :
    ∃ c : ℂ, ∀ μ ν, Φ μ ν = c * bcNode j μ ν
```

with `basisA j k` = `fourJT (j 0) (j 1) (j 2) (j 3) k` (the `(01)(23)` tree intertwiner of channel `k`), `basisB j l μ` = `fourJ (j 0) (j 2) (j 1) (j 3) l (μ 0) (μ 2) (μ 1) (μ 3)` (the `(02)(13)` tree intertwiner), `boxJ j` the box of projections, `legs j = ![j 0, j 1, j 2, j 3]`, and `bcNode j μ ν = Σ_{i ∈ channel} ι_i(μ) ι_i(ν)` (`BarrettCrane.lean`).

## 3. Dictionary

| Reisenberger | Lean | Remark |
|---|---|---|
| vertex with four incident edges, irreps (j_L, j_R) | `j : Fin 4 → ℕ` (doubled spins), each leg `(j k, j k)` | Condition 1 is built in. |
| H(j) ⊗ H(j), left and right factors | `Φ μ ν`, `μ` left (self-dual) projections, `ν` right | |
| Spin(4) = SU(2) × SU(2) invariance | `hμ`, `hν`: `IsInv` (weight zero, killed by J₊ and J₋, admissible support) of the real and imaginary parts in each factor | Lie-algebra invariance on the finite-dimensional representations, equal to group invariance for SU(2). |
| X diagonal in the tree basis of the pairing (12)(34) | `hA`: components on `ι_k ⊗ ι_k'` vanish for `k ≠ k'` | Reisenberger's legs 1..4 are Lean's 0..3. |
| X diagonal in the tree basis of the pairing (13)(24) | `hB`: the same in the `(02)(13)` basis | |
| X diagonal in the tree basis of the pairing (14)(23) | not assumed | See difference 1. |
| "up to a numerical factor", Φ ∝ P | `∃ c : ℂ, Φ = c · bcNode j` | `bcNode = Σ_i ι_i ⊗ ι_i` is the projector P as a tensor, in the real orthonormal basis `ι_i`; `c = 0` is allowed. |

## 4. Differences from the source

1. **Two pairings instead of three (direction: stronger).** Reisenberger's condition 2 covers all trees, which for four legs are the three pairings. The Lean theorem assumes diagonality for `(01)(23)` and `(02)(13)` only, so it applies to more tensors and has the same conclusion. Reisenberger's own proof also uses only two operators (G_12², G_13²).
2. **Four legs only.** Reisenberger proves the theorem for any valence by reduction to four-valent fragments of a tree. That reduction is not formalized; the milestone asks for the four-leg statement.
3. **Different proof.** Reisenberger: X is a polynomial in G_12², and the commutator with G_13² (matrix elements β_J of Lévy-Leblond–Lévy-Nahas, eq. (13)) kills the higher coefficients. Lean: the two diagonal matrices are related by the orthogonal 6j recoupling matrix (`sum_basisB_mul_basisA`, `sum_fourRecoupling_mul`), whose column at the extreme channel `l₀ = min(j₀+j₂, j₁+j₃)` is a stretched 6j symbol with a one-term Racah sum, nonzero for every admissible `k` (`sixJSym_extreme_ne_zero`, from `sixJSym_eq_racahW`). No β_J is used.
4. **Invariance as real and imaginary parts.** `IsInv` is stated for real tensors, so the hypotheses split Φ into its real and imaginary parts. The representation matrices of J₊, J₋ and J_z are real in the standard basis, so this is the same as complex invariance.

## 5. Why each hypothesis is needed

- **`hB` (the second pairing).** MEASURED in Lean: `Tests.single0_counterexample`. On four spin-½ legs (channels 0 and 2), `ι_0 ⊗ ι_0` is invariant in each factor and diagonal in the `(01)(23)` basis, but it is no multiple of `bcNode`.
- **`hA`.** The same counterexample with the roles of the two pairings exchanged (`κ_l ⊗ κ_l` in the `(02)(13)` basis). ASSUMPTION: not checked in Lean.
- **`hμ`, `hν`.** Without invariance, Φ need not lie in the span of the tree tensors (for example a delta tensor at one projection). The expansion `eq_sum_coefA` uses them. ASSUMPTION: no Lean counterexample.

## 6. Trust checks

- **Axioms** (MEASURED, `#print axioms` after compiling the file, 27 Nov 2026): `bcNode_unique`, `bcNode_hyp` and `Tests.single0_counterexample` depend only on `propext`, `Classical.choice` and `Quot.sound`.
- **Non-vacuity** (MEASURED, Lean): `bcNode_hyp` proves that `bcNode j` satisfies every hypothesis of `bcNode_unique` for every `j`. `coefA_bcNodeR_half`: on four spin-½ legs `⟨ι_0 ⊗ ι_0, bcNode⟩ = 1`, so the conclusion is not the zero tensor.
- **Wrong model** (MEASURED, Lean): `Tests.single0_counterexample`, above.
- **Not done by this card:** comparison with the printed J. Math. Phys. version; a numerical check of the stretched 6j values.

## 7. One question for the reviewer

Is assuming diagonality in two of the three tree bases an acceptable reading of "the hypotheses of Reisenberger's theorem" in the milestone's done-when? The Lean hypothesis is implied by Reisenberger's (which asks all three), so the theorem is at least as strong as the source's four-valent case.
