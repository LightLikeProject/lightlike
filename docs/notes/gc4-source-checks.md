# GC4: comparison of statements with sources

Only statements compared with a source that was read are listed as compared.

## `Lightlike/Gauge/ReducedForm.lean` against Cannas da Silva, Lemma 23.3

Source: A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764 (Springer, 2001); the
text read is the author's online version, chapter "The Marsden-Weinstein-Meyer Theorem", Section 23.2 "Ingredients",
item 2, Lemma 23.3 (printed pages 142-143 of that version).

Source statement: let `(V, ω)` be a symplectic vector space and `I` an isotropic subspace (`ω|_I ≡ 0`); then `ω` induces a
canonical symplectic form `Ω` on `I^ω / I`. Proof there: `Ω([u], [v]) = ω(u, v)` is well defined because `I` is
isotropic, and nondegenerate because `(I^ω)^ω = I`.

Match: `reducedForm` is `Ω` on `D^⊥ ⧸ D` with `Ω([u], [v]) = σ (u, v)` (`reducedForm_mk`); `reducedForm_isAlt` and
`reducedForm_nondegenerate` give that it is alternating and nondegenerate. The proof of nondegeneracy is the same
argument (`(D^⊥)^⊥ = D`, `LinearMap.BilinForm.orthogonal_orthogonal`).

Differences: (1) the source's symplectic vector space is finite-dimensional, as here (`FiniteDimensional ℝ E`); (2) the
source is over the reals, as here; (3) here the form `σ` is assumed alternating and nondegenerate through
`IsSymplecticForm`-style hypotheses and reflexive (a consequence of alternating), and `reducedForm` is defined for an
isotropic `D` without the nondegeneracy hypothesis (needed only for the nondegeneracy theorem). No statement of the
source is claimed beyond Lemma 23.3. Theorem 23.1 (the reduction theorem for a free action) is not covered.

Not compared: `finrank_reducedTangent` in `ConstraintsAPI.lean` (dimension count) against ingredient 1 of the same
section (kernel of the moment map's differential equals the symplectic orthogonal of the orbit tangent); the statement
there, `ker dμ_p = (T_p O_p)^ω`, is of the same kind but its proof in the source is a dimension count that has not been
compared line by line.
