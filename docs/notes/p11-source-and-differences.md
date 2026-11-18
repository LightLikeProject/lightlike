# T-GE2-P11: causal simplicity implies stable causality, source and differences

Lean: `Lightlike/Spacetime/CausalLadder/StablyCausalSimple.lean` (`isStablyCausal_of_isCausallySimple_euclid`), `NullBoundaryManifold.lean`,
`TimeFunctionAssembly.lean`, `FullSupportMeasure.lean`, `CausalPastLimsup.lean`, `CausalPastLiminf.lean`; the task file
`Tasks/GE2/T_GE2_P11.lean`.

## Source read (pdftotext of the arXiv PDF)

E. Minguzzi, *Causality theory for closed cone structures with applications*, arXiv:1709.06494 (Rev. Math. Phys. 31 (2019) 1930001):
* Definition 2.18: "A closed cone structure (M, C) is causally simple if J is closed and antisymmetric."
* Theorem 2.47 (causal ladder): "Globally hyperbolic ⇒ Causally simple ⇒ Causally continuous ⇒ Causally easy ⇒ Stably causal ⇒ Strongly causal ⇒ Distinguishing ⇒ ... ⇒ Causal."
* Theorem 3.17, printed p. 117: "Let (M, C) be a causally simple closed cone structure, then (M, C) is stably causal and J = J_S = K = T₁ = T₂." Proof: "Under the
  assumption J is closed, thus it is the smallest closed transitive relation containing J, hence K = J. But under the assumption J is antisymmetric hence K is antisymmetric
  (stable causality)", i.e. through K-causality (Section 3.2-3.6) and the existence of a temporal function (Theorem 3.11), not through Hawking's volume function.

## Condition 2: the source's manifolds have charts into ℝⁿ (read)

Same paper, section 1.3 "Notations and conventions" (printed p. 10): "The manifold M has dimension n + 1 ... A coordinate open neighborhood of M is an element of the
atlas, namely one diffeomorphic with some open set of R^{n+1}." and the first paragraph of section 2 (same page): "In this work the manifold M is assumed to be connected,
Hausdorff, second countable (hence paracompact) and of dimension n+1. Furthermore, it is C^r, 1 ≤ r ≤ ∞." So the charts take values in open subsets of ℝⁿ⁺¹ (in particular the
manifold has no boundary), second countable and Hausdorff: matches the statement over the model `𝓘(ℝ, Fin n → ℝ)` with `[T2Space M] [SecondCountableTopology M]` (here `n` is the dimension
of the model; the Lorentzian dimension is the same `n`). Connectedness (source) is not assumed in the statement (more general).

## Change from the earlier lock (condition 1 of the approval of 18 November 2026)

The earlier lock stated the theorem over an arbitrary normed model `E` with a `ModelWithCorners ℝ E H` (no boundaryless hypothesis, no `ℝⁿ`). The new statement fixes the model to
`Fin n → ℝ` with `𝓘(ℝ, Fin n → ℝ)` (so the manifold is boundaryless) and keeps `[T2Space M] [SecondCountableTopology M]`.

## Differences (all representation)

1. *Causal simplicity*: ours is `IsCausal ∧ ∀ x, IsClosed (J⁺ x) ∧ IsClosed (J⁻ x)` (the Hawking–Ellis form: closed futures and pasts of points); the source asks that the relation
   `J ⊂ M × M` be closed. The relation form implies the pointwise form.
2. *Stable causality*: ours is the existence of a time function (`IsStablyCausal`, with the docstring noting Hawking's equivalence with causality surviving a widening of the
   light cones); the source's is the widening of the cones. The equivalence (Hawking 1969) is not formalized.
3. *Setting*: a smooth Lorentzian manifold modelled on `ℝⁿ` (`Fin n → ℝ`) with a time orientation and the Borel σ-algebra, against closed cone structures (a more general setting). The model
   restriction is the one the statement of the task now carries (approved by the integrator for the maintainers, 18 November 2026): the volume measure of Hawking's function needs charts into `ℝⁿ`.
4. *Method*: the source's proof goes through K-causality; ours through Hawking's time function `x ↦ μ(J⁻(x))` (the hint of the task). The statement is the same.

Hawking-Ellis, ch. 6 (Proposition 6.4.? and Hawking's time function): not read at a location.
