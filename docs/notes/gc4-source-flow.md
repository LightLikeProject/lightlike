# GC4: first-class constraints and gauge flows against a source that was read

Source: A. Wipf, "Hamilton's Formalism for Systems with Constraints", lectures, arXiv:hep-th/9312078 (ETH-TH/93-48), read in its arXiv HTML version. Section 5.2, Theorem 4 and Theorem 5.

What the source says: Theorem 4: for a first-class system the induced two-form on the constraint surface is maximally
degenerate and its kernel is spanned by the Hamiltonian vector fields of the first-class constraints; in the proof the fields
`X_a` are tangent to the surface because `{γ_a, γ_b} ≈ 0`. Theorem 5: on the surface the `X_a` generate `M`-dimensional
manifolds (Frobenius, with the Lie brackets combinations of the `X`'s). Assumptions: the regularity of Section 3.3.

Match with the library: `KernelSpan.radical_eq` is Theorem 4's "kernel spanned by the Hamiltonian vector fields" at a point; `GaugeFlow.pairing_hamField_eq_zero_of_firstClass` is the tangency step of the proof of Theorem 4;
`GaugeFlow.gradForm_hamField_eq_zero` is that each `X_a` lies in the kernel of the form on the tangent directions. `FlowDeriv`
gives, for a single constraint with involutive brackets, a local integral curve staying on the surface.

Differences (the library is weaker than the source; none accepted): (1) [closed] Theorem 4's equality "kernel = span of the `X_a`" is `KernelSpan.radical_eq` (pointwise, finite-dimensional `X`;
regularity is not needed for the equality, only for the dimension count); (2) Theorem 5 (the `X_a` generate `M`-dimensional manifolds, the
gauge orbits) is not proved: only a forward local curve for one constraint, no manifold and no group action; (3) involutivity
is a hypothesis with continuous coefficients; the source has structure constants that may depend on the phase-space point;
(4) the library's phase space is Physlib's flat `X × X`, the source's is a general phase space of dimension `2N`.
