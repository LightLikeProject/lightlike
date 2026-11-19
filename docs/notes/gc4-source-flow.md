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

## Theorem 5 (gauge orbits are `M`-dimensional manifolds): what was tried and what is missing

Tried (compiled): `FlowDeriv.exists_flow_on_surface`: one constraint, a local integral curve staying on the surface, from
Mathlib's Picard-Lindelöf (`ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀`) and Gronwall
(`LinearODE`). The next step, `M` constraints, needs either (A) the flows of the fields `X_a` to commute when their Lie
brackets vanish, so that `(t₁, …, t_M) ↦ Φ¹_{t₁} ∘ … ∘ Φ^M_{t_M} (x)` parametrises the orbit, or (B) Frobenius' theorem
for the involutive family `{X_a}`.

Search in the pinned Mathlib and Physlib (case-insensitive greps over `.lake/packages/mathlib/Mathlib` and
`.lake/packages/Physlib`): no Frobenius integrability theorem (the only "Frobenius" hits are the Frobenius norm,
Frobenius number and field theory), no result about involutive distributions or integral manifolds, no statement that flows
of vector fields with vanishing Lie bracket commute (`Mathlib/Geometry/Manifold/VectorField/LieBracket.lean` has the Lie
bracket, its pullback and the Leibniz rule, `Mathlib/Geometry/Manifold/IntegralCurve/` has existence, uniqueness and uniform
time for one field).

Missing pieces, named: (i) flows of two `C¹` vector fields with `[V, W] = 0` commute (for A); (ii) the Frobenius theorem for
a finite involutive family (for B). Neither is in the pinned Mathlib or Physlib.

### Second attempt at Theorem 5: commuting flows by ODE uniqueness in the flat finite-dimensional setting

Route: for `C¹` fields `V`, `W` on a finite-dimensional normed space with `[V, W] = 0`, show that the flow `Φ_t` of `V` maps
integral curves of `W` to integral curves of `W`, hence the flows commute. With `Ψ_s` the flow of `W`, the curve
`s ↦ Φ_t (Ψ_s x)` has derivative `DΦ_t (Ψ_s x) · W (Ψ_s x)`; it is an integral curve of `W` iff `DΦ_t · W = W ∘ Φ_t`, which follows
from `d/dt ((DΦ_t)⁻¹ W ∘ Φ_t) = (DΦ_t)⁻¹ [V, W] ∘ Φ_t = 0` (Gronwall/uniqueness machinery of `LinearODE` is available for
the last step).

Concrete obstacle: the first step needs the flow `x ↦ Φ_t(x)` to be differentiable with `DΦ_t` satisfying the variational
equation `d/dt DΦ_t = DV(Φ_t) DΦ_t`. The pinned Mathlib has local existence and uniqueness of integral curves
(`Mathlib/Analysis/ODE/ExistUnique.lean`, `PicardLindelof.lean`, `Gronwall.lean`, `Transform.lean`) but no differentiability of the
flow in the initial condition (case-insensitive grep over `Mathlib/Analysis/ODE` and `Mathlib/Geometry/Manifold/IntegralCurve`
for differentiability/smoothness of the flow and for dependence on initial data finds only the existence statement
`ContDiffAt.exists_eventually_eq_hasDerivAt`). Without it neither this route nor the same step of the Frobenius proof is
available. Two attempts are therefore on record: the compiled single-constraint flow with the missing pieces `(i)` flow
commutation and `(ii)` Frobenius, and this route, blocked at differentiable dependence on initial data.
