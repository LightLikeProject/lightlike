# ODE flows, commuting flows and Frobenius: sources read, and how the library compares

Files: `Lightlike/ODE/` (`Gronwall`, `FlowDeriv`, `LocalFlow`, `FlowJoint`, `CommutingFlows`, `CommutingConverse`, `CommutingRectangle`,
`CommutingFrame`, `InvolutiveFrame`, `Frobenius`, `FrobeniusChart`, `FlowContDiff`,
`HigherVariational`, `Tests`).

## Sources (read at the locations given)

1. G. Teschl, *Ordinary Differential Equations and Dynamical Systems*, Graduate Studies in
   Mathematics 140, AMS 2012; read in the author's preliminary version (PDF on the author's page at
   the University of Vienna). Section 2.4, pages 45–47: equation (2.49) (first variational
   equation) and Theorem 2.10.
   - Theorem 2.10: for `f ∈ C^k(U, ℝⁿ)`, `k ≥ 1`, `U ⊆ ℝⁿ⁺¹` open, around each `(t₀, x₀) ∈ U` there
     is an open set `I × B ⊆ U` with `φ(t, s, x) ∈ C^k(I × I × B, ℝⁿ)`; `∂φ/∂t` is `C^k` too, and the
     partial derivatives of order `k` satisfy the higher variational equations.
   - Proof of the case `k = 1` (page 46–47): with `ψ` the solution of `ψ' = A(t) ψ`, `ψ(t₀) = I`,
     `A(t) = ∂f/∂x (t, φ(t))`, show `θ(t, x) = (φ(t, x) − φ(t) − ψ(t) x)/|x| → 0` by Grönwall.
2. P. W. Michor, *Topics in Differential Geometry*, Graduate Studies in Mathematics 93, AMS 2008;
   read in the author's version (PDF on the author's page at the University of Vienna).
   - 3.15 Corollary, page 28: for vector fields `X`, `Y` the following are equivalent: (1)
     `[X, Y] = 0`; (2) `(Fl^X_t)^* Y = Y` wherever defined; (3) `Fl^X_t ∘ Fl^Y_s = Fl^Y_s ∘ Fl^X_t`
     wherever one side is defined along the whole rectangle of times.
   - 3.17 Theorem, page 31: commuting fields that form a basis at `x` are the coordinate fields of
     a chart; the proof uses `f(t) = (Fl^{X₁}_{t₁} ∘ … ∘ Fl^{X_m}_{t_m})(x)` and `∂f/∂t_i = X_i ∘ f`.
   - 3.18, local version of Frobenius's theorem, pages 32–33: an integrable (involutive) subbundle
     `E ⊂ TM` of fibre dimension `k` has, about each point, a chart `u` with
     `u(U) = V × W ⊂ ℝᵏ × ℝ^{m−k}` such that `T(u⁻¹(V × {y})) = E | u⁻¹(V × {y})`. The proof
     normalises a frame to `Y_i = ∂/∂u^i + ∑_{p>k} h_i^p ∂/∂u^p` (equation (1)), shows
     `[Y_i, Y_j] = 0`, and takes `f(t, y) = (Fl^{Y₁}_{t₁} ∘ … ∘ Fl^{Y_k}_{t_k})(u⁻¹(y))`.
3. A. Wipf, *Hamilton's Formalism for Systems with Constraints*, arXiv:hep-th/9312078, Section 5.2,
   page 30, Theorem 5 and equation (5.27): "On `Γ_c` the vectors `X_a` generate `M`-dimensional
   manifolds", by Frobenius with `[X_a, X_b] ≈ −t_{ab}^c X_c`; for point-dependent structure
   functions the fields are integrable only on the constraint surface. (Not yet formalised; it is
   the reason for the "on an invariant set" forms below.)

## What the library proves, and every difference from the sources

### (a) Differentiable dependence of the flow on the initial point

`Lightlike.ODE.exists_flow_differentiable`, with the pieces `IsFlowBox.hasFDerivAt_of_variational`,
`IsFlowBox.differentiableAt_flow`, `IsFlowBox.hasDerivWithinAt_fderiv_flow`,
`IsFlowBox.fderiv_flow_zero`, `IsFlowBox.continuousOn_fderiv_flow`, `IsFlowBox.hasFDerivAt_uncurry`.

For an autonomous field `V`, `C¹` at `x₀`, on a real Banach space: there is a local flow `Φ` near
`x₀` such that `x ↦ Φ t x` is differentiable, `D_xΦ_0 = id`, `d/dt D_xΦ_t = DV(Φ_t x) ∘ D_xΦ_t`
(Teschl (2.49)), `(t, x) ↦ D_xΦ_t` is continuous, and `(t, x) ↦ Φ t x` is differentiable in both
variables at once.

`Lightlike.ODE.exists_solution_contDiffOn` (file `FlowContDiff`) is Theorem 2.10 itself: for
`f : ℝ × E → E` of class `C^{k+1}` at `(t₀, x₀)` there are `δ > 0` and `φ` with `φ(s, s, x) = x`,
`∂_t φ = f(t, φ)`, and `φ`, `∂_t φ` of class `C^{k+1}` on `I × I × B`, `I = (t₀ − δ, t₀ + δ)`,
`B = B(x₀, δ)`. Proof as in the source: reduction to the autonomous case by adding `t` to the
variables, the case `k = 1` by Grönwall, and induction on `k` through the pair `(Φ, D_xΦ)`
(`exists_isFlowBox_contDiffOn`, `prolong`).

`Lightlike.ODE.exists_solution_contDiffOn_variational` (file `HigherVariational`) adds the last
sentence of the theorem: for every `j ≤ k`, `∂/∂t D^j φ = D^j (f(t, φ))` on `I × I × B`, where
`D^j` is the iterated Fréchet derivative in `(t, s, x)` (all partial derivatives of order `j` at
once); this is (2.51), and it contains the commutation of `∂/∂t` with the derivatives of order
`j`. It rests on `fderiv_iteratedFDeriv_apply_comm`, proved by induction on the order from the
symmetry of the second derivative (the pinned Mathlib has no symmetry of iterated derivatives of
higher order).

Differences from Teschl, Theorem 2.10 (representation only; none accepted):
- representation: a real Banach space instead of `ℝⁿ`; `f` is `C^k` at the point `(t₀, x₀)`
  (so near it) instead of on a given open set `U`; the source's `k ≥ 1` is `k + 1` here;
- representation: "`D_k φ` satisfies the higher order variational equation obtained from (2.51)
  by applying the chain rule" is stated as (2.51) itself for the iterated Fréchet derivative,
  without expanding `D^j (f(t, φ))` by the chain rule; "this equation is linear in `D_k φ`" is a
  remark about that expansion and is not a separate statement here.

### (b) Commuting flows

`Lightlike.ODE.IsFlowBox.fderiv_flow_apply_eq_of_lieBracket_eq_zero` (Michor 3.15, (1) ⇒ (2)),
`IsFlowBox.flow_comm` and `Lightlike.ODE.exists_flows_commute` (Michor 3.15, (1) ⇒ (3)).

The converses are in `Lightlike.ODE.CommutingConverse`:
`IsFlowBox.fderiv_flow_apply_eq_of_flow_comm` ((3) ⇒ (2)),
`IsFlowBox.lieBracket_eq_zero_of_fderiv_flow_apply_eq` ((2) ⇒ (1)) and
`IsFlowBox.lieBracket_eq_zero_of_flow_comm` ((3) ⇒ (1)). So the three assertions of the corollary
are equivalent in flow boxes.

The non-local form is `Lightlike.ODE.hasDerivAt_of_lieBracket_eq_zero_rectangle` (and `…_neg` for
negative times of `V`), in `Lightlike.ODE.CommutingRectangle`: if `[V, W] = 0` on an open set `U`
and `β(τ, σ)` solves `∂_τ β = V(β)` in `U` for `τ ∈ [0, T]` and all `σ` near `σ₀`, with
`∂_σ β(0, σ₀) = W(β(0, σ₀))`, then `∂_σ β(τ, σ₀) = W(β(τ, σ₀))` for all `τ ∈ [0, T]`, with no
smallness condition on `T`. With `β(τ, σ) = Fl^V_τ(Fl^W_σ x)` this says that the composition is an
integral curve of `W` in `σ` wherever it is defined along the rectangle, which is Michor's
condition "one side is defined even along `[0, t] × [0, s]`".

Differences from Michor, Corollary 3.15 (representation only):
- representation: `C¹` fields on an open subset of a Banach space, not smooth fields on a manifold;
- representation: there is no global flow `Fl` in the library, so (3) is stated for a map `β`
  with the defining properties of `Fl^V_τ ∘ Fl^W_σ` and concludes that `σ ↦ β(τ, σ)` is an
  integral curve of `W` (which, by uniqueness of integral curves, is the equality with
  `Fl^W_σ(Fl^V_τ x)`); the converses (3) ⇒ (2) ⇒ (1) are stated in flow boxes, which is where the
  derivative at `t = 0` or `s = 0` is taken.

### (c) Frobenius

`Lightlike.ODE.exists_commuting_frame` (Michor 3.18, equation (1) and the claim after it),
`Lightlike.ODE.exists_flowComp_of_commuting` (the map `f` of 3.17/3.18 and `∂f/∂t_i = Y_i ∘ f`),
`Lightlike.ODE.exists_integral_manifold_of_involutive` and its form on an invariant set
`exists_integral_manifold_of_involutive_on`.

`Lightlike.ODE.exists_frobenius_chart` (file `FrobeniusChart`) is the chart form: a continuous
linear `π : E → ℝᵏ` and an open partial homeomorphism `φ : ℝᵏ × ker π → E` with `φ(0, 0) = x₀`,
differentiable on its source, whose derivative along the first factor has range the span of the
`X_k(φ p)` at every point `p` of the source. With `u = φ⁻¹` this is Michor's chart whose plaques
are integral manifolds.

Differences from Michor, 3.18 (all of representation; the chart is proved):
- representation: the subbundle is given by a frame `X_1, …, X_k`, and involutivity is "each
  `[X_i, X_j](y)` lies in the span of the `X_k(y)`"; the source's definition quantifies over all
  sections of the subbundle;
- representation: `C¹` fields on an open subset of a finite-dimensional normed space, not a smooth
  subbundle on a manifold;
- representation: the source of the chart is an open set containing `(0, 0)`; it is not stated to
  be a product `V × W` (it contains one).

## Search before building (pinned Mathlib and Physlib, local greps; Mathlib master and open pull requests not searched)

- `Mathlib/Analysis/ODE/` (`PicardLindelof`, `ExistUnique`, `Gronwall`, `Transform`, `Basic`) and
  `Mathlib/Geometry/Manifold/IntegralCurve/`: existence, uniqueness, Lipschitz dependence on the
  initial point (`IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith`);
  no differentiability in the initial point, no variational equation. Reused: `IsPicardLindelof`,
  `ODE.FunSpace` and its fixed point, `norm_le_gronwallBound_of_norm_deriv_right_le`.
- `Mathlib/Analysis/Calculus/VectorField.lean`: `VectorField.lieBracket` and its algebra (reused:
  `lieBracket_smul_right`, `lieBracket_add_right`, `lieBracket_swap`); no statement about flows.
- No Frobenius theorem, no involutive distributions (same finding as `docs/notes/gc4-source-flow.md`).
- No lemma "continuous partial derivatives imply differentiability" on a product in the pinned
  Mathlib; the joint derivative of the flow is proved directly.
