# G3-089 (state spaces): the pure states of `C(X)` are the points of `X`

Source read: N. P. Landsman, *Lecture Notes on C*-Algebras, Hilbert C*-modules, and Quantum Mechanics*,
arXiv:math-ph/9807030 (source key `landsman-1998`): Section 2.8, Definitions 2.8.1 (p. 35) and 2.8.6 (p. 36), Proposition
2.8.7 (p. 37); Section 2.12, Definition 2.12.1 (p. 44), Proposition 2.12.8 and Theorem 2.12.9 with its proof (p. 46).

| Source | Library | Check |
|---|---|---|
| Definition 2.12.1, p. 44: a pure state is an extreme point of the state space | `states X`, `IsPure X ω` (`ω ∈ Set.extremePoints ℝ (states X)`) | (representation) a state of `C(X)` is a linear functional nonnegative on the pointwise nonnegative functions with `ω(1) = 1`; in `C(X)` these are the positive elements; a state of `C₀(X)` is a positive functional with `sup {ω f | 0 ≤ f ≤ 1} = 1` (Definition 2.8.6, p. 36: "positive and has norm 1"; for a positive functional on `C₀(X)` the norm is this supremum); the extension `F ↦ ω(F - F(∞)) + F(∞)` is Proposition 2.8.7, p. 37 |
| Theorem 2.12.9, p. 46: "a bijective correspondence between the pure states and the multiplicative functionals", via `ω_g = ω(· g) = t ω` for `0 ≤ g ≤ 1` (Proposition 2.12.8) | `mul_of_isPure`, `isPure_iff_mul` | matches; the source's step through Proposition 2.12.8 is done directly (`ω = t ω₁ + (1 - t) ω₂` with `ω₁ = ω(· g)/t`) |
| the multiplicative functionals on `C(X)` are the points | `exists_eq_eval_of_mul` (the kernel is a closed maximal ideal, Mathlib's `ContinuousMap.ideal_isMaximal_iff`), `isPure_evalAt`, `isPure_iff_exists_eval` | matches |
| Theorem 2.12.9: "The pure state space of `C₀(X)` (with the relative w*-topology) is homeomorphic to `X`" | the points: `isPure_iff_exists_eval`; the topology: Mathlib's `WeakDual.CharacterSpace.homeoEval` (`X ≃ₜ` the characters of `C(X, ℂ)`) | matches for compact `X`; for locally compact Hausdorff `X`, `isPure₀_iff_exists_eval` (`PureStatesC0`) by the source's reduction: a state of `C₀(X)` extends to `F ↦ ω(F - F(∞)) + F(∞)` on `C(X̃)` (`ext_mem_states`), a pure one to a pure one (`isPure_ext`), and the point at infinity is excluded |

Row G3-089 also names Kantorovich-Rubinstein duality, which is not stated: the row stays partial.
