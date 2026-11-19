# T-HA6: the Pauli–Lubanski operator of the induced representations — attempts

The statement wanted: the operator identities `W² = −m² s(s+1)` on the massive and `W = h P` on the
massless induced representations, with `W^μ = ½ ε^{μνρσ} M_{νρ} P_σ` built from the generators `M_{νρ}` obtained as
derivatives of the representation `U` on smooth wave functions (Bekaert–Boulanger, arXiv:hep-th/0611263v2, §5.2,
equation (54), page 39; §3.2–3.3, pages 12–15).

## Attempt 1: generators at the standard momenta (compiled)

`Lightlike/Poincare/PauliLubanskiRest.lean`, `Lightlike/Poincare/MasslessGenerators.lean`.

* The little group fixes the standard momentum, so on the states of that momentum `U` acts through the little-group
  representation (`inducedAct_rest`, `helicityAct_base`), and the little-group generators are genuine derivatives of
  `U` at that momentum: `d/dθ (U(R_a(θ)) ψ)(q) = dSpin n (X_a) ψ(q)` (`hasDerivAt_inducedAct_rest`);
  `d/dθ (U(R(θ)) ψ)(K) = i (n/2) ψ(K)` and `d/dt (U(T_c(t)) ψ)(K) = 0` (`hasDerivAt_helicityAct_rot`,
  `hasDerivAt_helicityAct_trans`).
* From these: `W² = −m² s(s+1)` in the rest frame (`pauliLubanski_sq_rest`) and `W ψ(K) = h K ψ(K)` at the standard
  light-like momentum.
* Where it stops: the components of `W` at the standard momentum are identified with the little-group generators as
  in the source (`W = (0, m J)` at rest; `W⁰ = W³ = J₃`, `W¹, W²` the translations at `K`), not derived from
  `½ ε M P`; the boost generators (whose terms cancel by antisymmetry at the standard momentum) are not computed.
  Transporting to other momenta needs the covariance `U(A) M(X) U(A)⁻¹ = M(Ad_A X)` of the derivative generators,
  i.e. that the derivative of `t ↦ (U(γ t) ψ)(P)` depends only on `γ'(0)`: a chain rule for the induced action in
  both variables. That needs a differentiable structure on the mass shell and the light cone; here they are subtypes
  of `Matrix (Fin 2) (Fin 2) ℂ` without a manifold structure, and Mathlib has none for them.

## Attempt 2: the generators at a general momentum, directly (massless: stopped; massive: see below)

* Massless: the standard lift `coneLift` (`Lightlike/Poincare/LightCone.lean`) is `[[a, 0], [β̄/(2a), 1/a]]` with
  `a = √(P₀₀/2)` where `P₀₀ > 0`, and a different formula where `P₀₀ = 0`; near `P₀₀ = 0` the entry `1/a` is unbounded.
  This is not a choice we can repair: there is no continuous global section of `SL(2,ℂ) → light cone` (the helicity
  line bundle over the sphere of directions is not trivial). So for a generic smooth `ψ`, `A ↦ (U(A) ψ)(P)` is not
  differentiable at momenta with `P₀₀ = 0`, and `W = h P` at a general momentum needs local sections and the law by
  which the helicity phase changes between them; that machinery is not in the library.
* Massive: the section `stdLift` is smooth, so the computation is possible in principle: the spin part of `M(X)` at
  `P` is `dD` of `L(P)⁻¹ X L(P) − L(P)⁻¹ dL(P)[X · P]` with `L(P) = (Q + 1)/√(tr Q + 2)`, and `W` follows by the
  `ε`-contraction, where the orbital terms cancel. The derivative of `L` along the orbit and the contraction were
  set up on paper only; the computation is long and was not completed.

## Transport to every momentum (compiled)

`Lightlike/Poincare/PauliLubanskiMassive.lean`, end of `Lightlike/Poincare/MasslessGenerators.lean`.

The little group of a momentum `P` is `L(P) H L(P)⁻¹` (`H` the little group of the standard momentum, `L` the
standard lift), and by the group law of `U` its elements act on the states of momentum `P` exactly as `H` acts at the
standard momentum: `(U(L(P) u L(P)⁻¹) ψ)(P) = D(u) ψ(P)` (`inducedAct_conj`) and
`(U(L(P) A L(P)⁻¹) ψ)(P) = (A₀₀)ⁿ ψ(P)` (`helicityAct_conj`). The curves `θ ↦ L(P) R(θ) L(P)⁻¹` fix `P`, so their
derivatives at `P` exist for every wave function, with no differentiable structure and no continuity of `L`
(`hasDerivAt_inducedAct_littleGen`, `hasDerivAt_helicityAct_rot_at`, `hasDerivAt_helicityAct_trans_at`). Hence, with
`W(P)` in its little-group form (`W(P) = Λ(L(P)) W(standard momentum)`), `W² = −m² s(s+1)` and `W = h P` hold at every
momentum (`pauliLubanski_sq`, and the three massless derivatives).

What remained after the transport: the identity `W^μ = ½ ε^{μνρσ} M_{νρ} P_σ` for the full set of generators
`M_{νρ}` (boosts and the orbital parts, which cancel in the contraction). It is done in the massive case (next
section); in the massless case the obstruction of attempt 2 stands.

## Attempt 2, massive case: the full generators (compiled)

`Lightlike/Poincare/PauliLubanskiAlgebra.lean`, `GeneratorCurves.lean`, `LiftDerivative.lean`, `LorentzCurves.lean`,
`PauliLubanskiCasimir.lean`, `PauliLubanskiGenerators.lean`.

* Generators. A wave function `ψ` is taken differentiable at `P` in the chart of the mass shell by the spatial
  momentum (`ChartSmoothAt`). Along every curve `γ` in `SL(2,ℂ)` through `1` with velocity `X`, the derivative of
  `t ↦ (U(γ(t)) ψ)(P)` at `0` is `dSpin(w_X) ψ(P) + dφ(−(X P + P Xᴴ))`, with the Wigner velocity
  `w_X = L(P)⁻¹ X L(P) + L(P)⁻¹ dL(P)[−(X P + P Xᴴ)]` (`hasDerivAt_inducedAct_curve`); the derivative of the standard
  lift is `hasDerivAt_stdLiftMat`. The value depends on the curve only through `X` and is real-linear in `X`.
* The Lorentz generators `M_{νρ}` are fixed by their action on momenta, `(M_{νρ} p)^α = δ^α_ν p_ρ − δ^α_ρ p_ν`
  (`lorGen_act`); each is the velocity of a curve in `SL(2,ℂ)` (`exists_lorCurve`).
* The combination `½ ε^{μνρσ} p_σ M_{νρ}` (`ε^{0123} = 1`) is the matrix `X^μ_P` of `plGen` (`plComb_eq`), and
  `X^μ_P P + P (X^μ_P)ᴴ = 0` (`plGen_fix`): the orbital part and the derivative of the lift drop out, and `W^μ` acts at
  `P` by `dSpin(L(P)⁻¹ X^μ_P L(P))` (`plComb_genVal`, `hasDerivAt_pauliLubanski`).
* The square. The tensor `Σ_μ η_{μμ} X^μ_P ⊗ X^μ_P` is `(p²/4)` times the Fierz tensor `2 δ_{ad} δ_{bc} − δ_{ab} δ_{cd}`
  (`plGen_fierz`), which is invariant under conjugation, and the Casimir `Σ_μ η_{μμ} dSpin(Y^μ)²` depends only on this
  tensor (`casimir_eq_of_tensor`). So the square at `P` is the rest-frame one: with the Hermitian operators `i W^μ`,
  `W_μ W^μ = −m² s(s+1)` at every momentum (`pauliLubanski_sq_generators`).

Both orders of `M_{νρ}` and `P_σ` agree (`hasDerivAt_pauliLubanski_MP`: the commutator terms `(d p_σ)(M_{νρ} p)`
vanish in the contraction with `ε`), and since `W^μ` acts as multiplication by the matrix function `plMat`, the
operator square `W_μ W^μ` is the pointwise matrix product (`pauliLubanski_sq_operator`).

Remaining difference (kind: weaker): the generators are pointwise derivatives on wave functions differentiable in the
chart, not the Stone generators on `L²`.
