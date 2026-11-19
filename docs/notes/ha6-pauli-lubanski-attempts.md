# T-HA6: the Pauli–Lubanski operator of the induced representations — attempts

19 November 2026. The statement wanted: the operator identities `W² = −m² s(s+1)` on the massive and `W = h P` on the
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

## Attempt 2: the generators at a general momentum, directly (explored, not compiled)

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

Status: the operator identities at general momenta are open; the standard-momentum content is formalised.
