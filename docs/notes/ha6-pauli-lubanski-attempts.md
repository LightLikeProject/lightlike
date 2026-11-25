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

## The Stone generators on `L²` (compiled)

`Lightlike/Poincare/InducedL2.lean`, `ShellChart.lean`, `GeneratorL2.lean`, `PauliLubanskiL2.lean`,
`PauliLubanskiStone.lean`.

* For every `SL(2,ℂ)`-invariant measure `μ` on the mass shell, `U(A)` acts on `L²(μ; ℂ^{n+1})` as a unitary
  (`inducedL2E`: composition with the measure-preserving action, then multiplication by the continuous field of spin
  matrices), with `U(AB) = U(A) U(B)` (`inducedL2_mul`). The curves of the Lorentz generators are one-parameter
  subgroups (`lorCurve_add`), so `t ↦ U(γ_{νρ}(t))` is a one-parameter unitary group
  (`isOneParameterUnitaryGroup_lorGroupL2`).
* For a chart test function `ψ = φ ∘ q` (`φ` continuously differentiable with compact support), `μ` finite on
  compacts, the difference quotients converge in `L²` to the pointwise generator (`tendsto_diffQuot_L2`: dominated
  convergence; the derivative at every time is a unitary matrix times the generator, which is continuous with
  compact support, and the mean value theorem bounds the quotients off a compact set). So `ψ` is in the domain of the
  Stone generator and `A_{νρ} ψ = (1/i) M_{νρ} ψ` (`generator_lorGroupL2`).
* `p_σ ψ` is again a test function (`ChartTest.mulP`), and `½ ε^{μνρσ} A_{νρ} (p_σ ψ) = (1/i) plMat ψ` in `L²`
  (`pauliLubanski_stone`).

The operators act on the chart test functions; that is the domain on which the identity is stated.

## Attempt 3, massless case: the full generators on the chart `P₀₀ > 0` (compiled, 25 Nov 2026)

`Lightlike/Poincare/PauliLubanskiMassless.lean`. The obstruction of attempt 2 (no global smooth section: `coneLift`
has `1/a` with `a = √(P₀₀/2)`) is avoided by working on the open chart `P₀₀ > 0` of the light cone (all of it except
the negative `z`-axis, a null set), where `coneLift` is the smooth `[[a, 0], [P̄₀₁/(2a), 1/a]]`. There the `(0,0)`
entry of the Wigner element is `(A₀₀ a_Q + A₀₁ Q₁₀/(2 a_Q))/a_P` (`wigner00`), and along `γ(t)⁻¹ • P` its derivative
is `i · helCoef P X` (`helicity_phase_deriv`: the real parts cancel because `P₀₀ = 2a²`). Result:
`hasDerivAt_helicityAct_curve` (generator = helicity phase + orbital derivative), `plComb_genValM` (orbital part
cancels by `plGen_fix`, helicity coefficient `p^μ/2` by `helCoef_plGen`), and
`hasDerivAt_pauliLubanski_massless`: `½ ε^{μνρσ} p_σ M_{νρ} = i (n/2) p^μ` pointwise on the chart, for every
chart-differentiable wave function. Not done: the chart `P₀₀ = 0` (the section jumps there, so the pointwise
derivative of `helicityAct` does not exist for this section; a smooth-section model differs by a phase function),
and the `L²` Stone-generator version (the massive one is `PauliLubanskiStone.lean`).
