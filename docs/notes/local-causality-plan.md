# Local causality (Chruściel Prop. 2.4.5), gap rows G1-001, G1-002: plan

Branch `causal/local-causality` (from fable3's wip `fable3/local-causality` e2f8abd, on `fable3/geodesic-global` 8699ca8).

## Source read (pdftotext of the arXiv PDF)

P. T. Chruściel, *Elements of causality theory*, arXiv:1110.6706v1, section 2.4 "Futures, pasts", pp. 20–23:
Proposition 2.4.5 (p. 20): for `O ⊂ O_p` a normal-coordinate ball with `∇x⁰` timelike on `O`, and `σ_p(exp_p(x^μ)) = η_μν x^μ x^ν` (2.4.6),
`q = exp_p(x^μ) ∈ I⁺(p; O) ⟺ σ_p(q) < 0, x⁰ > 0`, `∈ J⁺(p; O) ⟺ σ_p(q) ≤ 0, x⁰ ≥ 0`, `∈ J̇⁺(p; O) ⟺ σ_p(q) = 0, x⁰ ≥ 0` (2.4.7);
Proposition 2.4.7 (p. 21): `I⁺(p; O)` is open; Lemma 2.4.8 (p. 21): a time function is non-decreasing along causal paths; Lemma 2.4.9 (p. 22);
the proof by perturbed metrics (pp. 22–23).

## Method (fable3's, no perturbed metrics)

In normal coordinates `v(s) = φ⁻¹(γ(s))` of a future causal curve from `p` in the time ball: `f = g_p(v, v)` (= σ_p) and
`h = −g_p(e, v)` (= x⁰). Then
1. `h' = −g(N, γ̇) > 0` a.e. (`IsTimeBall.dual`, future causal), so `h` increases from `0`;
2. Gauss lemma: `f' = 2 g(P, γ̇)` with `P = Dφ(v) v`, `g(P, P) = f`, `−g(P, N) = h`;
3. where `f > 0`: `f' h ≤ f h'` (`IsLorentzianForm.two_mul_le_of_spacelike`); where `f ≤ 0`: `f' ≤ 0` (`P` future causal or `v = 0`);
4. cone bound `f ≤ C h²`: a uniform cone estimate `‖w‖ ≤ C₁ (−g_p(e, w))` for future causal `Dφ(u) w`, `u` in a closed ball (compactness;
   the functional `−g_p(e, ·)` is fixed), integrated as in `ConeCurve.exists_cone_estimate_curve`, then `f ≤ ‖g_p‖ ‖v‖²`;
5. `nonpos_of_cone_inequality` (ConeTrap.lean) gives `f ≤ 0`; with `h ≥ 0` this is the `J⁺` line of (2.4.7), "⇒".

## Steps

* [ ] `exists_uniform_cone_estimate` (coordinate, compact ball).
* [ ] `coordinate_local_causality` (the `J⁺` line, "⇒") in normal coordinates.
* [ ] the `I⁺` line (strict inequality for timelike curves), the "⇐" directions (radial geodesics).
* [ ] existence of time balls for small `r`.
* [ ] bridge to the manifold relations `chronFuture`/`causalFuture` (`Spacetime/OpenCoordMetric.lean`), tests.
