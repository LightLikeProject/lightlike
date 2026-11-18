# T-GE2-P11: causal simplicity implies stable causality (plan)

Status: not closing by 20:00 on 18 November 2026. Nothing of P11 itself is proved; the pieces below
that exist are named.

Statement: `Lightlike.Causal.isStablyCausal_of_isCausallySimple` (T2, second countable): causal
simplicity (causal, `J±(x)` closed) gives a continuous time function.

Method (Hawking, "The existence of cosmic time functions", 1969; Hawking–Ellis, Chapter 6). Take a
finite measure `μ` on `M`, positive on open sets (from the volume measure `volumeMeasure g` of the
metric, Regge's `regge/volume-form`, by a countable sum of normalised restrictions to a compact
exhaustion; this needs second countability). Put `t⁻(x) = μ(J⁻(x))`. Then `t⁻` is the time function:
nondecreasing along causal curves, strictly increasing, continuous.

Sub-lemmas, in the order they are needed:

1. A finite measure with full support. From `volumeMeasure` (finite on compact sets, positive on
   nonempty opens) and a compact exhaustion. Needs Regge's file.
2. `J⁻(y) ⊆ J⁻(x)` for `y ∈ J⁻(x)` (`causal_trans`, exists on main), so `t⁻` is monotone.
3. Strict increase. For `y ∈ J⁺(x)`, `y ≠ x`: `y ∉ J⁻(x)` by causality, and `J⁻(x)` is closed, so a
   neighbourhood of `y` avoids it; `J⁻(y)` contains a nonempty open set near `y` (chart lines:
   `exists_line_between` in `CausalLadder/ChartLine.lean`, with the endpoint `y` fixed and the start
   in a small ball). Hence `t⁻(y) - t⁻(x) > 0`.
4. Lower semicontinuity of `t⁻`: openness of `I⁻(x)` (task P5, spinfoam) and `I⁻(x) ⊆ J⁻(x)`; for
   `x_k → x`, every compact subset of `I⁻(x)` lies in `I⁻(x_k)` for large `k`.
5. Upper semicontinuity of `t⁻`: from closedness of `J⁻(x)` (causal simplicity) and a limit argument
   on the relation `{(a, b) | a ∈ J⁻(b)}`; for `x_k → x`, `limsup 1_{J⁻(x_k)} ≤ 1_{J⁻(x)}` pointwise,
   then dominated convergence (finite `μ`).
6. The remaining gap between 4 and 5 is the measure of `J⁻(x) \ I⁻(x)` (the horismos): it must be
   null. Hawking–Ellis show the boundary of `J⁻(x)` is a Lipschitz graph in charts, hence null. This is
   the hardest step; with the cone estimate of `CausalLadder/ConeCurve.lean` the boundary is locally the
   graph of a function that is Lipschitz in the time direction.
7. Assemble `t⁻` and show `IsTimeFunction`: continuous and strictly increasing along causal curves
   (`causalFuture` membership).

Reusable results already proved: causal transitivity, cone estimate and limit curve in a chart
(LL-0151), chart straight lines and future/past points (`ChartLine.lean`), closedness of `J±` for
globally hyperbolic spaces (`GlobHypSimple.lean`, T-GE2-P12).

Risks: steps 4–6 are research-scale (several thousand lines); a statement without boundary
(`BoundarylessManifold`) is likely needed, as for P7, P12 and P13.
