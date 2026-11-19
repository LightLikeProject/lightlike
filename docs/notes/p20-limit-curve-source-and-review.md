# T-GE2-P20: the limit-curve theorem, review of regge's proof, source comparison

Task file `Tasks/GE2/T_GE2_P20.lean` (statement locked, unchanged: the diff against main is the import line and the proof line only);
proof in `Lightlike/Spacetime/CausalLadder/{AffineCurve,BoxExit,UnitArcEndpoint,GluedLimitCurve,LimitCurveStep}.lean`
(written by regge on regge/p20, taken over by the causal stream; the seven P20 commits cherry-picked onto main, without the merged
regge/ge11 branch: **P20 does not need GE11**, its files import only `Lightlike.Spacetime.Causal.*` and `Lightlike.Spacetime.CausalLadder.*`).

## Review

* Statement: line for line equal to the locked statement (`git diff origin/main -- Tasks/GE2/T_GE2_P20.lean`).
* Structure: `exists_inextendible_limit_curve_of_step` follows my interface (`.agent/p20-limit-curve-interface.lean`): `limit_curve_step` (uniform step,
  from the cone estimate, the first exit of a future-inextendible curve from a chart box `BoxExit`, the one-chart theorem `limit_curve_points_of_cone_estimate`
  (LL-0151 follow-up, on main), an affine reparametrisation `AffineCurve`), `exists_glued_limit_curve_of_step` (recursion over unit arcs with a diagonal subsequence),
  `not_tendsto_of_unit_arcs` (`UnitArcEndpoint`: a curve of unit arcs with chart displacement bounded below has no future endpoint).
* No `sorry`, standard axioms (gate step), `lake build Lightlike.Spacetime.CausalLadder.LimitCurveStep Tasks.GE2.T_GE2_P20` succeeds on main 6a16806.

## Source read (pdftotext of the arXiv PDF)

E. Minguzzi, *Causality theory for closed cone structures with applications*, arXiv:1709.06494, section 2.3 "Limit curve theorems":
* Lemma 2.1 (limit curve lemma), printed p. 28: "Let `x_n : (−∞, +∞) → M` be a sequence of inextendible continuous causal curves parametrized with respect to
  h-arc length [h a complete Riemannian metric], and suppose that `p ∈ M` is an accumulation point of the sequence `x_n(0)`. There is an inextendible continuous causal curve
  `x : (−∞, +∞) → M`, such that `x(0) = p` and a subsequence `x_k` which converges h-uniformly on compact subsets to `x`."
* Theorem 2.14 (limit curve theorem), pp. 28-29: for causal segments with converging endpoints: a limit curve, or future/past inextendible limit curves from `p` and ending at `q`.
* Theorem 2.13: arc-length parametrized causal curves in a compact set have a uniformly converging subsequence.
Hawking-Ellis, Lemma 6.2.1 (the locked source): not read.

## Differences from Minguzzi's Lemma 2.1 (all representation; against the locked HE form of the task)

1. *Curves*: the library's future causal curves (locally Lipschitz in charts, velocity in the future cone a.e.) against continuous causal curves (a larger class);
   the setting is a smooth Lorentzian manifold (cone structure of the metric), a special case of closed cone structures.
2. *Convergence*: ours says each point `q` of the limit curve is a limit of points of the curves of one subsequence ("all but finitely many curves meet every neighbourhood of
   `q`", the form of Hawking-Ellis' limit curve), not h-uniform convergence on compact sets of arc-length parametrizations (no Riemannian metric `h`, no completeness needed).
   The conclusion is therefore weaker in form than uniform convergence, and the hypothesis on the base point is that `p` is a limit point of the set of all points of the curves
   (every neighbourhood of `p` meets infinitely many curves), more general than `p` an accumulation point of `x_n(0)`.
3. *Inextendibility*: only the future end is asked (as in the locked statement), against both ends.
4. *Hypotheses*: `[T2Space M] [SecondCountableTopology M] [BoundarylessManifold I M]` (source: connected Hausdorff second countable `C^r` manifold, `n + 1` dimensional, section 1.3 / 2, p. 10).
