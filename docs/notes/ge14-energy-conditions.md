# GE14: energy conditions, compared with Curiel (read 18 November 2026)

Sources read: E. Curiel, *A Primer on Energy Conditions* (arXiv 1405.0403), section 2.1 "Pointilliste Energy Conditions", p. 5-6 of the pdf (the physical forms); S. M. Carroll, *Lecture Notes on General Relativity*
(arXiv gr-qc/9712019), the weak energy condition, eq. (4.72), p. 117. Hawking-Ellis, Chapter "The physical significance of curvature" (the task's source): not read, comparison pending.

* NEC: "for any null vector k^a, T_mn k^m k^n >= 0" (Curiel, physical form): our `NullEC`.
* WEC: "for any timelike vector ξ^a, T_mn ξ^m ξ^n >= 0": our `WeakEC`; Carroll (4.72) "T_{μν} V^μ V^ν >= 0 for all timelike vectors V".
* SEC: "for any timelike vector ξ^a, (T_mn − ½ T g_mn) ξ^m ξ^n >= 0": our `StrongEC` (four dimensions, trace by `traceG`, the trace of `g⁻¹ T`).
* DEC (physical form): "1. for any timelike vector ξ^a, T_mn ξ^m ξ^n >= 0, and T^a_n ξ^n is causal; 2. for any two co-oriented timelike vectors ξ^a and η^a, T_mn ξ^m η^n >= 0": our `DominantEC`,
  with "co-oriented" expressed as `g(ξ, η) < 0` (two timelike vectors are in the same cone iff their product is negative), and "causal" as `g(w, w) <= 0`.
* Effective forms in terms of ρ and the principal pressures (Curiel, same table) are not defined here; the trust checks are the three of the task: dust with ρ >= 0 satisfies all four; a positive
  cosmological constant violates the strong condition (`ρ + Σ p = ρ − 3ρ < 0`); the Klein-Gordon tensor with negative potential at a point of vanishing gradient violates the weak condition.
* Differences: Curiel works on a spacetime with a time orientation; ours is pointwise on a Lorentzian vector space, "co-oriented" is the pointwise notion above. The scalar-field tensor
  `T = dφ ⊗ dφ − (½ |dφ|² + V) g` is the standard form, not compared with a source here (comparison pending), stated at one point.
