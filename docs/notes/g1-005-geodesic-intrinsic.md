# G1-005 (GE3): the geodesic equation of a connection on a manifold, intrinsic form

`Lightlike/Spacetime/GeodesicIntrinsic.lean` (24 November 2026, regge/ge3).

* `IsGeodesicCov cov γ J`: `∇_{γ'} γ' = 0`, written through a smooth local extension `X` of `γ'` (a connection acts on
  vector fields; there is no covariant derivative along a curve in Mathlib's `CovariantDerivative`, checked).
* `isGeodesicCurveOn_of_isGeodesicCov`: for the Levi-Civita connection of a Lorentzian metric, an intrinsic geodesic is a
  chart-wise geodesic (`IsGeodesicCurveOn`, `Spacetime/PenroseSingularity/Defs.lean`). Proof: `hat_cov` (components of `∇_X X` are
  `D X̂ (X) + Γ̂(X̂, X̂)`), `gamHat_coord` (Γ̂ is the Christoffel symbol of the coordinate metric), the chain rules
  `hasDerivAt_chart_curve`, `hasDerivAt_hat_curve`, and `hv_eq_mfderiv` (components of a vector are its image under the
  derivative of the chart).

Source: Carroll, *Lecture Notes on General Relativity* (arXiv gr-qc/9712019), chapter 3, the geodesic equation; the
comparison with the page is pending (not read in this session), so no source comparison is claimed.

Limits: one direction only (the converse needs a smooth extension of `γ'` near `γ t`, available when `γ'(t) ≠ 0`);
Levi-Civita connections only; the non-vacuity example is a constant curve.
Next (GE3 extensions): expMap on a manifold, then Jacobi fields on a manifold.
