# F11: the CA1 brackets on a hypersurface Σ — design note

Status: the definitions are in `Lightlike/Canonical/Hypersurface.lean` (chart families with change laws, `momentumConstraintM`, `hamiltonianConstraintM`, `admBracketM`); the statements are the tasks T-CA1-P4 to P7 (`Tasks/CA/`). The proofs are open.

## Goal

The brackets `{D,D}`, `{D,H}`, `{H,H}` of milestone CA1 (now proved on one global chart `ℝᵈ`: `bracket_momentum_momentum`,
`admBracket_momentum_hamiltonian`, `bracket_hamiltonian_hamiltonian_of_smooth`) on a hypersurface `Σ`, a second countable
Hausdorff smooth manifold modelled on `ℝᵈ`, without a global chart. Difference (b) of CA1 (one global chart) is removed.

## Interface (what is reused, what is new)

Reused, not redefined:

* `h` is a `Bundle.ContMDiffRiemannianMetric` on the tangent bundle of `Σ` (Mathlib,
  `Mathlib/Geometry/Manifold/VectorBundle/Riemannian.lean`); `Lightlike.LorentzianMetric` mirrors it.
* Needed from the metric layer (`Lightlike/Spacetime/NondegMetric.lean`, `NondegOpen.lean`, `VolumeMeasure.lean`): the chart coordinate metric of `h`
  (as `LorentzianMetric.coordMetric`, with its tensor change law) and the volume measure of `h` (as `volumeMeasure`).
* The coordinate Christoffel symbols, curvature and scalar curvature of a coordinate metric, and their covariance under a
  change of chart (`Lightlike/Spacetime/Chart*.lean`): the scalar curvature `R` of `h` in a chart is the existing chart
  scalar curvature of the coordinate metric.
* The chart-level integrands and brackets of `Lightlike/Canonical/` (`hamiltonianDensity`, `momentumDensity`, `admBracket`,
  `lieTensor`).

New (this task):

1. **The momentum density.** `π` is a tensor density of weight one: a family of chart components `π_α : ℝᵈ → Matrix`
   (smooth, symmetric) with the change law `π_β(y) = |det J| · J π_α(x) Jᵀ` for `y = φ_β∘φ_α⁻¹(x)`, `J` the Jacobian.
   Its chart components are the object the existing chart integrands consume.
2. **The smeared constraints.** `D[ξ]` and `H[N]` are the sum over the atlas pieces (`atlasPiece`, `VolumeMeasure.lean`) of the
   chart integrals of the existing integrands, restricted to the image of the piece. For compactly supported `ξ`, `N` this is
   a finite sum. The chart-independence of the sum is the content of the covariance lemmas (the integrands are densities of
   weight one, `momentumDensity` is a scalar density by F12 and `LieDeriv`, `hamiltonianDensity` by
   `scalarCurvature_pullback`, `dkinJ_lie`).
3. **Lie derivative.** Chart-wise, in the F12 form `ℒ_ξ h_ij = ξ^k ∂_k h_ij + h_kj ∂_i ξ^k + h_ik ∂_j ξ^k`; a lemma that it
   agrees across charts (the chart components of the Lie derivative of a covariant 2-tensor).
4. **The bracket.** `admBracket` with Gateaux derivatives along compactly supported symmetric variations `k` of `h`
   (variations are sections of `Sym²T*Σ`; in a chart the components `k_α`) and of `π` (weight-one density variations).
5. **The theorems.** `{D[ξ], D[η]} = D[[ξ,η]]`, `{D[ξ], H[N]} = H[ξ N]`, `{H[N], H[M]} = D[Y]` with `Y = h⁻¹(N dM − M dN)`
   (index raised with `h`), on `Σ`, for smooth data, positive definite `h`, compactly supported `ξ`, `η`, `N`, `M`.

## Bridge lemma

If `Σ` has a global chart (an open embedding `ℝᵈ ≃ₜ Σ` that is a chart of the atlas), the objects of the manifold statement
are, in that chart, the objects of the existing chart statements, and the three manifold brackets reduce to
`bracket_momentum_momentum`, `admBracket_momentum_hamiltonian`, `bracket_hamiltonian_hamiltonian_of_smooth`.

## Non-vacuity example

A concrete `Σ`: for `d = 2` the torus `T²` with the flat metric, `π = 0`, `ξ`, `N` bump functions
supported in one chart (the bracket is then the one-chart bracket, which is non-trivial for a non-constant lapse and shift),
and a case where the supports meet two charts (a lapse equal to `1` near the seam).

## Open points (for the maintainers)

* The exact form of `π` as a weight-one density (a section of `Sym² TΣ ⊗ |Λ^d T*Σ|` or chart families with the change law);
  the chart-family form is the cheapest and needs no new bundle.
* Whether Gateaux variations of `h` are taken in `ContMDiffRiemannianMetric` (positive definiteness is open, so small
  compactly supported variations stay in it) or as symmetric tensor fields; the second is simpler.
* Difference to record against the source: the `Σ` statement is `partial` in one respect, a closed (compact) or compactly
  supported setting; boundary of `Σ` is excluded.

## Source

Same as CA1: Thiemann, arXiv:gr-qc/0110034 §I.1.1 (the constraint algebra is stated for a spatial manifold `σ`); Hojman–Kuchař–Teitelboim 1976 not read.
