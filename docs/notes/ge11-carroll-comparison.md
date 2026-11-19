# GE11: comparison of the coordinate curvature statements with Carroll (read 18 November 2026)

Source read: S. M. Carroll, *Lecture Notes on General Relativity* (1997), arXiv gr-qc/9712019, the pdf text, chapters 2, 3 and 5. Page numbers
are those of the arXiv pdf headers.

## What was checked, and the location
* Riemann tensor of the Christoffel connection in coordinates: eq. (3.67), p. 76:
  `R^ρ_{σμν} = ∂_μ Γ^ρ_{νσ} − ∂_ν Γ^ρ_{μσ} + Γ^ρ_{μλ} Γ^λ_{νσ} − Γ^ρ_{νλ} Γ^λ_{μσ}`. Our `riemann` (`Curvature.lean`) and `riemannW`
  (`CurvatureWithin.lean`) are this formula with the same index placement (`riemann g ρ σ μ ν`).
* Ricci tensor `R_{μν} = R^λ_{μλν}`, eq. (3.90), and scalar `R = g^{μν} R_{μν}`, eq. (3.92), p. 81: our `ricci`, `scalarCurvature` (and the `W` versions).
* Einstein tensor `G_{μν} = R_{μν} − ½ R g_{μν}`, eq. (3.95), p. 82: our `einsteinTensor`.
* Symmetries `R_{ρσμν} = −R_{σρμν}` (3.78), `R_{ρσμν} = R_{μνρσ}` (3.79), `R_{ρσμν} + R_{ρμνσ} + R_{ρνσμ} = 0` (3.80), p. 79: our
  `riemannLower_antisymm_first`, `riemannLower_pair_symm`, `bianchi_first_lower` (and the `W` versions). Carroll derives them in Riemann normal coordinates and
  extends by tensoriality; ours is a direct coordinate proof (mixed partials commute), a different route to the same statements.
* Bianchi identity `∇_{[λ} R_{ρσ]μν} = 0`, eq. (3.88), p. 81, and its double contraction `∇^μ R_{ρμ} = ½ ∇_ρ R` (3.94), equivalent to
  `∇^μ G_{μν} = 0` (3.96), p. 82: our `bianchi_second_proved`, `einstein_div_coord(W)`, `einstein_divergence_free_proved`.

## Match, and differences
* The formulas match as above. Our convention for the Riemann tensor's index order and sign is Carroll's.
* Carroll's definition of a manifold (ch. 2, p. 38: a set with a maximal atlas of charts to `ℝⁿ`) does not state a Hausdorff condition, so working
  without `[T2Space M]` is not stronger than the source. He does not discuss manifolds with boundary (ch. 3 notes, "we haven't discussed manifolds with
  boundary"): the corners version is a generalisation beyond the source, not a difference from it.
* The twice-contracted Bianchi identity is used by Carroll as a tensor identity; ours is stated for the covariant derivative `covDerivBilinAt` of the
  Levi-Civita connection of a smooth Lorentzian metric on a manifold (`C²` structure added).
* Signature: Carroll uses `−+++`, as the library.

## Not checked here
Differentiability class: Carroll assumes smooth throughout; we use `C^∞` metric and `C²` structure (a convention). Wald ch. 3 not read.
