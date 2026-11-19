# CO30: comparison of the Friedmann equations on `I × S³` with Carroll (read 18 November 2026)

Source read: S. M. Carroll, *Lecture Notes on General Relativity* (1997), arXiv gr-qc/9712019, ch. 8 (Cosmology), pdf text; page numbers of the arXiv pdf.

## Statements compared
* Spatial slices of constant curvature: `^{(3)}R_{ijkl} = k (γ_{ik} γ_{jl} − γ_{il} γ_{jk})`, with Ricci tensor `^{(3)}R_{jl} = 2k γ_{jl}`, eq. (8.3), p. 218-219. For the unit 3-sphere
  (Mathlib's `sphere (0 : EuclideanSpace ℝ (Fin 4)) 1`, round metric `h`) the Ricci tensor is `2h`, i.e. `k = 1`.
* Robertson-Walker metric `ds² = −dt² + a(t)² [dr²/(1 − k r²) + r² dΩ²]`, eq. (8.7), p. 219: ours is `−dt² + a(t)² h` on `J × S³` with `h` the unit round metric (`k = 1`),
  a global form of the same metric: Carroll's chart `r` covers the sphere minus a point, ours covers all of `S³` by Mathlib's stereographic atlas.
* Perfect fluid at rest in the comoving frame, `T_{μν} = diag(ρ, p γ_{ij}…)` i.e. `T = (ρ + p) u ⊗ u + p g` with `u = ∂_t`: eq. (8.17), p. 220: our `flrwFluid`.
* Einstein equations with a cosmological constant `G_{μν} = 8πG T_{μν} − Λ g_{μν}`, eq. (8.29), p. 222: ours is `G + Λ g = 8π G_N T`, the same equation.
* Friedmann equations `ä/a = −(4πG/3)(ρ + 3p)` (8.35) and `(ȧ/a)² = (8πG/3) ρ − k/a²` (8.36), pp. 223-224, derived from the `00` and `ij` components (8.33), (8.34): ours,
  `Cosmology.FirstFriedmann` / `SecondFriedmann` with `k = 1` and a cosmological term `Λ/3`: Carroll includes `Λ` as vacuum energy `ρ_vac = Λ/(8πG)`, `p_vac = −ρ_vac` ((8.30)-(8.31), p. 222),
  equivalent to our `Λ/3` term.

## Match and differences
* The equations match. Carroll derives the Friedmann equations from the Einstein equations for the Robertson-Walker form; we prove the equivalence (iff) of the Einstein equations on the manifold
  with the Friedmann equations, chartwise, for the Levi-Civita connection.
* Carroll's metric is `−dt² + a² (spatial metric of constant curvature k)` for any `k`; ours is the case `k = 1` of the product `J × S³`; `k ≤ 0` is the separate statement on the chart domain
  (`flrwManifold_einstein_iff_friedmann`).
* Hypotheses: `a` smooth and positive on an open `J ⊆ ℝ`; `ρ, p` arbitrary functions of `t` (no equation of state or conservation law assumed), as in the source.
* Not covered by the source reading: Carroll does not discuss the global topology `J × S³` versus the coordinate patch beyond choosing coordinates; nothing in the statement depends on it.

## Milestone row CO30 (to add to docs/tasks/sources.yaml in the rebuild)

Read 19 November 2026: S. M. Carroll, *Lecture Notes on General Relativity*, arXiv gr-qc/9712019, chapter 8, p. 223
(PDF p. 230): the Einstein equations for the FLRW metric (8.7) with a perfect fluid give (8.33)–(8.34), and after
eliminating `ä`, the Friedmann equations (8.35) `ä/a = -(4πG/3)(ρ + 3p)` and (8.36) `(ȧ/a)² = (8πG/3) ρ - k/a²`, for
all `k` including the closed universes `k = +1`. Milestone entry: `CO30`, class sourced, ref `carroll-1997`, location
"eq. (8.36)", check word "Friedmann".
