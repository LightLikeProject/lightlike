# Changelog

Notable changes to Lightlike. Results are identified by stable IDs (`LL-NNNN`), listed with their
sources and review status in [docs/RESULTS.md](docs/RESULTS.md). Versions follow
[Semantic Versioning](https://semver.org/); before 1.0.0, minor versions may change the API.

## [0.2.0]

### Library

- 19 new proven results, LL-0048 to LL-0066: Regge calculus (7), spin foams (7), dynamical
  triangulations (3, a new area) and PL topology (2).
- LL-0047, the large-spin asymptotic formula of the Euclidean EPRL vertex amplitude in coherent
  boundary states, a stated target in 0.1.0, is proven.
- The catalog has 66 entries: 65 proven results and 1 conditional result.
- Before the release, a reviewer agent compared each statement new in this release with its cited
  source at the cited location: conventions, quantifier ranges, junk values, non-vacuity, and
  whether title, note, docstrings and citation say what the Lean statement says. Its fixes are
  applied. For LL-0062 the cited book (Ambjørn, Durhuus and Jónsson 1997) was not accessible,
  so the entry now cites Ambjørn, Jurkiewicz and Loll (2001), eqs. (24) and (26), where the
  comparison was completed. The entries stay `kernel-checked`: none has had expert human review.

### Notable results

- LL-0065 (with LL-0064): a closed combinatorial manifold and a simplicial complex, both
  containing the empty face, are PL homeomorphic exactly when finitely many bistellar (Pachner)
  moves turn one into the other (Lickorish 1999, Theorem 5.9; Newman's theorem, LL-0064, is
  Theorem 4.5 there).
- LL-0047: the large-spin asymptotics of the Euclidean EPRL vertex amplitude in coherent boundary
  states, for 0 < γ < 1, with phases ±S and ±γS for the Regge action S: for a nondegenerate
  4-simplex with spins proportional to its triangle areas, an even spin sum at every node and a
  nonsingular Hessian at both critical points (Barrett, Fairbairn and Hellmann 2010, eqs. (16)
  and (26)). That the coherent integral equals the vertex on Livine–Speziale intertwiners is not
  proven.
- LL-0049, LL-0050, LL-0051: the gauge-fixed Ooguri state sum of 4D spin foams, with a gauge rule
  proposed in this library, is invariant under the 3-3, 2-4 and 1-5 Pachner moves and their
  inverses, at finite cutoff, under conditions that make the cutoffs on the faces inside the move
  non-binding; removing the cutoff and the independence of the gauge set are not proven, and the
  kernel examples for the 2-4 and 1-5 moves have no gauge triangles.
- LL-0052: in the normalisation used (orthonormal intertwiners, no dimension factor per
  tetrahedron, edge amplitude 1), the Barrett–Crane vertex amplitude is a sum of squared 15j
  symbols, so it is real and non-negative. Baez and Christensen's sign rule differs from it by
  (−1) to the sum of the doubled spins; that the vertex with this sign equals their 10j symbol is
  not proven.
- LL-0053: in dimension 2, Lipschitz-weighted sums of Regge deficit angles of fat vertex stars of
  bounded valence converge to the weighted integral of the Gauss curvature at rate O(h), given the
  vertex cells (LL-0054 builds them for explicit planar triangulations): a planar step towards the
  theorem of Cheeger, Müller and Schrader (1984), not that theorem.
- LL-0063: for a symmetric, C³, compactly supported perturbation of the flat plane and a C¹
  compactly supported weight, the weighted linearized deficit angles of the diagonal grid of mesh
  1/n converge to the weighted linearized Gauss curvature at rate O(1/n), with edge lengths from
  the first variation of the squared length (a 2D analogue, on one grid family, of Christiansen
  2011, who works in dimension 3).
- LL-0048: in Sorkin's Lorentzian Regge calculus with complex angles, a 4D triangulation embedded
  in Minkowski space, with the manifold condition at triangles, has zero deficit angles, and its
  Lorentzian Regge action is stationary under every variation of the squared edge lengths that
  fixes the boundary lengths (null triangles and tetrahedra excluded).
- LL-0061: two summations of the Ponzano–Regge sum of Bing's house: room spins summed first give
  1 under any cut-off on the central spin, while a simple cut-off Λ on all spins gives 37/12 at
  Λ = 1, a partial sum, not a limit; the partial sums do not settle (numerical, up to Λ = 14). The
  sum formula and the fact that the sum is not absolutely convergent, so that its value depends on
  how it is summed, are from Barrett and Naish-Guzman 2009, §2.4, and are not proven here.
- LL-0066: the Haar integral over SU(2)⁴ of the product of the six characters χ(g_i g_j⁻¹), one
  for each pair of the four group variables, is the square of the 6j symbol of the six spins
  (Freidel–Louapre 2004, eq. (94), read on the dual graph).

### Open work

- Spin foams: removing the cutoff and the independence of the gauge set in LL-0049 to LL-0051;
  the link from H² = 0 to removing the Ponzano–Regge cut-off (LL-0060).
- Regge calculus: Cheeger–Müller–Schrader in every dimension (LL-0053, LL-0054); null triangles
  (LL-0048); in LL-0063, edge lengths from the distance of the perturbed metric, dimension 3, and
  the Regge action itself.
- Dynamical triangulations: the Lorentzian causal action (LL-0059).

### Checks

- No new `maxHeartbeats 0`: a Lean file under `Lightlike/` may use it only if it is listed in
  `scripts/heartbeats_baseline.txt`, and only as often as listed there. The list has one file,
  `PL/TestsPachner.lean`, which already used it in 0.1.0, and the list may only shrink.
- Every Python script under `scripts/` is registered with the runner, as a cross-check or as a
  tool, and every registered cross-check can exit nonzero.
- Path references in comments and docstrings are checked (`scripts/doc_refs_check.py`, advisory).

## [0.1.0]

First public release.

### Library

- 45 proven results, 1 conditional result (proven under named hypotheses) and 1 stated target,
  in eight areas: harmonic analysis on Lie groups (16 proven); Lorentzian and Riemannian geometry
  (5); oscillatory and saddle-point asymptotics (2 proven, 1 stated target); operator algebras
  and quantum information (1); PL topology (3); quantum groups and state-sum TQFTs (7 proven,
  1 conditional); Regge calculus (5); spin foams (6). (Corrected in 0.2.0: this entry said 44
  proven results and 2 stated targets; LL-0030 was proven before the release.)
- `scripts/AxiomAudit.lean` checks the axioms of every declaration of the library; CI accepts only
  `propext`, `Classical.choice` and `Quot.sound`.

### Open work

- 27 areas in [ROADMAP.md](ROADMAP.md), each divided into milestones with their canonical sources
  ([docs/tasks/milestones.md](docs/tasks/milestones.md)).
- 226 tasks on the [task board](docs/tasks/README.md), including proof tasks whose statements are
  fixed in `Tasks/`, and candidates for Mathlib and Physlib.

### Checks

- CI hard rules: build, no `sorry`, the axiom audit of every declaration, docstrings, and the
  literature sources of the catalog. Advisory: the API maps, the task board, a self-test of the
  checks and the numerical cross-checks.
