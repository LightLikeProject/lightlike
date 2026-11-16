# Changelog

Notable changes to Lightlike. Results are identified by stable IDs (`LL-NNNN`), listed with their
sources and review status in [docs/RESULTS.md](docs/RESULTS.md). Versions follow
[Semantic Versioning](https://semver.org/); before 1.0.0, minor versions may change the API.

## [0.3.0]

### Library

- 19 new results, LL-0067 to LL-0085: Turaev–Viro (6), spin foams (5), PL topology (4), Regge
  calculus (3) and Lorentzian asymptotics (1). 17 are proven and 2 are conditional (LL-0074,
  LL-0075, under the q-Dougall summation).
- The catalog has 85 entries: 82 proven results and 3 conditional results.
- LL-0076's `since` said 0.2.0, but it was merged after that release, and LL-0070 to LL-0075 said
  0.2.1, a version that was not released; all of them now say 0.3.0.
- The new entries are `kernel-checked`. Unlike 0.2.0, no reviewer agent compared them with their
  cited sources before this release.
- Fix: the one-triangle action of the Lorentzian vertex (`lorAction`, Asymptotics) matched the
  EPRL integrand only for even doubled spins and differed by a sign for odd ones. It is now
  written in the power form and is exact for every doubled spin.
- The Racah certificate files have per-declaration heartbeat limits instead of file-level ones.
- Turaev–Viro: Jackson's summation of the terminating very-well-poised 6φ5 series, proved by a
  telescoping certificate. It has no catalog entry, because no edition, page and equation
  of the formula in a book has been verified; it is the main step towards the q-Dougall summation.

### Notable results

- LL-0076: the Jordan curve theorem for simple closed polygons in the plane. The complement is
  the disjoint union of a bounded and an unbounded connected open set, and the polygon is the
  frontier of each (Moise 1977, the chapter "Separation properties of polygons in R²").
- LL-0082 to LL-0084: the polygonal Schoenflies theorem. A simple closed polygon in the plane has a
  triangulation by its own vertices, and the closed region it bounds is a PL ball whose boundary is
  the polygon (Moise 1977, the chapter "The Schönflies theorem for polygons in R²").
- LL-0070 to LL-0073: for the real q-Racah sum at q = e^{iπ/r}, the three-term recurrence in the
  third colour (Koekoek and Swarttouw 1996, eqs. (3.2.1)–(3.2.2)); the row identity of the
  quantum 6j symbol, endpoints included; detailed balance and weighted orthogonality of the rows
  for different sixth colours; and one common weighted norm for all rows and columns. LL-0074
  and LL-0075 give norm one and q-orthogonality at every level r ≥ 2 under the q-Dougall
  summation, an explicit hypothesis that is checked numerically (exact at r = 4 to 7) and not
  proved in Lean.
- LL-0068: the gauge-fixed Ooguri state sum at finite cutoff is constant along every chain of
  3-3, 2-4 and 1-5 Pachner moves and their inverses (with the hypotheses of LL-0049 to LL-0051).
  LL-0069, LL-0077 and LL-0081 say when a gauge set that forces every triangle still does after a
  1-5, 3-3 or 2-4 move. Forcing is this library's rule, used to show that the gauge-fixed sum is 1.
- LL-0067: the cut-off sum of the tetrahedron over doubled edge spins up to N is at least
  (N + 1)², so it has no limit without rescaling.
- LL-0078 to LL-0080: steps towards the 3D convergence of the Regge action (task T-RC6, open):
  admissibility and dihedral angles of the Kuhn triangulation for every positive definite Gram
  matrix; explicit Christoffel symbols, Riemann tensor and scalar curvature at a point; and the
  jet-level star identity at a point where the first derivatives of the metric vanish.
- LL-0085: one link of the principal-series Lorentzian vertex is the exponential of the coherent
  action times the density of Ω, the first step of identifying the coherent vertex of Barrett,
  Dowdall, Fairbairn, Hellmann and Pereira (2010) with the principal-series vertex (task T-SF10,
  open; the identity of the two vertices is not proved).

### Open work

- Turaev–Viro: the q-Dougall summation itself (LL-0074, LL-0075), and qBiedenharnElliott for
  r ≥ 4, which with LL-0075 would give the invariance of LL-0031 at level r.
- Spin foams: forcing under the inverse moves 4-2 and 5-1; removing the cutoff and the independence
  of the gauge set (LL-0049 to LL-0051, LL-0068). A gauge set that does not force every triangle
  gives cutoff sums that change sign and grow (a numerical observation).
- Lorentzian asymptotics: the identity of the coherent and principal-series vertices (T-SF10).
- Regge calculus: the jet-level star identity at a general point (LL-0080), then the 3D
  convergence of the action (T-RC6).

### Checks

- A leak check (local paths, e-mail addresses, tokens) is a hard rule in CI.
- A pull request may carry draft IDs (LL-XXXX, LL-XXXX-a, ...); the ID is assigned when it is
  merged.
- CI counts a use of a result declaration under a namespace suffix as a test use.
- The Python scripts run on 3.9 to 3.14; CI tests 3.12.
- Every commit on main gets its own CI run; before, close merges cancelled the runs in between.
- CONTRIBUTING gives one template for module docstrings: a title, a summary, then
  `## Main results` and `## References` when the file has them.

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
