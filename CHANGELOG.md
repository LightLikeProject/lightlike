# Changelog

Notable changes to Lightlike. Results are identified by stable IDs (`LL-NNNN`), listed with their
sources and review status in [docs/RESULTS.md](docs/RESULTS.md). Versions follow
[Semantic Versioning](https://semver.org/); before 1.0.0, minor versions may change the API.

## [Unreleased]

### Library

- No planning IDs in Lean names. The folders under `Lightlike/Rows/` and eleven other ID-named
  folders move to subject folders. The namespaces `Lightlike.Rows.*`, `Lightlike.SP3Row`,
  `Lightlike.Lorentz.HARow055` and `Lightlike.OperatorAlgebras.OPRow154` take the names of their
  new folders (for example `Lightlike.Rows.G1_066` becomes `Lightlike.GR.KerrFirstLaw`), and four
  declarations get descriptive names: `op2_fock_and_shale` becomes `fockRepOf_implements_iff`,
  `op2_one_mode_alpha_beta` becomes `squeeze_norm_alpha_sq_sub_norm_beta_sq_one`,
  `op2_infinite_modes_not_implementable` becomes `squeezeEllTwo_not_implementable` and
  `op2_one_mode_implementable` becomes `squeeze_implementable`.
- Every renamed declaration keeps its old name as a deprecated alias for one release: deprecated
  since 0.4.0, removed in 0.5.0. Code that uses an old name still builds, with a warning that names
  the new one. Imports of moved files must use the new paths.
- A CI step keeps planning IDs out of Lean folder, file and declaration names.

## [0.3.0]

### Library

- 103 new results, LL-0067 to LL-0169: PL topology (23), Lorentzian asymptotics (18), Regge
  calculus (12), spacetime geometry and causal structure (11), spin foams (9), Turaev–Viro (8),
  operator algebras (7), group field theory (4), surfaces (4), canonical gravity (4), oscillatory
  integrals (1), cosmology (1) and Lorentz group representations (1). 102 are proven and 1 is
  conditional (LL-0135).
- Six areas have their first catalog entries: canonical gravity, cosmology, group field theory,
  operator algebras, oscillatory integrals and surfaces.
- The catalog has 169 entries: 167 proven results and 2 conditional results (LL-0031, LL-0135).
- LL-0074 and LL-0075 (norm one and q-orthogonality of the q-6j matrix at every level r ≥ 2) are
  proven without hypotheses: the boundary evaluation they need (the q-Dougall summation) is proved
  at every level r ≥ 2 (LL-0103, LL-0104).
- LL-0076's `since` said 0.2.0, but it was merged after that release, and LL-0070 to LL-0075 said
  0.2.1, a version that was not released; all of them now say 0.3.0.
- The new entries are `kernel-checked`; 67 are `established` and 36 are `frontier`. Unlike 0.2.0,
  no reviewer agent compared them with their cited sources before this release.
- Fix: the one-triangle action of the Lorentzian vertex (`lorAction`, Asymptotics) matched the
  EPRL integrand only for even doubled spins and differed by a sign for odd ones. It is now
  written in the power form and is exact for every doubled spin.
- The Racah certificate files have per-declaration heartbeat limits instead of file-level ones.
- Turaev–Viro: Jackson's summation of the terminating very-well-poised 6φ5 series, proved by a
  telescoping certificate. It has no catalog entry of its own, because no edition, page and
  equation of the formula in a book has been verified; it is the step that proves the boundary
  evaluation (LL-0103).
- Results without a catalog entry: in Lorentzian asymptotics, the pieces of the vertex
  asymptotics and the K5 edge pairing, the coherent 15j integral as the K5 contraction of coherent
  intertwiners, and the gauge-fixed Lorentzian vertex amplitude with a bound on its integrand and
  the integrability of the Ω density; in spin foams, the cut-off tetrahedron sum is monotone in the
  cutoff, and the cutoff can be removed exactly when the sums are bounded; in Turaev–Viro, the
  q-Racah sum at the lowest sixth colour has one term; in Regge calculus, the normal-coordinate
  slice of the jet-level star identity.

### Notable results

- LL-0125: the Jordan curve theorem (McCleary 2006, the chapter "The Jordan Curve Theorem").
  LL-0106 to LL-0115 are lemmas from the same chapter: gratings and chains, Alexander's theorem,
  the index of a loop and the Theta Lemma. LL-0100: the weak Jordan theorem, that the complement
  of a circle embedded in the plane is not connected; LL-0091 and LL-0099: K₃,₃ has no polygonal
  and no continuous drawing in the plane (Klazar 2026, Section 2).
- LL-0076: the Jordan curve theorem for simple closed polygons in the plane. The complement is
  the disjoint union of a bounded and an unbounded connected open set, and the polygon is the
  frontier of each (Moise 1977, the chapter "Separation properties of polygons in R²").
- LL-0082 to LL-0084: the polygonal Schoenflies theorem. A simple closed polygon in the plane has a
  triangulation by its own vertices, and the closed region it bounds is a PL ball whose boundary is
  the polygon (Moise 1977, the chapter "The Schönflies theorem for polygons in R²").
- LL-0143 and LL-0144: closed combinatorial surfaces are PL homeomorphic exactly when they have the
  same orientability and Euler characteristic, and each is related by 2D bistellar moves to exactly
  one standard model (Lickorish 1999, Theorem 5.9; Moise 1977). LL-0145: a stellar subdivision is a
  PL homeomorphism, and the Euler characteristic is an invariant of stellar equivalence (Lickorish
  1999, Theorem 4.5).
- LL-0126: stationary phase with a complex phase, the leading term (Hörmander 1990, Theorem 7.7.5).
- LL-0127: the 3D Regge action of the Kuhn triangulation of a grid converges to half the
  Einstein–Hilbert action of a Riemannian metric, the Kuhn-grid case of the convergence theorem
  of Cheeger, Müller and Schrader as described in Christiansen 2011, Section 1. LL-0093: the
  jet-level star identity holds at every point of a Riemannian metric, with no condition on the
  first derivatives. LL-0128 to LL-0132: the Regge action of a flat closed 3-complex is a quadratic
  form in the first variations of the lengths up to third order; on the 3-torus, the Regge action
  of the periodic Kuhn complex tends to half the Einstein–Hilbert action, its linearized sum
  converges to the Saint-Venant form, and the Saint-Venant and Fierz–Pauli forms have the same
  integral
  (Christiansen 2011, Section 1, eq. (5) and Proposition 3.2; Hinterbichler 2012, eq. (2.1)).
- LL-0070 to LL-0075: for the real q-Racah sum at q = e^{iπ/r}, the three-term recurrence in the
  third colour (Koekoek and Swarttouw 1996, eqs. (3.2.1)–(3.2.2)); the row identity of the
  quantum 6j symbol, endpoints included; detailed balance and weighted orthogonality of the rows
  for different sixth colours; one common weighted norm for all rows and columns; and norm one and
  q-orthogonality at every level r ≥ 2 (with LL-0104).
- LL-0134: the Plancherel formula of SL(2,ℂ) for smooth compactly supported functions (Knapp 1986,
  Chapter II).
- LL-0087: at the lowest level and for product coherent boundary arrays, the coherent
  principal-series Lorentzian vertex equals the coherent vertex of Barrett, Dowdall, Fairbairn,
  Hellmann and Pereira (2010, Section 4, eq. (17)) up to an explicit Haar normalisation factor.
  LL-0094 to LL-0098 and LL-0105: the critical points of the Lorentzian vertex action and its
  second derivatives there (BDFHP 2010, eqs. (18)–(21), (25) and (61)). LL-0135 (conditional): the
  scaled vertex is an integral over R^44 in fixed charts of SL(2,C), with a stationary-phase
  expansion under four named hypotheses (joint integrability, the critical set, an invertible
  Hessian and a bound on the far remainder; BDFHP 2010, eq. (53)).
- LL-0117 to LL-0122: the Euclidean EPRL vertex with coherent boundary data, for γ < 1 and for
  γ > 1 as a constant times a Spin(4)^5 integral of edge forms; the coherent 15j integral decays
  faster than every power of the spin scale when its maxima are noncritical, and exponentially for
  SU(2) boundary data without a gluing solution (Barrett, Dowdall, Fairbairn, Gomes and Hellmann
  2009, eqs. (14), (16), (17), (19) and (22)).
- LL-0146, LL-0147, LL-0152 and LL-0153: the hypersurface deformation algebra of the smeared
  momentum and Hamiltonian constraints (Thiemann 2007, the chapter "Classical Hamiltonian
  formulation of General Relativity"; Arnowitt, Deser and Misner 1962, Section 4).
- LL-0133: Einstein's equations for an FLRW spacetime with a perfect fluid are equivalent to
  Friedmann's two equations (Carroll 1997, eq. (8.36)). LL-0150: exterior Schwarzschild is a
  vacuum solution on the manifold layer (Carroll 1997, eq. (7.29)).
- LL-0151 and LL-0154 to LL-0162: causal structure (Hawking and Ellis 1973, the chapter "Causal
  structure"): a spacetime with a time function is strongly causal, a strongly causal one is
  causal and a causal one is chronological; a globally hyperbolic spacetime without boundary is
  causally simple; a Cauchy surface is achronal; Minkowski space is globally hyperbolic, with every
  slice of constant time a Cauchy surface; and, in one chart, a limit of future causal curves with
  converging endpoints is a future causal curve.
- LL-0163 to LL-0167: the generator of a strongly continuous one-parameter unitary group is
  self-adjoint and determines the group, and the momentum operator on smooth functions supported
  inside the unit interval has deficiency indices (1, 1) (Hall 2013). LL-0168 and LL-0169: every complex inner product space
  has a Fock representation of the Weyl relations, and any two are unitarily equivalent (Bratteli
  and Robinson 1997, the chapter "Continuous Quantum Systems. I").
- LL-0123, LL-0124, LL-0148 and LL-0149: colored graphs of group field theory, their bubbles, and
  the dual of a connected colored graph as a normal pseudo-manifold (Gurau 2010, Theorems 1 and 2).
- LL-0068: the gauge-fixed Ooguri state sum at finite cutoff is constant along every chain of
  3-3, 2-4 and 1-5 Pachner moves and their inverses (with the hypotheses of LL-0049 to LL-0051).
  LL-0069, LL-0077 and LL-0081 say when a gauge set that forces every triangle still does after a
  1-5, 3-3 or 2-4 move, and LL-0089 and LL-0136 to LL-0138 do the same for robust forcing sets;
  robustness is not kept by the 3-3 move (LL-0138). Forcing is this library's rule, used to show
  that the gauge-fixed sum is 1.
- LL-0067: the cut-off sum of the tetrahedron over doubled edge spins up to N is at least
  (N + 1)², so it has no limit without rescaling.

### Open work

- Turaev–Viro: qBiedenharnElliott for r ≥ 4, which with LL-0075 would give the invariance of
  LL-0031 at level r.
- Spin foams: forcing under the inverse moves 4-2 and 5-1; removing the cutoff and the independence
  of the gauge set (LL-0049 to LL-0051, LL-0068). A gauge set that does not force every triangle
  gives cutoff sums that change sign and grow (a numerical observation).
- Lorentzian asymptotics: the identity of the coherent and principal-series vertices beyond the
  lowest level (T-SF10), and proofs of the four hypotheses of LL-0135.
- Regge calculus: the convergence of the 3D Regge action beyond the Kuhn grid of LL-0127 (T-RC6).

### Checks

- A leak check (local paths, e-mail addresses, tokens) is a hard rule in CI.
- Building the task library is a hard rule in CI.
- The Python checks run 4 at a time; on a pull request, only the checks its change touches run.
- A pull request may carry draft IDs (LL-XXXX, LL-XXXX-a, ...); the ID is assigned when it is
  merged.
- CI counts a use of a result declaration under a namespace suffix as a test use.
- The Python scripts run on 3.9 to 3.14; CI tests 3.12.
- Every commit on main gets its own CI run; before, close merges cancelled the runs in between.
- The proof-task workflow checks only proof-task pull requests, and installs the pinned PyYAML. A
  proof task whose own `sorry` is filled counts as done.
- The build job has swap space and reports its memory use; a cold manual run skips the build-cache
  restores.
- Fixes from a test with a fresh agent: duplicate tasks, the fast gate, the setup and the commit
  format.

### Documentation

- AGENTS.md: one pull-request route for everyone; a statement that differs from its source needs a
  maintainer's approval; the libraries to check before building a new component. CONTRIBUTING has
  a paste-in prompt for contributors' agents and one template for module docstrings (a title, a
  summary, then `## Main results` and `## References` when the file has them); the maintainer
  section moved to docs/MAINTAINERS.md.
- The documentation site has a plain landing page at its root; the API documentation is under
  `docs/`.
- The README says how the spin-foam and Regge parts relate to the physics literature; the ROADMAP
  links each area's done milestones; the EPRL and Lorentzian API maps have titles in words.
- New sources with exact locations: Koekoek and Swarttouw for the quantum 6j task, equation-level
  sources for the EPRL asymptotics tasks T-SF9 and T-SF10, Klazar's weak Jordan paper, the
  Lorentzian EPRL numerics, and the sources of the new areas above.

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
