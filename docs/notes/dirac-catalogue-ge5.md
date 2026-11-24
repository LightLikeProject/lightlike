# GE5 (G1-017): catalogue entries for the Dirac files, and what is not entered

Question: which results of `Lightlike/Dirac/` (all on main) can be catalogued with a source location that was read?

Entered (docs/results.d/dirac-ge5.yaml, drafts LL-XXXX-a to LL-XXXX-e), sources verified by `scripts/sources.py verify`
(friedrich-kirchberg-2001, boldt-2015, martinetti-2016):
- a: Lichnerowicz formula in a torsion-free skew frame (local, V-valued functions on R^n); source: Friedrich-Kirchberg
  arXiv:math/0104121, formula (11); REPRESENTATION difference.
- b: Friedrich bound lambda^2 >= n^2/4 for compactly supported eigenspinors in the stereographic chart; source:
  Friedrich-Kirchberg Section 0; WEAKER (chart, compact support, no global statement).
- c: eigenspinor equation D f = epsilon (k+1) f on S^2 in the chart; source: Boldt arXiv:1504.03121 Theorem 3.1 p. 6; WEAKER
  (no multiplicity, no completeness, nonvanishing only for k = 0, 1).
- d, e: Connes distance on flat R^n and on the circle; source: Martinetti arXiv:1604.00499 eq. (2.10) p. 6; REPRESENTATION.

Not entered (no readable location, or the Lean statement is not what a paper would state):
- The Dirac spectrum of the unit 2-sphere as the milestone states it (`±(k+1)` with multiplicity `2(k+1)`): Lean has the
  eigenspinor equation for each k, but not the multiplicity count nor that there are no other eigenvalues. This is the main
  open part of GE5's trust check.
- The formula with `R/2` shown to fail (milestone trust check): not in Lean.
- The Dirac operator and `D^2 = nabla*nabla + R/4` on a spin manifold, spin structures, the spinor bundle: not in Lean
  (only frame-level statements on R^n); the source named in the milestone, Berline-Getzler-Vergne (`bgv-1992`), is a book
  that could not be read here, so no location was claimed.
- Weitzenboeck/Bianchi/Killing spinor/self-adjointness files: supporting lemmas, no catalogue entry by the rule.

Surprise: the Friedrich bound and the spectrum entries are chart-level, so they are weaker than the milestone's trust
checks; GE5 stays open on the multiplicity count (a Sobolev/representation-theoretic argument or Killing-spinor
counting) and on global spin structures.
