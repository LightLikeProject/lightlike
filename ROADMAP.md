# Roadmap

A map of the fields Lightlike covers: for each area, its scope, its key open questions and the
state of its milestones. The milestone tables, with sizes and the definition of done, are in
[docs/tasks/milestones.md](docs/tasks/milestones.md). Every open milestone is a task on the
[task board](docs/tasks/README.md), open to everyone. What is proven is listed in
[docs/RESULTS.md](docs/RESULTS.md).

## Aim

Lightlike formalizes the mathematics of fundamental physics in Lean 4: general relativity, black
holes and cosmology, the mathematical and quantum-field-theory foundations they use, and the
approaches to quantum gravity, with no preference among them. For each area it formalizes what is
rigorously defined: the definitions, the exactly solvable models, the perturbative structure and
the proven theorems. Where an area has no rigorous definition yet, the plan covers its rigorous
parts and says which parts have none. A formal proof shows that
a model has a property, not that the model describes nature.

## How to read this

The areas are in three groups: gravity and cosmology; mathematical and QFT foundations, the shared
infrastructure that several areas use; and the approaches to quantum gravity. Within the last two
groups the order is alphabetical; it is not a ranking. Each area lists:

- **Scope:** what the area covers, and for foundations which areas use it;
- **Open:** the main open questions of the field, or for foundations the main theorems the plan
  still needs;
- **Milestones:** how many there are, with links to the area's milestone table and its tasks on
  the board; which are done is on their issues.

## Gravity and cosmology

### Lorentzian and Riemannian geometry

- **Scope:** spacetime geometry on Mathlib's manifolds: curvature, causal structure, geodesics,
  spin structures, the Schwarzschild and Kerr solutions, conformal infinity, heat kernels. Used by
  most other areas.
- **Open:** in the field, weak and strong cosmic censorship. In the plan: intrinsic curvature on
  smooth manifolds (GE1), global causal structure (GE2) and Penrose's singularity theorem (GE4).
- **Milestones:** 10 · [milestones](docs/tasks/milestones.md#lorentzian-and-riemannian-geometry) · [tasks](docs/tasks/README.md#lorentzian-and-riemannian-geometry)

### Cosmology

- **Scope:** FLRW spacetimes and their perturbations, the thermal history and freeze-out, slow-roll
  inflation and the primordial spectra, the CMB, singularity theorems, Bianchi models, cosmic
  no-hair and nonlinear stability. Quantum cosmology is under canonical quantum gravity.
- **Open:** baryogenesis and the early phase transitions; the measure problem of eternal inflation;
  the back-reaction of inhomogeneities on the expansion.
- **Milestones:** 16 · [milestones](docs/tasks/milestones.md#cosmology) · [tasks](docs/tasks/README.md#cosmology)

### Semiclassical gravity

- **Scope:** quantum fields on curved spacetimes: the Unruh and Hawking effects, Bisognano–Wichmann,
  black-hole mechanics, Hadamard states, the renormalized stress tensor, the Page curve of random
  states.
- **Open:** back-reaction in general; islands and replica wormholes, which rest on the gravitational
  path integral; the conformal-factor problem of the Euclidean path integral.
- **Milestones:** 9 · [milestones](docs/tasks/milestones.md#semiclassical-gravity) · [tasks](docs/tasks/README.md#semiclassical-gravity)

## Mathematical and QFT foundations

Each foundation is cut to what the areas that use it need, so that no area builds its own copy.

### Conformal field theory

- **Scope:** the Witt and Virasoro algebras, free fields and central charges, vertex operator
  algebras, modular forms for partition functions, Cardy's formula. Used by string theory,
  holography and low-dimensional gravity.
- **Open:** in the plan, all of it; the first milestone decides whether to build on an existing
  Lean formalization of the Virasoro algebra.
- **Milestones:** 5 · [milestones](docs/tasks/milestones.md#conformal-field-theory) · [tasks](docs/tasks/README.md#conformal-field-theory)

### Gauge theory and constrained systems

- **Scope:** principal bundles and connections, connections on graphs and spin networks,
  Chern–Simons and BF functionals, constrained Hamiltonian systems, first-order gravity (Palatini,
  Holst, Ashtekar–Barbero). Used by canonical quantum gravity, low-dimensional and perturbative
  gravity, and spin foams.
- **Open:** in the field, the construction of 4D Yang–Mills theory. In the plan, all of it.
- **Milestones:** 5 · [milestones](docs/tasks/milestones.md#gauge-theory-and-constrained-systems) · [tasks](docs/tasks/README.md#gauge-theory-and-constrained-systems)

### Harmonic analysis on Lie groups

- **Scope:** SU(2), SL(2,ℂ) and SL(2,ℝ): Haar measures, unitary representations and Plancherel
  formulas. Used by spin foams, JT gravity and AdS₃ holography.
- **Open:** in the plan, the Plancherel measure of SL(2,ℂ) (HA2) and the representations of
  SL(2,ℝ) (HA3).
- **Milestones:** 4 · [milestones](docs/tasks/milestones.md#harmonic-analysis-on-lie-groups) · [tasks](docs/tasks/README.md#harmonic-analysis-on-lie-groups)

### Operator algebras and quantum information

- **Scope:** unbounded self-adjoint operators, CCR and CAR algebras, KMS states and modular theory,
  entropy inequalities, finite-dimensional quantum mechanics. Used by semiclassical gravity,
  canonical quantum gravity, holography, noncommutative geometry, causal sets and matrix models.
- **Open:** in the plan, Stone's theorem, Fock space, modular theory and strong subadditivity.
- **Milestones:** 5 · [milestones](docs/tasks/milestones.md#operator-algebras-and-quantum-information) · [tasks](docs/tasks/README.md#operator-algebras-and-quantum-information)

### Oscillatory and saddle-point asymptotics

- **Scope:** stationary phase on ℝⁿ with complex phases, and saddle-point asymptotics of
  alternating sums such as Racah's formula. Pure analysis and a candidate for Mathlib; used by
  spin-foam asymptotics and later by any semiclassical expansion.
- **Open:** in the plan, the asymptotics of balanced alternating Gamma-ratio sums (SP2), which
  real-variable methods cannot give.
- **Milestones:** 2 · [milestones](docs/tasks/milestones.md#oscillatory-and-saddle-point-asymptotics) · [tasks](docs/tasks/README.md#oscillatory-and-saddle-point-asymptotics)

### Perturbative QFT and the renormalization group

- **Scope:** Gaussian integrals and Feynman graphs, BPHZ and the Connes–Kreimer Hopf algebra,
  dimensional regularization, flows for finitely many couplings, BRST and BV in finite dimensions.
  Used by perturbative gravity, asymptotic safety, tensor and matrix models, and string theory.
- **Open:** in the field, a construction of interacting quantum field theories in four dimensions.
  The plan covers the perturbative and finite-dimensional parts.
- **Milestones:** 5 · [milestones](docs/tasks/milestones.md#perturbative-qft-and-the-renormalization-group) · [tasks](docs/tasks/README.md#perturbative-qft-and-the-renormalization-group)

### PL topology

- **Scope:** simplicial complexes, Pachner moves, PL maps and triangulations of 3-manifolds, in
  three layers: combinatorial, PL and topological. Used by spin foams, dynamical triangulations,
  tensor models, Regge calculus and low-dimensional gravity.
- **Open:** in the plan, the classification of surfaces up to bistellar moves (PL3), Newman's and
  Moise's theorems, and their assembly: homeomorphic closed 3-manifolds have triangulations related
  by Pachner moves.
- **Milestones:** 7 · [milestones](docs/tasks/milestones.md#pl-topology) · [tasks](docs/tasks/README.md#pl-topology)

### Quantum groups and state-sum TQFTs

- **Scope:** recoupling theory and the Biedenharn–Elliott identity, the Ponzano–Regge and
  Turaev–Viro state sums, `U_q(sl₂)` at roots of unity, the Crane–Yetter and Reshetikhin–Turaev
  invariants. Used by 3D and 4D state sums and low-dimensional gravity.
- **Open:** in the plan, the triangulation independence of the Ponzano–Regge amplitude (it needs
  the PL chain PL4–PL7 and the removal of the spin cutoff), and the quantum identities for `r ≥ 4`.
- **Milestones:** 5 · [milestones](docs/tasks/milestones.md#quantum-groups-and-state-sum-tqfts) · [tasks](docs/tasks/README.md#quantum-groups-and-state-sum-tqfts)

### Random geometry

- **Scope:** Poisson point processes, planar maps and their bijections, Galton–Watson trees and
  branched polymers, Wigner's semicircle law, the Gaussian free field and multiplicative chaos. Used
  by dynamical triangulations, causal sets, matrix and tensor models, and Liouville gravity.
- **Open:** in the plan, all of it; the Brownian map is a later target.
- **Milestones:** 5 · [milestones](docs/tasks/milestones.md#random-geometry) · [tasks](docs/tasks/README.md#random-geometry)

## Approaches to quantum gravity

### Asymptotic safety

- **Scope:** exact flow equations for finitely many variables, the Einstein–Hilbert truncation as
  an ODE, the 2 + ε expansion, asymptotic safety in rigorous toy models.
- **Open:** the gravitational renormalization-group flow beyond truncations, and the existence of
  its ultraviolet fixed point.
- **Milestones:** 4 · [milestones](docs/tasks/milestones.md#asymptotic-safety) · [tasks](docs/tasks/README.md#asymptotic-safety)

### Canonical quantum gravity

- **Scope:** the ADM formulation, the Ashtekar–Lewandowski Hilbert space and its uniqueness,
  discrete area and volume spectra, black-hole state counting, loop quantum cosmology and
  minisuperspace Wheeler–DeWitt models.
- **Open:** the physical Hilbert space of full loop quantum gravity (an anomaly-free constraint
  algebra and a physical inner product); the full Wheeler–DeWitt equation; semiclassical states.
- **Milestones:** 9 · [milestones](docs/tasks/milestones.md#canonical-quantum-gravity) · [tasks](docs/tasks/README.md#canonical-quantum-gravity)

### Causal sets

- **Scope:** locally finite posets, Poisson sprinklings, dimension estimators, the
  Lorentz-invariance theorem, classical sequential growth, the Sorkin–Johnston state.
- **Open:** the quantum dynamics (quantum sequential growth, the quantum measure); the
  Hauptvermutung, that a causal set approximates at most one spacetime.
- **Milestones:** 8 · [milestones](docs/tasks/milestones.md#causal-sets) · [tasks](docs/tasks/README.md#causal-sets)

### Dynamical triangulations

- **Scope:** Euclidean and causal dynamical triangulations: the 2D models as random planar maps and
  their exact solutions, the Brownian map, finite triangulations in 3D and 4D.
- **Open:** the continuum limit in 3D and 4D; the 4D phase diagram is known numerically only.
- **Milestones:** 5 · [milestones](docs/tasks/milestones.md#dynamical-triangulations) · [tasks](docs/tasks/README.md#dynamical-triangulations)

### Group field theory and tensor models

- **Scope:** Feynman expansions as formal series, the 1/N expansion and melonic dominance,
  renormalizability of tensorial group field theories, constructive results.
- **Open:** a 4D gravitational group field theory beyond perturbation theory; the condensate phase
  used in group field theory cosmology.
- **Milestones:** 7 · [milestones](docs/tasks/milestones.md#group-field-theory-and-tensor-models) · [tasks](docs/tasks/README.md#group-field-theory-and-tensor-models)

### Holography

- **Scope:** AdS geometry and its boundary, asymptotic symmetries, BTZ black holes and Cardy's
  formula, Ryu–Takayanagi in AdS₃, entropy inequalities of minimal cuts, holographic codes,
  holographic renormalization.
- **Open:** the AdS/CFT correspondence itself, a conjecture tested in many limits; bulk
  reconstruction beyond code models.
- **Milestones:** 8 · [milestones](docs/tasks/milestones.md#holography) · [tasks](docs/tasks/README.md#holography)

### Low-dimensional gravity

- **Scope:** 2+1 gravity as a Chern–Simons theory, the Witten–Reshetikhin–Turaev and Turaev–Viro
  invariants, JT gravity and the Schwarzian, Weil–Petersson volumes and topological recursion,
  Liouville theory.
- **Open:** the 3D gravity path integral with a sum over topologies; the completion of JT gravity
  by a matrix model, which is a proposal.
- **Milestones:** 7 · [milestones](docs/tasks/milestones.md#low-dimensional-gravity) · [tasks](docs/tasks/README.md#low-dimensional-gravity)

### Matrix models

- **Scope:** Gaussian matrix integrals and the genus expansion, the planar limit and map
  enumeration, the double-scaling limit and Painlevé I, the BFSS and IKKT models.
- **Open:** BFSS and IKKT as definitions of M-theory and type IIB string theory, which are
  conjectures; BFSS threshold bound states for all N.
- **Milestones:** 5 · [milestones](docs/tasks/milestones.md#matrix-models) · [tasks](docs/tasks/README.md#matrix-models)

### Noncommutative geometry

- **Scope:** spectral triples and the finite ones' classification, Connes' distance, the finite
  geometry of the Standard Model, fuzzy spaces, the spectral action, the reconstruction theorem.
- **Open:** Lorentzian spectral triples (several proposals, none accepted); a quantum theory of the
  spectral action.
- **Milestones:** 6 · [milestones](docs/tasks/milestones.md#noncommutative-geometry) · [tasks](docs/tasks/README.md#noncommutative-geometry)

### Perturbative quantum gravity

- **Scope:** gravity quantized around a background and as an effective field theory: linearized
  gravity, massive spin 2, massless representations, one- and two-loop divergences, the tree-level
  double copy.
- **Open:** a non-perturbative completion; the ultraviolet finiteness of N = 8 supergravity rests
  on explicit computations, not on a theorem.
- **Milestones:** 7 · [milestones](docs/tasks/milestones.md#perturbative-quantum-gravity) · [tasks](docs/tasks/README.md#perturbative-quantum-gravity)

### Regge calculus

- **Scope:** the Regge action and equations in 3D and 4D, the convergence of curvature measures
  (Cheeger–Müller–Schrader), Lorentzian and area Regge calculus, linearized convergence.
- **Open:** convergence of solutions of the full Regge equations to Einstein solutions; a quantum
  Regge measure.
- **Milestones:** 6 · [milestones](docs/tasks/milestones.md#regge-calculus) · [tasks](docs/tasks/README.md#regge-calculus)

### Spin foams

- **Scope:** amplitudes on labelled 2-complexes: the 3D state sums, the Ooguri (BF) model, the EPRL
  vertex and state sum on a fixed 2-complex, finiteness of the Lorentzian vertex, vertex
  asymptotics.
- **Open:** the refinement and continuum limit of the 4D models; the sum over 2-complexes; whether
  the semiclassical regime reproduces curved geometries (the flatness question).
- **Milestones:** 16 · [milestones](docs/tasks/milestones.md#spin-foams) · [tasks](docs/tasks/README.md#spin-foams)

### String theory

- **Scope:** classical strings, the critical dimension and the no-ghost theorem, tree amplitudes,
  the superstring spectrum, toroidal compactifications and T-duality, Calabi–Yau data, the proven
  parts of mirror symmetry.
- **Open:** non-perturbative string theory and M-theory; superstring perturbation theory at all
  genera; the landscape of vacua.
- **Milestones:** 11 · [milestones](docs/tasks/milestones.md#string-theory) · [tasks](docs/tasks/README.md#string-theory)

### Twistor theory

- **Scope:** twistor geometry, the Penrose transform, the Ward correspondence and the nonlinear
  graviton, spinor-helicity methods and recursion for amplitudes, the amplituhedron.
- **Open:** a twistor formulation of quantum gravity; the nonlinear graviton gives only self-dual
  geometries.
- **Milestones:** 6 · [milestones](docs/tasks/milestones.md#twistor-theory) · [tasks](docs/tasks/README.md#twistor-theory)

### Other approaches

- **Scope:** Hořava–Lifshitz gravity (power counting; renormalizability of the projectable
  version), induced and analogue gravity, causal fermion systems. Covered in other areas: shape
  dynamics (canonical), supergravity (perturbative gravity, strings), higher-spin gravity
  (holography), Euclidean quantum gravity (semiclassical).
- **Open:** the consistency of non-projectable Hořava–Lifshitz gravity; the thermodynamic and
  entropic derivations of Einstein's equations are heuristic.
- **Milestones:** 4 · [milestones](docs/tasks/milestones.md#other-approaches) · [tasks](docs/tasks/README.md#other-approaches)

## What's next

Every open milestone is a task anyone can take; those whose prerequisites are done are marked
**ready** on the [task board](docs/tasks/README.md). New areas, new milestones and changes of
scope are proposed in an issue and enter the tables as **proposed** until the maintainers approve
them. See [CONTRIBUTING.md](CONTRIBUTING.md).
