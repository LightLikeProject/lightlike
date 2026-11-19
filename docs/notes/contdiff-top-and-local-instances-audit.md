# Audit: `⊤` versus `∞` in smoothness orders, and local instances that could change statements

18 November 2026, `spinfoam/contdiff-top`, main 473d1011. Method: `grep` over `Lightlike/` and `Tasks/` (statements and
definitions), then reading the Mathlib signature of every hit. Current Mathlib: for `n : WithTop ℕ∞` (`ℕ∞ω`) `⊤`
means analytic (`ω`), for `n : ℕ∞` it means `∞` (smooth).

## 4a. `⊤` in smoothness orders: no statement is affected

Searches: `ContDiff*`, `ContMDiff*`, `IsManifold`, `contDiff*`, `HasFTaylorSeries*` with `⊤` or `ω` on the same line; named
arguments `(n := ⊤)`, `(m := ⊤)`, `(r := ⊤)`; `(⊤ : ℕ∞)`, `WithTop ℕ∞`, `ℕ∞ω`. The `ω` hits are all variable names
(`T.ω₀`, `loopIndex ω`, in `Lightlike/PL/`), none a smoothness order. Every `⊤` hit is on an argument of type `ℕ∞`, where `⊤ = ∞`:

| Hit | Mathlib signature | Verdict |
| --- | --- | --- |
| `Lightlike/Asymptotics/Lorentzian/VertexLocal.lean:40` `exists_contDiff_zero_iff_one_iff_of_isClosed (n := ⊤)` | `{n : ℕ∞}` (`Mathlib/Geometry/Manifold/PartitionOfUnity.lean`, section variable) | `∞`, correct |
| `Lightlike/Oscillatory/Localisation.lean:161` `Real.smoothTransition.contDiff (n := ⊤)` | `{n : ℕ∞}` (`SmoothTransition.lean:206`) | `∞`, correct |
| `Lightlike/Oscillatory/StationaryPhaseTests.lean:556` `expNegInvGlue.contDiff (n := ⊤)`, stated as `ContDiff ℝ ∞ …` | `{n : ℕ∞}` (`SmoothTransition.lean:140`) | `∞`, correct |
| `Lightlike/Spacetime/CurvatureSymmetries.lean:63` `((⊤ : ℕ∞) : ℕ∞ω) + 1` | cast of `⊤ : ℕ∞` into `ℕ∞ω`: `∞`, not `ω` | `∞`, correct |
| `Lightlike/Spacetime/CurvatureSymmetries.lean:67` `ContMDiffAt.mlieBracket_vectorField (m := ⊤) (n := ⊤)` | `{m n : ℕ∞}` (`VectorField/LieBracket.lean:981`) | `∞`, correct |

No `ContDiff ℝ ⊤ …`, `IsManifold I ⊤ M`, `ContMDiff … ⊤` or `ω` order occurs in `Lightlike/` or `Tasks/`. Result: nothing to fix.
(Residual risk: a smoothness order passed through a variable of type `ℕ∞ω` that is instantiated with `⊤` in a later file;
a grep cannot see that, and no hit points to one.)

## 4c. The 25 files with `local instance` / `attribute [local instance]` (26th, `Lorentz/LimitFormula.lean:45`, only mentions it in a docstring)

* **Harmless, Prop-valued or decidability only**:
  `SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ)` and `… SU2` in `Spin4/CoherentIntertwiner.lean:257,260`,
  `SpinFoam/GroupIntegral.lean:143,146`, `Asymptotics/EPRL/{EprlHighProj:35,38; Localise:21,24; HaarSphere:139,141; HaarChart:28,30; EprlHighEdge:59,62; Localise4:45,48; Pieces:20,23; GaugeFix:42,45}.lean`;
  `ContinuousStar` for the operator-norm topology in `SpinFoam/TwistedCohomologySU2.lean:88`;
  `Decidable (∀ e, P e)` through an explicit list in `SpinFoam/MoveBlocks.lean:46,53` and `SpinFoam/Move33.lean:291,298`
  (`Decidable` is a subsingleton, no statement changes).
* **Matrix norms (`Matrix.linftyOp*`)**, which are needed only to state `NormedSpace.exp`, `HasDerivAt`, `ContDiff`, `fderiv`
  on matrices: `Spin4/ClebschGordan.lean:59`, `SpinFoam/TwistedCohomologySU2.lean:29`, `Canonical/MatrixDeriv.lean:20,94`,
  `Asymptotics/EPRL/{Gluing:147; HessianChart:23; MaxSetFinite:23; ChartPieces:67}.lean`,
  `SU2/{Su2Exp:32; Differential:28; Brackets:28; Completeness:37}.lean`. The topology of these norms is the product topology
  (stated in `SU2/Su2Exp.lean:20`), so `HasDerivAt`, `fderiv`, `ContDiff` and `NormedSpace.exp` mean the usual thing; none
  of the statements contains the norm of a matrix (the `‖·‖` in `MaxSetFinite.lean:189,233` is the modulus of a complex
  number). Verdict: harmless. Open point for a second reader: the defeq of the two topologies is taken from Mathlib's
  construction (`PiLp 1`); it is not re-proved here.
* **Statement-defining, intended**: `attribute [local instance 100] LieRing.ofAssociativeRing` in
  `SU2/LieBridge.lean:127` and `SU2/Completeness.lean:120,283` makes `⁅A, B⁆` on matrices the commutator `AB − BA`;
  `noncomputable local instance : MeasurableSpace ℍ[ℝ] := borel ℍ[ℝ]` with `BorelSpace ℍ[ℝ]` in
  `Asymptotics/EPRL/HaarSphere.lean:21,22` and `HaarGraph.lean:167,168`: statements about measures on `ℍ[ℝ]` use the Borel
  σ-algebra (canonical; the same instance is declared in both files, so the two files agree).
* **Scoped, not local instances, but meaning-bearing**: `open scoped ComplexOrder` in `SpinFoam/Tetrahedron.lean:14`,
  `OperatorAlgebras/FockKernel.lean:19`, `OperatorAlgebras/FockExists.lean:11` (`≤` on `ℂ` is the order `re ≤ re ∧ im = im`);
  `open scoped Classical` in `PL/{SliceSubdiv,CellGeom,RadialGauge,DerivedGeom}.lean`, `GFT/DualSurface.lean:17`, and `in`-scoped in
  `SpinFoam/EPRL.lean:107`, `SU2/Differential.lean:43` (classical `Decidable`, a subsingleton: harmless).

Result: no statement changes meaning by a local instance; the only statement-defining instances (`LieRing.ofAssociativeRing`,
Borel σ-algebra on `ℍ[ℝ]`, `ComplexOrder`) are intended and visible at the statement. Nothing to fix.
