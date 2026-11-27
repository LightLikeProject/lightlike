# Milestones

<!-- Read by scripts/tasks.py: edit the tables here, then run `python3 scripts/tasks.py generate`. -->

The milestone tables of every area, in the order of the [roadmap](../../ROADMAP.md). Each
milestone is a task on the [task board](README.md). These tables are the plan; whether a milestone
is ready, claimed or done is on its GitHub issue (the task ID starts the issue title), and a change
of scope is proposed in an issue first. Milestone IDs are a short area code and a number.
Where the done-when text is long, it is in a bullet below the table. Literature values in the trust
checks are the values to reproduce; each is checked against the cited source, including its
conventions, when the milestone starts.

## Sizes

Sizes measure scope, not time.

- **S**: a few definitions and lemmas, or a computation, on existing infrastructure.
- **M**: a self-contained theory on existing infrastructure.
- **L**: a major theorem, or one that first needs new infrastructure.
- **R**: research-level formalization. Either no proof exists at the detail a formalization needs,
  or the infrastructure is far from Mathlib. The milestone is a target; partial results with
  tracked gaps count as progress.

## Definition of done (every milestone)

A milestone is done, and its issue is closed, when all of the following hold on `main`. Items 1
and 2 are enforced by CI; items 3 to 5 are the project's standard for calling a milestone
finished, checked through the milestone's review items (the evidence is written into the
checklist), and do not block individual contributions.

1. **Proofs complete.** Its main theorems have zero `sorry`, and they use only Lean's standard
   axioms `propext`, `Classical.choice`, `Quot.sound` (checked for every declaration of the
   library by `scripts/AxiomAudit.lean`).
2. **Documented.** Every definition, and every declaration named in an API map or in
   `docs/results.yaml`, has a docstring (`scripts/DocCheck.lean`).
3. **Trust checks.** The new definitions reproduce known values or identities from the
   literature, and at least one deliberately wrong model or input is shown to give a different
   result. Statements are checked against Lean's junk values (`a / 0 = 0`, the inverse of a
   singular matrix is `0`, `fderiv` of a non-differentiable function is `0`), so that a theorem
   cannot hold for a degenerate reason.
4. **No weaker results.** Each theorem proves what the milestone describes, at full strength. A
   weaker version (an added hypothesis, a case left out, a smaller class) may be merged as
   progress, stated explicitly as weaker in the module docstring and in the results entry, but it
   never ticks a checklist item and never closes a milestone. Technical choices inside a proof are
   the contributor's, as long as no stated result ends up weaker than its source; a change that
   would weaken a stated result goes to the maintainers first. Nobody changes a milestone's
   done-when, size or checklist items, in either direction, without the maintainers' decision:
   propose the change with the reason.
5. **Recorded.** Its results are entered in `docs/results.yaml`, from which
   [RESULTS.md](../RESULTS.md) is generated, and in the API map of its folder.

## Gravity and cosmology

### Lorentzian and Riemannian geometry

Folder `Lightlike/Geometry/`. Intrinsic geometry on Mathlib's smooth
manifolds, linked to the coordinate geometry of GE9 (`Spacetime/`, `GR/`) and to the chart-level
geodesics of Regge calculus.

| ID | Milestone | Done when | Trust checks | Size | Needs |
|---|---|---|---|---|---|
| GE1 | Smooth curvature from connections: Levi-Civita connection, Riemann, Ricci and scalar curvature on a smooth manifold | the curvature is defined intrinsically and proven to agree in every chart with the coordinate curvature | round 2-sphere of radius `r` has scalar curvature `2/r²`; Schwarzschild is Ricci-flat; a connection with torsion shown to give a different Ricci tensor | L | Mathlib manifolds |
| GE2 | Causal structure: time orientation, causal curves, chronological and causal futures, global hyperbolicity, Cauchy surfaces | time orientation, future causal/timelike/inextendible curves, chronological and causal futures, global hyperbolicity and Cauchy surfaces are defined; chron ⊆ causal, causal and chronological futures are transitive, causal ⇒ chronological relation; Minkowski space is globally hyperbolic with `t = 0` a Cauchy surface | Minkowski's causal future is the closed light cone; anti-de Sitter is not globally hyperbolic; a spacetime with closed timelike curves (Minkowski with time rolled up) violates chronology | L | GE1 |
| GE3 | Geodesics, the exponential map and the Raychaudhuri equation on a manifold | the Raychaudhuri equation for timelike geodesic congruences, and focusing under the strong energy condition for rotation-free congruences | expansion of comoving congruences in Minkowski and in FLRW in closed form; a congruence in a spacetime violating the energy condition does not focus | M | GE1 |
| GE4 | Penrose's singularity theorem (1965) | a globally hyperbolic spacetime with a non-compact Cauchy surface, the null energy condition and a closed trapped surface is null-geodesically incomplete | the hypotheses hold in the Schwarzschild interior (trapped spheres at `r < 2M`); Minkowski has no closed trapped surface | R | GE2, GE3 |
| GE5 | Spin structures and the Dirac operator, on Mathlib's Clifford algebras; the Lichnerowicz formula | a spin structure on a Riemannian manifold is defined, the Dirac operator on its spinor bundle and the rough Laplacian `∇*∇` are defined, and `D² = ∇*∇ + R/4` holds; the Dirac operator on ℝⁿ is defined | Dirac spectrum on the unit 2-sphere `±(k+1)` with multiplicity `2(k+1)`; the formula with `R/2` shown to fail | L | GE1 |
| GE6 | Kerr in Boyer–Lindquist coordinates; Killing horizons, surface gravity and angular velocity | Kerr proven a vacuum solution; `κ` defined by `∇_χ χ = κχ` and `Ω_H` by the horizon Killing field `χ = ∂_t + Ω_H ∂_φ`, and shown equal to `√(M²−a²)/(2Mr₊)` and `a/(2Mr₊)` | `a = 0` gives Schwarzschild with `κ = 1/(4M)`; the coefficient of `g_tφ` halved shown not to be Ricci-flat (flipping its sign gives Kerr with `-a`, which is Ricci-flat) | M | GE10 |
| GE7 | Conformal compactification: null infinity of Minkowski space, the conformal boundary of anti-de Sitter space | future null infinity `ℐ⁺` of Minkowski space and the conformal boundary of AdS are defined as subsets of a conformal compactification; the Poincaré group acts on `ℐ⁺` by conformal maps, and the AdS isometry group acts on the AdS boundary by conformal maps | the compactified Minkowski space as a region of the Einstein static universe; a non-conformal rescaling shown to fail | M | GE2 |
| GE8 | Heat-kernel expansion of Laplace-type operators on compact Riemannian manifolds (Seeley–DeWitt coefficients `a₀`, `a₁`, `a₂`) | for the scalar Laplacian on a compact Riemannian n-manifold, `Tr e^{−tΔ} ~ Σ a_k t^{k−n/2}` as `t → 0`, with `a₀ = (4π)^{−n/2} vol` and `a₁ = (4π)^{−n/2}∫R/6` | unit 2-sphere: `Σ(2l+1)e^{−t l(l+1)} = 1/t + 1/3 + t/15 + O(t²)`; the flat torus has no `t⁰` term | L | GE1 |
| GE9 | Spacetime geometry: Lorentzian metrics, Minkowski space, coordinate curvature, Riemann symmetries, chart changes | Lorentzian metrics and Minkowski space are defined; the coordinate Christoffel symbols and the Riemann, Ricci and scalar curvature are defined, with the Riemann symmetries (pair symmetry, first Bianchi identity) proven, and they transform as tensors under chart changes | - | - | - |
| GE10 | Vacuum Einstein equations; Minkowski and exterior Schwarzschild as solutions | the vacuum Einstein equations with `Λ` are defined; Minkowski space (`Λ = 0`) and exterior Schwarzschild (`M > 0`, `r > 2M`) satisfy them | - | - | - |
| GE11 | Generalize the curvature results of GE1 (the curvature tensor computed by any extensions, its symmetries, the Ricci tensor, the second Bianchi identity, the divergence of the Einstein tensor, the chart agreement) to any non-degenerate (pseudo-Riemannian) metric, any `ModelWithCorners` and without a Hausdorff hypothesis | the statements of the former tasks T-GE1-P2 to P8 hold in that generality (the library proves them for Lorentzian metrics on Hausdorff manifolds modelled on `Fin n → ℝ` or a finite-dimensional space without boundary) | the round 2-sphere (Riemannian) has the same identities; a manifold with boundary; a non-Hausdorff example | L | GE1 |
| GE12 | Lie derivatives of tensor fields, Killing vector fields and isometries; maximally symmetric spaces (de Sitter, anti-de Sitter, hyperbolic space) | the Lie derivative of tensor fields on a smooth manifold is defined, `£_V g = 0` is proven equivalent to Killing's equation `∇_(μ V_ν) = 0`, and the Killing fields form a Lie algebra; de Sitter, anti-de Sitter and `Hⁿ` are defined and proven maximally symmetric, with constant sectional curvature | the `n(n+1)/2` Killing fields of Minkowski space close into the Poincaré algebra; the rotation field of the round 2-sphere is Killing and a dilation is not | M | GE1 |
| GE13 | Hypersurfaces: induced metric, unit normal, second fundamental form (extrinsic curvature), the Gauss and Codazzi relations | for a non-null hypersurface of a pseudo-Riemannian manifold the extrinsic curvature is defined and proven symmetric, and the Gauss and Codazzi relations are proven; the two relations are lockable statements | the sphere of radius `r` in ℝ³ has `K = h/r` and scalar curvature `2/r²` from the Gauss relation; a constant-time slice of FLRW has `K = (ȧ/a) h` | M | GE1 |
| GE14 | Stress-energy tensors and energy conditions: perfect fluids, scalar and electromagnetic fields; the null, weak, strong and dominant energy conditions | the four energy conditions are defined for a symmetric (0,2)-tensor on a Lorentzian manifold, with dominant ⇒ weak ⇒ null and strong ⇒ null proven; for a perfect fluid each condition is proven equivalent to its inequalities in `ρ` and `p` | dust with `ρ ≥ 0` satisfies all four; a positive cosmological constant violates the strong condition; a Klein–Gordon field with a negative potential shown to violate the weak condition | M | GE1 |
| GE15 | The Einstein–Hilbert action and its first variation; Einstein's equations as Euler–Lagrange equations | for a compact domain `D` with smooth boundary and a variation `h` compactly supported in `D` or vanishing on `∂D`, `d/dε ∫_D √−g (R − 2Λ) = ∫_D √−g (G_{μν} + Λ g_{μν}) δg^{μν}` plus a boundary term on `∂D`, and the action is critical for all `h` vanishing on `∂D` iff `G + Λg = 0`; the variation formula is a lockable statement | the Palatini identity for `δR_{μν}`; in two dimensions the variation of `∫ √g R` vanishes (Gauss–Bonnet); a wrong sign of `Λ` shown to give the wrong de Sitter radius | L | GE1 |
| GE16 | Spinors on Lorentzian spacetimes: Spin(1,3) → SO⁺(1,3), spin structures on oriented, time-oriented Lorentzian 4-manifolds, the Dirac operator in signature (−+++) | a spin structure on an oriented, time-oriented Lorentzian manifold of dimension 4 is a lift of its SO⁺(1,3) frame bundle through the double cover Spin⁺(1,3) = SL(2,ℂ) → SO⁺(1,3) (the kernel {+1, −1} proved); the spinor bundle (Dirac spinors, the Weyl splitting) and the Dirac operator for `γ^μ γ^ν + γ^ν γ^μ = 2 η^{μν}` are defined; the Dirac current is conserved for solutions of the Dirac equation; the Lichnerowicz formula `D² = ∇*∇ + R/4` holds with `∇*∇ = −g^{μν} ∇_μ ∇_ν` (sign conventions stated); on Minkowski space the plane waves of the Dirac equation satisfy `E² = \|p\|² + m²` | the kernel of `Spin⁺(1,3) → SO⁺(1,3)` is `{+1, −1}` and the group is `SL(2,ℂ)`; the free Dirac equation has exactly the positive and negative energy plane waves with `E² = \|p\|² + m²` | L | GE1, GE2, GE5 |

### Cosmology

Folder `Lightlike/Cosmology/`: the FLRW universe and its perturbations, the thermal history, inflation, the cosmic microwave background, and the mathematical theory of cosmological spacetimes (singularities, Bianchi models, stability), scalar-field dark energy and modified gravity, and cosmic strings.

- **Needs:** GE1–GE4, SC6, DS1, ST1; Physlib's FLRW background.

| ID | Milestone | Done when | Trust checks | Size | Needs |
|---|---|---|---|---|---|
| CO1 | The FLRW spacetime on `I × Σ` with `Σ` of constant curvature `k`; perfect fluids; the Friedmann equations from the Einstein equations, for every `k` | the Einstein equations with a perfect fluid are equivalent to Friedmann's two equations and the continuity equation; linked to Physlib's Friedmann definitions | de Sitter has `ρ = Λ/8πG`; Einstein's static universe has `Λ = 1/a² = 4πGρ`; a flipped sign of `k` breaks the closed case | M | GE1 |
| CO2 | The big bang in FLRW | Physlib's Big-Bang bound (`Cosmology.FLRW.lt_of_mem_I_of_decelerating`, for `ρ, p ≥ 0` and `Λ = 0`) extended to the strong energy condition `ρ + 3p ≥ 0` with `Λ ≤ 0`; the Ricci scalar of the CO1 metric blows up as `a → 0` for dust and radiation; the integrand of Physlib's `particleHorizon` is integrable iff `∫ da/(a²H)` converges | the Milne universe (`a = t`, `k = −1`) reaches `a = 0` but is flat, so the blow-up step must fail there | S | CO1 |
| CO3 | Hawking's cosmological singularity theorem (Hawking 1967) | a globally hyperbolic spacetime with the timelike convergence condition and a Cauchy surface of mean curvature `K ≤ C < 0` has no past-directed timelike curve from it longer than `−3/C` | in FLRW the bound is `1/H₀`, as in CO2; de Sitter in the `k = +1` slicing violates the hypothesis and is complete | L | GE2, GE3, GE4, CO2 |
| CO4 | Linear perturbations of FLRW: scalar-vector-tensor decomposition, gauge transformations, Bardeen potentials (Bardeen 1980) | the Bardeen potentials are gauge invariant; the scalar sector reduces to one second-order equation; tensor modes obey `h'' + 2𝓗h' − ∇²h = 0` | `Φ` is constant in matter domination; a pure-gauge perturbation gives `Φ = Ψ = 0` | L | CO1 |
| CO5 | Newtonian growth of structure and the Jeans scale | the growth equation `δ'' + 2Hδ' − 4πGρδ = 0` from the linearized Euler–Poisson system in comoving coordinates; the growth integral `D ∝ H ∫ da/(aH)³` (Heath 1977); the Jeans wavenumber `k_J² = 4πGρ/c_s²` | Einstein–de Sitter has `D₊ ∝ a` and `D₋ ∝ t⁻¹`; under Λ domination `D` tends to a constant | M | Physlib |
| CO6 | Equilibrium thermodynamics of the hot universe | Bose and Fermi densities `ρ = (π²/30) g T⁴` with the factor `7/8` and `n = ζ(3) g T³/π²` with `3/4`; entropy conservation gives `T_ν/T_γ = (4/11)^{1/3}`; the Saha equation | `∫₀^∞ x³/(eˣ − 1) dx = π⁴/15`; `ρ_rad = (1 + (21/8)(4/11)^{4/3}) ρ_γ ≈ 1.681 ρ_γ` | M | Mathlib |
| CO7 | Freeze-out: the Boltzmann equation for a relic in FLRW | `dY/dx = −(λ/x²)(Y² − Y_eq²)` has a unique global solution with a finite limit `Y_∞`, with two-sided bounds on `Y_∞` | with `Y_eq ≡ 0`, `Y_∞ = Y₀/(1 + λY₀/x₀)` exactly; `x_f ≈ 20–25` for weak-scale cross-sections (numeric script) | M | Mathlib |
| CO8 | Isotropic singularities (Goode–Wainwright 1985; Anguige–Tod 1999) | the definition; FLRW with a linear equation of state has an isotropic singularity, and the Weyl tensor of the regular conformal metric is finite | Kasner has no isotropic singularity: its Weyl curvature blows up | M | CO1, CO13 |
| CO9 | Single-field inflation and the slow-roll approximation (Rendall 2005) | to be checked against Rendall's full text before work starts (only the abstract was read; the paper's title is "Intermediate inflation and the slow-roll approximation", and the attractor statement may need another source): solutions of `φ̈ + 3Hφ̇ + V′(φ) = 0` with `3H² = φ̇²/2 + V` approach the slow-roll solution; the number of e-folds is `N = ∫ V/V′ dφ` to leading order | for `V = m²φ²/2` (units `8πG = 1`): `ε = 1` at `φ = √2`, `n_s − 1 ≈ −2/N`, `r ≈ 8/N` | M | Physlib, CO29, DS1 |
| CO10 | Inflationary perturbations: the Mukhanov–Sasaki equation, Bunch–Davies modes, the exact solution for power-law inflation (Lucchin–Matarrese 1985) | Bunch–Davies mode functions in Hankel form with the Wronskian normalization; the scalar and tensor power spectra; `r = 16ε` | the massless de Sitter mode has `v_k v̄_k = (1/2k)(1 + 1/(kτ)²)`; power-law inflation has `n_s − 1 = −2/(p − 1)` | L | CO4, CO9 |
| CO11 | Quantum states on FLRW: adiabatic states (Lüders–Roberts 1990; Junker–Schrohe 2002); the Bunch–Davies state among the de Sitter-invariant vacua (Allen 1985) | adiabatic states of high enough order are Hadamard; of the de Sitter-invariant α-vacua only Bunch–Davies is Hadamard | the `α ≠ 0` vacua fail the Hadamard condition; a massless conformally coupled field gives the conformal vacuum | L | SC6, CO1 |
| CO12 | The cosmic microwave background in FLRW (Sachs–Wolfe 1967) | free streaming (the Liouville equation on FLRW) maps a Planck spectrum to a Planck spectrum with `T ∝ 1/a`; the Sachs–Wolfe effect `ΔT/T = Φ/3` in matter domination; the tight-coupling oscillator | a massive species does not keep an equilibrium shape; without the intrinsic-temperature term the `1/3` becomes `1` | M | CO1, CO4 |
| CO13 | Bianchi cosmologies: the classification of 3D real Lie algebras (Bianchi 1898; Ellis–MacCallum 1969); Kasner; the Wainwright–Hsu system | the classification into class A and B, types I–IX and the families VI_h and VII_h; Kasner solves vacuum Bianchi I iff `Σp = Σp² = 1`; the Kasner map | Kasner `(1, 0, 0)` is flat; the count of types matches the table of Ellis–MacCallum | L | GE1 |
| CO14 | The Bianchi IX attractor theorem (Ringström 2001; Heinzle–Uggla 2009) | the past attractor of generic vacuum Bianchi IX solutions lies in the union of the Bianchi I and II vacuum sets | the non-generic Taub (LRS) solutions are excluded | R | CO13 |
| CO15 | Cosmic no-hair for Bianchi models (Wald 1983; Rendall 2005 for a scalar field) | Bianchi models other than type IX with `Λ > 0` and matter under the dominant and strong energy conditions approach de Sitter exponentially | type IX with large positive curvature recollapses; with `Λ = 0` there is no isotropization | M | CO13, GE3 |
| CO16 | Nonlinear stability: de Sitter (Friedrich 1986), FLRW with Λ (Ringström 2008; Rodnianski–Speck 2013), stable big-bang formation (Rodnianski–Speck 2018; Fournodavlos–Rodnianski–Speck 2023) | the statements, reviewed and locked; the proofs are research-level | the statements specialize to the exact FLRW and Kasner solutions | R | CO1, CO13, GE2 |
| CO17 | Dark energy as a scalar field: quintessence with an exponential potential, as an autonomous system (Copeland–Sami–Tsujikawa 2006) | with `x = φ̇/(√6 H)`, `y = √V/(√3 H)` the Friedmann and field equations reduce to a planar system on the closed unit half-disc; its fixed points, their existence conditions and their stability (by DS1) are determined for `V = V₀e^{−λφ}`, with and without a matter fluid | the scalar-field-dominated point has `w_φ = −1 + λ²/3`; the kinetic point has `w_φ = 1`; at `λ² = 3` two points merge, and the stability of the scaling point flips | M | CO1, CO29, DS1 |
| CO18 | Scaling and tracker solutions (Copeland–Sami–Tsujikawa 2006) | the scaling solution of the exponential potential has `Ω_φ = 3(1 + w_m)/λ²` and `w_φ = w_m`, and is a stable node or spiral where it exists; for inverse power-law potentials the tracker condition `Γ = V″V/V′² > 1` gives an attractor with `w_φ` below `w_m` | `Ω_φ ≤ 1` forces `λ² ≥ 3(1 + w_m)`; for `Γ < 1` the tracking claim fails (numeric script) | M | CO17 |
| CO19 | Phantom, k-essence and tachyon fields (Copeland–Sami–Tsujikawa 2006) | the equation of state `w < −1` for a field with a negative kinetic term; for `L = p(X, φ)` the effective sound speed `c_s² = p,X/(p,X + 2X p,XX)`; the tachyon `V(φ)√(1 − φ̇²)` with its fixed points | the phantom `ρ` grows with `a`; a k-essence model with `c_s² > 1` is flagged as superluminal; the canonical field has `c_s = 1` | M | CO17, CO29 |
| CO20 | `f(R)` gravity and scalar-tensor theories (De Felice–Tsujikawa 2010; Sotiriou–Faraoni 2010) | the field equations of `f(R)` for `f′ > 0`; the equivalence with a Brans–Dicke theory with `ω = 0` and a potential (Legendre transform, for `f″ ≠ 0`); the FLRW equations of the theory; its stability condition `f″ > 0` | `f = R` gives general relativity; `f = R + αR²` has the Starobinsky de Sitter point; the equivalence fails at `f″ = 0` | L | CO1, GE1 |
| CO21 | Kaluza–Klein reduction on a circle (Overduin–Wesson 1997) | the 5D vacuum Einstein equations for a metric independent of the fifth coordinate are equivalent to 4D Einstein gravity with a Maxwell field and a dilaton; the mass spectrum `m_n = n/R` of a massless 5D scalar | the gauge coupling is fixed by the radius; with the dilaton frozen, the Maxwell stress tensor has the right sign; a non-constant dilaton changes the Einstein-frame metric | L | GE1 |
| CO22 | The cosmological constant problem: Weinberg's no-go theorem (Weinberg 1989; reviewed in Padilla 2015) | Under Lorentz invariance of the vacuum, a field-independent adjustment of the vacuum energy cannot make it vanish without tuning: the stated hypotheses and the conclusion, with the one-loop zero-point energy `ρ = ∑ ½ω` cut off at a scale `Λ_c` | the cut-off sum scales as `Λ_c⁴`; a scale-invariant example with a free parameter is shown to be tuned; the conclusion fails if one hypothesis is dropped | M | CO1, CO17 |
| CO23 | Swampland conjectures as explicit hypotheses (Obied–Ooguri–Spodyneiko–Vafa 2018; Ooguri–Vafa 2006; Palti 2019) | The distance conjecture, the de Sitter conjecture `\|∇V\|/V ≥ c` and its refinement are stated as hypotheses on a scalar potential; the consequences for CO17 and CO9 are proven as theorems from the hypotheses, never as claims about nature | the exponential potential satisfies the de Sitter conjecture with `c = λ`; a potential with a de Sitter critical point violates it; slow roll in CO9 contradicts it for `c` above `√2` | M | CO9, CO17 |
| CO24 | Abelian-Higgs vortices on `ℝ²`: winding number and the Bogomolny identity (Kibble 1976; Nielsen–Olesen 1973; Hindmarsh–Kibble 1995) | for a finite-energy configuration with `\|φ\| → v` at infinity, the winding number `n` of `φ` on a large circle is well defined (Mathlib's `AddCircle.windingNumber`), the flux is `∫B = 2πn/e` under stated decay hypotheses, and at critical coupling the energy is a sum of squares plus `\|n\|` times a constant, so `E ≥ 2π\|n\|v²` in the normalization of the cited equation (fixed when the statement is locked) | `n = 0` vacuum has `E = 0`; the `n = 1` Nielsen–Olesen ansatz has `E` above the bound away from critical coupling and equal to it at critical coupling; flipping the sign of `n` or of the first-order equations breaks the identity | M | Mathlib |
| CO25 | Existence of the radial vortex profile (Nielsen–Olesen ansatz) | the radial ODE system for `f(r), a(r)` with `f(0) = 0, a(0) = 0, f(∞) = 1, a(∞) = n` has a solution for `n ≥ 1` at critical coupling, with `0 < f < 1`; proof by an explicit ODE argument (shooting or sub/super-solutions), not by citation | `n = 0` gives `f ≡ 1`; the linearization at `r = 0` gives `f ∼ r^n`; a profile with `f > 1` violates the first-order equations | L | CO24 |
| CO26 | The conical metric of a straight string (Vilenkin 1981; Hiscock 1985; Garfinkle 1985) | the metric `−dt² + dz² + dr² + (1 − 4Gμ)² r² dθ²` is flat away from the axis (coordinate curvature) and its holonomy around the axis is a rotation by `8πGμ`; the identification of `μ` with the vortex energy per length is stated as a hypothesis | `μ = 0` is Minkowski; the deficit angle is `2π` at `4Gμ = 1`, where the metric degenerates and the statement is excluded; a metric without the factor `(1 − 4Gμ)` has no holonomy | M | GE1 |
| CO27 | Nambu–Goto strings in Minkowski space: general solution and cusps (Goto 1971; Kibble–Turok 1982) | in conformal gauge the general solution is `X = (a(σ₋) + b(σ₊))/2` with `\|a′\| = \|b′\| = 1`; a closed loop has a cusp where `a′ = b′` (a point on `S²` meeting the other curve), and the generic loop has one | the circular loop collapses to a point in time `R`; a loop with `a′` and `b′` curves that never meet has no cusp; a non-null `a′` violates the constraints | M | ST1 |
| CO28 | Existence of vortices of every winding number as an explicit hypothesis (Taubes 1980) | the statement that for every finite configuration of `N` points there is a solution of the first-order vortex equations with exactly those zeros is stated as a hypothesis `TaubesExistence`, and its consequences (energy `π N v²`-type count, the moduli-space dimension `2N`, in the normalization of CO24) are theorems from it | `N = 1` agrees with CO25; `N = 0` is the vacuum; the hypothesis is not assumed anywhere in CO24-CO27 | S | CO24 |
| CO29 | The scalar field in FLRW: the Einstein–Klein–Gordon equations for a homogeneous field | for a homogeneous scalar field `φ(t)` with potential `V` on the CO1 metric, the Einstein equations with the scalar stress tensor together with the Klein–Gordon equation are equivalent to the first Friedmann equation with `ρ = φ̇²/2 + V` plus the Klein–Gordon equation `φ̈ + 3Hφ̇ + V′(φ) = 0`, with the same two caveats as CO1's equivalence (the division by `G` and by `ȧ`); the field is a perfect fluid with `p = φ̇²/2 − V` | `φ̇ = 0` gives `w = −1`; a wrong-sign kinetic term gives `w < −1`; a constant potential gives de Sitter | S | CO1 |

### Semiclassical gravity

Folder `Lightlike/Semiclassical/`: quantum fields on curved
spacetimes, the Unruh and Hawking effects, black-hole thermodynamics and the information problem.
Not to be confused with the semiclassical limits of spin foam amplitudes (SF8–SF10).

- **Needs:** GE1–GE3, GE6, GE8, OP1–OP4.

| ID | Milestone | Done when | Trust checks | Size | Needs |
|---|---|---|---|---|---|
| SC1 | The Unruh effect in coordinates (Unruh 1976) | Bogoliubov coefficients between Minkowski and Rindler modes give a Planck spectrum at `T = a/2π` | the factor `1/(e^{2πω/a} − 1)`; an inertial detector sees no particles | M | OP2 |
| SC2 | Bisognano–Wichmann (1975), in the standard-subspace form of Brunetti–Guido–Longo (2002) | the modular group of the wedge is the boost group with parameter `2π` | KMS at `β = 2π` for the boost; a rotation flow fails KMS | L | OP2, OP3 |
| SC3 | Euclidean black holes (Gibbons–Hawking 1977) | Euclidean Schwarzschild is smooth at `r = 2M` iff the period is `8πM`; `T_H = 1/(8πM)` | another period gives a conical deficit `2π(1 − β/8πM)` | S | GE6 |
| SC4 | Hawking radiation from a collapse geometry (Fredenhagen–Haag 1990), or the Hartle–Hawking–Israel state and its uniqueness (Kay–Wald 1991) | the late-time state is thermal at `T = κ/2π` | `T = 1/(8πM)` for Schwarzschild; the Boulware state shown singular at the horizon | R | SC2, SC6 |
| SC5 | The laws of black-hole mechanics (Bardeen–Carter–Hawking 1973); the area theorem (Hawking 1971) | first law and Smarr `M = 2Ω_H J + κA/4π` for Kerr; the area theorem under the null energy condition | Kerr in closed form; a wrong area formula breaks Smarr | M (Kerr), L (area theorem) | GE3, GE6 |
| SC6 | Free quantum fields on globally hyperbolic spacetimes: Klein–Gordon well-posedness and Green operators (Bär–Ginoux–Pfäffle 2007); the CCR algebra; Hadamard states (Radzikowski 1996) | existence and uniqueness of the advanced and retarded Green operators | the Pauli–Jordan function of Minkowski; a spacetime with closed timelike curves where uniqueness fails | R | GE2, OP2 |
| SC7 | The renormalized stress tensor: Wald's axioms (1977); the 2D trace anomaly | `⟨T⟩` unique up to local curvature terms; `⟨T^μ_μ⟩ = cR/(24π)` in 2D | `c = 1` for one scalar; point splitting without the Hadamard subtraction diverges | R | SC6, GE8 |
| SC8 | The Page curve of random pure states (Page 1993; Foong–Kanno 1994; Sánchez-Ruiz 1995; Sen 1996) | the average entanglement entropy on `ℂ^m ⊗ ℂ^n` (`m ≤ n`) is `Σ_{k=n+1}^{mn} 1/k − (m − 1)/(2n)` | `m = n = 2` gives `1/3`; product states have zero entropy | L | OP4 |
| SC9 | Semiclassical Einstein equations in cosmology (Pinamonti 2011; Meda–Pinamonti–Siemssen 2021) | existence of solutions in their setting | the de Sitter case; a state violating the Hadamard condition shown to fail | R | SC6, SC7 |

## Mathematical and QFT foundations

### Conformal field theory

Folder `Lightlike/CFT/`. A Lean formalization of the Virasoro algebra
exists elsewhere ([VirasoroProject](https://github.com/kkytola/VirasoroProject)); CF1 starts by
deciding whether to depend on it.

| ID | Milestone | Done when | Trust checks | Size | Needs |
|---|---|---|---|---|---|
| CF1 | Witt and Virasoro algebras; Verma modules; the Kac determinant | Virasoro as the universal central extension of the Witt algebra; the Kac determinant at levels 1 and 2 at least | level-2 Gram determinant `2h(16h² + 2(c−5)h + c)`; a central term `∝ m` shown to be a coboundary | M | - |
| CF2 | Free fields and central charges: free boson, bc and βγ systems | central charges from the mode algebras: `c = 1`, `∓2(6λ² − 6λ + 1)` | bc at `λ = 2` gives `−26`, βγ at `λ = 3/2` gives `11`, so `D = 26` and `D = 10` cancel them; a shifted normal-ordering constant shown to change `c` | M | CF1 |
| CF3 | Vertex operator algebras: the Heisenberg and lattice VOAs | the axioms verified for both | the Heisenberg character `∏ (1−qⁿ)^{−1}`; a wrong locality order shown to fail | L | CF1, Mathlib vertex algebras |
| CF4 | Modular forms for partition functions: η and θ functions, the compact boson | modular invariance of the compact-boson partition function; Jacobi's identity `θ₃⁴ = θ₂⁴ + θ₄⁴` | invariance under `R ↔ 1/R` in the stated units; a partition function without the winding sum shown not invariant | L | CF2, Mathlib modular forms |
| CF5 | Cardy's formula from modular invariance, with the Tauberian error control of Mukhametzhanov–Zhiboedov (2019) | the asymptotic density of states `log ρ(Δ) ∼ 2π√(cΔ/3)` for `c_L = c_R = c`, and `2π√(ch/6)` for one chiral half | the chiral free boson (`c = 1`) against Hardy–Ramanujan `p(n) ∼ e^{π√(2n/3)}/(4n√3)`; a non-invariant spectrum shown to violate it | L | CF4 |

### Dynamical systems

Folder `Lightlike/Dynamics/`: general infrastructure for autonomous ordinary differential equations, in Mathlib style and not specific to physics. Cosmology uses it in CO17 and later; so can any other area. Related work to coordinate with: Mathlib's open pull request on linearizing a flow at a fixed point, and the Lyapunov–Perron machinery of the Tau Ceti library, which is limited to symmetric operators.

- **Needs:** Mathlib.

| ID | Milestone | Done when | Trust checks | Size | Needs |
|---|---|---|---|---|---|
| DS1 | Linearized stability of an equilibrium of `ẋ = f(x)` with `f` of class `C¹` on a finite-dimensional real space | if every eigenvalue of `Df(x₀)` has negative real part, `x₀` is asymptotically stable, with an exponential rate; if one has positive real part, `x₀` is unstable; for a non-symmetric `Df(x₀)` | `ẋ = −x` is stable and `ẋ = x` unstable; the centre `ẋ = (−y, x)` has purely imaginary eigenvalues and is not covered; a non-normal Jordan-block example `[[−1, 100], [0, −1]]` is stable although its symmetric part is not negative | L | Mathlib |
| DS2 | Planar systems: classification of hyperbolic equilibria and the Poincaré–Bendixson theorem | node, saddle and spiral are classified from the trace and determinant; a bounded forward orbit with no equilibrium in its limit set approaches a periodic orbit | the van der Pol oscillator has a limit cycle; a centre has none; a saddle is excluded from the stable cases | L | DS1 |
| DS3 | The Hartman–Grobman theorem and the stable manifold theorem at a hyperbolic equilibrium | the flow is conjugate to its linearization near `x₀`; the local stable and unstable sets are graphs of `C¹` maps tangent to the eigenspaces | the saddle `ẋ = x, ẏ = −y` has the axes as manifolds; a non-hyperbolic example shows that the theorem fails | R | DS1 |

### Gauge theory and constrained systems

Folder `Lightlike/Gauge/`.

| ID | Milestone | Done when | Trust checks | Size | Needs |
|---|---|---|---|---|---|
| GC1 | Principal bundles, connections, curvature, holonomy (trivial bundles over ℝⁿ first) | holonomy of a small loop to second order is the curvature | U(1) holonomy around a loop is `exp(i·flux)`; a flat connection has trivial holonomy on contractible loops | L | GE1 |
| GC2 | Connections on graphs: holonomies, gauge action, cylindrical functions, spin-network functions | gauge-invariant functions on `SU(2)^E` are spanned by spin-network functions (Peter–Weyl on graphs) | invariant-space dimensions on the theta graph; a non-invariant function shown not in the span | M | `SU2/`, `Recoupling/` |
| GC3 | Chern–Simons and BF functionals | the Chern–Simons action changes by `2πk·(winding number)` under large gauge transformations on `S³`; BF field equations `F = 0`, `d_A B = 0` | the basic SU(2) winding; a wrong normalization gives non-integer changes | L | GC1 |
| GC4 | Constrained Hamiltonian systems: first- and second-class constraints; Marsden–Weinstein reduction (with Physlib's moment maps where available) | reduction for a free proper action at a regular value | the particle on a circle; a second-class constraint treated as first class gives the wrong count of degrees of freedom | L | Mathlib |
| GC5 | First-order gravity: Palatini and Holst actions, Ashtekar–Barbero variables | the Palatini and Holst equations are equivalent to Einstein's for non-degenerate tetrads | the Schwarzschild tetrad solves them; the degenerate tetrad `e = 0` solves Palatini without being a metric | L | GE1, GC1 |

### Harmonic analysis on Lie groups

SU(2) representation theory is HA4; Spin(4) = SU(2) × SU(2) is in the spin foams section (SF5a).

| ID | Milestone | Done when | Trust checks | Size | Needs |
|---|---|---|---|---|---|
| HA1 | SL(2,ℂ), its Haar measure and its unitary principal series; their restriction to SU(2) | below | below | L | `SU2/` |
| HA2 | The Plancherel measure of SL(2,ℂ) and the harmonic analysis the Lorentzian amplitudes use | below | below | L | HA1 |
| HA3 | SL(2,ℝ): principal and discrete series, the Plancherel measure | the principal (even and odd) and discrete series of SL(2,ℝ) are defined, unitary and irreducible, and `L²(SL(2,ℝ))` decomposes by a Plancherel formula with principal densities `ρ tanh(πρ)` (even) and `ρ coth(πρ)` (odd) and discrete weights `(n − 1/2)` | Casimir values; the Plancherel density of the principal series `∝ ρ tanh(πρ)`; a non-unitary complementary-series parameter outside `(0, 1/2)` shown to fail | L | HA2 |
| HA4 | Unitary irreducible representations of SU(2) and their completeness; link to Physlib's `sl₂`-modules and 6j symbols | the spin `n/2` representations of SU(2) are unitary and irreducible, every irreducible continuous unitary representation is isomorphic to one of them, the Lie-algebra action matches Physlib's `sl₂`-modules, and the 6j symbols of Lightlike are the recoupling coefficients of their tensor products | - | - | - |
| HA5 | The Peter–Weyl theorem for compact groups | for a compact Hausdorff group `G` with its Haar measure, (a) the matrix coefficients of finite-dimensional unitary representations are dense in `C(G)` and in `L²(G)`, and (b) `L²(G)` is the Hilbert direct sum of the isotypic components `End(V_π)`; (a) and (b) are lockable statements | for `U(1)` the characters `e^{inθ}` form an orthonormal basis of `L²`; Schur orthogonality of characters for SU(2); a non-compact group (ℝ) shown to have no square-integrable matrix coefficients | L | Mathlib |
| HA6 | Unitary irreducible representations of the Poincaré group (Wigner 1939): the little-group method, mass, spin and helicity | the massive and massless one-particle representations are constructed by induction from the little groups SO(3) and ISO(2), unitary, with `P² = m²` and the Pauli–Lubanski square `W² = −m² s(s+1)` in signature `(+,−,−,−)`; the classification of the irreducible representations with positive energy is a lockable statement | massless finite-helicity states satisfy `W = h P`; a massive spin-1/2 representation has two states per momentum; a tachyonic orbit shown to have a non-compact little group | L | HA4 |

- **HA1, done when:** the principal series `π_{n,ρ}` (`n ∈ ℤ`, `ρ` real) of SL(2,ℂ) is defined, is
  a unitary representation, and its restriction to SU(2) is the Hilbert sum of the spin-`j`
  representations `j = |n|/2, |n|/2 + 1, …`, each once. Trust checks: the
  Casimir values, and a non-unitary parameter shown to fail.
- **HA2, done when:** for `f` the restriction of a smooth compactly supported function on the 2×2
  complex matrices, `Σ_n ∫ (n² + 4ρ²) ‖π_{n,ρ}(f)‖²_HS dρ = 16π⁴ ∫ |f|² dg` for the Haar measure
  `haarC`, and the normalisation agrees with Perez–Rovelli (A11)/(A16) or the difference is explained.

### Operator algebras and quantum information

Folder `Lightlike/Operators/`.

| ID | Milestone | Done when | Trust checks | Size | Needs |
|---|---|---|---|---|---|
| OP1 | Unbounded self-adjoint operators: adjoints, essential self-adjointness, deficiency indices, Stone's theorem | (a) the generator of a strongly continuous one-parameter unitary group on a complex Hilbert space is self-adjoint, and (b) every self-adjoint operator generates exactly one such group (Stone's theorem in both directions, on Mathlib's Hilbert spaces) | `−i d/dx` is essentially self-adjoint on `C_c^∞(ℝ)` and generates translations; on `L²[0,1]` without boundary conditions it has deficiency indices `(1,1)` | L | Mathlib |
| OP2 | CCR and CAR algebras: Weyl algebra, Fock space, quasi-free states, Bogoliubov transformations | on every complex Hilbert space `h` a Fock representation exists, and in it a Bogoliubov transformation is unitarily implementable iff its `β` part is Hilbert–Schmidt (Shale 1962) | `\|α\|² − \|β\|² = 1` for one mode; infinitely many modes with constant `\|β\|` shown not implementable | L | OP1 |
| OP3 | States, the KMS condition and modular theory: Tomita–Takesaki in finite dimensions, standard subspaces (Mathlib) | for a positive definite density matrix `ρ` on `M_n(ℂ)`, the modular operator is `Δ_ρ ξ = ρ ξ ρ⁻¹`, and `ρ` is KMS at `β = 1` for the flow `σ_t(A) = ρ^{it} A ρ^{-it}` | the Gibbs state of a qubit is KMS at its temperature; a non-Gibbs state fails | M | OP1 |
| OP4 | Entropy: von Neumann and relative entropy, subadditivity, strong subadditivity (Lieb–Ruskai 1973) | strong subadditivity for finite-dimensional density matrices | Bell state: `S(A) = log 2`, `S(AB) = 0`; the classical inequality `S(AB) ≥ S(A)` shown to fail for it | L | Mathlib matrices |
| OP5 | Finite-dimensional quantum mechanics: unitary evolution, Schrödinger equation, Born rule | on a finite-dimensional complex Hilbert space, for self-adjoint `H`, `exp(−itH)` is a unitary group, `t ↦ exp(−itH)ψ` solves `i dψ/dt = Hψ`, and the Born probabilities of an observable sum to 1 on unit states | - | - | - |
| OP6 | Trace-class and Hilbert–Schmidt operators: the Schatten ideals `S¹` and `S²`, the trace, duality with the compact and the bounded operators | on a separable Hilbert space, the trace-class and Hilbert–Schmidt operators are proven two-sided ideals in the bounded operators with `S²·S² ⊆ S¹`, the trace well defined and cyclic, and the dualities `K* ≅ S¹`, `(S¹)* ≅ B(H)`; the dualities are lockable statements | the diagonal operator with eigenvalues `1/n` is Hilbert–Schmidt and not trace class; `tr(AB) = tr(BA)` for rank-one `A`, `B`; a bounded non-compact operator shown not to be Hilbert–Schmidt | L | Mathlib |

### Oscillatory and saddle-point asymptotics

Pure analysis, independent of the physics, and a candidate for
upstreaming to Mathlib.

| Milestone | Content | Size |
|---|---|---|
| SP1 | Stationary phase for oscillatory integrals on ℝⁿ, including complex phases with `Im φ ≥ 0` | L |
| SP2 | Saddle-point asymptotics of balanced alternating Gamma-ratio sums (complex saddles) | L |
| SP3 | Tauberian theorems for Laplace transforms: Karamata's theorem and Ingham's theorem with exponential growth | L |
| SP4 | The Morse lemma, with smooth dependence on parameters | M |

- **SP1, done when:** the stationary-phase theorem for `∫ a(x) e^{iλφ(x)} dx` on `ℝⁿ`, with a
  smooth compactly supported amplitude and non-degenerate critical points, is proven: the leading
  term with the Hessian's determinant and signature, and an `O(λ^{-n/2-1})` error. It covers
  complex phases with `Im φ ≥ 0` (Hörmander, *The Analysis of Linear Partial Differential
  Operators I*, Theorem 7.7.5), which the EPRL asymptotics (SF9, SF10) need. Trust checks: Gaussian
  integrals in closed form, and a degenerate phase shown to change the order.
- **SP2, done when:** the asymptotics of balanced alternating Gamma-ratio sums
  `Σ_t (−1)^t Γ(t+2)/(∏ Γ(t−a_i+1) ∏ Γ(b_k−t+1))` (the shape of Racah's single-sum formula for the 6j
  symbol, as SF8 needs it) is proven by the complex saddle-point method; the statement is
  `Lightlike.Asymptotics.RacahSumAsymptotics`, the one SF8 uses:
  - the sum as a contour integral `(1/2πi)∮ πT(z)/sin(πz) dz`;
  - complex Stirling, uniform on sectors;
  - a descent contour through the saddle in the upper half-plane;
  - a local Laplace estimate there.

  The summands are exponentially larger than the sum and `(−1)^t` oscillates at the lattice scale,
  so real-variable methods (Riemann sums, Euler–Maclaurin) cannot give it; the Riemann-sum step of
  Gurau (*Ann. Henri Poincaré* 9 (2008) 1413) is not valid as stated. The exact statement and
  hypotheses are agreed with the SF8 milestone. Trust checks: exact Racah sums for a family of growing
  spins against the formula; a sum with known asymptotics; the formula with only one of the two
  complex-conjugate saddles shown to fail; the real-variable estimate shown to be wrong.

- **SP3, done when:** for a positive measure `ρ` on `[0, ∞)`, Karamata's Tauberian theorem (if
  `∫ e^{−βx} dρ(x) ~ β^{−α} ℓ(1/β)` as `β → 0`, with `ℓ` slowly varying, then
  `ρ[0, X] ~ X^α ℓ(X)/Γ(α+1)`) and Ingham's theorem for Laplace transforms growing like `e^{a/β}`
  (Mukhametzhanov–Zhiboedov 2019, eq. (1.8)) are proven; both are lockable statements. The counting
  function `ρ[0, X]` has the asymptotics of Mukhametzhanov–Zhiboedov (1.8); the logarithmic form
  `log ρ[0, X] ~ 2√(aX)` alone does not count. The Cardy
  formula bounds of CF5 use them. Trust checks: Lebesgue measure gives `α = 1`; the growth of the
  spectrum of a free boson; a signed measure shown to break the conclusion.
- **SP4, done when:** the Morse lemma is proven: near a non-degenerate critical point `p` a smooth
  function on ℝⁿ equals `f(p) − y₁² − … − y_k² + y_{k+1}² + … + y_n²`, where `k` is the number of
  negative eigenvalues of the Hessian at `p` (the Morse index), in suitable smooth coordinates
  (Milnor, *Morse Theory*, Part I), with the coordinates depending smoothly on parameters; the
  statement is lockable. Trust checks: `k` equals the number of negative eigenvalues of the Hessian;
  `x³` at `0` shown to have no such chart.

### Perturbative QFT and the renormalization group

Folder `Lightlike/FieldTheory/`.

| ID | Milestone | Done when | Trust checks | Size | Needs |
|---|---|---|---|---|---|
| FT1 | Gaussian integrals, Wick's theorem, Feynman graphs; zero-dimensional QFT as formal power series | the expansion of `∫ e^{−x²/2 − g x⁴/4!} dx` equals the sum over Feynman graphs with symmetry factors | order `g²`: `35/384 = 1/128 + 1/16 + 1/48` from the three vacuum graphs; a wrong symmetry factor shown to fail | M | Mathlib |
| FT2 | Renormalization of graphs: BPHZ forests, the Connes–Kreimer Hopf algebra (1998–2000), Birkhoff decomposition | the Hopf algebra with the antipode as the BPHZ counterterm map | coproduct and antipode on small rooted trees; a non-coassociative coproduct shown to fail | L | FT1 |
| FT3 | Dimensional regularization at one loop | one-loop Euclidean integrals as meromorphic functions of the dimension `d`, with their poles | the massive tadpole `π^{d/2} Γ(1−d/2) m^{d−2}` and its poles; a cutoff scheme shown to give a different finite part | M | Mathlib Gamma |
| FT4 | The renormalization group for finitely many couplings: flows, fixed points, linearization, critical exponents | linearization at a hyperbolic fixed point; the one-loop φ⁴ flow in `4 − ε` dimensions | Wilson–Fisher `ν = 1/2 + ε/12` at one loop (`N = 1`); the Gaussian fixed point gives `ν = 1/2` | M | FT1 |
| FT5 | BRST and BV formalism in finite dimensions | for a free action of a compact group, BRST cohomology in degree 0 is the invariant functions on the constraint set | U(1) acting on ℝ²; a non-nilpotent differential shown to fail | M | Mathlib |
| FT6 | The Legendre–Fenchel transform and the one-particle-irreducible effective action | the Legendre–Fenchel transform of a convex lower-semicontinuous function on ℝⁿ is proven convex and involutive (Fenchel–Moreau), and in zero dimensions the Legendre transform of `W = log Z` is proven to generate the one-particle-irreducible graphs of FT1's expansion; both are lockable statements | the Gaussian `W(J) = J²/2` gives `Γ(φ) = φ²/2`; the order-`g` 1PI vertex of the quartic model; a non-convex function shown to differ from its biconjugate | M | FT1 |

### PL topology

Folder `Lightlike/PL/`. Three layers, so that every intermediate result is
a theorem in its own right and none has to be redone: layer 1 is combinatorial, layer 2 connects
it to PL topology, layer 3 to topological 3-manifolds.

| Milestone | Layer | Content | Size |
|---|---|---|---|
| PL1 | 1 | Simplicial complexes in every dimension; links, stars, joins, cones; stellar subdivisions and welds; bistellar moves; combinatorial manifolds and PL spheres | M |
| PL2 | 1 | Pachner's theorem: closed combinatorial manifolds are stellar-equivalent exactly when they are related by bistellar moves | L |
| PL3 | 1 | The classification of closed combinatorial surfaces up to 2D bistellar moves | L |
| PL4 | 2 | Geometric realisations, PL maps and PL homeomorphisms; Newman's theorem: PL-homeomorphic realisations exactly when stellar-equivalent | L |
| PL5 | 3 | The topology Moise's proof needs: Jordan curve and Schoenflies theorems in the plane, and the 3-dimensional tools fixed by a survey at the start of PL5 | R |
| PL6 | 3 | Moise's theorem: every topological 3-manifold has a triangulation, unique up to PL homeomorphism | R |
| PL7a | - | Assembly up to PL homeomorphism: PL-homeomorphic closed combinatorial 3-manifolds have triangulations related by the moves on `Complex3`; consequences for the state sums | M |
| PL7b | - | Assembly up to homeomorphism: homeomorphic closed 3-manifolds have triangulations related by the moves on `Complex3` (needs Moise's theorem, PL6); consequences for the state sums | R |
| PL7c | - | Unconditional triangulation independence of the regularised Ponzano–Regge amplitude on the PL side | R |

- **PL1, done when:** the definitions of the title (complexes in every dimension; links, stars,
  joins, cones; stellar subdivisions and welds; bistellar moves; combinatorial manifolds and PL
  spheres) exist, with the properties of checklist items p2–p5 and the four trust checks: the
  boundary of an (n+1)-simplex is a PL n-sphere, small known examples (the octahedron is a PL
  2-sphere), a non-manifold (two spheres glued at a vertex) is rejected, and the 3-dimensional
  bistellar moves agree with `Lightlike.PR.move23` and `Lightlike.PR.move14` on `Complex3`.
- **PL2, done when:** Pachner's theorem is proven at least in dimension 3 (in every dimension if the
  proof allows; following Lickorish, *Simplicial moves on complexes and manifolds*, 1999), with the
  corollary that stellar-equivalent closed combinatorial 3-manifolds are related by chains of
  2-3, 3-2, 1-4 and 4-1 moves on `Complex3`. Also in PL2: a bridge from `Lightlike.FourD.Complex4` to the simplicial complexes of PL1 under which
  the five 4D Pachner moves of `FourD/Pachner.lean` are bistellar moves, so that Pachner's theorem
  applies to `Complex4`; and combinatorial 4-manifolds on `Complex4` (every vertex link a PL
  3-sphere), preserved by those moves.
- **PL3, done when:** every connected closed combinatorial surface is related by 2D bistellar
  moves to a standard model determined by its orientability and Euler characteristic, and the
  models are pairwise inequivalent. Builds on `IsSurfaceSphere` and the converse
  `IsSurfaceSphere → IsSphere2` (QU5).
- **PL4, done when:** Newman's theorem is proven: finite simplicial complexes `K`, `L` have
  PL-homeomorphic realisations iff they are stellar-equivalent; trust checks: a subdivision is PL-homeomorphic to
  the original complex, and complexes with non-homeomorphic realisations (different Euler
  characteristic) are not stellar-equivalent.
- **PL5, done when:** the statements fixed by the survey at the start of PL5 are proven.
- **PL6, done when:** both parts of Moise's theorem are proven.
- **PL7a, done when:** the Turaev–Viro state sum at `r = 3`, which is already unconditionally
  invariant under the moves, is proven to be an invariant of closed 3-manifolds up to PL homeomorphism (from PL2 and PL4); and a theorem, or a docs note cited in the API map, states which PL invariance of the
  Ponzano–Regge amplitude follows from PL2 and PL4, with its cutoff and gauge-tree conditions.
- **PL7b, done when:** the same up to homeomorphism (from PL7a and Moise's theorem, PL6).
- **PL7c, done when:** `PachnerForwardHyp` is proven (any two triangulations of one closed combinatorial
  3-manifold on `Complex3` have a common descendant under forward Pachner moves), so that LL-0522 holds
  without that hypothesis; the route is Adiprasito–Pak, arXiv:2404.05930, Theorems 1.1 and 1.3 (common
  stellar subdivisions), with PL7a's p4. Trust checks: an explicit common forward descendant of two
  different triangulations of S³; the edge case of PL7a's p4 (an edge subdivision is not itself a forward
  descendant).

### Quantum groups and state-sum TQFTs

Folder `Lightlike/TuraevViro/`.

| ID | Milestone | Done when | Trust checks | Size | Needs |
|---|---|---|---|---|---|
| QU1 | q-deformed Biedenharn–Elliott identity and orthogonality for `r ≥ 4` | below | below | L | `TuraevViro/` |
| QU2 | The Crane–Yetter state sum: quantum 15j symbols at roots of unity, invariance under the 4D Pachner moves | below | below | L | QU1, SF3 |
| QU3 | Modular tensor categories from `U_q(sl₂)` at roots of unity, and the Reshetikhin–Turaev invariant from surgery | the RT invariant of closed 3-manifolds given by surgery on framed links is defined and proven invariant under the Kirby moves | `S³`, `S²×S¹` and lens spaces `L(p,1)` against published values; a non-modular S-matrix shown to break invariance | R | QU1 |
| QU4 | Biedenharn–Elliott identity for all spins; Ponzano–Regge amplitude; invariance under the 2-3 move at the level of the weight (exact for the gauge-fixed amplitude below) | the Biedenharn–Elliott identity for the SU(2) 6j symbols is proven for all spins, the Ponzano–Regge amplitude is defined, and its weight is proven invariant under the 2-3 move, exactly for the gauge-fixed amplitude, i.e. `amplitudeGF K T cut` is unchanged by the 2-3 move under `T ⊆ K.edges` and the cutoff inequality | a known 6j value; a wrong sign convention in the 6j symbol shown to break the Biedenharn–Elliott identity | M | HA4 |
| QU5 | Triangulation independence of the regularised Ponzano–Regge amplitude as far as it goes without Pachner's theorem | the statements of **QU5, what is proven** below hold: the 1-4 move; the gauge-fixed amplitude is invariant along chains of 2-3, 3-2, 1-4 and 4-1 moves, also with a maximal tree; 3-2 and 4-1 moves are recognised on any complex; a tree change by triangle exchange leaves the amplitude unchanged; closed combinatorial 3-manifolds are preserved by all four moves; combinatorial 2-spheres have `χ = 2` | - | - | - |

- **QU1, done when**: for every `r ≥ 4`, `qBiedenharnElliott` and `qOrthogonality` are theorems
  without hypotheses, and `turaevViro_move23` and `turaevViro_move14` hold at level `r` without
  hypotheses; trust checks: q-6j values for some `r ≥ 4` agree with an independent source, and a
  changed `q` makes one of the identities false.
- **QU2, done when:** a Crane–Yetter state sum of a combinatorial 4-complex (colourings, weights,
  the sum of products of `qFifteenJ` at `q = e^{iπ/r}`) is defined, and its value is unchanged under
  the 2-4, 3-3, 4-2, 1-5 and 5-1 moves (hypotheses on the complex stated). Builds on the q-recoupling of TV `r ≥ 4`. Trust checks: the invariant of `S⁴` and of `CP²` against the known values
  (Crane–Kauffman–Yetter, *J. Knot Theory Ramif.* 6 (1997) 177), and a wrong `q` shown to break
  invariance.

- **QU5, what is proven:** the 1-4 move; the gauge-fixed amplitude is invariant along chains of
  2-3, 3-2, 1-4 and 4-1 moves, also with a maximal tree as gauge set; the 3-2 and 4-1 moves are
  recognised on any complex; changing the maximal tree by triangle exchanges leaves the amplitude
  unchanged for every cutoff; closed combinatorial 3-manifolds are preserved by all four moves.
- **QU5, what it does not give:** triangulation independence itself. That also needs Pachner's
  theorem (which needs piecewise-linear topology that Mathlib lacks) and the removal of the spin
  cut-off (a divergence question that depends on the topology); both are planned below. Proven
  partial answers: the cutoff is irrelevant when the gauge set forces every edge (the amplitude is
  then `1`, e.g. for the boundary of the 4-simplex), and for maximal trees not connected by triangle
  exchanges the amplitude with finite cutoffs does depend on the tree (a Lean counterexample on a
  ring of three tetrahedra; the ring is not a 3-manifold, so this lies outside the assumptions of
  Freidel–Louapre's tree independence, and the closed-manifold case is open). Combinatorial
  2-spheres are proven to be connected closed pseudo-surfaces with Euler characteristic 2, and
  exactly the intrinsic triangulated 2-spheres (both directions).

### Random geometry

Folder `Lightlike/Random/`.

| ID | Milestone | Done when | Trust checks | Size | Needs |
|---|---|---|---|---|---|
| RN1 | Poisson point processes on measure spaces | existence, independence on disjoint sets, conditioning on the count | count mean and variance equal the volume; a binomial process shown to have dependent counts | M | Mathlib |
| RN2 | Planar maps as permutation triples; Tutte's count; the Cori–Vauquelin–Schaeffer bijection | rooted planar maps with `n` edges number `2·3ⁿ(2n)!/(n!(n+2)!)` | `n = 1, 2, 3` give `2, 9, 54`; dropping connectivity shown to overcount | L | Mathlib permutations |
| RN3 | Galton–Watson trees and branched polymers | generating functions of plane trees and their singularity, exponent `γ = 1/2` for branched polymers | Catalan counts; a subcritical tree shown to be finite almost surely | M | - |
| RN4 | Wigner's semicircle law by moments | moments of scaled Wigner matrices converge to the Catalan numbers | moments `1, 2, 5, 14`; Wishart matrices (Narayana moments, Marchenko–Pastur) shown different | L | FT1, RN2 |
| RN5 | Gaussian free field and Gaussian multiplicative chaos (Kahane 1985; Berestycki 2017) | the planar GFF and its chaos measure, non-trivial for `γ < 2` | expected chaos mass equals Lebesgue measure; `γ ≥ 2` gives the zero measure | R | RN1 |

## Approaches to quantum gravity

### Asymptotic safety

Folder `Lightlike/AsymptoticSafety/`.

- **Needs:** FT1, FT3, FT4, GE8.

| ID | Milestone | Done when | Trust checks | Size | Needs |
|---|---|---|---|---|---|
| AS1 | The Wetterich equation for finitely many variables | the exact flow proven for a regulated zero-dimensional integral; its `k → 0` limit is the effective action | agreement with FT1's series; a truncation at order φ⁴ shown to deviate at order `g²` | M | FT1, FT4 |
| AS2 | The Einstein–Hilbert truncation (Reuter 1998; Litim 2004) as an ODE system for `(g, λ)` | the non-Gaussian fixed point and its critical exponents, for the ODE | fixed-point values and exponents against Litim (2004), with a Python cross-check; a sign error in the anomalous dimension shown to move or remove the fixed point | M | FT4 |
| AS3 | The `2 + ε` expansion (Gastmans–Kallosh–Truffin 1978; Christensen–Duff 1978; Weinberg 1979) | the one-loop beta function of Newton's constant and its fixed point of order ε | the one-loop coefficient against both papers; a wrong-sign ghost contribution shown to change it | M | FT3, FT4 |
| AS4 | A rigorous non-trivial UV fixed point in a toy model: the 3D Gross–Neveu model at large N (Gawędzki–Kupiainen 1985) or the Grosse–Wulkenhaar model (vanishing beta function, Disertori–Gurau–Magnen–Rivasseau 2007) | one of these, chosen at the start | the model's published leading coefficients; the model without its UV mechanism shown to diverge | R | FT2, OP1 |

### Canonical quantum gravity

Folder `Lightlike/Canonical/`: loop quantum gravity, loop quantum
cosmology and Wheeler–DeWitt quantization.

- **Needs:** GE1, GE2 (foliations, Cauchy surfaces), GC2, GC4, GC5 (graphs, constraints,
  Ashtekar–Barbero variables), OP1 (self-adjointness), Mathlib projective limits of measures.

| ID | Milestone | Done when | Trust checks | Size | Needs |
|---|---|---|---|---|---|
| CA1 | ADM formulation: lapse, shift, Hamiltonian and momentum constraints, the hypersurface deformation algebra (Hojman–Kuchař–Teitelboim 1976) | the constraints defined on a foliated globally hyperbolic spacetime; their brackets on smeared constraints computed, with structure functions | Schwarzschild and flat FLRW data satisfy the constraints; data with wrong extrinsic curvature violates the momentum constraint | L | GE2, GC4 |
| CA2 | Ashtekar–Lewandowski kinematics: cylindrical functions, projective limit, AL measure, spin-network basis | the AL measure as a projective limit of Haar measures; spin networks an orthonormal basis (Ashtekar–Lewandowski 1995; Baez 1996) | norm of a theta-graph spin network; a family of measures that is not cylindrically consistent shown to have no limit | L | GC2 |
| CA3 | The area operator and its spectrum (Rovelli–Smolin 1995; Ashtekar–Lewandowski 1997) | `A(S) = 8πγℓ_P² Σ √(j(j+1))` for transversal punctures | the area gap `4√3 π γ ℓ_P²`; `j` in place of `√(j(j+1))` shown to give another spectrum | L | CA2 |
| CA4 | The volume operator (Ashtekar–Lewandowski; spectral analysis by Brunnemann–Thiemann 2006) | defined on spin networks; eigenvalues on 4-valent nodes with small spins | zero on gauge-invariant trivalent nodes; published 4-valent eigenvalues; a wrong regularization constant shown to differ | M | CA2 |
| CA5 | Uniqueness of the kinematical representation (Lewandowski–Okołów–Sahlmann–Thiemann 2006; Fleischhack 2009) | the AL representation is the unique diffeomorphism-invariant cyclic representation of the holonomy–flux algebra, under the stated hypotheses | hypotheses hold for AL; a representation with a background flux (Koslowski–Sahlmann) differs | R | CA2, OP1 |
| CA6 | Black-hole entropy from puncture counting (Domagala–Lewandowski 2004; Meissner 2004) | the asymptotics of the counting give `S = (γ_M/γ) A/4` with `γ_M ≈ 0.2375` | `γ_M` to four digits; counting only `j = 1/2` punctures gives `ln 2/(π√3) ≈ 0.127`, shown to differ | L | CA3 |
| CA7 | Loop quantum cosmology (Ashtekar–Pawlowski–Singh 2006): polymer Hilbert space, the `μ̄` evolution operator, self-adjointness (Kamiński–Lewandowski 2008), effective Friedmann equation | the effective equation `H² = (8πG/3)ρ(1 − ρ/ρ_c)` with a bounce at `ρ_c = √3/(32π²γ³) ρ_Pl` | `ρ_c ≈ 0.41 ρ_Pl` at `γ = γ_M`; the Wheeler–DeWitt limit has no bounce; the `μ₀` scheme's `ρ_c` depends on the fiducial cell | L | OP1 |
| CA8 | Minisuperspace Wheeler–DeWitt: closed FLRW with a cosmological constant; Hartle–Hawking (1983) and Vilenkin boundary conditions | the minisuperspace operator, its self-adjoint extensions, and the two wave functions as Airy-type solutions | Hartle–Hawking `∝ Ai`, Vilenkin `∝ Ai + iBi`; their WKB asymptotics | M | OP1 |
| CA9 | Thiemann's Hamiltonian constraint (1998) on the kinematical space | the operator for a fixed regularization, with its covariance and the dependence on choices recorded | published matrix elements on a 4-valent node; a non-covariant regularization shown to fail covariance | R | CA2–CA4 |

### Causal sets

Folder `Lightlike/CausalSets/`.

- **Needs:** Mathlib orders, RN1, GE2 (sprinkling into curved spacetimes), OP2 (continuum
  comparison of the Sorkin–Johnston state).

| ID | Milestone | Done when | Trust checks | Size | Needs |
|---|---|---|---|---|---|
| CS1 | Causal sets as locally finite partial orders: links, chains, antichains, intervals | definitions with basic properties | a 4-element diamond; a non-transitive relation rejected | S | Mathlib |
| CS2 | Poisson sprinkling into Minkowski regions; the Myrheim–Meyer relation count | `⟨R⟩ = n(n−1) Γ(d+1)Γ(d/2)/(4Γ(3d/2))` for `n` uniform points in a `d`-dimensional causal diamond | `1/4` of `n(n−1)` in 2D, `1/20` in 4D; points in a cube instead of a diamond give a different count | M | CS1, RN1 |
| CS3 | Longest chains: `∼ 2√n` in a 2D diamond (Vershik–Kerov 1977; Logan–Shepp 1977) | the limit via random permutations | `E[longest chain] = 2` for `n = 3` by enumeration; the constant 1 shown wrong | L | CS2 |
| CS4 | Discreteness without symmetry breaking (Bombelli–Henson–Sorkin 2009) | no measurable equivariant map from Minkowski sprinklings to timelike directions | a regular lattice admits one | L | CS2 |
| CS5 | The causal-set d'Alembertian and the Benincasa–Dowker action (2010) | the expected value of the 2D operator converges to `□φ` for smooth `φ` in flat space | polynomial `φ` in closed form; the unweighted layer sum shown not to converge | R | CS2 |
| CS6 | Classical sequential growth (Rideout–Sorkin 2000) | the general solution of Bell causality and discrete general covariance is generalized percolation | transitive-percolation probabilities on 2- and 3-element orders; a law violating Bell causality fails consistency | L | CS1 |
| CS7 | The Sorkin–Johnston state on finite causal sets (Johnston 2009; Afshordi–Aslanbeigi–Sorkin 2012) | the positive part of the Pauli–Jordan matrix defines a pure quasi-free state | the 2-chain in closed form; a non-antisymmetric Pauli–Jordan matrix rejected | M | CS1, OP2 |
| CS8 | Almost all finite posets have three layers (Kleitman–Rothschild 1975) | the asymptotic statement | counts for small `n`; two-layer orders shown to be a vanishing fraction | R | CS1 |

### Dynamical triangulations

Folder `Lightlike/Triangulations/`: Euclidean and causal dynamical
triangulations.

- **Needs:** RN2, RN3, PL topology (PL2), 4D combinatorics (SF3), Regge action (RC5).

| ID | Milestone | Done when | Trust checks | Size | Needs |
|---|---|---|---|---|---|
| DT1 | 2D dynamical triangulations as planar maps: the partition function as a generating function; `γ_str = −1/2` | the counting asymptotics `c·ρ⁻ⁿ n^{−5/2}` for rooted maps | Tutte's `(2/√π)·12ⁿ n^{−5/2}`; branched polymers (`γ = 1/2`) shown different | M | RN2 |
| DT2 | The Brownian map (Le Gall 2013; Miermont 2013) | uniform quadrangulations, distances scaled by `n^{−1/4}`, converge in Gromov–Hausdorff distance | typical distance `∼ n^{1/4}` (Chassaing–Schaeffer 2004); trees (`n^{1/2}`) shown different | R | RN2, RN3 |
| DT3 | 2D causal dynamical triangulations: the exact solution (Ambjørn–Loll 1998), the bijection with plane trees, the uniform infinite causal triangulation (Durhuus–Jonsson–Wheater 2010) | Hausdorff dimension 2 and spectral dimension at most 2 | the disc amplitude of Ambjørn–Loll; Euclidean 2D DT (Hausdorff dimension 4) shown different | L | RN3 |
| DT4 | Dynamical triangulations in 3D and 4D on finite triangulations: the Einstein–Regge action `−κ₂N₂ + κ₄N₄`, causal (layered) triangulations, ergodicity of the moves from Pachner's theorem | definitions and ergodicity for fixed topology | the Dehn–Sommerville relations `2N₃ = 5N₄` and `2N₁ − 3N₂ + 6N₃ − 10N₄ = 0` (the boundary of the 5-simplex: `N = (6, 15, 20, 15, 6)`); a non-manifold shown to violate them | M | PL2, SF3, RC5 |
| DT5 | The exponential bound for 3-sphere triangulations | the bound for locally constructible triangulations (Durhuus–Jonsson 1995); not all are LC (Benedetti–Ziegler 2011); the general case stated as open | counts for small N; a non-LC example | R | DT4 |

### Group field theory and tensor models

Folder `Lightlike/Tensor/`.

- **Needs:** FT1, FT2, RN3, PL topology (colored graphs and pseudo-manifolds), recoupling (SF4)
  and the Ooguri model (SF5b).

| ID | Milestone | Done when | Trust checks | Size | Needs |
|---|---|---|---|---|---|
| GF1 | Colored graphs and their dual pseudo-manifolds (Gurau 2010; crystallization theory) | every closed (D+1)-colored graph gives a normal pseudo-manifold | in D = 2 the genus from Euler's formula; an improperly colored graph shown not to | M | PL1 |
| GF2 | The Boulatov (1992) and Ooguri (1992) models: the Feynman amplitude of each graph equals the Ponzano–Regge or Ooguri amplitude of its dual complex | per-graph equality, with the cutoff conventions of `PonzanoRegge/` and `SpinFoam/` | the two-tetrahedron 3-sphere against Ponzano–Regge; a model without the gauge projection shown to give other amplitudes | M | GF1, FT1, SF5b |
| GF3 | The 1/N expansion of colored tensor models (Gurau 2011) | the Gurau degree is non-negative and zero exactly for melonic graphs | melonic counts `binom(pn, n)/((p−1)n+1)` with `p = D+1` (Bonzom–Gurau–Riello–Rivasseau 2011); a non-melonic graph has positive degree | M | GF1 |
| GF4 | Melonic dominance and the critical point | the leading free energy is the melonic generating function, with exponent `γ = 1/2` at the critical coupling | the series against GF3's counts; a matrix-model (genus) count shown different | M | GF3, RN3 |
| GF5 | Melons are branched polymers (Gurau–Ryan 2014) | Hausdorff dimension 2 and spectral dimension 4/3 of the melonic continuum limit | the random-path case (Hausdorff dimension 2, spectral 1) shown different | R | GF4, RN3 |
| GF6 | Renormalizability of tensorial GFTs: T⁴₄ (Ben Geloun–Rivasseau 2013), SU(2) in 3D (Carrozza–Oriti–Rivasseau 2014) | renormalizability to all orders of one model | power-counting degrees of melonic graphs; a model above the critical rank shown non-renormalizable by power counting | R | FT2, GF3 |
| GF7 | Borel summability: the modified Boulatov model (Freidel–Louapre 2003), quartic tensor models (Delepouve–Gurau–Rivasseau 2016) | Borel summability of one model via the loop vertex expansion | Borel sum against the series at small coupling; the unmodified model's growth shown to prevent it | R | FT1 |

### Holography

Folder `Lightlike/Holography/`.

- **Needs:** GE1, GE2, GE7, CF1, CF5, OP4, HA3, GC4.

| ID | Milestone | Done when | Trust checks | Size | Needs |
|---|---|---|---|---|---|
| HO1 | Anti-de Sitter space: hyperboloid model, `SO(d,2)` isometries, Poincaré and global coordinates, conformal boundary | AdS solves `R_μν = −(d/ℓ²)g_μν` | geodesic distance formula; de Sitter (other sign of Λ) shown different | M | GE1, GE7 |
| HO2 | Asymptotic symmetries of AdS₃ (Brown–Henneaux 1986) | two Virasoro algebras with `c = 3ℓ/(2G)` from the canonical charges | `c`; a boundary fall-off violating the conditions shown not to close | L | HO1, CF1, GC4 |
| HO3 | The BTZ black hole (Bañados–Teitelboim–Zanelli 1992) and its Cardy entropy (Strominger 1998) | BTZ as a quotient of AdS₃; `S = 2πr₊/(4G)` equals Cardy's formula with `c = 3ℓ/(2G)` | the match; a wrong central charge shown not to match | M | HO1, HO2, CF5 |
| HO4 | Ryu–Takayanagi in AdS₃ | the regularized geodesic length gives `S = (c/3) log(L/ε)`, as in Calabrese–Cardy (2004) | the coefficient `c/3`; a non-geodesic curve shown longer | M | HO1 |
| HO5 | Holographic entropy inequalities for minimal cuts on graphs (Headrick–Takayanagi 2007; Hayden–Headrick–Maloney 2013; Bao et al. 2015) | strong subadditivity and monogamy of mutual information for min-cut entropies | the 4-party GHZ state has `I₃ = log 2 > 0`, so it violates monogamy and has no graph model | M | OP4 |
| HO6 | Holographic codes: the HaPPY code (Pastawski–Yoshida–Harlow–Preskill 2015); operator-algebra error correction (Almheiri–Dong–Harlow 2015) | the [[5,1,3]] code corrects any single-qubit error; complementary recovery on a small network | distance 3; a code with distance 2 shown not to correct all single errors | M | OP4 |
| HO7 | Holographic renormalization and the Weyl anomaly (Henningson–Skenderis 1998) | the boundary anomaly from the on-shell action in AdS₃ and AdS₅ | `c = 3ℓ/(2G)` in AdS₃; `a = c = πℓ³/(8G)` in AdS₅ | L | HO1 |
| HO8 | Generalized entropy from the replica trick (Lewkowycz–Maldacena 2013), conditional | stated with its assumptions as hypotheses | the AdS₃ case reproduces HO4 | R | HO4, SC3 |

### Low-dimensional gravity

Folder `Lightlike/LowDim/`: 2+1 gravity, JT gravity and the Schwarzian,
topological gravity, Liouville gravity. The 3D state sums (Ponzano–Regge, Turaev–Viro) are in the
spin foams section and are also 3D quantum gravity models.

- **Needs:** GC1, GC3, GC5, QU3, HA3, CF1, RN5, the 3D state sums.

| ID | Milestone | Done when | Trust checks | Size | Needs |
|---|---|---|---|---|---|
| LD1 | 2+1 gravity as Chern–Simons theory (Achúcarro–Townsend 1986; Witten 1988) | equal actions and equations of motion for invertible triads, for each sign of Λ | BTZ as a flat `SL(2,ℝ) × SL(2,ℝ)` connection; degenerate triads give flat connections that are not metrics | M | GC3, GC5 |
| LD2 | Turaev–Viro equals the square of Reshetikhin–Turaev (Turaev 1991; Walker 1991; Roberts 1995) | `TV(M) = \|RT(M)\|²` | `S³`, `S² × S¹`, lens spaces; RT alone shown different from TV for a chiral case | R | QU3, QU1 |
| LD3 | Ponzano–Regge as quantized 3D gravity: the relation to Reidemeister torsion (Barrett–Naish-Guzman 2009); coupling to point particles (Freidel–Louapre 2004; Noui–Perez 2005) | the stated relation on a class of manifolds | lens spaces; a manifold outside the class shown to diverge | R | SF2 |
| LD4 | JT gravity and the Schwarzian; disk partition function by Duistermaat–Heckman (Stanford–Witten 2017) | `Z(β) ∝ (C/β)^{3/2} e^{2π²C/β}`, one-loop exact, with density `∝ sinh(2π√(2CE))` | the Laplace transform of the density; the classical term without the `β^{−3/2}` factor shown wrong | L | HA3 |
| LD5 | Weil–Petersson volumes: Mirzakhani's recursion (2007) and Eynard–Orantin (2007) for the JT spectral curve (Saad–Shenker–Stanford 2019) | the recursion and its equivalence with topological recursion | `V_{1,1} = (L² + 4π²)/48` (with the orbifold factor ½), `V_{0,4} = (4π² + ΣL_i²)/2`; a kernel with a sign error gives negative volumes | R | LD4 |
| LD6 | Intersection numbers on moduli of curves (Witten 1991; Kontsevich 1992) | string and dilaton equations, and the DVV recursion for the numbers | `⟨τ₀³⟩₀ = 1`, `⟨τ₁⟩₁ = 1/24`, `⟨τ₄⟩₂ = 1/1152`; a wrong recursion coefficient shown to give other values | R | - |
| LD7 | Liouville quantum gravity: the probabilistic construction (David–Kupiainen–Rhodes–Vargas 2016), KPZ (Duplantier–Sheffield 2011), DOZZ (Kupiainen–Rhodes–Vargas 2020) | the Liouville measure on the sphere and the KPZ relation `x = (γ²/4)Δ² + (1 − γ²/4)Δ` | `c_L = 1 + 6Q²` with `Q = γ/2 + 2/γ` gives `c_L = 26` at `γ = √(8/3)`; KPZ with a wrong `γ` shown to mismatch the planar-map exponents | R | RN5, CF1 |

### Matrix models

Folder `Lightlike/MatrixModels/`: matrix models of 2D gravity, and the
BFSS and IKKT models.

- **Needs:** FT1, RN2, RN4, OP1.

| ID | Milestone | Done when | Trust checks | Size | Needs |
|---|---|---|---|---|---|
| MM1 | Gaussian matrix integrals: the genus expansion of `⟨tr M^{2k}⟩`; the Harer–Zagier recursion (1986) | `(n+1)ε_g(n) = 2(2n−1)ε_g(n−1) + (n−1)(2n−1)(2n−3)ε_{g−1}(n−2)` | genus 0 gives Catalan numbers; `ε₁(2) = 1`; real symmetric matrices (GOE) count non-orientable gluings too | M | FT1, RN2 |
| MM2 | The planar quartic model (Brézin–Itzykson–Parisi–Zuber 1978) | the planar free energy and its critical coupling `g_c = −1/48`; coefficients count quadrangulations | the `12ⁿ` growth of RN2; the cubic model counts triangulations instead | L | RN2, RN4 |
| MM3 | The double-scaling limit (1990) and Painlevé I; the Riemann–Hilbert approach (Fokas–Its–Kitaev 1992) | the specific heat satisfies Painlevé I | the leading asymptotics; a single-scaling limit shown to give only the planar term | R | MM2 |
| MM4 | The BFSS Hamiltonian (Banks–Fischler–Shenker–Susskind 1997) | its spectrum is `[0, ∞)` (de Wit–Lüscher–Nicolai 1989) | the bosonic model has purely discrete spectrum (Simon 1983; Lüscher 1983) | R | OP1 |
| MM5 | IKKT integrals (Ishibashi–Kawai–Kitazawa–Tsuchiya 1997): convergence (Krauth–Nicolai–Staudacher 1998; Austing–Wheater 2001) | convergence of the supersymmetric Yang–Mills integrals in the stated dimensions | SU(2) values against Krauth–Nicolai–Staudacher; a divergent bosonic case | R | - |

### Noncommutative geometry

Folder `Lightlike/NCG/`.

- **Needs:** GE5, GE8, OP1, Mathlib C*-algebras.

| ID | Milestone | Done when | Trust checks | Size | Needs |
|---|---|---|---|---|---|
| NC1 | Spectral triples; finite spectral triples and Krajewski diagrams (Krajewski 1998; Paschke–Sitarz 1998) | definitions; the classification of finite real spectral triples on small algebras | ℂ ⊕ ℂ; a Dirac operator violating the first-order condition rejected | M | Mathlib C*-algebras |
| NC2 | Connes' distance formula | the spectral distance equals arc length on the circle, and `1/\|m\|` on the two-point space | both values; a Dirac operator scaled by 2 halves all distances | M | GE5, OP1 |
| NC3 | The finite geometry of the Standard Model (Chamseddine–Connes–Marcolli 2007; Barrett 2007) | `ℂ ⊕ ℍ ⊕ M₃(ℂ)` with KO-dimension 6 and the fermion representation | the signs `(ε, ε', ε'') = (1, 1, −1)`; KO-dimension 0 shown to give other signs | M | NC1 |
| NC4 | The fuzzy sphere (Madore 1992) | the Laplacian on `M_N(ℂ)` has spectrum `l(l+1)`, `l = 0, …, N−1`, multiplicity `2l+1` | `N²` eigenvalues in total; a wrong Casimir normalization shown to differ | S | `SU2/` |
| NC5 | The spectral action (Chamseddine–Connes 1997) | the heat-kernel expansion of `Tr f(D/Λ)` gives the cosmological and Einstein–Hilbert terms | the round sphere and flat torus; a missing `a₁` coefficient shown to drop the Einstein–Hilbert term | L | GE5, GE8 |
| NC6 | Connes' reconstruction theorem (2013) | commutative spectral triples satisfying the axioms come from spin manifolds | the circle and the torus; a triple violating orientability excluded | R | NC1, GE5 |

### Perturbative quantum gravity

Folder `Lightlike/PerturbativeGravity/`: perturbative quantization
around a background, and gravity as an effective field theory.

- **Needs:** GE1, GE7, GE8, FT1–FT3, FT5, HA1 (Poincaré and Lorentz representations), GC4.

| ID | Milestone | Done when | Trust checks | Size | Needs |
|---|---|---|---|---|---|
| PG1 | Linearized gravity on Minkowski: gauge symmetry, de Donder and TT gauges, plane waves | two polarizations in TT gauge | plus and cross waves solve the equations; a longitudinal wave does not | M | GE1 |
| PG2 | Massive spin 2: Fierz–Pauli (1939); the vDVZ discontinuity (van Dam–Veltman 1970; Zakharov 1970) | five degrees of freedom exactly for the Fierz–Pauli mass term; light bending of the massless limit is 3/4 of GR's | a detuned mass term propagates a sixth, ghost mode | M | PG1, GC4 |
| PG3 | Gravitons as massless helicity ±2 representations; Weinberg's soft theorem (1965); Weinberg–Witten (1980) | the Weinberg–Witten no-go statement for massless spin `> 1` with a covariant conserved stress tensor | helicity ±1 and ±2 examples; a massive spin-2 particle evades it | L | HA1, PG1 |
| PG4 | One loop ('t Hooft–Veltman 1974) | the on-shell one-loop counterterm of pure gravity vanishes (field equations and Gauss–Bonnet), and gravity with a scalar has a non-zero one | the counterterm coefficients of 't Hooft–Veltman; the scalar case shown non-zero | L | GE8, FT3, FT5 |
| PG5 | Two loops: the Goroff–Sagnotti counterterm (1986; van de Ven 1992) | the coefficient `209/2880` of the `R³` counterterm, in their normalization | the coefficient; a wrong graph set shown to differ | R | PG4 |
| PG6 | Gravity as an effective field theory (Donoghue 1994): the quantum correction to the Newtonian potential (Bjerrum-Bohr–Donoghue–Holstein 2003) | the coefficient `41/(10π)` of `Għ/r²` from the one-loop non-analytic terms | the coefficient; dropping the vertex diagrams shown to give another | R | PG4 |
| PG7 | Double copy: KLT relations (Kawai–Lewellen–Tye 1986) and BCJ (Bern–Carrasco–Johansson 2008) at tree level | four-point KLT as an identity of rational functions in spinor-helicity variables | the MHV four-graviton amplitude against Hodges (TW5); a relation with `s₁₃` in place of `s₁₂` fails | M | TW4 |
| PG8 | Lie superalgebras and the four-dimensional supersymmetry algebra: super-Poincaré, massless and massive supermultiplets | the N-extended super-Poincaré algebra is proven a Lie superalgebra (graded Jacobi identity), and its massless supermultiplets are proven to have `2^N` helicity states, from `λ` to `λ + N/2` | N = 1: helicities `(λ, λ + 1/2)`; the N = 8 multiplet has 256 states with helicities from −2 to 2; a wrong sign in `{Q, Q̄} = 2σ·P` shown to break the Jacobi identity | L | HA6 |

### Regge calculus

Folder `Lightlike/Regge/`.

- **Needs:** SF3, GE1 (smooth curvature for RC6), the Regge geodesics (RC4).

| ID | Milestone | Done when | Trust checks | Size | Needs |
|---|---|---|---|---|---|
| RC4 | 3D Regge calculus: deficit angles and the Regge action on a triangulation | below | below | M | GE9 |
| RC5 | 4D Regge calculus: 4-simplex geometry, deficit angles, the Regge action | below | below | M | RC4, SF3 |
| RC6 | Regge calculus converges to the Einstein–Hilbert action (Cheeger–Müller–Schrader) | below | below | L (dim 2), R (all dims) | GE1 or the coordinate curvature of GE9 |
| RC1 | Lorentzian Regge calculus (Sorkin 1975) | `lorDeficit` and `lorReggeAction` are defined, and the action is stationary under boundary-fixed edge-length variations iff `Σ ∂A_t/∂L_e · ε_t = 0` at every interior edge | a flat Lorentzian triangulation has zero deficits; Euclidean angles on Lorentzian data shown wrong | M | RC5 |
| RC2 | Area Regge calculus (Barrett–Roček–Williams 1999) | the area-to-length map of a 4-simplex and its local invertibility | the Jacobian is invertible at the regular 4-simplex; a configuration where areas do not determine lengths | S | RC5 |
| RC3 | Linearized Regge calculus converges to linearized gravity (Roček–Williams 1981; Christiansen 2011) | convergence of solutions in the finite-element setting of Christiansen | flat background gives zero; a non-fat refinement shown to fail | R | RC5, GE1 |

- **RC4, done when:** the deficit angle is 0 at every interior edge of a geometric triangulation in
  3-dimensional Euclidean space; it is positive on the boundary of the 4-simplex; and the
  exterior-angle and face-angle formulas (wrong ones) give a non-zero deficit on the flat cube.
- **RC5, done when:** as RC4, in 4D.
- **RC6, target:** the literal Cheeger–Müller–Schrader statement, with geodesic
  edge lengths. RC6a first provides geodesics, the exponential map and the distance expansion in a
  chart (none of them is in Mathlib); RC6b proves the convergence.
- **RC6, done when:** for a smooth compact Riemannian manifold and fat triangulations with mesh
  going to zero, the Regge curvature measures converge to the scalar-curvature measure
  (Cheeger–Müller–Schrader, *Commun. Math. Phys.* 92 (1984) 405), in dimension 2 at least and in
  every dimension if the proof allows. Uses smooth curvature from connections (GE1)
  or the coordinate curvature of GE9. Trust checks: flat triangulations give zero curvature
  measure; the round 2-sphere gives `4π` (the deficit angles sum to `½∫R dA = 2πχ`); a curvature density without the volume weights fails to
  converge.

### Spin foams

A spin foam model assigns amplitudes to labellings of a fixed 2-complex (dual to a triangulation) by group representations and intertwiners, and sums over the labels.

- **Needs:** PL topology (PL), recoupling and SU(2)/Spin(4) representations (HA4, SF4, SF5a),
  harmonic analysis (HA1, HA2), oscillatory asymptotics (SP1, SP2), quantum groups (QU), Regge
  calculus (RC4, RC5).

| ID | Milestone | Size | Needs |
|---|---|---|---|
| SF3 | 4D combinatorics: 4-complexes, 4-simplices, boundary data, orientation, 4D Pachner moves as operations | M | - |
| SF4 | 15j symbols and 4-valent intertwiners from 3j/6j symbols, with orthogonality | M | HA4 |
| SF4b | The recoupling identities behind the 4D Pachner invariance of the Ooguri model (3-3, 2-4, 1-5) | L | SF4 |
| SF5a | Representations of Spin(4) = SU(2) × SU(2), built from the existing SU(2) work | M | HA4 |
| SF5b | The 4D SU(2) BF (Ooguri) model and its invariance under the 4D Pachner moves | L | SF3, SF4b |
| SF5c | EPRL kinematics: the EPRL map `V_j → V_{j₊} ⊗ V_{j₋}`, fusion coefficients, simplicity for `0 < γ < 1` | M | SF5a |
| SF5d | Gauge fixing and regularization of the Ooguri model (the 4D analogue of Freidel–Louapre) | L | SF5b |
| SF5e | Coherent states of SU(2) and Spin(4); Livine–Speziale coherent intertwiners | M | SF5a |
| SF6 | The Euclidean EPRL vertex amplitude with fusion coefficients (Immirzi parameter `γ < 1`) | L | SF5c |
| SF6b | The EPRL state sum: face and edge amplitudes and the full amplitude on a 4-complex | M | SF6, SF5b |
| SF7 | The Lorentzian EPRL vertex amplitude (`ρ = γ(j+1)`, `k = j`) and its finiteness | L | HA2, SF5c |
| SF8 | The Ponzano–Regge asymptotic formula for the 6j symbol (equivalent to Roberts' Theorem 1 via his §6.1) | R | SP2 |
| SF9 | EPRL vertex asymptotics: the Regge action of the 4-simplex (Barrett et al.) | R | SF5e, SF6, RC5, SP1 |
| SF10 | Lorentzian EPRL vertex asymptotics (Barrett et al. 2010) | R | SF7, SP1 |
| SF1 | The Barrett–Crane model (Barrett–Crane 1998) | M | SF5a, SF5b |
| SF2 | A criterion for when the spin cut-off of the Ponzano–Regge amplitude can be removed | R | SF5d, HA2 |

- **SF3, done when:** the definitions above are in place with their basic properties, such as the
  face counts and Euler characteristic of the simplex and its boundary, the closedness of the
  boundary, and what each move does to these; invariance proofs under the Pachner moves are not
  required yet. Trust checks: the face counts
  of a 4-simplex and of its boundary, and a malformed move shown not to produce a valid complex.
- **SF4, done when:** 15j symbols and 4-valent intertwiners are defined from 3j/6j symbols and
  their orthogonality is proven. Trust checks: known 15j values or reduction identities from the
  literature.
  Also proven, for all spins: the orthogonality of the 15j symbol itself and the identity between
  the contraction of ten 3j symbols and the 15j symbol.
- **SF4b, done when:** the identities that make the Ooguri state sum invariant under the 3-3, 2-4
  and 1-5 moves of `Complex4` (the 4D analogues of Biedenharn–Elliott and orthogonality for the
  6j) are proven as identities of sums of 15j symbols, and they are used to prove the invariance of
  the gauge-fixed finite-cutoff Ooguri state sum under these moves. Trust checks: numerical
  verification for small spins, and a perturbed 15j shown
  to violate the 3-3 identity.
- **SF5a, done when**: the irreducible representations of Spin(4) are defined as
  tensor products of two SU(2) representations, with unitarity, irreducibility and dimension
  `(2j₊+1)(2j₋+1)`.
- **SF5b, done when:** the Ooguri model's amplitude is stated on a 4-complex and its invariance
  under the 3-3, 2-4, 4-2, 1-5 and 5-1 moves is proven for the gauge-fixed finite-cutoff amplitude,
  with the cutoff and gauge hypotheses stated explicitly, using the identities of SF4b. Trust
  checks: values on the boundary of the 5-simplex, and a wrong vertex amplitude shown to break the 3-3 invariance.
- **SF5c, done when:** for `0 < γ < 1` the labels `j± = |1 ± γ| j / 2` and their admissible set,
  the EPRL map as the isometric, SU(2)-equivariant embedding of `V_j` into `V_{j₊} ⊗ V_{j₋}`, its
  action on 4-valent intertwiners (fusion coefficients) and the weak linear simplicity constraint
  on its image are proven. Trust checks: fusion coefficients against published values, and a
  non-EPRL label assignment shown to violate the constraint.
- **SF5d, done when:** a gauge fixing of the Ooguri state sum (fixed spins on a set of triangles
  chosen by a combinatorial rule, the 4D analogue of Freidel–Louapre's maximal tree) is defined, the
  gauge-fixed amplitude is proven invariant under the five 4D Pachner moves under explicit cutoff
  and gauge-rule hypotheses, and independent of the gauge choice for gauge sets that force every
  triangle (or each other); the failure for other sets need not be proven. The general case
  (non-forcing gauge sets) is an open research question, recorded under G2-023. Trust checks: the
  boundary of the 5-simplex, and a gauge set violating the hypotheses shown to change the amplitude.
- **SF5e, done when:** Perelomov coherent states of SU(2) and Spin(4) and the Livine–Speziale
  coherent intertwiners are defined, with their overlap formula and the resolution of the identity
  on the invariant subspace proven. Trust checks: the norm of a coherent intertwiner from its
  normals, and normals that do not close giving the suppression expected in the literature.
- **SF6, done when:** the EPRL vertex amplitude (built on SF5c) is stated, and these are proven:
  selection rules, the value at zero spins, the BF-limit value, reality and the 9j form. Trust
  checks: values against published numerics where available, and a wrong simplicity constraint shown
  to give a different result.
- **SF6b, done when:** the EPRL state sum on a closed 4-complex (the vertex amplitude of SF6, a
  stated face amplitude and the edge normalizations) is defined, with its basic properties (its
  stated dependence on the vertex order) and its relation to the Ooguri model at the BF point stated
  and proven: at `γ = 1` the EPRL amplitude equals the Ooguri amplitude on the same complex and
  cutoffs, up to the stated sign twist and normalisation, written out. Trust checks: on a small
  closed 4-complex at low spins, the state sum computed in Lean equals the Ooguri amplitude at the
  BF point; a wrong face amplitude shown to break that equality.
- **SF7, done when:** the Lorentzian EPRL vertex amplitude is defined as in Engle–Pereira–Rovelli–Livine
  2008 (`ρ = γ(j+1)`, `k = j`, with the `ε` twist on the bra legs for SU(2)-invariant intertwiners)
  and proven finite for all `γ`, spins and intertwiners (Engle–Pereira 2009).
- **SF8, done when:** `PR.PonzanoReggeFormula` (`PonzanoRegge/Asymptotics.lean`) is proven
  (Roberts, *Geom. Topol.* 3 (1999) 21). Trust checks: the numerical comparison already in the
  repository, and the wrong phase shown to fail.
- **SF9, done when:** `Asymptotics.EPRL.EPRLAsymptoticFormula` (`Asymptotics/EPRL/Formula.lean`),
  the large-spin asymptotics of the Euclidean EPRL vertex amplitude governed by the Regge action of
  the 4-simplex, is proven together with its 15j form `Coh15jAsymptoticFormula`, and the coherent
  integral it uses is shown equal to `eprlVertex` on Livine–Speziale intertwiners (Barrett et al.,
  *J. Math. Phys.* 50 (2009) 112504), using SF5c, SF5e (coherent intertwiners), SF6, RC5 and SP1.
  Trust checks: the numerical comparison with the exact integral at the regular 4-simplex already
  in the repository; spins not proportional to the areas, or with an odd sum at a node, shown to
  violate the hypotheses; boundary data that do not glue shown to be exponentially suppressed.
- **SF10, done when:** the large-spin asymptotics of the Lorentzian EPRL vertex amplitude is proven
  (Barrett, Dowdall, Fairbairn, Hellmann, Pereira, *Class. Quantum Grav.* 27 (2010) 165009), using
  SF7, SF5e and SP1. Trust checks: against published numerics of the Lorentzian vertex, and a
  boundary state with normals that do not close shown to be suppressed.
- **SF1, done when:** the Barrett–Crane vertex is defined from the simple representations
  `j₊ = j₋` of Spin(4) and the Barrett–Crane intertwiner, and the Barrett–Crane intertwiner is
  proven to be, up to scale, the unique Spin(4)-invariant vector in the tensor product of four simple
  representations `(j_i, j_i)` satisfying the hypotheses of Reisenberger's theorem (Reisenberger
  1999; the hypotheses stated in the docstring). Trust checks: published 10j values; a non-simple representation
  shown to violate the constraint.
- **SF2, done when:** a general criterion for when the spin cut-off can be removed
  (Barrett–Naish-Guzman; needs harmonic analysis on SU(2)) is proven. Proven: the cutoff is irrelevant when the gauge set
  forces every edge, and it cannot be removed for the ring of three tetrahedra, which is not a
  3-manifold; for closed combinatorial 3-manifolds the question is open.

### String theory

Folder `Lightlike/Strings/`: worldsheet CFT, perturbative amplitudes,
compactifications and dualities.

- **Needs:** CF1–CF5, FT5, GE5, Mathlib Gamma and Beta functions, Mathlib algebraic geometry.

| ID | Milestone | Done when | Trust checks | Size | Needs |
|---|---|---|---|---|---|
| ST1 | Classical strings: Nambu–Goto and Polyakov, conformal gauge, Virasoro constraints | the two actions are equivalent on shell; mode expansion in conformal gauge | rotating open string `J = α'E²`; a non-conformal gauge does not give free wave equations | M | - |
| ST2 | The critical dimension from BRST (Kato–Ogawa 1983) | `Q² = 0` iff `D = 26` (bosonic) or `D = 10` (superstring) | the ghost central charges of CF2; `D = 25` shown to give `Q² ≠ 0` | M | CF2, FT5 |
| ST3 | Light-cone quantization (Goddard–Goldstone–Rebbi–Thorn 1973) | Lorentz invariance of the light-cone open string requires `D = 26` and intercept 1 | the ground-state energy `−(D−2)/24` from `ζ(−1) = −1/12`; `D = 25` breaks `[M^{i−}, M^{j−}] = 0` | L | CF1 |
| ST4 | The no-ghost theorem (Goddard–Thorn 1972; Brower 1972) | physical states have non-negative norm for `D ≤ 26` | norms at levels 1 and 2 at `D = 26`; a negative-norm physical state at level 2 for `D > 26` | L | CF1 |
| ST5 | Tree amplitudes: Veneziano (1968), Virasoro–Shapiro (1969–70) | the worldsheet integrals equal the Gamma-function ratios; poles and residues | `s ↔ t` symmetry; the residue at the first massive pole a polynomial of degree 2 in `t`; a wrong intercept shown to break crossing | M | Mathlib Gamma |
| ST6 | The GSO projection (1977) and spacetime supersymmetry | equal boson and fermion counts at every level, from `θ₃⁴ − θ₄⁴ − θ₂⁴ = 0` | the first levels; the unprojected theory has a tachyon | M | CF4 |
| ST7 | Toroidal compactification: T-duality (Kikkawa–Yamasaki 1984), Narain lattices (1986) | the spectrum invariant under `R ↔ α'/R`; Narain lattices even and self-dual | extra massless states at `R = √α'`; an odd lattice breaks modular invariance | M | CF4 |
| ST8 | Calabi–Yau data: the quintic threefold; Yau's theorem (1978) stated | Hodge numbers `(h¹¹, h²¹) = (1, 101)`, `χ = −200` | the sextic in ℙ⁴ (not Calabi–Yau) shown to have `c₁ ≠ 0` | L | Mathlib algebraic geometry |
| ST9 | Mirror symmetry for the quintic (Candelas–de la Ossa–Green–Parkes 1991; Givental 1996; Lian–Liu–Yau 1997); homological mirror symmetry for the elliptic curve (Polishchuk–Zaslow 1998) | the genus-0 invariants from the mirror computation | 2875 lines and 609250 conics; a wrong mirror map shown to give non-integers | R | ST8 |
| ST10 | Strominger–Vafa (1996): the microscopic count for 5D extremal black holes | `log d ∼ 2π√(Q₁Q₅N)` from the elliptic genus via Cardy | equal to `A/4G` of the 5D metric; a count without the momentum charge shown to differ | R | CF5, GE6 |
| ST11 | Closed string field theory (Zwiebach 1993) at the algebraic level | the classical BV master equation as `L∞` relations | small-order brackets; a non-cyclic bracket shown to fail | R | FT5 |

### Twistor theory

Folder `Lightlike/Twistors/`.

- **Needs:** Mathlib projective geometry and sheaf cohomology, PG1.

| ID | Milestone | Done when | Trust checks | Size | Needs |
|---|---|---|---|---|---|
| TW1 | Twistor space and the incidence relation (Penrose 1967) | points of complexified Minkowski space as lines in ℙ³; null separation iff the lines meet | timelike-separated points give skew lines | M | Mathlib |
| TW2 | The Penrose transform for zero-rest-mass fields, by contour integrals (Eastwood–Penrose–Wells 1981 for the cohomological form) | contour integrals of homogeneous functions of degree `−2h−2` solve the zero-rest-mass equations | helicity 0 gives the wave equation; a wrong degree fails | L | TW1 |
| TW3 | The Ward correspondence (1977) and the nonlinear graviton (Penrose 1976); Atiyah–Hitchin–Singer (1978) | self-dual Yang–Mills fields correspond to holomorphic bundles on twistor space | the BPST instanton; an anti-self-dual field shown not to | R | TW2, GC1 |
| TW4 | Spinor-helicity and the Parke–Taylor formula via BCFW (Britto–Cachazo–Feng–Witten 2005) | the BCFW recursion with three-point seeds gives `⟨ij⟩⁴/(⟨12⟩⟨23⟩⋯⟨n1⟩)` for all `n` | agreement with Feynman rules at `n = 4, 5`; a shift with a boundary term at large `z` shown to fail | L | Mathlib |
| TW5 | Hodges' formula (2012) for MHV graviton amplitudes | the reduced determinant is independent of the removed rows and columns | agreement with KLT (PG7) at `n = 4, 5` | M | TW4, PG7 |
| TW6 | The amplituhedron (Arkani-Hamed–Trnka 2014); BCFW triangulation for `m = 4` (Even-Zohar–Lakrec–Tessler 2021) | the `m = 2` case's triangulations, then `m = 4` | volumes of small cases; a non-positive configuration lies outside | R | TW4 |

### Other approaches

Folder `Lightlike/OtherApproaches/`. The additions are justified under
[roadmap](../../ROADMAP.md#other-approaches).

| ID | Milestone | Done when | Trust checks | Size | Needs |
|---|---|---|---|---|---|
| OA1 | Hořava–Lifshitz gravity (2009): anisotropic scaling; projectable renormalizability (Barvinsky et al. 2016) | power counting: with `z = 3` in 3+1 dimensions the couplings are dimensionless | `z = 1` gives `[G] = −2`; `z = 2` is not enough | S (power counting), R (renormalizability) | FT1 |
| OA2 | Analogue gravity: the acoustic metric (Unruh 1981; Visser 1998) | perturbations of an irrotational barotropic inviscid flow satisfy the wave equation of the acoustic metric; acoustic horizons and their surface gravity | the draining bathtub; a rotational flow shown not to reduce to a metric | M | GE1 |
| OA3 | Induced gravity (Sakharov 1967) | the one-loop effective action of a matter field has an Einstein–Hilbert term with the coefficient from `a₁` | the scalar's `a₁ = R/6`; a conformally coupled scalar shown to cancel it | M | GE8 |
| OA4 | Causal fermion systems (Finster 2010) | existence of minimizers of the causal action in the finite-dimensional setting | small explicit minimizers; a non-compact constraint set without minimizers | L | Mathlib measure theory |
