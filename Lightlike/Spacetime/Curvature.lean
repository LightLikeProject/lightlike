module

public import Lightlike.Spacetime.Minkowski

/-!
# Curvature in local coordinates; Minkowski space is flat

Mathlib (v4.35) has a Levi-Civita connection for *Riemannian* (positive definite) metrics, but no
curvature tensor and nothing for indefinite metrics. We therefore work in **local coordinates**,
which is how curvature is computed in every GR textbook:

* a *coordinate metric* is a matrix-valued function `g : ℝⁿ → Matrix (Fin n) (Fin n) ℝ`
  (the components `g_{μν}(x)` in a chart);
* `christoffel`, `riemann`, `ricci`, `scalarCurvature` are the standard coordinate formulas
  (Carroll, *Spacetime and Geometry*, eqs. 3.27, 3.67, 3.89, 3.91), with partial derivatives
  given by Mathlib's Fréchet derivative `fderiv`.
* `LorentzianMetric.coordMetric g x₀` extracts the coordinate components of a manifold-level
  `LorentzianMetric` in the preferred chart of `M` at `x₀`.

**What is *not* proved here:** that these coordinate expressions transform as tensors under a change
of chart. For Minkowski space this does not matter for the flatness statement below, because the
model-space atlas consists of a single chart (the identity), so "the Riemann tensor vanishes in
every chart of the atlas" is literally what `minkowski_flat` states.
-/

@[expose] public section

open Matrix Manifold
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- Partial derivative `∂_k f (x)` of a scalar function on `ℝⁿ`. -/
def pd (k : Fin n) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single k 1)

/-- Christoffel symbols of the second kind
`Γ^i_{jk} = ½ gⁱˡ (∂_j g_{lk} + ∂_k g_{lj} − ∂_l g_{jk})`. -/
def christoffel (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (i j k : Fin n)
    (x : Fin n → ℝ) : ℝ :=
  (1 / 2) * ∑ l, (g x)⁻¹ i l *
    (pd j (fun y => g y l k) x + pd k (fun y => g y l j) x - pd l (fun y => g y j k) x)

/-- Riemann tensor `R^ρ_{σμν} = ∂_μ Γ^ρ_{νσ} − ∂_ν Γ^ρ_{μσ} + Γ^ρ_{μλ}Γ^λ_{νσ} − Γ^ρ_{νλ}Γ^λ_{μσ}`. -/
def riemann (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (ρ σ μ ν : Fin n)
    (x : Fin n → ℝ) : ℝ :=
  pd μ (christoffel g ρ ν σ) x - pd ν (christoffel g ρ μ σ) x +
    ∑ l, (christoffel g ρ μ l x * christoffel g l ν σ x -
      christoffel g ρ ν l x * christoffel g l μ σ x)

/-- Ricci tensor `R_{σν} = R^ρ_{σρν}`. -/
def ricci (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (σ ν : Fin n) (x : Fin n → ℝ) : ℝ :=
  ∑ ρ, riemann g ρ σ ρ ν x

/-- Scalar curvature `R = g^{σν} R_{σν}`. -/
def scalarCurvature (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ σ, ∑ ν, (g x)⁻¹ σ ν * ricci g σ ν x

/-! ## Coordinate metrics on an open domain

Lean is a total language: `(g x)⁻¹` is the **zero matrix** when `g x` is singular, `a / 0 = 0`, and
`fderiv` is `0` wherever a function is not differentiable. Curvature formulas therefore return
*junk values* (not errors) on degenerate or non-smooth input, and a statement like "the Riemann
tensor vanishes" can be true for meaningless reasons (e.g. for `g = 0`).

All curvature *predicates* below therefore require `IsCoordMetric g U`: `U` open, and on `U` the
matrix `g` is symmetric, invertible, with smooth (`C^∞`) components. Pure formula identities (e.g.
antisymmetry of `riemann` in its last two indices) are stated without these hypotheses because they
hold for every input. -/

/-- `g` is a **coordinate metric on the open set `U`**: smooth, symmetric and invertible on `U`.
(Signature is not part of this predicate; Lorentzian signature is imposed separately where needed.) -/
structure IsCoordMetric (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (U : Set (Fin n → ℝ)) :
    Prop where
  isOpen : IsOpen U
  symm : ∀ x ∈ U, (g x)ᵀ = g x
  isUnit_det : ∀ x ∈ U, IsUnit (g x).det
  smooth : ∀ i j, ContDiffOn ℝ ∞ (fun y => g y i j) U

/-- `g` has **Lorentzian signature on `U`**: a coordinate metric on `U` that at every point is
congruent to `η` (`g x = Pᵀ η P` with `P` invertible) - the coordinate form of "admits a Lorentz
frame". -/
def IsLorentzianCoordMetric (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (U : Set (Fin n → ℝ)) :
    Prop :=
  IsCoordMetric g U ∧ ∀ x ∈ U, ∃ P : Matrix (Fin n) (Fin n) ℝ, IsUnit P.det ∧ g x = Pᵀ * eta n * P

/-- `g` is **flat on `U`**: a coordinate metric on `U` whose Riemann tensor vanishes on `U`. -/
def IsFlatOn (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (U : Set (Fin n → ℝ)) : Prop :=
  IsCoordMetric g U ∧ ∀ x ∈ U, ∀ ρ σ μ ν, riemann g ρ σ μ ν x = 0

/-- A diagonal matrix-valued function with smooth, nonvanishing entries on an open `U` is a
coordinate metric on `U`. -/
lemma isCoordMetric_diagonal (d : (Fin n → ℝ) → Fin n → ℝ) {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    (hd : ∀ i, ContDiffOn ℝ ∞ (fun y => d y i) U) (hne : ∀ x ∈ U, ∀ i, d x i ≠ 0) :
    IsCoordMetric (fun y => Matrix.diagonal (d y)) U where
  isOpen := hU
  symm _ _ := Matrix.diagonal_transpose _
  isUnit_det x hx := by
    rw [Matrix.det_diagonal]
    exact (Finset.prod_ne_zero_iff.mpr fun i _ => hne x hx i).isUnit
  smooth i j := by
    by_cases h : i = j
    · subst h; simpa [Matrix.diagonal_apply_eq] using hd i
    · simpa [Matrix.diagonal_apply_ne _ h] using (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ => (0 : ℝ)) U)

/-! ## Constant metrics are flat -/

lemma pd_const (k : Fin n) (c : ℝ) (x : Fin n → ℝ) : pd k (fun _ => c) x = 0 := by
  simp [pd]

/-- The Christoffel symbols of a constant metric vanish. -/
lemma christoffel_const (G : Matrix (Fin n) (Fin n) ℝ) (i j k : Fin n) :
    christoffel (fun _ => G) i j k = fun _ => 0 := by
  funext x
  simp [christoffel, pd_const]

/-- The Riemann tensor of a constant matrix vanishes. This is a pure formula fact and holds even
for degenerate `G` - which is exactly why `IsFlatOn` also demands `IsCoordMetric`. -/
lemma riemann_const (G : Matrix (Fin n) (Fin n) ℝ) (ρ σ μ ν : Fin n) (x : Fin n → ℝ) :
    riemann (fun _ => G) ρ σ μ ν x = 0 := by
  simp [riemann, christoffel_const, pd_const]

/-- A constant symmetric invertible matrix is a coordinate metric on all of `ℝⁿ`. -/
lemma isCoordMetric_const {G : Matrix (Fin n) (Fin n) ℝ} (hsym : Gᵀ = G) (hdet : IsUnit G.det) :
    IsCoordMetric (fun _ => G) Set.univ :=
  ⟨isOpen_univ, fun _ _ => hsym, fun _ _ => hdet, fun _ _ => contDiffOn_const⟩

/-- **Any constant symmetric invertible metric is flat** on `ℝⁿ`. -/
theorem isFlatOn_const {G : Matrix (Fin n) (Fin n) ℝ} (hsym : Gᵀ = G) (hdet : IsUnit G.det) :
    IsFlatOn (fun _ => G) Set.univ :=
  ⟨isCoordMetric_const hsym hdet, fun x _ ρ σ μ ν => riemann_const G ρ σ μ ν x⟩

/-- If the Riemann tensor vanishes at `x`, so does the Ricci tensor. -/
lemma ricci_eq_zero_of_riemann_eq_zero {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    {x : Fin n → ℝ} (h : ∀ ρ σ μ ν, riemann g ρ σ μ ν x = 0) (σ ν : Fin n) :
    ricci g σ ν x = 0 :=
  Finset.sum_eq_zero fun _ _ => h _ _ _ _

/-- If the Riemann tensor vanishes at `x`, so does the scalar curvature. -/
lemma scalarCurvature_eq_zero_of_riemann_eq_zero {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    {x : Fin n → ℝ} (h : ∀ ρ σ μ ν, riemann g ρ σ μ ν x = 0) : scalarCurvature g x = 0 := by
  simp [scalarCurvature, ricci_eq_zero_of_riemann_eq_zero h]

/-! ## Coordinate components of a manifold-level Lorentzian metric -/

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]

/-- The components `g_{ij}(y) = g(∂ᵢ, ∂ⱼ)` of a Lorentzian metric in the preferred chart of `M`
at `x₀`, where `∂ᵢ` is the coordinate vector field: the image of the standard basis vector `eᵢ`
under the derivative of the inverse chart. Defined for all `y : ℝⁿ`; meaningful on the chart's
target. -/
def LorentzianMetric.coordMetric (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) (x₀ : M)
    (y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    g.g ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)
      (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y
        (Pi.single i 1))
      (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y
        (Pi.single j 1))

/-- In the (only) chart of Minkowski space, the metric components are the constant matrix `η`. -/
theorem minkowski_coordMetric (x₀ : Fin n → ℝ) :
    (minkowskiMetric n).coordMetric x₀ = fun _ => eta n := by
  funext y
  ext i j
  have hd : ∀ v : Fin n → ℝ, mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ)
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y v = v := fun v => by
    rw [extChartAt_model_space_eq_id]; simp; rfl
  show minkowskiForm n _ _ = _
  rw [hd, hd]
  exact minkowskiForm_single i j

/-- `det η` is a unit (`η² = 1`). -/
lemma eta_isUnit_det (n : ℕ) : IsUnit (eta n).det :=
  IsUnit.of_mul_eq_one (b := (eta n).det) (by rw [← Matrix.det_mul, eta_mul_eta, Matrix.det_one])

/-- Minkowski space's chart components form a coordinate metric on all of `ℝⁿ`. -/
theorem minkowski_isCoordMetric (x₀ : Fin n → ℝ) :
    IsCoordMetric ((minkowskiMetric n).coordMetric x₀) Set.univ := by
  rw [minkowski_coordMetric]
  exact isCoordMetric_const (eta_transpose n) (eta_isUnit_det n)

/-- **Minkowski space is flat**: in its chart, `η` is a coordinate metric on all of `ℝⁿ` and its
Riemann tensor vanishes everywhere. -/
theorem minkowski_flat (x₀ : Fin n → ℝ) :
    IsFlatOn ((minkowskiMetric n).coordMetric x₀) Set.univ := by
  rw [minkowski_coordMetric]
  exact isFlatOn_const (eta_transpose n) (eta_isUnit_det n)

end Lightlike
