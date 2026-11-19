module

public import Lightlike.Spacetime.Curvature
public import Lightlike.GR.Einstein

/-!
# Coordinate curvature within a set (GE11, corners)

The coordinate formulas of `Curvature.lean` take derivatives on the whole space, `pd k f x = fderiv ℝ f x (e_k)`. In a chart of a
manifold with corners the chart image is a subset `range I` of the model space with nonempty interior and unique differentiability,
and a function defined on it is differentiated within it. This file states the same coordinate formulas with derivatives within a set
`S` (`pdW S`, `christoffelW S`, `riemannW S`, `ricciW S`, `scalarCurvatureW S`) and proves that for `S = univ` they are the formulas of
`Curvature.lean`. The calculus of these formulas (symmetries, the contracted Bianchi identity) within `range I` is the content of the
corners version of the chart-agreement files.

`IsCoordMetricW S g U` is the coordinate-metric predicate for a set `S` with unique differentiability (every point of `S` in the closure
of its interior, as for `range I`) and `U` relatively open in `S`; `IsCoordMetric.toW` shows the boundaryless predicate is the case `S = univ`.

**Limits.** Definitions, the comparison with the formulas of `Curvature.lean`, and the predicate; the symmetries are in `RiemannSymmetry.lean`.
-/

@[expose] public section

open Set
open scoped Manifold ContDiff Matrix

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- Partial derivative `∂_k f (x)` of a scalar function within `S`. -/
def pdW (S : Set (Fin n → ℝ)) (k : Fin n) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  fderivWithin ℝ f S x (Pi.single k 1)

/-- Christoffel symbols of the second kind with derivatives within `S`. -/
def christoffelW (S : Set (Fin n → ℝ)) (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (i j k : Fin n)
    (x : Fin n → ℝ) : ℝ :=
  (1 / 2) * ∑ l, (g x)⁻¹ i l *
    (pdW S j (fun y => g y l k) x + pdW S k (fun y => g y l j) x - pdW S l (fun y => g y j k) x)

/-- Riemann tensor with derivatives within `S`. -/
def riemannW (S : Set (Fin n → ℝ)) (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (ρ σ μ ν : Fin n)
    (x : Fin n → ℝ) : ℝ :=
  pdW S μ (christoffelW S g ρ ν σ) x - pdW S ν (christoffelW S g ρ μ σ) x +
    ∑ l, (christoffelW S g ρ μ l x * christoffelW S g l ν σ x -
      christoffelW S g ρ ν l x * christoffelW S g l μ σ x)

/-- Ricci tensor with derivatives within `S`. -/
def ricciW (S : Set (Fin n → ℝ)) (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (σ ν : Fin n) (x : Fin n → ℝ) : ℝ :=
  ∑ ρ, riemannW S g ρ σ ρ ν x

/-- Scalar curvature with derivatives within `S`. -/
def scalarCurvatureW (S : Set (Fin n → ℝ)) (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ σ, ∑ ν, (g x)⁻¹ σ ν * ricciW S g σ ν x

theorem pdW_univ (k : Fin n) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : pdW univ k f x = pd k f x := by
  simp [pdW, pd, fderivWithin_univ]

theorem christoffelW_univ (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (i j k : Fin n) (x : Fin n → ℝ) :
    christoffelW univ g i j k x = christoffel g i j k x := by
  simp only [christoffelW, christoffel, pdW_univ]

theorem riemannW_univ (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (ρ σ μ ν : Fin n) (x : Fin n → ℝ) :
    riemannW univ g ρ σ μ ν x = riemann g ρ σ μ ν x := by
  have : (christoffelW univ g : Fin n → Fin n → Fin n → (Fin n → ℝ) → ℝ) = christoffel g := by
    funext i j k x; exact christoffelW_univ g i j k x
  simp only [riemannW, riemann, pdW_univ, this]

theorem ricciW_univ (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (σ ν : Fin n) (x : Fin n → ℝ) :
    ricciW univ g σ ν x = ricci g σ ν x := by
  simp only [ricciW, ricci, riemannW_univ]

theorem scalarCurvatureW_univ (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    scalarCurvatureW univ g x = scalarCurvature g x := by
  simp only [scalarCurvatureW, scalarCurvature, ricciW_univ]

/-- `g` is a **coordinate metric on `U`, relatively open in `S`**: smooth within `S`, symmetric and invertible on `U`; `S` has unique
differentiability and every point of `S` is in the closure of its interior (true for `range I`), so that derivatives within `S`
are determined and mixed second derivatives within `S` commute. -/
structure IsCoordMetricW (S : Set (Fin n → ℝ)) (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (U : Set (Fin n → ℝ)) : Prop where
  uniqueDiff : UniqueDiffOn ℝ S
  closure : ∀ x ∈ S, x ∈ closure (interior S)
  isRelOpen : ∃ V : Set (Fin n → ℝ), IsOpen V ∧ U = S ∩ V
  symm : ∀ x ∈ U, (g x)ᵀ = g x
  isUnit_det : ∀ x ∈ U, IsUnit (g x).det
  smooth : ∀ i j, ContDiffOn ℝ ∞ (fun y => g y i j) U

/-- A boundaryless coordinate metric is a coordinate metric within the whole space. -/
theorem IsCoordMetric.toW {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}
    (hg : IsCoordMetric g U) : IsCoordMetricW univ g U where
  uniqueDiff := uniqueDiffOn_univ
  closure x _ := by simp
  isRelOpen := ⟨U, hg.isOpen, by simp⟩
  symm := hg.symm
  isUnit_det := hg.isUnit_det
  smooth := hg.smooth

/-- The Einstein tensor with derivatives within `S`. -/
def einsteinTensorW (S : Set (Fin n → ℝ)) (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (μ ν : Fin n)
    (x : Fin n → ℝ) : ℝ :=
  ricciW S g μ ν x - (1 / 2) * scalarCurvatureW S g x * g x μ ν

/-- **Vacuum Einstein equations with cosmological constant `Λ`** for derivatives within `S`, on `U` relatively open in `S`. -/
def IsVacuumSolutionW (S : Set (Fin n → ℝ)) (Λ : ℝ) (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (U : Set (Fin n → ℝ)) : Prop :=
  IsCoordMetricW S g U ∧ ∀ x ∈ U, ∀ μ ν, einsteinTensorW S g μ ν x + Λ * g x μ ν = 0

theorem einsteinTensorW_univ (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (μ ν : Fin n) (x : Fin n → ℝ) :
    einsteinTensorW univ g μ ν x = einsteinTensor g μ ν x := by
  simp only [einsteinTensorW, einsteinTensor, ricciW_univ, scalarCurvatureW_univ]

/-- A boundaryless coordinate metric on `U` is the same as one within the whole space. -/
theorem isCoordMetricW_univ_iff {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)} :
    IsCoordMetricW univ g U ↔ IsCoordMetric g U := by
  refine ⟨fun h => ⟨?_, h.symm, h.isUnit_det, h.smooth⟩, IsCoordMetric.toW⟩
  obtain ⟨V, hV, hU⟩ := h.isRelOpen
  simpa [hU] using hV

/-- The vacuum Einstein equations within the whole space are the boundaryless ones. -/
theorem isVacuumSolutionW_univ_iff {Λ : ℝ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)} :
    IsVacuumSolutionW univ Λ g U ↔ IsVacuumSolution Λ g U := by
  unfold IsVacuumSolutionW IsVacuumSolution
  simp only [einsteinTensorW_univ, isCoordMetricW_univ_iff]

/-- Without boundary the range of the model is the whole space. -/
theorem range_modelWithCornersSelf_eq_univ : range (𝓘(ℝ, Fin n → ℝ)) = univ := by
  simp [modelWithCornersSelf_coe]

theorem pdW_range_self (k : Fin n) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    pdW (range (𝓘(ℝ, Fin n → ℝ))) k f x = pd k f x := by
  rw [range_modelWithCornersSelf_eq_univ, pdW_univ]

theorem christoffelW_range_self (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (i j k : Fin n) (x : Fin n → ℝ) :
    christoffelW (range (𝓘(ℝ, Fin n → ℝ))) g i j k x = christoffel g i j k x := by
  rw [range_modelWithCornersSelf_eq_univ, christoffelW_univ]

end Lightlike
