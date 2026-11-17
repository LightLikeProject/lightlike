import Lightlike.Gauge.Constraints
import Mathlib.LinearAlgebra.Matrix.Rank
import Physlib.Mathematics.Calculus.Gradient

open InnerProductSpace
open ClassicalMechanics
open scoped ContDiff

namespace Lightlike.Gauge

/-- The configuration space of the example: the plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- **The particle on a circle** as a constrained system: the plane with the two constraints
`φ₀ = |q|² - 1` (the particle is on the unit circle) and `φ₁ = ⟨p, q⟩` (its momentum is tangent: the
consistency condition `dφ₀/dt = 0`). -/
noncomputable def circleConstraints : Fin 2 → Plane → Plane → ℝ := fun a p q =>
  if a = 0 then ⟪q, q⟫_ℝ - 1 else ⟪p, q⟫_ℝ

/-- The bracket matrix of the circle constraints at `(p, q)`: `{φ₀, φ₁} = 2 |q|²`. -/
theorem circle_bracketMatrix (p q : Plane) :
    bracketMatrix circleConstraints p q = !![0, 2 * ⟪q, q⟫_ℝ; -(2 * ⟪q, q⟫_ℝ), 0] := by
  have h00 : HasGradientAt (fun p' : Plane => circleConstraints 0 p' q) 0 p := by
    simpa [circleConstraints] using (hasGradientAt_const (c := ⟪q, q⟫_ℝ - 1) (x := p))
  have h0q : HasGradientAt (fun q' : Plane => circleConstraints 0 p q') ((2 : ℝ) • q) q := by
    simpa [circleConstraints] using (hasGradientAt_inner_self (F := Plane) q).sub
      (hasGradientAt_const (c := (1 : ℝ)) (x := q))
  have h1p : HasGradientAt (fun p' : Plane => circleConstraints 1 p' q) q p := by
    simpa [circleConstraints] using hasGradientAt_inner_right (F := Plane) q p
  have h1q : HasGradientAt (fun q' : Plane => circleConstraints 1 p q') p q := by
    simpa [circleConstraints] using hasGradientAt_inner_left (F := Plane) p q
  ext a b
  fin_cases a <;> fin_cases b
  · simp [bracketMatrix, poissonBracket_self]
  · show poissonBracket (circleConstraints 0) (circleConstraints 1) p q = 2 * ⟪q, q⟫_ℝ
    rw [poissonBracket_eq_of_hasGradientAt h00 h0q h1p h1q]
    simp [inner_smul_left]
  · show poissonBracket (circleConstraints 1) (circleConstraints 0) p q = -(2 * ⟪q, q⟫_ℝ)
    rw [poissonBracket_eq_of_hasGradientAt h1p h1q h00 h0q]
    simp [inner_smul_right]
  · simp [bracketMatrix, poissonBracket_self]

/-- The constraint surface of the circle: `|q|² = 1` and `⟨p, q⟩ = 0` (the unit tangent bundle, of dimension 2). -/
theorem circle_mem_constraintSet (x : Plane × Plane) :
    x ∈ constraintSet circleConstraints ↔ ⟪x.2, x.2⟫_ℝ = 1 ∧ ⟪x.1, x.2⟫_ℝ = 0 := by
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    simp only [circleConstraints, ↓reduceIte] at h0
    simp only [circleConstraints] at h1
    refine ⟨by linarith, by simpa using h1⟩
  · rintro ⟨h0, h1⟩ a
    fin_cases a
    · have h0' : ‖x.2‖ ^ 2 = 1 := by rwa [← real_inner_self_eq_norm_sq]
      simp [circleConstraints, h0']
    · simpa [circleConstraints] using h1

/-- **Trust check, the particle on a circle: the constraints are second class.** On the constraint surface the
bracket matrix is `!![0, 2; -2, 0]` with determinant `4`. -/
theorem circle_isSecondClass : IsSecondClass circleConstraints := by
  intro x hx
  rw [circle_mem_constraintSet] at hx
  rw [circle_bracketMatrix, hx.1]
  simp [Matrix.det_fin_two_of]

/-- The bracket matrix of the circle has full rank `2` on the surface. -/
theorem circle_bracketRank (x : Plane × Plane) (hx : x ∈ constraintSet circleConstraints) :
    bracketRank circleConstraints x = 2 := by
  have hdet := circle_isSecondClass x hx
  have hu : IsUnit (bracketMatrix circleConstraints x.1 x.2) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  rw [bracketRank, Matrix.rank_of_isUnit _ hu]
  simp

/-- **Trust check: the degrees of freedom of the particle on a circle.** With `n = 2` (a plane), `m = 2`
constraints of bracket rank `r = 2`, the reduced phase space has dimension `2`, that of `T*S¹`. -/
theorem circle_reducedDim : reducedDim 2 2 2 = 2 := by decide

/-- **Wrong-model check: a second-class constraint treated as first class gives the wrong count.** Treating
both circle constraints as first class gives `2·2 - 2·2 = 0` instead of `2`. -/
theorem circle_wrong_count : reducedDimAllFirstClass 2 2 = 0 ∧ reducedDimAllFirstClass 2 2 ≠ reducedDim 2 2 2 := by
  decide

/-- The circle constraints are not first class: on the surface the bracket `{φ₀, φ₁} = 2` does not vanish. -/
theorem circle_not_firstClass : ¬ IsFirstClass circleConstraints := by
  intro h
  have hx : ((0 : Plane), EuclideanSpace.single 0 (1 : ℝ)) ∈ constraintSet circleConstraints := by
    rw [circle_mem_constraintSet]
    simp
  have := h _ hx
  have h01 := congrFun (congrFun this 0) 1
  rw [circle_bracketMatrix] at h01
  simp at h01

end Lightlike.Gauge
