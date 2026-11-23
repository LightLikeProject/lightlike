import Mathlib

/-!
# Three-dimensional real Lie algebras in Bianchi form

The Bianchi classification of three-dimensional real Lie algebras writes the structure constants
in a basis `e₁, e₂, e₃` as `C^c_{ab} = ε_{abd} n^{dc} + a_a δ^c_b - a_b δ^c_a`, with a symmetric
matrix `n` and a vector `a` (Ellis–MacCallum form; the same parametrization is used in the
Wainwright–Hsu treatment of Bianchi cosmologies).  On `ℝ³ = Fin 3 → ℝ` the bracket is
`[x, y] = n (x × y) + (a · x) y - (a · y) x`.  The Jacobi identity holds iff `n a = 0`.

## Main definitions

* `Lightlike.Rows.G1_039.bracket`: the bracket attached to `(n, a)`.
* `Lightlike.Rows.G1_039.IsClassA`, `IsClassB`: class A is `a = 0`, class B is `a ≠ 0`.

## Main results

* `Lightlike.Rows.G1_039.jacobi_bracket_eq`: the Jacobi expression equals
  `2 det(x, y, z) • (n a)`.
* `Lightlike.Rows.G1_039.jacobi_bracket_iff`: Jacobi for all arguments iff `n a = 0`.

## References

* heinzle-uggla-2009a (Section 3)
-/

namespace Lightlike.Rows.G1_039

/-- The bracket on `ℝ³` with Bianchi data `(n, a)`:
`[x, y] = n (x × y) + (a · x) y - (a · y) x`. -/
def bracket (n : Matrix (Fin 3) (Fin 3) ℝ) (a : Fin 3 → ℝ) (x y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  n.mulVec (crossProduct x y) + (a ⬝ᵥ x) • y - (a ⬝ᵥ y) • x

/-- Class A: the vector `a` vanishes. -/
def IsClassA (a : Fin 3 → ℝ) : Prop := a = 0

/-- Class B: the vector `a` is non-zero. -/
def IsClassB (a : Fin 3 → ℝ) : Prop := a ≠ 0

/-- The cyclic Jacobi sum of the bracket. -/
def jacobi (n : Matrix (Fin 3) (Fin 3) ℝ) (a : Fin 3 → ℝ) (x y z : Fin 3 → ℝ) : Fin 3 → ℝ :=
  bracket n a (bracket n a x y) z + bracket n a (bracket n a y z) x +
    bracket n a (bracket n a z x) y

theorem jacobi_bracket_eq (n : Matrix (Fin 3) (Fin 3) ℝ) (hn : n.IsSymm) (a x y z : Fin 3 → ℝ) :
    jacobi n a x y z = (2 * (x ⬝ᵥ crossProduct y z)) • n.mulVec a := by
  have h01 : n 1 0 = n 0 1 := by simpa using congrFun (congrFun hn 0) 1
  have h02 : n 2 0 = n 0 2 := by simpa using congrFun (congrFun hn 0) 2
  have h12 : n 2 1 = n 1 2 := by simpa using congrFun (congrFun hn 1) 2
  ext i
  fin_cases i <;>
  simp [jacobi, bracket, crossProduct, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h01, h02, h12] <;>
  ring

/-- The Jacobi identity for all arguments holds iff `n a = 0`. -/
theorem jacobi_bracket_iff (n : Matrix (Fin 3) (Fin 3) ℝ) (hn : n.IsSymm) (a : Fin 3 → ℝ) :
    (∀ x y z, jacobi n a x y z = 0) ↔ n.mulVec a = 0 := by
  constructor
  · intro h
    have := h (Pi.single 0 1) (Pi.single 1 1) (Pi.single 2 1)
    rw [jacobi_bracket_eq n hn] at this
    have h1 : (Pi.single 0 (1 : ℝ) : Fin 3 → ℝ) ⬝ᵥ
        crossProduct (Pi.single 1 (1 : ℝ) : Fin 3 → ℝ) (Pi.single 2 (1 : ℝ)) = 1 := by
      simp [crossProduct, dotProduct, Fin.sum_univ_three]
    rw [h1] at this
    simpa using this
  · intro h x y z
    rw [jacobi_bracket_eq n hn, h, smul_zero]

/-- The bracket is alternating. -/
theorem bracket_self (n : Matrix (Fin 3) (Fin 3) ℝ) (a x : Fin 3 → ℝ) : bracket n a x x = 0 := by
  simp [bracket]

/-- The bracket is bilinear in the first argument. -/
theorem bracket_add_left (n : Matrix (Fin 3) (Fin 3) ℝ) (a x x' y : Fin 3 → ℝ) :
    bracket n a (x + x') y = bracket n a x y + bracket n a x' y := by
  ext i
  simp [bracket, crossProduct, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- The bracket is bilinear in the second argument. -/
theorem bracket_add_right (n : Matrix (Fin 3) (Fin 3) ℝ) (a x y y' : Fin 3 → ℝ) :
    bracket n a x (y + y') = bracket n a x y + bracket n a x y' := by
  ext i
  simp [bracket, crossProduct, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

end Lightlike.Rows.G1_039
