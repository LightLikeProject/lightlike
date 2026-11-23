import Mathlib

/-!
# Bianchi algebras: the bracket `[x, y] = n (x × y) + (a·x) y − (a·y) x` on `ℝ³` (G1-039)

The Ellis–MacCallum parametrisation of a three-dimensional real Lie algebra by a symmetric matrix
`n = (n^{ab})` and a vector `a = (a_c)`: the structure constants are
`γ^c_{ab} = ε_{abd} n^{dc} + δ^c_b a_a − δ^c_a a_b`, i.e. in vector form
`[x, y] = n (x × y) + (a·x) y − (a·y) x`.  The Jacobi identity holds iff `n a = 0`
(`bBracket_jacobi_iff`).  Class A is `a = 0` and class B is `a ≠ 0`.

**Sources.** `heinzle-uggla-2009a`, Section 3 (the Bianchi classification); the parametrisation is
that of Ellis–MacCallum (1969), which is not in `docs/tasks/sources.yaml`, so no location is cited.
-/

open Matrix

namespace Lightlike.Rows.G1_039

/-- The bracket of the Bianchi algebra with data `(n, a)`:
`[x, y] = n (x × y) + (a·x) y − (a·y) x`. -/
def bBracket (n : Matrix (Fin 3) (Fin 3) ℝ) (a : Fin 3 → ℝ) (x y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  n *ᵥ (x ⨯₃ y) + (a ⬝ᵥ x) • y - (a ⬝ᵥ y) • x

/-- The Jacobi sum of the Bianchi bracket. -/
def bJac (n : Matrix (Fin 3) (Fin 3) ℝ) (a : Fin 3 → ℝ) (x y z : Fin 3 → ℝ) : Fin 3 → ℝ :=
  bBracket n a x (bBracket n a y z) + bBracket n a y (bBracket n a z x) +
    bBracket n a z (bBracket n a x y)

theorem bJac_eq (n : Matrix (Fin 3) (Fin 3) ℝ) (hn : n.IsSymm) (a x y z : Fin 3 → ℝ) :
    bJac n a x y z = (-2 * (x ⬝ᵥ (y ⨯₃ z))) • (n *ᵥ a) := by
  have h01 : n 0 1 = n 1 0 := by simpa using (congrFun (congrFun hn 1) 0)
  have h02 : n 0 2 = n 2 0 := by simpa using (congrFun (congrFun hn 2) 0)
  have h12 : n 1 2 = n 2 1 := by simpa using (congrFun (congrFun hn 2) 1)
  funext i
  fin_cases i <;>
  · simp [bJac, bBracket, crossProduct, mulVec, dotProduct, Fin.sum_univ_three, h01, h02, h12]
    ring

/-- **The Jacobi identity of the Bianchi bracket holds iff `n a = 0`** (for symmetric `n`). -/
theorem bBracket_jacobi_iff (n : Matrix (Fin 3) (Fin 3) ℝ) (hn : n.IsSymm) (a : Fin 3 → ℝ) :
    (∀ x y z, bJac n a x y z = 0) ↔ n *ᵥ a = 0 := by
  constructor
  · intro h
    have h1 := h (Pi.single 0 1) (Pi.single 1 1) (Pi.single 2 1)
    rw [bJac_eq n hn] at h1
    have h2 : ((Pi.single 0 1 : Fin 3 → ℝ) ⬝ᵥ ((Pi.single 1 1 : Fin 3 → ℝ) ⨯₃ Pi.single 2 1)) = 1 := by
      simp [crossProduct, dotProduct, Fin.sum_univ_three]
    rw [h2] at h1
    simpa using h1
  · intro h x y z
    rw [bJac_eq n hn, h, smul_zero]

end Lightlike.Rows.G1_039
