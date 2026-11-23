import Lightlike.Rows.G1_039.Bianchi

/-!
# The Lie algebra `𝔟(n, a)`, class A/B and unimodularity (G1-039)

For data `(n, a)` with `n` symmetric and `n a = 0` the bracket `bBracket n a` makes `ℝ³` a Lie
algebra over `ℝ` (`BianchiAlg d`).  The trace of `ad x` is `2 (a·x)` (`trace_adMat`,
`trace_ad_eq`), so class A (`a = 0`) is exactly the unimodular case (`unimodular_iff_classA`).

**Sources.** `heinzle-uggla-2009a`, Section 3; the parametrisation is that of Ellis–MacCallum
(1969), not in `docs/tasks/sources.yaml`, so no location is cited.
-/

open Matrix

namespace Lightlike.Rows.G1_039

/-- Data `(n, a)` of a Bianchi algebra: `n` symmetric, `a` a vector, with `n a = 0`
(the Jacobi condition, `bBracket_jacobi_iff`). -/
structure BianchiData where
  /-- the symmetric matrix `n` -/
  n : Matrix (Fin 3) (Fin 3) ℝ
  /-- the vector `a` -/
  a : Fin 3 → ℝ
  symm : n.IsSymm
  na : n *ᵥ a = 0

namespace BianchiData

/-- Class A: `a = 0`. -/
def IsClassA (d : BianchiData) : Prop := d.a = 0

/-- Class B: `a ≠ 0`. -/
def IsClassB (d : BianchiData) : Prop := d.a ≠ 0

end BianchiData

theorem bBracket_add_left (n : Matrix (Fin 3) (Fin 3) ℝ) (a x x' y : Fin 3 → ℝ) :
    bBracket n a (x + x') y = bBracket n a x y + bBracket n a x' y := by
  funext i
  fin_cases i <;>
  · simp [bBracket, crossProduct, mulVec, dotProduct, Fin.sum_univ_three]
    ring

theorem bBracket_add_right (n : Matrix (Fin 3) (Fin 3) ℝ) (a x y y' : Fin 3 → ℝ) :
    bBracket n a x (y + y') = bBracket n a x y + bBracket n a x y' := by
  funext i
  fin_cases i <;>
  · simp [bBracket, crossProduct, mulVec, dotProduct, Fin.sum_univ_three]
    ring

theorem bBracket_smul_left (n : Matrix (Fin 3) (Fin 3) ℝ) (a : Fin 3 → ℝ) (t : ℝ) (x y : Fin 3 → ℝ) :
    bBracket n a (t • x) y = t • bBracket n a x y := by
  funext i
  fin_cases i <;>
  · simp [bBracket, crossProduct, mulVec, dotProduct, Fin.sum_univ_three]
    ring

theorem bBracket_smul_right (n : Matrix (Fin 3) (Fin 3) ℝ) (a : Fin 3 → ℝ) (t : ℝ) (x y : Fin 3 → ℝ) :
    bBracket n a x (t • y) = t • bBracket n a x y := by
  funext i
  fin_cases i <;>
  · simp [bBracket, crossProduct, mulVec, dotProduct, Fin.sum_univ_three]
    ring

theorem bBracket_self (n : Matrix (Fin 3) (Fin 3) ℝ) (a x : Fin 3 → ℝ) :
    bBracket n a x x = 0 := by
  simp [bBracket]

theorem bBracket_anti (n : Matrix (Fin 3) (Fin 3) ℝ) (a x y : Fin 3 → ℝ) :
    bBracket n a x y = - bBracket n a y x := by
  funext i
  fin_cases i <;>
  · simp [bBracket, crossProduct, mulVec, dotProduct, Fin.sum_univ_three]
    ring

theorem bBracket_neg_right (n : Matrix (Fin 3) (Fin 3) ℝ) (a x y : Fin 3 → ℝ) :
    bBracket n a x (-y) = - bBracket n a x y := by
  have := bBracket_smul_right n a (-1) x y
  simpa using this

/-- The Leibniz form of the Jacobi identity for the Bianchi bracket when `n a = 0`. -/
theorem bBracket_leibniz (n : Matrix (Fin 3) (Fin 3) ℝ) (hn : n.IsSymm) {a : Fin 3 → ℝ}
    (hna : n *ᵥ a = 0) (x y z : Fin 3 → ℝ) :
    bBracket n a x (bBracket n a y z) =
      bBracket n a (bBracket n a x y) z + bBracket n a y (bBracket n a x z) := by
  have hz : bJac n a x y z = 0 := by rw [bJac_eq n hn, hna, smul_zero]
  unfold bJac at hz
  have e1 : bBracket n a y (bBracket n a z x) = - bBracket n a y (bBracket n a x z) := by
    rw [bBracket_anti n a z x, bBracket_neg_right]
  have e2 : bBracket n a (bBracket n a x y) z = - bBracket n a z (bBracket n a x y) :=
    bBracket_anti _ _ _ _
  rw [e1] at hz
  rw [e2, ← sub_eq_zero, ← hz]
  abel

/-- The Lie algebra of a Bianchi datum: `ℝ³` with the bracket `bBracket`. -/
def BianchiAlg (_d : BianchiData) : Type := Fin 3 → ℝ

namespace BianchiAlg

variable (d : BianchiData)

instance : AddCommGroup (BianchiAlg d) := inferInstanceAs (AddCommGroup (Fin 3 → ℝ))

instance : Module ℝ (BianchiAlg d) := inferInstanceAs (Module ℝ (Fin 3 → ℝ))

instance : Bracket (BianchiAlg d) (BianchiAlg d) :=
  ⟨fun x y => bBracket d.n d.a (show Fin 3 → ℝ from x) (show Fin 3 → ℝ from y)⟩

theorem bracket_def (x y : BianchiAlg d) :
    ⁅x, y⁆ = (bBracket d.n d.a (show Fin 3 → ℝ from x) (show Fin 3 → ℝ from y) :
      Fin 3 → ℝ) := rfl

instance : LieRing (BianchiAlg d) where
  add_lie x y z := bBracket_add_left _ _ _ _ _
  lie_add x y z := bBracket_add_right _ _ _ _ _
  lie_self x := bBracket_self _ _ _
  leibniz_lie x y z := by
    exact bBracket_leibniz d.n d.symm d.na x y z

instance : LieAlgebra ℝ (BianchiAlg d) where
  lie_smul t _ _ := bBracket_smul_right _ _ t _ _

instance : Module.Free ℝ (BianchiAlg d) := inferInstanceAs (Module.Free ℝ (Fin 3 → ℝ))

instance : Module.Finite ℝ (BianchiAlg d) := inferInstanceAs (Module.Finite ℝ (Fin 3 → ℝ))

end BianchiAlg

/-- The matrix of `y ↦ x × y`. -/
def crossMat (x : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -x 2, x 1; x 2, 0, -x 0; -x 1, x 0, 0]

/-- The matrix of `ad x` in the standard basis: `n [x]ₓ + (a·x) 1 − x aᵀ`. -/
def adMat (n : Matrix (Fin 3) (Fin 3) ℝ) (a x : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  n * crossMat x + (a ⬝ᵥ x) • (1 : Matrix (Fin 3) (Fin 3) ℝ) - Matrix.vecMulVec x a

theorem adMat_mulVec (n : Matrix (Fin 3) (Fin 3) ℝ) (a x y : Fin 3 → ℝ) :
    adMat n a x *ᵥ y = bBracket n a x y := by
  funext i
  fin_cases i <;>
  · simp [adMat, crossMat, bBracket, crossProduct, mulVec, dotProduct, Fin.sum_univ_three,
      Matrix.mul_apply, Matrix.vecMulVec_apply]
    ring

/-- **`tr (ad x) = 2 (a·x)`** for symmetric `n`. -/
theorem trace_adMat (n : Matrix (Fin 3) (Fin 3) ℝ) (hn : n.IsSymm) (a x : Fin 3 → ℝ) :
    Matrix.trace (adMat n a x) = 2 * (a ⬝ᵥ x) := by
  have h01 : n 0 1 = n 1 0 := by simpa using (congrFun (congrFun hn 1) 0)
  have h02 : n 0 2 = n 2 0 := by simpa using (congrFun (congrFun hn 2) 0)
  have h12 : n 1 2 = n 2 1 := by simpa using (congrFun (congrFun hn 2) 1)
  simp [adMat, crossMat, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three,
    dotProduct, Matrix.vecMulVec_apply, h01, h02, h12]
  ring

namespace BianchiAlg

variable (d : BianchiData)

/-- The trace of `ad x` on `𝔟(n, a)` is `2 (a·x)`. -/
theorem trace_ad_eq (x : BianchiAlg d) :
    LinearMap.trace ℝ (BianchiAlg d) (LieAlgebra.ad ℝ (BianchiAlg d) x) =
      2 * (d.a ⬝ᵥ (show Fin 3 → ℝ from x)) := by
  have h : LieAlgebra.ad ℝ (BianchiAlg d) x =
      (Matrix.toLin' (adMat d.n d.a (show Fin 3 → ℝ from x)) :
        (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) := by
    refine LinearMap.ext fun y => ?_
    exact (adMat_mulVec d.n d.a _ _).symm
  rw [h]
  have h2 : LinearMap.trace ℝ (BianchiAlg d)
      (Matrix.toLin' (adMat d.n d.a (show Fin 3 → ℝ from x))) =
      LinearMap.trace ℝ (Fin 3 → ℝ) (Matrix.toLin' (adMat d.n d.a (show Fin 3 → ℝ from x))) := rfl
  rw [h2, Matrix.trace_toLin'_eq]
  exact trace_adMat _ d.symm _ _

/-- **Class A is exactly the unimodular case**: `tr (ad x) = 0` for all `x` iff `a = 0`. -/
theorem unimodular_iff_classA :
    (∀ x : BianchiAlg d, LinearMap.trace ℝ (BianchiAlg d) (LieAlgebra.ad ℝ (BianchiAlg d) x) = 0)
      ↔ d.IsClassA := by
  constructor
  · intro h
    have h1 := h (show BianchiAlg d from d.a)
    rw [trace_ad_eq] at h1
    have : d.a ⬝ᵥ d.a = 0 := by
      change 2 * (d.a ⬝ᵥ d.a) = 0 at h1
      linarith
    exact dotProduct_self_eq_zero.mp this
  · intro h x
    rw [trace_ad_eq]
    have h0 : d.a = 0 := h
    have h3 : d.a ⬝ᵥ (show Fin 3 → ℝ from x) = 0 := by
      rw [h0]
      exact zero_dotProduct _
    rw [h3, mul_zero]

end BianchiAlg

end Lightlike.Rows.G1_039
