import Lightlike.Rows.G2_015.Algebra

/-!
# Non-vacuity tests for the diffeomorphism action (row G2-015)

The translation `x ↦ x + c` is a `C¹` diffeomorphism; it acts on a connection by `A ↦ A(· + c)`, on a flux field by
`E ↦ E(· + c)`, and the generators of the algebra are moved to the translated edges.
-/

open Matrix Set
open scoped ContDiff

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

noncomputable section

namespace Lightlike.Canonical

/-- The translation by `c` as a `C¹` diffeomorphism of the chart. -/
def translation (c : Fin 3 → ℝ) : Diff where
  equiv := Equiv.addRight c
  smooth := contDiff_id.add contDiff_const
  smooth_symm := contDiff_id.sub contDiff_const

example {n : ℕ} (c : Fin 3 → ℝ) (A : MatConn n) (x : Fin 3 → ℝ) :
    pullConn (translation c) A x = A (x + c) := by
  ext a i j
  simp [pullConn, translation, Pi.single_apply]

example {n : ℕ} (c : Fin 3 → ℝ) (E : Fl n) (x : Fin 3 → ℝ) :
    pullFlux (translation c) E x = E (x + c) := by
  have hj : jac (fun y => y + c) x = 1 := by
    ext a b
    simp [jac, Pi.single_apply, Matrix.one_apply]
  show pullFlux (fun y => y + c) E x = E (x + c)
  ext a i j
  simp [pullFlux, hj, Matrix.one_apply]

/-- The action of a translation moves a holonomy generator to the translated edge. -/
example {n : ℕ} (c : Fin 3 → ℝ) (e : Edge) (i j : Fin n) :
    translation c • FreeAlgebra.ι ℂ (HFGen.hol e i j) =
      FreeAlgebra.ι ℂ (HFGen.hol (e.map (translation c) (translation c).smooth) i j) := by
  rw [Diff.smul_def, Diff.act_ι]; rfl

end Lightlike.Canonical
