import Lightlike.TuraevViro.CraneYetter
import Lightlike.TuraevViro.LevelOne

/-!
# The Crane–Yetter vertex at `r = 3`

At `r = 3` (`q = e^{iπ/3}`, level `1`) the quantum numbers are `[0] = 0`, `[1] = [2] = 1`, `[3] = 0`, the colours are `0, 1`
and every Kauffman–Lins evaluation is `0` or `±1`. This file evaluates the vertex `cyVertexLoc 3` on a nonzero local
colouring, which agrees with the numerical model of the closed form.
-/

open Finset Lightlike.Pentagon

namespace Lightlike.TV

/-- `Δ₀ = 1` at `r = 3`. -/
lemma tlDelta3_zero : tlDelta 3 0 = 1 := by simp [tlDelta, qnum3_one]
/-- `Δ₁ = -1` at `r = 3`. -/
lemma tlDelta3_one : tlDelta 3 1 = -1 := by simp [tlDelta, qnum3_two]

/-- A local colouring: the triangles `034, 134, 234` and the tetrahedra omitting `0, 1, 2` have colour `1`. -/
def J1 : Finset (Fin 5) → ℕ := fun F => if F = {0, 3, 4} ∨ F = {1, 3, 4} ∨ F = {2, 3, 4} then 1 else 0

/-- The tetrahedra omitting `0, 1, 2` have colour `1`, the others `0`. -/
def I1 : Fin 5 → ℕ := ![1, 1, 1, 0, 0]

/-- The admissible triads at `r = 3`. -/
lemma qAdm3_iff {a b c : ℕ} : qAdm 3 a b c ↔ Tri a b c ∧ a + b + c ≤ 2 := by
  unfold qAdm; norm_num

/-- `Tet[1 1 1; 0 0 0] = -1` at `r = 3`. -/
lemma tlTet3_a : tlTet 3 1 1 1 0 0 0 = -1 := by
  norm_num [tlTet, qAdm, Tri, qfact3, Fin.prod_univ_succ]

/-- `Tet[1 0 1; 1 0 1] = -1` at `r = 3`. -/
lemma tlTet3_b : tlTet 3 1 0 1 1 0 1 = -1 := by
  norm_num [tlTet, qAdm, Tri, qfact3, Fin.prod_univ_succ]

/-- `Tet[0 0 1; 1 1 0] = -1` at `r = 3`. -/
lemma tlTet3_c : tlTet 3 0 0 1 1 1 0 = -1 := by
  norm_num [tlTet, qAdm, Tri, qfact3, Fin.prod_univ_succ]

/-- `θ(1, 0, 1) = -1` at `r = 3`. -/
lemma tlTheta3_a : tlTheta 3 1 0 1 = -1 := by
  norm_num [tlTheta, qAdm, Tri, qfact3]

/-- `θ(0, 1, 1) = -1` at `r = 3`. -/
lemma tlTheta3_b : tlTheta 3 0 1 1 = -1 := by
  norm_num [tlTheta, qAdm, Tri, qfact3]

/-- `R^{10}_1 = 1` at `r = 3`. -/
lemma Rbr_three_101 : Rbr 3 1 0 1 = 1 := by
  simp [Rbr]

/-- **The vertex at `r = 3` on a nonzero local colouring**: `-1`, as in the numerical model of the closed form. -/
theorem cyVertexLoc_three_J1 : cyVertexLoc 3 J1 I1 = -1 := by
  have e1 : J1 {2, 3, 4} = 1 := by decide
  have e2 : J1 {1, 2, 3} = 0 := by decide
  have e3 : J1 {0, 1, 2} = 0 := by decide
  have e4 : J1 {0, 1, 4} = 0 := by decide
  have e5 : J1 {0, 3, 4} = 1 := by decide
  have e6 : J1 {1, 2, 4} = 0 := by decide
  have e7 : J1 {1, 3, 4} = 1 := by decide
  have e8 : J1 {0, 1, 3} = 0 := by decide
  have e9 : J1 {0, 2, 3} = 0 := by decide
  have e10 : J1 {0, 2, 4} = 0 := by decide
  unfold cyVertexLoc
  simp [I1, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, Fin.prod_univ_succ, Finset.sum_range_succ, qAdm3_iff, Tri]
  rw [tlDelta3_one, Rbr_three_101, tlTet3_a, tlTet3_b, tlTet3_c, tlTheta3_a, tlTheta3_b]
  norm_num


/-- A local colouring whose vertex is `i`: the triangles `014, 023, 123, 124, 134, 234` and the tetrahedra omitting `1, 4`. -/
def J2 : Finset (Fin 5) → ℕ := fun F =>
  if F = {0, 1, 4} ∨ F = {0, 2, 3} ∨ F = {1, 2, 3} ∨ F = {1, 2, 4} ∨ F = {1, 3, 4} ∨ F = {2, 3, 4} then 1 else 0

/-- The tetrahedra omitting `1, 4` have colour `1`, the others `0`. -/
def I2 : Fin 5 → ℕ := ![0, 1, 0, 0, 1]

/-- `Tet[0 1 1; 0 1 1] = -1` at `r = 3`. -/
lemma tlTet3_d : tlTet 3 0 1 1 0 1 1 = -1 := by
  norm_num [tlTet, qAdm, Tri, qfact3, Fin.prod_univ_succ]

/-- `q^{1/2}` cubed at `r = 3` is `i`. -/
lemma qHalf3_cube : qHalf 3 ^ 3 = Complex.I := by
  unfold qHalf
  rw [← Complex.exp_nat_mul]
  have : ((3 : ℕ) : ℂ) * (Complex.I * Real.pi / (2 * ((3 : ℕ) : ℂ))) = Real.pi / 2 * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_pi_div_two_mul_I]

/-- **The vertex at `r = 3` on a local colouring of value `i`** (the phase `q^{3/2}` and an odd sign), as in the numerical model
of the closed form. -/
theorem cyVertexLoc_three_J2 : cyVertexLoc 3 J2 I2 = Complex.I := by
  have e1 : J2 {2, 3, 4} = 1 := by decide
  have e2 : J2 {1, 2, 3} = 1 := by decide
  have e3 : J2 {0, 1, 2} = 0 := by decide
  have e4 : J2 {0, 1, 4} = 1 := by decide
  have e5 : J2 {0, 3, 4} = 0 := by decide
  have e6 : J2 {1, 2, 4} = 1 := by decide
  have e7 : J2 {1, 3, 4} = 1 := by decide
  have e8 : J2 {0, 1, 3} = 0 := by decide
  have e9 : J2 {0, 2, 3} = 1 := by decide
  have e10 : J2 {0, 2, 4} = 0 := by decide
  unfold cyVertexLoc
  simp [I2, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, Fin.prod_univ_succ, Finset.sum_range_succ, qAdm3_iff, Tri]
  rw [qHalf3_cube, tlDelta3_one, Rbr_three_101, tlTet3_a, tlTet3_b, tlTet3_c, tlTet3_d, tlTheta3_a,
    tlTheta3_b]
  norm_num

end Lightlike.TV
