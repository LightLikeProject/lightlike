import Mathlib

/-!
# Area Regge calculus on a 4-simplex

In area Regge calculus the triangle areas replace the edge lengths as the variables
(Barrett-Rocek-Williams). A 4-simplex has 10 edges and 10 triangles, so the area map
`ℝ¹⁰ → ℝ¹⁰`, from the squared edge lengths to the squared triangle areas, can be locally
invertible. This file proves:

* at the regular simplex (all squared lengths `1`) the Jacobian of the squared-area map is
  invertible (`jac_regular_isUnit`, with an explicit inverse);
* at the corner simplex (`s₀ᵢ = 1`, `sᵢⱼ = 2`) the Jacobian is singular, with an explicit kernel
  vector (`jac_corner_det`), and this is not only a derivative statement: two different valid
  length assignments give the same ten areas (`corner_pair`).

Edges are numbered `01,02,03,04,12,13,14,23,24,34`, triangles
`012,013,014,023,024,034,123,124,134,234`.
-/

open Matrix

namespace Lightlike.AreaRegge

noncomputable section

/-- Heron's formula in squared lengths: the squared area of a triangle with squared edge lengths
`a b c` is `((a+b+c)² - 2(a²+b²+c²)) / 16`. -/
def triAreaSq (a b c : ℝ) : ℝ := ((a + b + c) ^ 2 - 2 * (a ^ 2 + b ^ 2 + c ^ 2)) / 16

/-- The three edges (indices into the list of ten) of each of the ten triangles of a 4-simplex. -/
def triEdges : Fin 10 → Fin 3 → Fin 10 :=
  ![![0, 1, 4], ![0, 2, 5], ![0, 3, 6], ![1, 2, 7], ![1, 3, 8], ![2, 3, 9], ![4, 5, 7],
    ![4, 6, 8], ![5, 6, 9], ![7, 8, 9]]

/-- The squared areas of the ten triangles of a 4-simplex with squared edge lengths `s`. -/
def areaSq (s : Fin 10 → ℝ) (t : Fin 10) : ℝ :=
  triAreaSq (s (triEdges t 0)) (s (triEdges t 1)) (s (triEdges t 2))

/-- The areas of the ten triangles. -/
def area (s : Fin 10 → ℝ) (t : Fin 10) : ℝ := Real.sqrt (areaSq s t)

/-- Partial derivative of `triAreaSq` in its `j`-th slot at the squared lengths `s` of triangle
`t`: `(sum of the other two - this one) / 8`. -/
def slotDeriv (s : Fin 10 → ℝ) (t : Fin 10) (j : Fin 3) : ℝ :=
  ((∑ i, s (triEdges t i)) - 2 * s (triEdges t j)) / 8

/-- The Jacobian `∂ (areaSq s t) / ∂ (s e)` of the squared-area map. -/
def jac (s : Fin 10 → ℝ) : Matrix (Fin 10) (Fin 10) ℝ := fun t e =>
  ∑ j, if triEdges t j = e then slotDeriv s t j else 0

/-- The Jacobian is the derivative of the squared-area map: for a direction `v`, the first-order
change of `areaSq (s + ε v) t` is `ε (jac s *ᵥ v) t`, and the second-order term is
`triAreaSq` of `v` (the formula is quadratic). -/
theorem areaSq_add (s v : Fin 10 → ℝ) (ε : ℝ) (t : Fin 10) :
    areaSq (s + ε • v) t = areaSq s t + ε * (jac s *ᵥ v) t + ε ^ 2 * areaSq v t := by
  fin_cases t
  all_goals
    simp [areaSq, jac, slotDeriv, triEdges, triAreaSq, mulVec, dotProduct, Fin.sum_univ_succ]
    ring

/-- Trust check: a right isoceles triangle with legs `1` (squared hypotenuse `2`) has area `1/2`. -/
theorem triAreaSq_right : triAreaSq 1 1 2 = (1 / 2) ^ 2 := by norm_num [triAreaSq]

/-- Trust check: an equilateral triangle of side `1` has squared area `3/16`. -/
theorem triAreaSq_equilateral : triAreaSq 1 1 1 = 3 / 16 := by norm_num [triAreaSq]

/-- Trust check: a wrong Heron formula (dropping the factor 2) gives a different value. -/
theorem triAreaSq_wrong : ((1 + 1 + 2 : ℝ) ^ 2 - (1 ^ 2 + 1 ^ 2 + 2 ^ 2)) / 16 ≠ (1 / 2) ^ 2 := by
  norm_num

/-! ### Regular simplex -/

/-- The regular simplex: all squared lengths `1`. -/
def sReg : Fin 10 → ℝ := fun _ => 1

/-- The incidence matrix of edges in triangles. -/
def inc : Matrix (Fin 10) (Fin 10) ℤ := fun t e => ∑ j, if triEdges t j = e then 1 else 0

/-- Six times the inverse of the incidence matrix (found with SymPy, verified by `decide`). -/
def incInv6 : Matrix (Fin 10) (Fin 10) ℤ :=
  !![2, 2, 2, -1, -1, -1, -1, -1, -1, 2; 2, -1, -1, 2, 2, -1, -1, -1, 2, -1;
    -1, 2, -1, 2, -1, 2, -1, 2, -1, -1; -1, -1, 2, -1, 2, 2, 2, -1, -1, -1;
    2, -1, -1, -1, -1, 2, 2, 2, -1, -1; -1, 2, -1, -1, 2, -1, 2, -1, 2, -1;
    -1, -1, 2, 2, -1, -1, -1, 2, 2, -1; -1, -1, 2, 2, -1, -1, 2, -1, -1, 2;
    -1, 2, -1, -1, 2, -1, -1, 2, -1, 2; 2, -1, -1, -1, -1, 2, -1, -1, 2, 2]

theorem inc_mul : inc * incInv6 = (6 : ℤ) • (1 : Matrix (Fin 10) (Fin 10) ℤ) := by
  decide +kernel

theorem jac_regular : jac sReg = (1 / 8 : ℝ) • inc.map (Int.cast : ℤ → ℝ) := by
  ext t e
  fin_cases t <;> fin_cases e <;>
    simp only [jac, slotDeriv, Fin.sum_univ_succ, Fin.sum_univ_zero] <;>
    simp only [Matrix.smul_apply, Matrix.map_apply, inc, Fin.sum_univ_succ, Fin.sum_univ_zero] <;>
    simp [sReg, triEdges] <;> norm_num

/-- **The Jacobian of the area map is invertible at the regular 4-simplex.** The explicit inverse
is `8/6` times the integer matrix `incInv6`; the determinant is `-48 / 8¹⁰` (SymPy). -/
theorem jac_regular_isUnit : IsUnit (jac sReg).det := by
  have hm : inc.map (Int.cast : ℤ → ℝ) * incInv6.map (Int.cast : ℤ → ℝ) =
      (6 : ℝ) • (1 : Matrix (Fin 10) (Fin 10) ℝ) := by
    ext i j
    have h := congrArg (fun M : Matrix (Fin 10) (Fin 10) ℤ => (M i j : ℝ)) inc_mul
    simp only [Matrix.mul_apply, Int.cast_sum, Int.cast_mul, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul] at h
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    rw [h]
    split_ifs <;> simp
  have h : jac sReg * ((8 / 6 : ℝ) • incInv6.map (Int.cast : ℤ → ℝ)) = 1 := by
    rw [jac_regular, smul_mul_assoc, mul_smul_comm, hm, smul_smul, smul_smul]
    try norm_num
  exact Matrix.isUnit_det_of_right_inverse h

/-! ### The corner simplex: the wrong model -/

/-- The corner simplex `s₀ᵢ = 1`, `sᵢⱼ = 2` (a valid Euclidean simplex). -/
def sCorner : Fin 10 → ℝ := ![1, 1, 1, 1, 2, 2, 2, 2, 2, 2]

/-- A kernel direction: `+1` on edges `13, 24`, `-1` on `14, 23`. -/
def kCorner : Fin 10 → ℝ := ![0, 0, 0, 0, 0, 1, -1, -1, 1, 0]

/-- The direction `kCorner` lies in the kernel of the Jacobian at the corner point. -/
theorem jac_corner_kernel : jac sCorner *ᵥ kCorner = 0 := by
  ext t
  fin_cases t <;>
    simp [jac, sCorner, kCorner, slotDeriv, triEdges, mulVec, dotProduct, Fin.sum_univ_succ] <;>
    try norm_num

theorem jac_corner_kernel_apply (t : Fin 10) : (jac sCorner *ᵥ kCorner) t = 0 := by
  rw [jac_corner_kernel]; rfl

/-- **The Jacobian of the area map is singular at the corner simplex.** -/
theorem jac_corner_det : (jac sCorner).det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨kCorner, ?_, jac_corner_kernel⟩
  intro h
  have := congrFun h 5
  simp [kCorner] at this

/-- The Gram matrix of the edge vectors from vertex `0`, in terms of the squared lengths:
`G ᵢⱼ = (s₀ᵢ + s₀ⱼ - sᵢⱼ) / 2`. -/
def gram (s : Fin 10 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![s 0, (s 0 + s 1 - s 4) / 2, (s 0 + s 2 - s 5) / 2, (s 0 + s 3 - s 6) / 2;
    (s 0 + s 1 - s 4) / 2, s 1, (s 1 + s 2 - s 7) / 2, (s 1 + s 3 - s 8) / 2;
    (s 0 + s 2 - s 5) / 2, (s 1 + s 2 - s 7) / 2, s 2, (s 2 + s 3 - s 9) / 2;
    (s 0 + s 3 - s 6) / 2, (s 1 + s 3 - s 8) / 2, (s 2 + s 3 - s 9) / 2, s 3]

/-- Squared lengths `s` are those of a nondegenerate Euclidean 4-simplex iff the Gram matrix of the
edge vectors from vertex `0` is positive definite; by Sylvester's criterion, iff its four leading
principal minors are positive. -/
def IsSimplex (s : Fin 10 → ℝ) : Prop :=
  0 < ((gram s).submatrix (Fin.castLE (by omega : 1 ≤ 4)) (Fin.castLE (by omega : 1 ≤ 4))).det ∧
  0 < ((gram s).submatrix (Fin.castLE (by omega : 2 ≤ 4)) (Fin.castLE (by omega : 2 ≤ 4))).det ∧
  0 < ((gram s).submatrix (Fin.castLE (by omega : 3 ≤ 4)) (Fin.castLE (by omega : 3 ≤ 4))).det ∧
  0 < (gram s).det

/-- The two length assignments `s₀ ± ½ k`. -/
def sPlus : Fin 10 → ℝ := ![1, 1, 1, 1, 2, 5 / 2, 3 / 2, 3 / 2, 5 / 2, 2]

/-- The mirror assignment. -/
def sMinus : Fin 10 → ℝ := ![1, 1, 1, 1, 2, 3 / 2, 5 / 2, 5 / 2, 3 / 2, 2]

theorem sPlus_eq : sPlus = sCorner + (1 / 2 : ℝ) • kCorner := by
  ext i; fin_cases i <;> simp [sPlus, sCorner, kCorner] <;> norm_num

theorem sMinus_eq : sMinus = sCorner + (-1 / 2 : ℝ) • kCorner := by
  ext i; fin_cases i <;> simp [sMinus, sCorner, kCorner] <;> norm_num

theorem isSimplex_plus : IsSimplex sPlus := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp [gram, sPlus, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.submatrix,
      Fin.succAbove]
    try norm_num

theorem isSimplex_minus : IsSimplex sMinus := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp [gram, sMinus, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.submatrix,
      Fin.succAbove]
    try norm_num

/-- **Wrong-model check: the areas do not determine the lengths.** Two different valid Euclidean
4-simplices have the same ten triangle areas. -/
theorem corner_pair : sPlus ≠ sMinus ∧ area sPlus = area sMinus ∧ IsSimplex sPlus ∧
    IsSimplex sMinus := by
  refine ⟨?_, ?_, isSimplex_plus, isSimplex_minus⟩
  · intro h; have := congrFun h 5; simp [sPlus, sMinus] at this
  · ext t; unfold area
    congr 1
    rw [sPlus_eq, sMinus_eq, areaSq_add, areaSq_add, jac_corner_kernel_apply]
    ring

end

end Lightlike.AreaRegge
