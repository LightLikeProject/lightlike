import Mathlib
import Lightlike.Regge.Conv3.DihedralDeriv

/-!
# The algebraic core of the 3D convergence on the Kuhn triangulation

The Kuhn (Freudenthal) triangulation of the cube grid has six congruent tetrahedra per cube, the
orthoscheme `0, e₁, e₁+e₂, e₁+e₂+e₃` and its images under coordinate permutations. Its edges fall
into seven classes (3 axis edges, 3 face diagonals, 1 body diagonal) and the 36 pairs of a
tetrahedron and one of its edges are the incidences of the seven classes.

In normal coordinates at the midpoint of an edge, the squared distance of two points `y, z` is
`|y - z|² - (1/3) Rm(y, z, y, z) + O(5)`. This file takes the first-order variation
`-(1/3) Rm(y, z, y, z)` of the squared lengths of the six tetrahedra, for an algebraic curvature
tensor of dimension 3 with Ricci tensor `ric`, and computes the variation of the dihedral angles.

## Main results

* `h01_angle`, …, `h23_angle`: the six dihedral angles of the orthoscheme (`π/4, π/2, π/3,
  π/2, π/2, π/4`), computed from the squared lengths.
* `star_angle_sum`: the angles of the hinges in each of the seven edge classes add up to `2π`.
* `kuhn_regge_core`: summed over the 36 incidences, the edge length times the first variation of
  the dihedral angle is `-R/2`, for every algebraic curvature tensor of dimension 3.
* `wrong_weight_sq`, `wrong_weight_one`, `wrong_weights_differ`: weighting by the squared length,
  or by `1`, gives a different value (`√3 - 1`, `1/√3 - 1` against `0`).
* `kuhn_regge_core_identity`: non-vacuity, with `ric = 1` the value is `-3/2`.
-/

open Real

namespace Lightlike.Regge.Conv3

theorem h01_deriv (a₁ b₁ c₁ d₁ e₁ f₁ : ℝ) :
    √1 * dihSq' 1 2 1 3 2 1 a₁ b₁ c₁ d₁ e₁ f₁ = -e₁ / 4 + f₁ / 2 := by
  have h2 : √2 ^ 2 = 2 := sq_sqrt (by norm_num)
  have h3 : √3 ^ 2 = 3 := sq_sqrt (by norm_num)
  have h2' : 0 < √2 := by positivity
  have h3' : 0 < √3 := by positivity
  simp only [dihSq', Nn, Nn', Pp, Pp']
  norm_num
  field_simp
  try ring_nf
  try simp only [h2, h3]
  try ring

theorem h02_deriv (a₁ b₁ c₁ d₁ e₁ f₁ : ℝ) :
    √2 * dihSq' 2 1 1 3 1 2 a₁ b₁ c₁ d₁ e₁ f₁ = a₁ / 2 - d₁ / 2 - c₁ - e₁ / 2 + f₁ := by
  have h2 : √2 ^ 2 = 2 := sq_sqrt (by norm_num)
  have h3 : √3 ^ 2 = 3 := sq_sqrt (by norm_num)
  have h2' : 0 < √2 := by positivity
  have h3' : 0 < √3 := by positivity
  simp only [dihSq', Nn, Nn', Pp, Pp']
  norm_num
  field_simp
  try ring_nf
  try simp only [h2, h3]
  try ring

theorem h03_deriv (a₁ b₁ c₁ d₁ e₁ f₁ : ℝ) :
    √3 * dihSq' 3 1 2 2 1 1 a₁ b₁ c₁ d₁ e₁ f₁ = a₁ / 2 - 3 * d₁ / 4 - 3 * c₁ / 4 + 3 * f₁ / 2 := by
  have h2 : √2 ^ 2 = 2 := sq_sqrt (by norm_num)
  have h3 : √3 ^ 2 = 3 := sq_sqrt (by norm_num)
  have h2' : 0 < √2 := by positivity
  have h3' : 0 < √3 := by positivity
  simp only [dihSq', Nn, Nn', Pp, Pp']
  norm_num
  field_simp
  try ring_nf
  try simp only [h2, h3]
  try ring

theorem h12_deriv (a₁ b₁ c₁ d₁ e₁ f₁ : ℝ) :
    √1 * dihSq' 1 1 2 2 1 3 a₁ b₁ c₁ d₁ e₁ f₁ = a₁ / 2 - d₁ / 2 - c₁ / 2 + f₁ / 2 := by
  have h2 : √2 ^ 2 = 2 := sq_sqrt (by norm_num)
  have h3 : √3 ^ 2 = 3 := sq_sqrt (by norm_num)
  have h2' : 0 < √2 := by positivity
  have h3' : 0 < √3 := by positivity
  simp only [dihSq', Nn, Nn', Pp, Pp']
  norm_num
  field_simp
  try ring_nf
  try simp only [h2, h3]
  try ring

theorem h13_deriv (a₁ b₁ c₁ d₁ e₁ f₁ : ℝ) :
    √2 * dihSq' 2 1 3 1 1 2 a₁ b₁ c₁ d₁ e₁ f₁ = a₁ / 2 - b₁ / 2 - d₁ - c₁ / 2 + f₁ := by
  have h2 : √2 ^ 2 = 2 := sq_sqrt (by norm_num)
  have h3 : √3 ^ 2 = 3 := sq_sqrt (by norm_num)
  have h2' : 0 < √2 := by positivity
  have h3' : 0 < √3 := by positivity
  simp only [dihSq', Nn, Nn', Pp, Pp']
  norm_num
  field_simp
  try ring_nf
  try simp only [h2, h3]
  try ring

theorem h23_deriv (a₁ b₁ c₁ d₁ e₁ f₁ : ℝ) :
    √1 * dihSq' 1 2 3 1 2 1 a₁ b₁ c₁ d₁ e₁ f₁ = -b₁ / 4 + f₁ / 2 := by
  have h2 : √2 ^ 2 = 2 := sq_sqrt (by norm_num)
  have h3 : √3 ^ 2 = 3 := sq_sqrt (by norm_num)
  have h2' : 0 < √2 := by positivity
  have h3' : 0 < √3 := by positivity
  simp only [dihSq', Nn, Nn', Pp, Pp']
  norm_num
  field_simp
  try ring_nf
  try simp only [h2, h3]
  try ring


/-- The cosine of the dihedral angle at a hinge, evaluated at the Kuhn orthoscheme. -/
private lemma cos_eval_quarter {a b c d e f : ℝ} (h : cosSq a b c d e f = √2 / 2) :
    dihSq a b c d e f = π / 4 := by
  rw [dihSq, h, ← cos_pi_div_four, arccos_cos (by positivity) (by linarith [pi_pos])]

private lemma cos_eval_third {a b c d e f : ℝ} (h : cosSq a b c d e f = 1 / 2) :
    dihSq a b c d e f = π / 3 := by
  rw [dihSq, h, ← cos_pi_div_three, arccos_cos (by positivity) (by linarith [pi_pos])]

private lemma cos_eval_half {a b c d e f : ℝ} (h : cosSq a b c d e f = 0) :
    dihSq a b c d e f = π / 2 := by
  rw [dihSq, h, arccos_zero]

private lemma sqrt_half : √(1 / 2 : ℝ) = √2 / 2 := by
  rw [Real.sqrt_div (by norm_num), Real.sqrt_one]
  have : 0 < √2 := by positivity
  field_simp
  nlinarith [sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]

/-- The dihedral angle of the orthoscheme at its first hinge is `π/4`. -/
theorem h01_angle : dihSq 1 2 1 3 2 1 = π / 4 := by
  apply cos_eval_quarter
  have : √(2:ℝ) ≠ 0 := by positivity
  simp only [cosSq, Nn, Pp]; norm_num
  field_simp
  nlinarith [sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]

theorem h23_angle : dihSq 1 2 3 1 2 1 = π / 4 := by
  apply cos_eval_quarter
  have : √(2:ℝ) ≠ 0 := by positivity
  simp only [cosSq, Nn, Pp]; norm_num
  field_simp
  nlinarith [sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]

theorem h03_angle : dihSq 3 1 2 2 1 1 = π / 3 := by
  apply cos_eval_third
  simp only [cosSq, Nn, Pp]; norm_num

theorem h02_angle : dihSq 2 1 1 3 1 2 = π / 2 := by
  apply cos_eval_half
  simp only [cosSq, Nn, Pp]; norm_num

theorem h12_angle : dihSq 1 1 2 2 1 3 = π / 2 := by
  apply cos_eval_half
  simp only [cosSq, Nn, Pp]; norm_num

theorem h13_angle : dihSq 2 1 3 1 1 2 = π / 2 := by
  apply cos_eval_half
  simp only [cosSq, Nn, Pp]; norm_num

/-! ### The curvature perturbation of squared lengths -/

/-- The bilinear form of a matrix `ric`. -/
def bil (ric : Fin 3 → Fin 3 → ℝ) (y z : Fin 3 → ℝ) : ℝ :=
  ∑ i, ∑ j, ric i j * y i * z j

/-- The scalar curvature of an algebraic curvature tensor with Ricci tensor `ric` (the trace). -/
def scal (ric : Fin 3 → Fin 3 → ℝ) : ℝ := ∑ i, ric i i

/-- The algebraic curvature tensor of dimension 3 with Ricci tensor `ric`, in an orthonormal
frame: `Rm a b c d = δ_ac ric_bd - δ_ad ric_bc - δ_bc ric_ad + δ_bd ric_ac
- (R/2)(δ_ac δ_bd - δ_ad δ_bc)`. -/
noncomputable def Rm (ric : Fin 3 → Fin 3 → ℝ) (a b c d : Fin 3) : ℝ :=
  (if a = c then ric b d else 0) - (if a = d then ric b c else 0) - (if b = c then ric a d else 0)
    + (if b = d then ric a c else 0)
    - scal ric / 2 * ((if a = c ∧ b = d then 1 else 0) - (if a = d ∧ b = c then 1 else 0))

/-- The sectional-curvature term `Rm(y, z, y, z) = K(y, z) |y ∧ z|²`. -/
noncomputable def Qc (ric : Fin 3 → Fin 3 → ℝ) (y z : Fin 3 → ℝ) : ℝ :=
  ∑ a, ∑ b, ∑ c, ∑ d, Rm ric a b c d * y a * z b * y c * z d

/-- In closed form: `|y|² ric(z,z) + |z|² ric(y,y) - 2 (y·z) ric(y,z) - (R/2)(|y|²|z|² - (y·z)²)`
for symmetric `ric`. -/
theorem Qc_eq (ric : Fin 3 → Fin 3 → ℝ) (hs : ∀ i j, ric i j = ric j i) (y z : Fin 3 → ℝ) :
    Qc ric y z = (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2) * bil ric z z
      + (z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2) * bil ric y y
      - 2 * (y 0 * z 0 + y 1 * z 1 + y 2 * z 2) * bil ric y z
      - scal ric / 2 * ((y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2) * (z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2)
          - (y 0 * z 0 + y 1 * z 1 + y 2 * z 2) ^ 2) := by
  simp only [Qc, Rm, bil, scal, Fin.sum_univ_three]
  simp
  rw [hs 1 0, hs 2 0, hs 2 1]
  ring

/-! ### The Kuhn orthoscheme and its six hinges -/

/-- The vertices `0, e₁, e₁+e₂, e₁+e₂+e₃` of the orthoscheme (one of the 6 Kuhn tetrahedra of
the unit cube). -/
def kv : Fin 4 → Fin 3 → ℝ := ![![0, 0, 0], ![1, 0, 0], ![1, 1, 0], ![1, 1, 1]]

/-- The six hinges `01, 02, 03, 12, 13, 23`: the hinge `(p, q)` and the other two vertices `(r, s)`. -/
def hP : Fin 6 → Fin 4 := ![0, 0, 0, 1, 1, 2]
/-- Second vertex of the hinge. -/
def hQ : Fin 6 → Fin 4 := ![1, 2, 3, 2, 3, 3]
/-- First opposite vertex of the hinge. -/
def hR : Fin 6 → Fin 4 := ![2, 1, 1, 0, 0, 0]
/-- Second opposite vertex of the hinge. -/
def hS : Fin 6 → Fin 4 := ![3, 3, 2, 3, 2, 1]

/-- The squared lengths `(pq, pr, qr, ps, qs, rs)` at each hinge. -/
def hbase : Fin 6 → Fin 6 → ℝ :=
  ![![1, 2, 1, 3, 2, 1], ![2, 1, 1, 3, 1, 2], ![3, 1, 2, 2, 1, 1], ![1, 1, 2, 2, 1, 3],
    ![2, 1, 3, 1, 1, 2], ![1, 2, 3, 1, 2, 1]]

/-- The squared distance of two points of `ℝ³`. -/
def sqd (y z : Fin 3 → ℝ) : ℝ := (y 0 - z 0) ^ 2 + (y 1 - z 1) ^ 2 + (y 2 - z 2) ^ 2

/-- The table `hbase` lists the squared lengths of the orthoscheme at each hinge. -/
theorem hbase_eq (h : Fin 6) :
    hbase h = ![sqd (kv (hP h)) (kv (hQ h)), sqd (kv (hP h)) (kv (hR h)),
      sqd (kv (hQ h)) (kv (hR h)), sqd (kv (hP h)) (kv (hS h)), sqd (kv (hQ h)) (kv (hS h)),
      sqd (kv (hR h)) (kv (hS h))] := by
  fin_cases h <;> (simp [hbase, hP, hQ, hR, hS, kv, sqd]; norm_num)

/-- The derivative `√a · dθ` at each hinge, as a rational linear form of the first variations
`(a₁, …, f₁)` of the squared lengths. -/
noncomputable def dth : Fin 6 → (Fin 6 → ℝ) → ℝ :=
  ![fun x => -x 4 / 4 + x 5 / 2,
    fun x => x 0 / 2 - x 3 / 2 - x 2 - x 4 / 2 + x 5,
    fun x => x 0 / 2 - 3 * x 3 / 4 - 3 * x 2 / 4 + 3 * x 5 / 2,
    fun x => x 0 / 2 - x 3 / 2 - x 2 / 2 + x 5 / 2,
    fun x => x 0 / 2 - x 1 / 2 - x 3 - x 2 / 2 + x 5,
    fun x => -x 1 / 4 + x 5 / 2]

/-- At every hinge, the edge length times the derivative of the dihedral angle is `dth`. -/
theorem hinge_deriv (h : Fin 6) (x : Fin 6 → ℝ) :
    √(hbase h 0) * dihSq' (hbase h 0) (hbase h 1) (hbase h 2) (hbase h 3) (hbase h 4) (hbase h 5)
      (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) = dth h x := by
  fin_cases h
  · simpa [hbase, dth] using h01_deriv (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)
  · simpa [hbase, dth] using h02_deriv (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)
  · simpa [hbase, dth] using h03_deriv (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)
  · simpa [hbase, dth] using h12_deriv (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)
  · simpa [hbase, dth] using h13_deriv (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)
  · simpa [hbase, dth] using h23_deriv (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

/-! ### The six Kuhn tetrahedra of a cube and the sum over all 36 (tetrahedron, hinge) pairs -/

/-- The six coordinate permutations; applied to the orthoscheme they give the six Kuhn
tetrahedra of the unit cube. -/
def perms : Fin 6 → Fin 3 → Fin 3 :=
  ![![0, 1, 2], ![0, 2, 1], ![1, 0, 2], ![1, 2, 0], ![2, 0, 1], ![2, 1, 0]]

/-- The vertex `k` of the tetrahedron `σ`, relative to the midpoint of the hinge `h`. -/
noncomputable def kpos (σ : Fin 6) (h : Fin 6) (k : Fin 4) : Fin 3 → ℝ := fun i =>
  kv k (perms σ i) - (kv (hP h) (perms σ i) + kv (hQ h) (perms σ i)) / 2

/-- The first variation `-(1/3) Rm(y, z, y, z)` of the squared lengths of the tetrahedron `σ`
at the hinge `h`, ordered `(pq, pr, qr, ps, qs, rs)`: the leading change of the squared geodesic
distance in normal coordinates at the midpoint of the hinge. -/
noncomputable def kds (ric : Fin 3 → Fin 3 → ℝ) (σ h : Fin 6) : Fin 6 → ℝ :=
  ![-Qc ric (kpos σ h (hP h)) (kpos σ h (hQ h)) / 3, -Qc ric (kpos σ h (hP h)) (kpos σ h (hR h)) / 3,
    -Qc ric (kpos σ h (hQ h)) (kpos σ h (hR h)) / 3, -Qc ric (kpos σ h (hP h)) (kpos σ h (hS h)) / 3,
    -Qc ric (kpos σ h (hQ h)) (kpos σ h (hS h)) / 3, -Qc ric (kpos σ h (hR h)) (kpos σ h (hS h)) / 3]

/-- The sum over the six tetrahedra of `dth` at the hinge `h`, as a linear form of the Ricci tensor
(entries above the diagonal). -/
noncomputable def Th : Fin 6 → (Fin 3 → Fin 3 → ℝ) → ℝ :=
  ![fun ric => -(ric 0 0 + ric 1 1 + ric 2 2) / 6 - (ric 0 1 + ric 0 2 + ric 1 2) / 4,
    fun _ => 0,
    fun ric => ric 0 1 + ric 0 2 + ric 1 2,
    fun ric => -(ric 0 0 + ric 1 1 + ric 2 2) / 6 - (ric 0 1 + ric 0 2 + ric 1 2) / 2,
    fun _ => 0,
    fun ric => -(ric 0 0 + ric 1 1 + ric 2 2) / 6 - (ric 0 1 + ric 0 2 + ric 1 2) / 4]

set_option maxHeartbeats 1000000 in
/-- Summed over the six Kuhn tetrahedra, the first variation at each hinge is `Th`. -/
theorem kuhn_hinge (ric : Fin 3 → Fin 3 → ℝ) (hs : ∀ i j, ric i j = ric j i) (h : Fin 6) :
    ∑ σ : Fin 6, dth h (kds ric σ h) = Th h ric := by
  fin_cases h <;>
  · simp only [Fin.sum_univ_six, dth, kds, kpos, perms, hP, hQ, hR, hS, kv, Qc_eq ric hs, bil, scal,
      Th]
    simp [Fin.sum_univ_three]
    rw [hs 1 0, hs 2 0, hs 2 1]
    ring

/-- **The algebraic core of the 3D convergence.** Summed over the 6 tetrahedra of a cube and their
6 hinges (36 pairs, which are the incidences of the 7 edge classes), the hinge length times the
first variation of the dihedral angle, for the squared-length variation of a curvature tensor with
Ricci tensor `ric`, is `-R/2`. -/
theorem kuhn_sum (ric : Fin 3 → Fin 3 → ℝ) (hs : ∀ i j, ric i j = ric j i) :
    ∑ σ : Fin 6, ∑ h : Fin 6, dth h (kds ric σ h) = -(scal ric) / 2 := by
  rw [Finset.sum_comm]
  simp only [kuhn_hinge ric hs, Fin.sum_univ_six, Th, scal]
  simp [Fin.sum_univ_three]
  ring

/-- The squared length of every hinge is positive. -/
theorem hbase_pos (h : Fin 6) : 0 < hbase h 0 := by
  fin_cases h <;> simp [hbase] <;> norm_num

/-- The derivative of the dihedral angle at a hinge is `dth / length`. -/
theorem dihSq'_eq (h : Fin 6) (x : Fin 6 → ℝ) :
    dihSq' (hbase h 0) (hbase h 1) (hbase h 2) (hbase h 3) (hbase h 4) (hbase h 5)
      (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) = dth h x / √(hbase h 0) := by
  have hp : 0 < √(hbase h 0) := sqrt_pos.mpr (hbase_pos h)
  rw [eq_div_iff hp.ne', mul_comm]
  exact hinge_deriv h x

/-- **Weighted sum of the angle variations over the 36 incidences.** With the weight `w` of the
hinge length. -/
theorem weighted_sum (w : ℝ → ℝ) (ric : Fin 3 → Fin 3 → ℝ) (hs : ∀ i j, ric i j = ric j i) :
    ∑ σ : Fin 6, ∑ h : Fin 6, w (√(hbase h 0)) *
      dihSq' (hbase h 0) (hbase h 1) (hbase h 2) (hbase h 3) (hbase h 4) (hbase h 5)
        (kds ric σ h 0) (kds ric σ h 1) (kds ric σ h 2) (kds ric σ h 3) (kds ric σ h 4)
        (kds ric σ h 5) = ∑ h : Fin 6, w (√(hbase h 0)) / √(hbase h 0) * Th h ric := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp only [dihSq'_eq, ← kuhn_hinge ric hs h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  ring

/-- **Algebraic core of the 3D convergence (weight = hinge length).** Summed over the 36
(tetrahedron, hinge) pairs of a cube, the hinge length times the first variation of the dihedral
angle under the squared-length variation `-(1/3) Rm(y, z, y, z)` is `-R/2`, for every algebraic
curvature tensor of dimension 3 (with symmetric Ricci tensor `ric`). -/
theorem kuhn_regge_core (ric : Fin 3 → Fin 3 → ℝ) (hs : ∀ i j, ric i j = ric j i) :
    ∑ σ : Fin 6, ∑ h : Fin 6, √(hbase h 0) *
      dihSq' (hbase h 0) (hbase h 1) (hbase h 2) (hbase h 3) (hbase h 4) (hbase h 5)
        (kds ric σ h 0) (kds ric σ h 1) (kds ric σ h 2) (kds ric σ h 3) (kds ric σ h 4)
        (kds ric σ h 5) = -(scal ric) / 2 := by
  rw [← kuhn_sum ric hs]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun h _ => ?_
  exact hinge_deriv h _

/-- A Ricci tensor with only the off-diagonal entry `(0,1)`: scalar curvature `0`. -/
def ricOff : Fin 3 → Fin 3 → ℝ := fun i j => if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then 1 else 0

theorem ricOff_symm (i j : Fin 3) : ricOff i j = ricOff j i := by
  fin_cases i <;> fin_cases j <;> simp [ricOff]

theorem ricOff_scal : scal ricOff = 0 := by
  simp only [scal, ricOff, Fin.sum_univ_three]
  norm_num

/-- **Wrong-weight control (squared length).** Weighting by `|e|²` instead of `|e|` gives `√3 - 1`
on `ricOff`, not the value `-R/2 = 0` of the correct weight. -/
theorem wrong_weight_sq :
    ∑ σ : Fin 6, ∑ h : Fin 6, (√(hbase h 0)) ^ 2 *
      dihSq' (hbase h 0) (hbase h 1) (hbase h 2) (hbase h 3) (hbase h 4) (hbase h 5)
        (kds ricOff σ h 0) (kds ricOff σ h 1) (kds ricOff σ h 2) (kds ricOff σ h 3)
        (kds ricOff σ h 4) (kds ricOff σ h 5) = √3 - 1 := by
  rw [weighted_sum (fun l => l ^ 2) ricOff ricOff_symm]
  have : (√3 : ℝ) ≠ 0 := by positivity
  simp [Fin.sum_univ_six, Th, hbase, ricOff]
  field_simp
  norm_num
  ring

/-- **Wrong-weight control (unit weight).** Weighting every hinge by `1` gives `1/√3 - 1` on
`ricOff`. -/
theorem wrong_weight_one :
    ∑ σ : Fin 6, ∑ h : Fin 6, (1 : ℝ) *
      dihSq' (hbase h 0) (hbase h 1) (hbase h 2) (hbase h 3) (hbase h 4) (hbase h 5)
        (kds ricOff σ h 0) (kds ricOff σ h 1) (kds ricOff σ h 2) (kds ricOff σ h 3)
        (kds ricOff σ h 4) (kds ricOff σ h 5) = 1 / √3 - 1 := by
  rw [weighted_sum (fun _ => 1) ricOff ricOff_symm]
  have : (√3 : ℝ) ≠ 0 := by positivity
  simp [Fin.sum_univ_six, Th, hbase, ricOff]
  field_simp
  norm_num
  ring

/-- Both wrong weights miss the correct value `-R/2 = 0` on `ricOff`, while the weight `|e|` gives
exactly `0` (`kuhn_regge_core`). -/
theorem wrong_weights_differ :
    (√3 - 1 : ℝ) ≠ -(scal ricOff) / 2 ∧ (1 / √3 - 1 : ℝ) ≠ -(scal ricOff) / 2 := by
  rw [ricOff_scal]
  have h3 : (√3 : ℝ) ^ 2 = 3 := sq_sqrt (by norm_num)
  have hp : 0 < √3 := by positivity
  constructor
  · intro h; nlinarith
  · intro h
    have : 1 / √3 = 1 := by linarith
    field_simp at this
    nlinarith

/-- The identity as Ricci tensor (`R = 3`): non-vacuity of `kuhn_regge_core`, value `-3/2`. -/
theorem kuhn_regge_core_identity :
    ∑ σ : Fin 6, ∑ h : Fin 6, √(hbase h 0) *
      dihSq' (hbase h 0) (hbase h 1) (hbase h 2) (hbase h 3) (hbase h 4) (hbase h 5)
        (kds (fun i j => if i = j then 1 else 0) σ h 0) (kds (fun i j => if i = j then 1 else 0) σ h 1)
        (kds (fun i j => if i = j then 1 else 0) σ h 2) (kds (fun i j => if i = j then 1 else 0) σ h 3)
        (kds (fun i j => if i = j then 1 else 0) σ h 4) (kds (fun i j => if i = j then 1 else 0) σ h 5)
      = -3 / 2 := by
  have := kuhn_regge_core (fun i j : Fin 3 => if i = j then (1 : ℝ) else 0) (fun i j => by
    simp [eq_comm])
  rw [this]
  simp [scal]

/-! ### The angles of the orthoscheme and the sum around each edge class -/

/-- The dihedral angle of the orthoscheme at each hinge (exact values). -/
noncomputable def hang : Fin 6 → ℝ := ![π / 4, π / 2, π / 3, π / 2, π / 2, π / 4]

/-- The table `hang` is the dihedral angle `dihSq` computed from the squared lengths. -/
theorem hang_eq (h : Fin 6) :
    dihSq (hbase h 0) (hbase h 1) (hbase h 2) (hbase h 3) (hbase h 4) (hbase h 5) = hang h := by
  fin_cases h
  · simpa [hbase, hang] using h01_angle
  · simpa [hbase, hang] using h02_angle
  · simpa [hbase, hang] using h03_angle
  · simpa [hbase, hang] using h12_angle
  · simpa [hbase, hang] using h13_angle
  · simpa [hbase, hang] using h23_angle

/-- **The angles around each of the 7 edge classes sum to `2π`.** The 36 (tetrahedron, hinge)
pairs of a cube, for the tetrahedra `σ`, are sorted by the direction `(w₀, w₁, w₂)` of the hinge in
the cube, one of the seven nonzero `0/1` vectors; the dihedral angles at the hinges with direction
`w` add up to `2π`. -/
theorem star_angle_sum (w0 w1 w2 : ℝ) (h0 : w0 = 0 ∨ w0 = 1) (h1 : w1 = 0 ∨ w1 = 1)
    (h2 : w2 = 0 ∨ w2 = 1) (hne : ¬(w0 = 0 ∧ w1 = 0 ∧ w2 = 0)) :
    ∑ σ : Fin 6, ∑ h : Fin 6,
      (if kv (hQ h) (perms σ 0) - kv (hP h) (perms σ 0) = w0 ∧
          kv (hQ h) (perms σ 1) - kv (hP h) (perms σ 1) = w1 ∧
          kv (hQ h) (perms σ 2) - kv (hP h) (perms σ 2) = w2 then hang h else 0) = 2 * π := by
  rcases h0 with rfl | rfl <;> rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;>
    first
    | exact absurd ⟨rfl, rfl, rfl⟩ hne
    | (simp [Fin.sum_univ_six, perms, hP, hQ, kv, hang]; norm_num; ring)

end Lightlike.Regge.Conv3
