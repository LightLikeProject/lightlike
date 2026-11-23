import Lightlike.Regge.CMS4.Kuhn4Lin

/-!
# The 4D algebraic core: curvature variation of the Kuhn simplices

The 24 Kuhn simplices of the unit 4-cube are the images `perms4 σ` of the orthoscheme `kv4`.
For a curvature operator `K` on bivectors (a `6 × 6` matrix indexed by the pairs `01, 02, 03, 12,
13, 23`), the leading change of a squared geodesic distance in normal coordinates at the
centroid of a hinge is `-(1/3) K(y ∧ z, y ∧ z)` (`kds4`).
-/

open Real

namespace Lightlike.Regge4

/-- The 24 coordinate permutations (lexicographic order). -/
def perms4 : Fin 24 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![0, 1, 3, 2], ![0, 2, 1, 3], ![0, 2, 3, 1], ![0, 3, 1, 2], ![0, 3, 2, 1],
    ![1, 0, 2, 3], ![1, 0, 3, 2], ![1, 2, 0, 3], ![1, 2, 3, 0], ![1, 3, 0, 2], ![1, 3, 2, 0],
    ![2, 0, 1, 3], ![2, 0, 3, 1], ![2, 1, 0, 3], ![2, 1, 3, 0], ![2, 3, 0, 1], ![2, 3, 1, 0],
    ![3, 0, 1, 2], ![3, 0, 2, 1], ![3, 1, 0, 2], ![3, 1, 2, 0], ![3, 2, 0, 1], ![3, 2, 1, 0]]

/-- First index of the bivector pair `i`. -/
def pa : Fin 6 → Fin 4 := ![0, 0, 0, 1, 1, 2]
/-- Second index of the bivector pair `i`. -/
def pb : Fin 6 → Fin 4 := ![1, 2, 3, 2, 3, 3]

/-- The Plücker coordinate `y_a z_b - y_b z_a` of the pair `i`. -/
def pl (y z : Fin 4 → ℝ) (i : Fin 6) : ℝ := y (pa i) * z (pb i) - y (pb i) * z (pa i)

/-- The curvature `K(y ∧ z, y ∧ z) = Rm(y, z, y, z)` of a curvature operator `K` on bivectors. -/
def Qc4 (K : Fin 6 → Fin 6 → ℝ) (y z : Fin 4 → ℝ) : ℝ :=
  ∑ i, ∑ j, K i j * pl y z i * pl y z j

/-- The scalar curvature `∑_{a,b} Rm(a, b, a, b)` of a curvature operator. -/
def scal4 (K : Fin 6 → Fin 6 → ℝ) : ℝ := 2 * ∑ i, K i i

/-- The vertex `k` of the simplex `σ`, relative to the centroid of the hinge `h`. -/
noncomputable def kpos4 (σ : Fin 24) (h : Fin 10) (k : Fin 5) : Fin 4 → ℝ := fun i =>
  kv4 k (perms4 σ i)
    - (kv4 (hP h) (perms4 σ i) + kv4 (hQ h) (perms4 σ i) + kv4 (hR h) (perms4 σ i)) / 3

/-- The first variation `-(1/3) Rm(y, z, y, z)` of the squared lengths of the simplex `σ`
at the hinge `h`. -/
noncomputable def kds4 (K : Fin 6 → Fin 6 → ℝ) (σ : Fin 24) (h : Fin 10) :
    Fin 5 → Fin 5 → ℝ := fun x y => -Qc4 K (kpos4 σ h x) (kpos4 σ h y) / 3

/-- The area-weighted first variation of the hinge angle `h`, a rational linear form. -/
noncomputable def wlin (h : Fin 10) (δ : Fin 5 → Fin 5 → ℝ) : ℝ :=
  match h with
  | 0 => kuhn4_dih_lin 0 δ / 2
  | 1 => -(δ 1 0 / 2 + δ 1 2 - δ 0 2 - δ 1 3 / 2 + δ 0 3 / 2) / 2
  | 2 => -(δ 1 3 - δ 0 3 - δ 1 4 / 2 + δ 0 4 / 2 - δ 1 2 / 2 + δ 0 2 / 2) / 2
  | 3 => kuhn4_dih_lin 3 δ / 2
  | 4 => -(-(1 / 2) * δ 0 3 - (1 / 8) * δ 3 3 + (3 / 4) * δ 0 2 + (1 / 4) * δ 3 2
          - (3 / 2) * δ 1 2 + (7 / 8) * δ 1 3 - (1 / 8) * δ 3 1 + (3 / 8) * δ 1 1
          + (3 / 8) * δ 2 2 - (1 / 4) * δ 2 3) / 2
  | 5 => kuhn4_dih_lin 5 δ
  | 6 => -(-(δ 0 3 + δ 2 3) / 2 + (δ 0 4 + δ 2 4) / 2 - δ 1 4 + δ 1 3) / 2
  | 7 => -(-(1 / 8) * δ 1 1 - (1 / 2) * δ 1 4 + (7 / 8) * δ 1 3 - (1 / 8) * δ 4 4
          + (1 / 4) * δ 4 3 - (3 / 2) * δ 2 3 + (7 / 8) * δ 2 4 + (1 / 4) * δ 2 1
          - (1 / 4) * δ 1 2 - (1 / 8) * δ 4 2 + (3 / 8) * δ 2 2 + (3 / 8) * δ 3 3
          - (1 / 4) * δ 3 4 - (1 / 8) * δ 3 1) / 2
  | 8 => -(-(δ 1 3 + δ 3 3) / 2 + (δ 1 4 + δ 3 4) / 2 - δ 2 4 + δ 2 3) / 2
  | 9 => kuhn4_dih_lin 9 δ / 2

/-- The area of the hinge triangle `pqr` of the orthoscheme. -/
noncomputable def harea : Fin 10 → ℝ :=
  ![1 / 2, √2 / 2, √2 / 2, 1 / 2, √3 / 2, 1, √2 / 2, √3 / 2, √2 / 2, 1 / 2]

/-- The tabulated area is the area of the triangle: `16 A² = 4 ab - (a + b - c)²` for the squared
side lengths `a = pq`, `b = pr`, `c = qr`. -/
theorem harea_sq (h : Fin 10) :
    16 * harea h ^ 2 = 4 * kd4 (hP h) (hQ h) * kd4 (hP h) (hR h)
      - (kd4 (hP h) (hQ h) + kd4 (hP h) (hR h) - kd4 (hQ h) (hR h)) ^ 2 := by
  have h2 : √2 ^ 2 = 2 := sq_sqrt (by norm_num)
  have h3 : √3 ^ 2 = 3 := sq_sqrt (by norm_num)
  fin_cases h <;> simp [harea, hP, hQ, hR, kd4, kv4, Fin.sum_univ_four] <;>
    first | (rw [div_pow, h2]; norm_num) | (rw [div_pow, h3]; norm_num) | norm_num

/-- The area-weighted first variation is the hinge area times the first variation of the angle. -/
theorem harea_mul_lin (h : Fin 10) (δ : Fin 5 → Fin 5 → ℝ) :
    harea h * kuhn4_dih_lin h δ = wlin h δ := by
  have h2 : (0 : ℝ) < √2 := by positivity
  have h3 : (0 : ℝ) < √3 := by positivity
  fin_cases h <;> simp [harea, wlin, kuhn4_dih_lin] <;> field_simp

set_option maxHeartbeats 20000000 in
/-- **The algebraic core of the 4D convergence.** Summed over the 24 Kuhn simplices of a cube and
their 10 hinges (240 incidences), the hinge area times the first variation of the dihedral angle,
for the squared-length variation of a curvature operator `K`, is `-R/2` with `R = scal4 K`
(that is `-∑ K_ii`). No symmetry or Bianchi identity of `K` is used: the off-diagonal terms cancel. -/
theorem kuhn4_sum (K : Fin 6 → Fin 6 → ℝ) :
    ∑ h : Fin 10, ∑ σ : Fin 24, wlin h (kds4 K σ h) = -(scal4 K) / 2 := by
  simp (config := {maxSteps := 200000000}) only [Fin.sum_univ_succ, Fin.sum_univ_zero, wlin, kds4,
    Qc4, kpos4, pl, pa, pb, perms4, hP, hQ, hR, kv4, kuhn4_dih_lin, scal4]
  simp (config := {maxSteps := 200000000})
  ring_nf

end Lightlike.Regge4
