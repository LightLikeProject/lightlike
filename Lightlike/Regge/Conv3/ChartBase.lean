import Lightlike.Regge.Conv3.KuhnCore
/-!
# The diagonal chart: Gram identity, incidence geometry and the closed forms

For a tetrahedron with edge vectors `x, y, z` from one vertex, the product of the two face quantities
`Pp` minus the square of `Nn`, times the hinge length, is the squared determinant (`gram_identity`,
`gram_pts`). In the diagonal chart `diag(α, β, γ)` of `ℝ³` the squared lengths of the 36 incidences
(tetrahedron, hinge) of the Kuhn triangulation are `dsq`, the first-order variations
`-(1/3) Rm(y, z, y, z)` are `dkds`, and the hinge length times the first variation of the dihedral
angle is `ldth`. `inc_geom` evaluates the geometry of every incidence, and `cf00, …, cf55` are the
closed forms proved in `ChartCases0` … `ChartCases5`.

## Main results

* `gram_identity`, `gram_pts`: the Gram identity.
* `inc_geom`: the squared lengths and the volume of each of the 36 incidences in the diagonal chart.
* `ldth_eq_of`: `ldth` from the derivative combination of the polynomial quantities.
-/

open Real
namespace Lightlike.Regge.Conv3

/-- The Gram identity for a tetrahedron with edge vectors `x, y, z` from one vertex: with `a = |x|²`,
the product of the two face quantities `Pp` minus the square of `Nn` times `a` equals the squared
determinant `det(x, y, z)²`, i.e. `36 V²`. -/
theorem gram_identity (x₀ x₁ x₂ y₀ y₁ y₂ z₀ z₁ z₂ : ℝ)
    (ha : x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 ≠ 0) :
    (x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2) *
      (Pp (x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2) (y₀ ^ 2 + y₁ ^ 2 + y₂ ^ 2)
          ((y₀ - x₀) ^ 2 + (y₁ - x₁) ^ 2 + (y₂ - x₂) ^ 2) *
        Pp (x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2) (z₀ ^ 2 + z₁ ^ 2 + z₂ ^ 2)
          ((z₀ - x₀) ^ 2 + (z₁ - x₁) ^ 2 + (z₂ - x₂) ^ 2) -
        Nn (x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2) (y₀ ^ 2 + y₁ ^ 2 + y₂ ^ 2)
          ((y₀ - x₀) ^ 2 + (y₁ - x₁) ^ 2 + (y₂ - x₂) ^ 2) (z₀ ^ 2 + z₁ ^ 2 + z₂ ^ 2)
          ((z₀ - x₀) ^ 2 + (z₁ - x₁) ^ 2 + (z₂ - x₂) ^ 2)
          ((z₀ - y₀) ^ 2 + (z₁ - y₁) ^ 2 + (z₂ - y₂) ^ 2) ^ 2) =
    (x₀ * (y₁ * z₂ - y₂ * z₁) - x₁ * (y₀ * z₂ - y₂ * z₀) + x₂ * (y₀ * z₁ - y₁ * z₀)) ^ 2 := by
  unfold Pp Nn
  field_simp
  ring

/-- The determinant of the edge vectors `Q - P, R - P, S - P`. -/
def det4 (P Q R S : Fin 3 → ℝ) : ℝ :=
  (Q 0 - P 0) * ((R 1 - P 1) * (S 2 - P 2) - (R 2 - P 2) * (S 1 - P 1))
  - (Q 1 - P 1) * ((R 0 - P 0) * (S 2 - P 2) - (R 2 - P 2) * (S 0 - P 0))
  + (Q 2 - P 2) * ((R 0 - P 0) * (S 1 - P 1) - (R 1 - P 1) * (S 0 - P 0))

/-- The Gram identity for four points. -/
theorem gram_pts (P Q R S : Fin 3 → ℝ) (ha : sqd P Q ≠ 0) :
    sqd P Q * (Pp (sqd P Q) (sqd P R) (sqd Q R) * Pp (sqd P Q) (sqd P S) (sqd Q S) -
      Nn (sqd P Q) (sqd P R) (sqd Q R) (sqd P S) (sqd Q S) (sqd R S) ^ 2) = det4 P Q R S ^ 2 := by
  have h := gram_identity (Q 0 - P 0) (Q 1 - P 1) (Q 2 - P 2) (R 0 - P 0) (R 1 - P 1) (R 2 - P 2)
    (S 0 - P 0) (S 1 - P 1) (S 2 - P 2) (by
      intro h0; apply ha; simp only [sqd]; nlinarith [h0])
  have e1 : sqd P Q = (Q 0 - P 0) ^ 2 + (Q 1 - P 1) ^ 2 + (Q 2 - P 2) ^ 2 := by simp only [sqd]; ring
  have e2 : sqd P R = (R 0 - P 0) ^ 2 + (R 1 - P 1) ^ 2 + (R 2 - P 2) ^ 2 := by simp only [sqd]; ring
  have e3 : sqd Q R = ((R 0 - P 0) - (Q 0 - P 0)) ^ 2 + ((R 1 - P 1) - (Q 1 - P 1)) ^ 2
      + ((R 2 - P 2) - (Q 2 - P 2)) ^ 2 := by simp only [sqd]; ring
  have e4 : sqd P S = (S 0 - P 0) ^ 2 + (S 1 - P 1) ^ 2 + (S 2 - P 2) ^ 2 := by simp only [sqd]; ring
  have e5 : sqd Q S = ((S 0 - P 0) - (Q 0 - P 0)) ^ 2 + ((S 1 - P 1) - (Q 1 - P 1)) ^ 2
      + ((S 2 - P 2) - (Q 2 - P 2)) ^ 2 := by simp only [sqd]; ring
  have e6 : sqd R S = ((S 0 - P 0) - (R 0 - P 0)) ^ 2 + ((S 1 - P 1) - (R 1 - P 1)) ^ 2
      + ((S 2 - P 2) - (R 2 - P 2)) ^ 2 := by simp only [sqd]; ring
  rw [e1, e2, e3, e4, e5, e6]
  rw [h]
  simp only [det4]

/-- A face height squared is nonnegative. -/
theorem Pp_nonneg_pts (P Q R : Fin 3 → ℝ) (ha : 0 < sqd P Q) :
    0 ≤ Pp (sqd P Q) (sqd P R) (sqd Q R) := by
  unfold Pp
  rw [sub_nonneg, div_le_iff₀ (by linarith)]
  simp only [sqd]
  nlinarith [sq_nonneg ((Q 1 - P 1) * (R 2 - P 2) - (Q 2 - P 2) * (R 1 - P 1)),
    sq_nonneg ((Q 2 - P 2) * (R 0 - P 0) - (Q 0 - P 0) * (R 2 - P 2)),
    sq_nonneg ((Q 0 - P 0) * (R 1 - P 1) - (Q 1 - P 1) * (R 0 - P 0))]

/-- The rational form `ℓ dθ` of the first variation of a dihedral angle, with the volume `V`. -/
noncomputable def ldth (V a b c d e f a₁ b₁ c₁ d₁ e₁ f₁ : ℝ) : ℝ :=
  -(a / (6 * V)) * (Nn' a b c d e f a₁ b₁ c₁ d₁ e₁ f₁ -
    Nn a b c d e f / 2 * (Pp' a b c a₁ b₁ c₁ / Pp a b c + Pp' a d e a₁ d₁ e₁ / Pp a d e))

/-- A chart whose metric at the vertex is diagonal `diag(s₀², s₁², s₂²)`: the vertex `k` of the
tetrahedron `σ`, relative to the midpoint of the hinge `h`, in an orthonormal frame. -/
noncomputable def dpos (s : Fin 3 → ℝ) (σ h : Fin 6) (k : Fin 4) : Fin 3 → ℝ :=
  fun i => s i * kpos σ h k i

/-- Squared lengths `(pq, pr, qr, ps, qs, rs)` of the chart tetrahedron at the hinge `h`. -/
noncomputable def dsq (s : Fin 3 → ℝ) (σ h : Fin 6) : Fin 6 → ℝ :=
  ![sqd (dpos s σ h (hP h)) (dpos s σ h (hQ h)), sqd (dpos s σ h (hP h)) (dpos s σ h (hR h)),
    sqd (dpos s σ h (hQ h)) (dpos s σ h (hR h)), sqd (dpos s σ h (hP h)) (dpos s σ h (hS h)),
    sqd (dpos s σ h (hQ h)) (dpos s σ h (hS h)), sqd (dpos s σ h (hR h)) (dpos s σ h (hS h))]

/-- The squared-length variation `-(1/3) Rm(y, z, y, z)` of the chart tetrahedron. -/
noncomputable def dkds (ric : Fin 3 → Fin 3 → ℝ) (s : Fin 3 → ℝ) (σ h : Fin 6) : Fin 6 → ℝ :=
  ![-Qc ric (dpos s σ h (hP h)) (dpos s σ h (hQ h)) / 3,
    -Qc ric (dpos s σ h (hP h)) (dpos s σ h (hR h)) / 3,
    -Qc ric (dpos s σ h (hQ h)) (dpos s σ h (hR h)) / 3,
    -Qc ric (dpos s σ h (hP h)) (dpos s σ h (hS h)) / 3,
    -Qc ric (dpos s σ h (hQ h)) (dpos s σ h (hS h)) / 3,
    -Qc ric (dpos s σ h (hR h)) (dpos s σ h (hS h)) / 3]


/-- Clearing the face denominators of `ldth`. -/
theorem ldth_eq_of {V a b c d e f a₁ b₁ c₁ d₁ e₁ f₁ t : ℝ} (hP1 : Pp a b c ≠ 0) (hP2 : Pp a d e ≠ 0)
    (hV : V ≠ 0)
    (h : -(a / (6 * V)) * (Nn' a b c d e f a₁ b₁ c₁ d₁ e₁ f₁ * (Pp a b c * Pp a d e) -
        Nn a b c d e f / 2 * (Pp' a b c a₁ b₁ c₁ * Pp a d e + Pp' a d e a₁ d₁ e₁ * Pp a b c)) =
      t * (Pp a b c * Pp a d e)) :
    ldth V a b c d e f a₁ b₁ c₁ d₁ e₁ f₁ = t := by
  apply mul_right_cancel₀ (mul_ne_zero hP1 hP2)
  rw [← h]
  unfold ldth
  field_simp

set_option maxHeartbeats 4000000 in
/-- For every incidence of the diagonal chart: the hinge is non-degenerate, the two faces have
positive height, and the Gram determinant is `(αβγ)²`. -/
theorem inc_geom (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (σ h : Fin 6) :
    0 < dsq ![α, β, γ] σ h 0 ∧ 0 < Pp (dsq ![α, β, γ] σ h 0) (dsq ![α, β, γ] σ h 1)
        (dsq ![α, β, γ] σ h 2) ∧
      0 < Pp (dsq ![α, β, γ] σ h 0) (dsq ![α, β, γ] σ h 3) (dsq ![α, β, γ] σ h 4) ∧
      dsq ![α, β, γ] σ h 0 * (Pp (dsq ![α, β, γ] σ h 0) (dsq ![α, β, γ] σ h 1)
          (dsq ![α, β, γ] σ h 2) * Pp (dsq ![α, β, γ] σ h 0) (dsq ![α, β, γ] σ h 3)
          (dsq ![α, β, γ] σ h 4) - Nn (dsq ![α, β, γ] σ h 0) (dsq ![α, β, γ] σ h 1)
          (dsq ![α, β, γ] σ h 2) (dsq ![α, β, γ] σ h 3) (dsq ![α, β, γ] σ h 4)
          (dsq ![α, β, γ] σ h 5) ^ 2) = (α * β * γ) ^ 2 := by
  set s : Fin 3 → ℝ := ![α, β, γ]
  have e0 : dsq s σ h 0 = sqd (dpos s σ h (hP h)) (dpos s σ h (hQ h)) := rfl
  have e1 : dsq s σ h 1 = sqd (dpos s σ h (hP h)) (dpos s σ h (hR h)) := rfl
  have e2 : dsq s σ h 2 = sqd (dpos s σ h (hQ h)) (dpos s σ h (hR h)) := rfl
  have e3 : dsq s σ h 3 = sqd (dpos s σ h (hP h)) (dpos s σ h (hS h)) := rfl
  have e4 : dsq s σ h 4 = sqd (dpos s σ h (hQ h)) (dpos s σ h (hS h)) := rfl
  have e5 : dsq s σ h 5 = sqd (dpos s σ h (hR h)) (dpos s σ h (hS h)) := rfl
  have hpos : 0 < dsq s σ h 0 := by
    rw [e0]
    fin_cases σ <;> fin_cases h <;>
      simp [s, dpos, kpos, perms, hP, hQ, kv, sqd] <;> ring_nf <;> positivity
  have hdet : det4 (dpos s σ h (hP h)) (dpos s σ h (hQ h)) (dpos s σ h (hR h))
      (dpos s σ h (hS h)) ^ 2 = (α * β * γ) ^ 2 := by
    fin_cases σ <;> fin_cases h <;>
      simp [s, det4, dpos, kpos, perms, hP, hQ, hR, hS, kv] <;> ring
  have hg := gram_pts (dpos s σ h (hP h)) (dpos s σ h (hQ h)) (dpos s σ h (hR h))
    (dpos s σ h (hS h)) (by rw [← e0]; exact hpos.ne')
  rw [← e0, ← e1, ← e2, ← e3, ← e4, ← e5, hdet] at hg
  have n1 := Pp_nonneg_pts (dpos s σ h (hP h)) (dpos s σ h (hQ h)) (dpos s σ h (hR h)) (by
    rw [← e0]; exact hpos)
  have n2 := Pp_nonneg_pts (dpos s σ h (hP h)) (dpos s σ h (hQ h)) (dpos s σ h (hS h)) (by
    rw [← e0]; exact hpos)
  rw [← e0, ← e1, ← e2] at n1
  rw [← e0, ← e3, ← e4] at n2
  refine ⟨hpos, ?_, ?_, hg⟩
  all_goals
    have hW : 0 < Pp (dsq s σ h 0) (dsq s σ h 1) (dsq s σ h 2) * Pp (dsq s σ h 0) (dsq s σ h 3)
        (dsq s σ h 4) - Nn (dsq s σ h 0) (dsq s σ h 1) (dsq s σ h 2) (dsq s σ h 3) (dsq s σ h 4)
        (dsq s σ h 5) ^ 2 := by
      by_contra hneg
      have : _ ≤ (0 : ℝ) := not_lt.mp hneg
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hpos.le this, mul_pos (mul_pos hα hβ) hγ]
    have hpp : 0 < Pp (dsq s σ h 0) (dsq s σ h 1) (dsq s σ h 2) * Pp (dsq s σ h 0) (dsq s σ h 3)
        (dsq s σ h 4) := by nlinarith [sq_nonneg (Nn (dsq s σ h 0) (dsq s σ h 1) (dsq s σ h 2)
          (dsq s σ h 3) (dsq s σ h 4) (dsq s σ h 5))]
  · exact lt_of_le_of_ne n1 (fun h0 => by rw [← h0] at hpp; simp at hpp)
  · exact lt_of_le_of_ne n2 (fun h0 => by rw [← h0] at hpp; simp at hpp)

/-- Closed form of the dihedral variation at tetrahedron 0, hinge 0. -/
noncomputable def cf00 (α β γ : ℝ) (ric : Fin 3 → Fin 3 → ℝ) : ℝ :=
  α*γ*(α^2*β*(ric 1 1) - α^2*β*(ric 2 2) + 2*α^2*γ*(ric 1 2) - 4*α*β^2*(ric 0 1) - 4*α*γ^2*(ric 0 1) + 2*β^3*(ric 0 0) - 2*β^3*(ric 1 1) - 2*β^3*(ric 2 2) + 2*β*γ^2*(ric 0 0) - 2*β*γ^2*(ric 1 1) - 2*β*γ^2*(ric 2 2))/(24*(β^2 + γ^2))

/-- Closed form of the dihedral variation at tetrahedron 0, hinge 1. -/
noncomputable def cf01 (α β γ : ℝ) (ric : Fin 3 → Fin 3 → ℝ) : ℝ :=
  (α^2 + β^2)*(-α*(ric 1 2) - β*(ric 0 2) + 2*γ*(ric 0 1))/12

/-- Closed form of the dihedral variation at tetrahedron 0, hinge 2. -/
noncomputable def cf02 (α β γ : ℝ) (ric : Fin 3 → Fin 3 → ℝ) : ℝ :=
  β*(α^2 + β^2 + γ^2)*(2*α^3*β*(ric 1 2) - α^3*γ*(ric 1 1) + α^3*γ*(ric 2 2) + 2*α^2*β^2*(ric 0 2) + 2*α^2*γ^2*(ric 0 2) + 2*α*β^3*(ric 1 2) + α*β^2*γ*(ric 0 0) - 2*α*β^2*γ*(ric 1 1) + α*β^2*γ*(ric 2 2) + α*γ^3*(ric 0 0) - α*γ^3*(ric 1 1) + 2*β^4*(ric 0 2) + 2*β^3*γ*(ric 0 1) + 2*β^2*γ^2*(ric 0 2) + 2*β*γ^3*(ric 0 1))/(24*(α^2 + β^2)*(β^2 + γ^2))

/-- Closed form of the dihedral variation at tetrahedron 0, hinge 3. -/
noncomputable def cf03 (α β γ : ℝ) (ric : Fin 3 → Fin 3 → ℝ) : ℝ :=
  -β*(2*α*β*(ric 1 2) + α*γ*(ric 0 0) - α*γ*(ric 1 1) + α*γ*(ric 2 2) - β^2*(ric 0 2) + 2*β*γ*(ric 0 1))/12

/-- Closed form of the dihedral variation at tetrahedron 0, hinge 4. -/
noncomputable def cf04 (α β γ : ℝ) (ric : Fin 3 → Fin 3 → ℝ) : ℝ :=
  -(β^2 + γ^2)*(-2*α*(ric 1 2) + β*(ric 0 2) + γ*(ric 0 1))/12

/-- Closed form of the dihedral variation at tetrahedron 0, hinge 5. -/
noncomputable def cf05 (α β γ : ℝ) (ric : Fin 3 → Fin 3 → ℝ) : ℝ :=
  -α*γ*(2*α^2*β*(ric 0 0) + 2*α^2*β*(ric 1 1) - 2*α^2*β*(ric 2 2) + 4*α^2*γ*(ric 1 2) - 2*α*γ^2*(ric 0 1) + 2*β^3*(ric 0 0) + 2*β^3*(ric 1 1) - 2*β^3*(ric 2 2) + 4*β^2*γ*(ric 1 2) + β*γ^2*(ric 0 0) - β*γ^2*(ric 1 1))/(24*(α^2 + β^2))

/-- Closed form of the dihedral variation at tetrahedron 1, hinge 0. -/
noncomputable def cf10 (α β γ : ℝ) (ric : Fin 3 → Fin 3 → ℝ) : ℝ :=
  α*β*(2*α^2*β*(ric 1 2) - α^2*γ*(ric 1 1) + α^2*γ*(ric 2 2) - 4*α*β^2*(ric 0 2) - 4*α*γ^2*(ric 0 2) + 2*β^2*γ*(ric 0 0) - 2*β^2*γ*(ric 1 1) - 2*β^2*γ*(ric 2 2) + 2*γ^3*(ric 0 0) - 2*γ^3*(ric 1 1) - 2*γ^3*(ric 2 2))/(24*(β^2 + γ^2))

/-- Closed form of the dihedral variation at tetrahedron 1, hinge 1. -/
noncomputable def cf11 (α β γ : ℝ) (ric : Fin 3 → Fin 3 → ℝ) : ℝ :=
  -(α^2 + γ^2)*(α*(ric 1 2) - 2*β*(ric 0 2) + γ*(ric 0 1))/12

/-- Closed form of the dihedral variation at tetrahedron 1, hinge 2. -/
noncomputable def cf12 (α β γ : ℝ) (ric : Fin 3 → Fin 3 → ℝ) : ℝ :=
  γ*(α^2 + β^2 + γ^2)*(α^3*β*(ric 1 1) - α^3*β*(ric 2 2) + 2*α^3*γ*(ric 1 2) + 2*α^2*β^2*(ric 0 1) + 2*α^2*γ^2*(ric 0 1) + α*β^3*(ric 0 0) - α*β^3*(ric 2 2) + α*β*γ^2*(ric 0 0) + α*β*γ^2*(ric 1 1) - 2*α*β*γ^2*(ric 2 2) + 2*α*γ^3*(ric 1 2) + 2*β^3*γ*(ric 0 2) + 2*β^2*γ^2*(ric 0 1) + 2*β*γ^3*(ric 0 2) + 2*γ^4*(ric 0 1))/(24*(α^2 + γ^2)*(β^2 + γ^2))

/-- Closed form of the dihedral variation at tetrahedron 1, hinge 3. -/
noncomputable def cf13 (α β γ : ℝ) (ric : Fin 3 → Fin 3 → ℝ) : ℝ :=
  -γ*(α*β*(ric 0 0) + α*β*(ric 1 1) - α*β*(ric 2 2) + 2*α*γ*(ric 1 2) + 2*β*γ*(ric 0 2) - γ^2*(ric 0 1))/12

/-- Closed form of the dihedral variation at tetrahedron 1, hinge 4. -/
noncomputable def cf14 (α β γ : ℝ) (ric : Fin 3 → Fin 3 → ℝ) : ℝ :=
  -(β^2 + γ^2)*(-2*α*(ric 1 2) + β*(ric 0 2) + γ*(ric 0 1))/12

/-- Closed form of the dihedral variation at tetrahedron 1, hinge 5. -/
noncomputable def cf15 (α β γ : ℝ) (ric : Fin 3 → Fin 3 → ℝ) : ℝ :=
  -α*β*(4*α^2*β*(ric 1 2) + 2*α^2*γ*(ric 0 0) - 2*α^2*γ*(ric 1 1) + 2*α^2*γ*(ric 2 2) - 2*α*β^2*(ric 0 2) + β^2*γ*(ric 0 0) - β^2*γ*(ric 2 2) + 4*β*γ^2*(ric 1 2) + 2*γ^3*(ric 0 0) - 2*γ^3*(ric 1 1) + 2*γ^3*(ric 2 2))/(24*(α^2 + γ^2))

/-- Closed form of the dihedral variation at tetrahedron 2, hinge 0. -/
noncomputable def cf20 (α β γ : ℝ) (ric : Fin 3 → Fin 3 → ℝ) : ℝ :=
  -β*γ*(2*α^3*(ric 0 0) - 2*α^3*(ric 1 1) + 2*α^3*(ric 2 2) + 4*α^2*β*(ric 0 1) - α*β^2*(ric 0 0) + α*β^2*(ric 2 2) + 2*α*γ^2*(ric 0 0) - 2*α*γ^2*(ric 1 1) + 2*α*γ^2*(ric 2 2) - 2*β^2*γ*(ric 0 2) + 4*β*γ^2*(ric 0 1))/(24*(α^2 + γ^2))

/-- Closed form of the dihedral variation at tetrahedron 2, hinge 1. -/
noncomputable def cf21 (α β γ : ℝ) (ric : Fin 3 → Fin 3 → ℝ) : ℝ :=
  (α^2 + β^2)*(-α*(ric 1 2) - β*(ric 0 2) + 2*γ*(ric 0 1))/12

/-- Closed form of the dihedral variation at tetrahedron 2, hinge 2. -/
noncomputable def cf22 (α β γ : ℝ) (ric : Fin 3 → Fin 3 → ℝ) : ℝ :=
  -α*(α^2 + β^2 + γ^2)*(-2*α^4*(ric 1 2) - 2*α^3*β*(ric 0 2) - 2*α^3*γ*(ric 0 1) - 2*α^2*β^2*(ric 1 2) + 2*α^2*β*γ*(ric 0 0) - α^2*β*γ*(ric 1 1) - α^2*β*γ*(ric 2 2) - 2*α^2*γ^2*(ric 1 2) - 2*α*β^3*(ric 0 2) - 2*α*γ^3*(ric 0 1) + β^3*γ*(ric 0 0) - β^3*γ*(ric 2 2) - 2*β^2*γ^2*(ric 1 2) + β*γ^3*(ric 0 0) - β*γ^3*(ric 1 1))/(24*(α^2 + β^2)*(α^2 + γ^2))

/-- Closed form of the dihedral variation at tetrahedron 2, hinge 3. -/
noncomputable def cf23 (α β γ : ℝ) (ric : Fin 3 → Fin 3 → ℝ) : ℝ :=
  α*(α^2*(ric 1 2) - 2*α*β*(ric 0 2) - 2*α*γ*(ric 0 1) + β*γ*(ric 0 0) - β*γ*(ric 1 1) - β*γ*(ric 2 2))/12

/-- Closed form of the dihedral variation at tetrahedron 2, hinge 4. -/
noncomputable def cf24 (α β γ : ℝ) (ric : Fin 3 → Fin 3 → ℝ) : ℝ :=
  -(α^2 + γ^2)*(α*(ric 1 2) - 2*β*(ric 0 2) + γ*(ric 0 1))/12

/-- Closed form of the dihedral variation at tetrahedron 2, hinge 5. -/
noncomputable def cf25 (α β γ : ℝ) (ric : Fin 3 → Fin 3 → ℝ) : ℝ :=
  -β*γ*(2*α^3*(ric 0 0) + 2*α^3*(ric 1 1) - 2*α^3*(ric 2 2) + 4*α^2*γ*(ric 0 2) + 2*α*β^2*(ric 0 0) + 2*α*β^2*(ric 1 1) - 2*α*β^2*(ric 2 2) - α*γ^2*(ric 0 0) + α*γ^2*(ric 1 1) + 4*β^2*γ*(ric 0 2) - 2*β*γ^2*(ric 0 1))/(24*(α^2 + β^2))

/-- Closed form of the dihedral variation at tetrahedron 3, hinge 0. -/
noncomputable def cf30 (α β γ : ℝ) (ric : Fin 3 → Fin 3 → ℝ) : ℝ :=
  -β*γ*(2*α^3*(ric 0 0) + 2*α^3*(ric 1 1) - 2*α^3*(ric 2 2) + 4*α^2*γ*(ric 0 2) + 2*α*β^2*(ric 0 0) + 2*α*β^2*(ric 1 1) - 2*α*β^2*(ric 2 2) - α*γ^2*(ric 0 0) + α*γ^2*(ric 1 1) + 4*β^2*γ*(ric 0 2) - 2*β*γ^2*(ric 0 1))/(24*(α^2 + β^2))

/-- Closed form of the dihedral variation at tetrahedron 3, hinge 1. -/
noncomputable def cf31 (α β γ : ℝ) (ric : Fin 3 → Fin 3 → ℝ) : ℝ :=
  -(α^2 + γ^2)*(α*(ric 1 2) - 2*β*(ric 0 2) + γ*(ric 0 1))/12

/-- Closed form of the dihedral variation at tetrahedron 3, hinge 2. -/
noncomputable def cf32 (α β γ : ℝ) (ric : Fin 3 → Fin 3 → ℝ) : ℝ :=
  -α*(α^2 + β^2 + γ^2)*(-2*α^4*(ric 1 2) - 2*α^3*β*(ric 0 2) - 2*α^3*γ*(ric 0 1) - 2*α^2*β^2*(ric 1 2) + 2*α^2*β*γ*(ric 0 0) - α^2*β*γ*(ric 1 1) - α^2*β*γ*(ric 2 2) - 2*α^2*γ^2*(ric 1 2) - 2*α*β^3*(ric 0 2) - 2*α*γ^3*(ric 0 1) + β^3*γ*(ric 0 0) - β^3*γ*(ric 2 2) - 2*β^2*γ^2*(ric 1 2) + β*γ^3*(ric 0 0) - β*γ^3*(ric 1 1))/(24*(α^2 + β^2)*(α^2 + γ^2))

/-- Closed form of the dihedral variation at tetrahedron 3, hinge 3. -/
noncomputable def cf33 (α β γ : ℝ) (ric : Fin 3 → Fin 3 → ℝ) : ℝ :=
  α*(α^2*(ric 1 2) - 2*α*β*(ric 0 2) - 2*α*γ*(ric 0 1) + β*γ*(ric 0 0) - β*γ*(ric 1 1) - β*γ*(ric 2 2))/12

/-- Closed form of the dihedral variation at tetrahedron 3, hinge 4. -/
noncomputable def cf34 (α β γ : ℝ) (ric : Fin 3 → Fin 3 → ℝ) : ℝ :=
  (α^2 + β^2)*(-α*(ric 1 2) - β*(ric 0 2) + 2*γ*(ric 0 1))/12

/-- Closed form of the dihedral variation at tetrahedron 3, hinge 5. -/
noncomputable def cf35 (α β γ : ℝ) (ric : Fin 3 → Fin 3 → ℝ) : ℝ :=
  -β*γ*(2*α^3*(ric 0 0) - 2*α^3*(ric 1 1) + 2*α^3*(ric 2 2) + 4*α^2*β*(ric 0 1) - α*β^2*(ric 0 0) + α*β^2*(ric 2 2) + 2*α*γ^2*(ric 0 0) - 2*α*γ^2*(ric 1 1) + 2*α*γ^2*(ric 2 2) - 2*β^2*γ*(ric 0 2) + 4*β*γ^2*(ric 0 1))/(24*(α^2 + γ^2))

/-- Closed form of the dihedral variation at tetrahedron 4, hinge 0. -/
noncomputable def cf40 (α β γ : ℝ) (ric : Fin 3 → Fin 3 → ℝ) : ℝ :=
  -α*β*(4*α^2*β*(ric 1 2) + 2*α^2*γ*(ric 0 0) - 2*α^2*γ*(ric 1 1) + 2*α^2*γ*(ric 2 2) - 2*α*β^2*(ric 0 2) + β^2*γ*(ric 0 0) - β^2*γ*(ric 2 2) + 4*β*γ^2*(ric 1 2) + 2*γ^3*(ric 0 0) - 2*γ^3*(ric 1 1) + 2*γ^3*(ric 2 2))/(24*(α^2 + γ^2))

/-- Closed form of the dihedral variation at tetrahedron 4, hinge 1. -/
noncomputable def cf41 (α β γ : ℝ) (ric : Fin 3 → Fin 3 → ℝ) : ℝ :=
  -(β^2 + γ^2)*(-2*α*(ric 1 2) + β*(ric 0 2) + γ*(ric 0 1))/12

/-- Closed form of the dihedral variation at tetrahedron 4, hinge 2. -/
noncomputable def cf42 (α β γ : ℝ) (ric : Fin 3 → Fin 3 → ℝ) : ℝ :=
  γ*(α^2 + β^2 + γ^2)*(α^3*β*(ric 1 1) - α^3*β*(ric 2 2) + 2*α^3*γ*(ric 1 2) + 2*α^2*β^2*(ric 0 1) + 2*α^2*γ^2*(ric 0 1) + α*β^3*(ric 0 0) - α*β^3*(ric 2 2) + α*β*γ^2*(ric 0 0) + α*β*γ^2*(ric 1 1) - 2*α*β*γ^2*(ric 2 2) + 2*α*γ^3*(ric 1 2) + 2*β^3*γ*(ric 0 2) + 2*β^2*γ^2*(ric 0 1) + 2*β*γ^3*(ric 0 2) + 2*γ^4*(ric 0 1))/(24*(α^2 + γ^2)*(β^2 + γ^2))

/-- Closed form of the dihedral variation at tetrahedron 4, hinge 3. -/
noncomputable def cf43 (α β γ : ℝ) (ric : Fin 3 → Fin 3 → ℝ) : ℝ :=
  -γ*(α*β*(ric 0 0) + α*β*(ric 1 1) - α*β*(ric 2 2) + 2*α*γ*(ric 1 2) + 2*β*γ*(ric 0 2) - γ^2*(ric 0 1))/12

/-- Closed form of the dihedral variation at tetrahedron 4, hinge 4. -/
noncomputable def cf44 (α β γ : ℝ) (ric : Fin 3 → Fin 3 → ℝ) : ℝ :=
  -(α^2 + γ^2)*(α*(ric 1 2) - 2*β*(ric 0 2) + γ*(ric 0 1))/12

/-- Closed form of the dihedral variation at tetrahedron 4, hinge 5. -/
noncomputable def cf45 (α β γ : ℝ) (ric : Fin 3 → Fin 3 → ℝ) : ℝ :=
  α*β*(2*α^2*β*(ric 1 2) - α^2*γ*(ric 1 1) + α^2*γ*(ric 2 2) - 4*α*β^2*(ric 0 2) - 4*α*γ^2*(ric 0 2) + 2*β^2*γ*(ric 0 0) - 2*β^2*γ*(ric 1 1) - 2*β^2*γ*(ric 2 2) + 2*γ^3*(ric 0 0) - 2*γ^3*(ric 1 1) - 2*γ^3*(ric 2 2))/(24*(β^2 + γ^2))

/-- Closed form of the dihedral variation at tetrahedron 5, hinge 0. -/
noncomputable def cf50 (α β γ : ℝ) (ric : Fin 3 → Fin 3 → ℝ) : ℝ :=
  -α*γ*(2*α^2*β*(ric 0 0) + 2*α^2*β*(ric 1 1) - 2*α^2*β*(ric 2 2) + 4*α^2*γ*(ric 1 2) - 2*α*γ^2*(ric 0 1) + 2*β^3*(ric 0 0) + 2*β^3*(ric 1 1) - 2*β^3*(ric 2 2) + 4*β^2*γ*(ric 1 2) + β*γ^2*(ric 0 0) - β*γ^2*(ric 1 1))/(24*(α^2 + β^2))

/-- Closed form of the dihedral variation at tetrahedron 5, hinge 1. -/
noncomputable def cf51 (α β γ : ℝ) (ric : Fin 3 → Fin 3 → ℝ) : ℝ :=
  -(β^2 + γ^2)*(-2*α*(ric 1 2) + β*(ric 0 2) + γ*(ric 0 1))/12

/-- Closed form of the dihedral variation at tetrahedron 5, hinge 2. -/
noncomputable def cf52 (α β γ : ℝ) (ric : Fin 3 → Fin 3 → ℝ) : ℝ :=
  β*(α^2 + β^2 + γ^2)*(2*α^3*β*(ric 1 2) - α^3*γ*(ric 1 1) + α^3*γ*(ric 2 2) + 2*α^2*β^2*(ric 0 2) + 2*α^2*γ^2*(ric 0 2) + 2*α*β^3*(ric 1 2) + α*β^2*γ*(ric 0 0) - 2*α*β^2*γ*(ric 1 1) + α*β^2*γ*(ric 2 2) + α*γ^3*(ric 0 0) - α*γ^3*(ric 1 1) + 2*β^4*(ric 0 2) + 2*β^3*γ*(ric 0 1) + 2*β^2*γ^2*(ric 0 2) + 2*β*γ^3*(ric 0 1))/(24*(α^2 + β^2)*(β^2 + γ^2))

/-- Closed form of the dihedral variation at tetrahedron 5, hinge 3. -/
noncomputable def cf53 (α β γ : ℝ) (ric : Fin 3 → Fin 3 → ℝ) : ℝ :=
  -β*(2*α*β*(ric 1 2) + α*γ*(ric 0 0) - α*γ*(ric 1 1) + α*γ*(ric 2 2) - β^2*(ric 0 2) + 2*β*γ*(ric 0 1))/12

/-- Closed form of the dihedral variation at tetrahedron 5, hinge 4. -/
noncomputable def cf54 (α β γ : ℝ) (ric : Fin 3 → Fin 3 → ℝ) : ℝ :=
  (α^2 + β^2)*(-α*(ric 1 2) - β*(ric 0 2) + 2*γ*(ric 0 1))/12

/-- Closed form of the dihedral variation at tetrahedron 5, hinge 5. -/
noncomputable def cf55 (α β γ : ℝ) (ric : Fin 3 → Fin 3 → ℝ) : ℝ :=
  α*γ*(α^2*β*(ric 1 1) - α^2*β*(ric 2 2) + 2*α^2*γ*(ric 1 2) - 4*α*β^2*(ric 0 1) - 4*α*γ^2*(ric 0 1) + 2*β^3*(ric 0 0) - 2*β^3*(ric 1 1) - 2*β^3*(ric 2 2) + 2*β*γ^2*(ric 0 0) - 2*β*γ^2*(ric 1 1) - 2*β*γ^2*(ric 2 2))/(24*(β^2 + γ^2))

/-- The closed form of `ℓ dθ` at each (tetrahedron, hinge) pair. -/
noncomputable def cf (α β γ : ℝ) (ric : Fin 3 → Fin 3 → ℝ) : Fin 6 → Fin 6 → ℝ :=
![
  ![
    cf00 α β γ ric,
    cf01 α β γ ric,
    cf02 α β γ ric,
    cf03 α β γ ric,
    cf04 α β γ ric,
    cf05 α β γ ric],
  ![
    cf10 α β γ ric,
    cf11 α β γ ric,
    cf12 α β γ ric,
    cf13 α β γ ric,
    cf14 α β γ ric,
    cf15 α β γ ric],
  ![
    cf20 α β γ ric,
    cf21 α β γ ric,
    cf22 α β γ ric,
    cf23 α β γ ric,
    cf24 α β γ ric,
    cf25 α β γ ric],
  ![
    cf30 α β γ ric,
    cf31 α β γ ric,
    cf32 α β γ ric,
    cf33 α β γ ric,
    cf34 α β γ ric,
    cf35 α β γ ric],
  ![
    cf40 α β γ ric,
    cf41 α β γ ric,
    cf42 α β γ ric,
    cf43 α β γ ric,
    cf44 α β γ ric,
    cf45 α β γ ric],
  ![
    cf50 α β γ ric,
    cf51 α β γ ric,
    cf52 α β γ ric,
    cf53 α β γ ric,
    cf54 α β γ ric,
    cf55 α β γ ric]]

/-- Rational form of `√a · dihSq'` when the Gram determinant `a (P₁P₂ − N²) = 36 V²`. -/
theorem sqrt_mul_dihSq' {a b c d e f a₁ b₁ c₁ d₁ e₁ f₁ V : ℝ} (ha : 0 < a)
    (hP1 : 0 < Pp a b c) (hP2 : 0 < Pp a d e) (hV : 0 < V)
    (hG : a * (Pp a b c * Pp a d e - Nn a b c d e f ^ 2) = 36 * V ^ 2) :
    √a * dihSq' a b c d e f a₁ b₁ c₁ d₁ e₁ f₁ =
      -(a / (6 * V)) * (Nn' a b c d e f a₁ b₁ c₁ d₁ e₁ f₁ -
        Nn a b c d e f / 2 * (Pp' a b c a₁ b₁ c₁ / Pp a b c + Pp' a d e a₁ d₁ e₁ / Pp a d e)) := by
  set P1 := Pp a b c
  set P2 := Pp a d e
  set N := Nn a b c d e f
  have hpp : 0 < P1 * P2 := mul_pos hP1 hP2
  have hW : 0 < P1 * P2 - N ^ 2 := by
    by_contra hneg
    have hneg' : P1 * P2 - N ^ 2 ≤ 0 := not_lt.mp hneg
    nlinarith [mul_nonpos_of_nonneg_of_nonpos ha.le hneg', sq_nonneg V, mul_pos hV hV]
  have hS : 0 < √(P1 * P2) := sqrt_pos.mpr hpp
  have hS2 : √(P1 * P2) ^ 2 = P1 * P2 := sq_sqrt hpp.le
  have h1 : 1 - (N / √(P1 * P2)) ^ 2 = (P1 * P2 - N ^ 2) / (P1 * P2) := by
    rw [div_pow, hS2]; field_simp
  have hsq : √(1 - (N / √(P1 * P2)) ^ 2) = √(P1 * P2 - N ^ 2) / √(P1 * P2) := by
    rw [h1, sqrt_div hW.le]
  have hWp : 0 < √(P1 * P2 - N ^ 2) := sqrt_pos.mpr hW
  have hWsq : √(P1 * P2 - N ^ 2) ^ 2 = P1 * P2 - N ^ 2 := sq_sqrt hW.le
  have hasq : √a ^ 2 = a := sq_sqrt ha.le
  have hasp : 0 < √a := sqrt_pos.mpr ha
  -- √a * W = 6 V
  have hk : √a * √(P1 * P2 - N ^ 2) = 6 * V := by
    have : (√a * √(P1 * P2 - N ^ 2)) ^ 2 = (6 * V) ^ 2 := by
      rw [mul_pow, hasq, hWsq]; nlinarith [hG]
    exact (sq_eq_sq₀ (by positivity) (by positivity)).mp this
  unfold dihSq'
  rw [hsq]
  have hWne := hWp.ne'
  have hSne := hS.ne'
  have hP1n := hP1.ne'
  have hP2n := hP2.ne'
  have hVn := hV.ne'
  have : a / (6 * V) = √a / √(P1 * P2 - N ^ 2) := by
    rw [div_eq_div_iff (by positivity) hWne]
    calc a * √(P1 * P2 - N ^ 2) = √a ^ 2 * √(P1 * P2 - N ^ 2) := by rw [hasq]
      _ = √a * (6 * V) := by rw [← hk]; ring
  rw [this]
  generalize √(P1 * P2) = S at hS2 hSne hsq ⊢
  field_simp
  have e1 : P1 = Pp a b c := rfl
  have e2 : P2 = Pp a d e := rfl
  have e3 : N = Nn a b c d e f := rfl
  rw [e1, e2] at hS2
  rw [e1, e2, e3, hS2]
  ring


end Lightlike.Regge.Conv3
