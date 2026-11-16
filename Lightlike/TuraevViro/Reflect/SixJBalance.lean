import Lightlike.TuraevViro.Reflect.SixJRow

/-!
# Detailed balance of the recurrence of the q-6j symbol

The recurrence of `SixJRow` is symmetric for the weight `[x+1] Δ(j₁,j₂,x)² Δ(j₄,j₅,x)²`: the upper
coefficient at `x` times the weight at `x` equals the lower coefficient at `x+2` times the weight at
`x+2`. This is the algebra that makes the eigenvectors for different eigenvalues orthogonal.
-/

set_option maxRecDepth 100000

namespace Lightlike.TV.Refl

open Lightlike.TV Finset

lemma qfact_succ' (r n : ℕ) : qfact r (n + 1) = qfact r n * qnum r (n + 1) := by
  unfold qfact; rw [Finset.prod_range_succ]

/-- `Δ² ` as a ratio of quantum factorials. -/
lemma qDelta_sq {r : ℕ} (hr : 2 ≤ r) {a b c : ℕ} (h : qAdm r a b c) :
    qDelta r a b c ^ 2 = qfact r ((a + b + c) / 2 - a) * qfact r ((a + b + c) / 2 - b) *
      qfact r ((a + b + c) / 2 - c) / qfact r ((a + b + c) / 2 + 1) := by
  unfold qDelta
  rw [Real.sq_sqrt]
  have hs : (a + b + c) / 2 + 1 < r := by
    unfold qAdm Lightlike.Pentagon.Tri at h; omega
  have p1 := qfact_pos hr (show (a + b + c) / 2 - a < r by omega)
  have p2 := qfact_pos hr (show (a + b + c) / 2 - b < r by omega)
  have p3 := qfact_pos hr (show (a + b + c) / 2 - c < r by omega)
  have p4 := qfact_pos hr hs
  positivity

/-- One step of `Δ²` when the third colour grows by `2`. -/
lemma qDelta_sq_step {r : ℕ} (hr : 2 ≤ r) {j1 j2 x : ℕ} (h : qAdm r j1 j2 x)
    (h' : qAdm r j1 j2 (x + 2)) :
    qDelta r j1 j2 (x + 2) ^ 2 * (qnum r ((j1 + j2 + x) / 2 - x) * qnum r ((j1 + j2 + x) / 2 + 2))
      = qDelta r j1 j2 x ^ 2 * (qnum r ((j1 + j2 + x) / 2 - j1 + 1) * qnum r ((j1 + j2 + x) / 2 - j2 + 1)) := by
  rw [qDelta_sq hr h, qDelta_sq hr h']
  unfold qAdm Lightlike.Pentagon.Tri at h h'
  obtain ⟨c, hc⟩ : ∃ c, (j1 + j2 + x) / 2 - x = c + 1 := ⟨(j1 + j2 + x) / 2 - x - 1, by omega⟩
  have e1 : (j1 + j2 + (x + 2)) / 2 - j1 = (j1 + j2 + x) / 2 - j1 + 1 := by omega
  have e2 : (j1 + j2 + (x + 2)) / 2 - j2 = (j1 + j2 + x) / 2 - j2 + 1 := by omega
  have e3 : (j1 + j2 + (x + 2)) / 2 - (x + 2) = c := by omega
  have e4 : (j1 + j2 + (x + 2)) / 2 + 1 = (j1 + j2 + x) / 2 + 1 + 1 := by omega
  rw [e1, e2, e3, e4, hc, qfact_succ' r c, qfact_succ' r ((j1 + j2 + x) / 2 - j1),
    qfact_succ' r ((j1 + j2 + x) / 2 - j2), qfact_succ' r ((j1 + j2 + x) / 2 + 1)]
  have p4 := qfact_pos hr (show (j1 + j2 + x) / 2 + 1 < r by omega)
  have n4 : qnum r ((j1 + j2 + x) / 2 + 1 + 1) ≠ 0 := by
    have := qnum_pos hr (show 0 < (j1 + j2 + x) / 2 + 1 + 1 by omega)
      (show (j1 + j2 + x) / 2 + 1 + 1 < r by omega)
    exact this.ne'
  field_simp

lemma uC_sub_ne {r : ℕ} (hr : 2 ≤ r) : uC r - (uC r)⁻¹ ≠ 0 := by
  have := bk_uC_ne hr (m := 1) (by
    intro h; have := Int.le_of_dvd one_pos h; omega)
  simpa [bk] using this

lemma bz_nat {r : ℕ} (hr : 2 ≤ r) (n : ℕ) :
    bz r (n : ℤ) = (uC r - (uC r)⁻¹) * ((qnum r n : ℝ) : ℂ) := by
  have h := bk_uC_div hr (n : ℤ)
  have hd := uC_sub_ne hr
  have e : qZ r (n : ℤ) = qnum r n := by simp [qZ, qnum]
  rw [e] at h
  unfold bz
  rw [← h, mul_div_assoc']
  exact (mul_div_cancel_left₀ _ hd).symm

lemma qnum_ne {r : ℕ} (hr : 2 ≤ r) {n : ℕ} (h0 : 0 < n) (h1 : n < r) : qnum r n ≠ 0 :=
  (qnum_pos hr h0 h1).ne'

/-- The weight of the recurrence. -/
noncomputable def jOmega (r j1 j2 j4 j5 x : ℕ) : ℝ :=
  qnum r (x + 1) * qDelta r j1 j2 x ^ 2 * qDelta r j4 j5 x ^ 2

/-- The upper coefficient of the recurrence. -/
noncomputable def jA (r j1 j2 j4 j5 x : ℕ) : ℂ :=
  2 * (jNa r j1 j2 j4 j5 (((j1 : ℤ) + j2 + x) / 2) (((j4 : ℤ) + j5 + x) / 2) / 2 /
    (bz r (x + 1) * bz r (x + 2)))

/-- The middle coefficient of the recurrence. -/
noncomputable def jB (r j1 j2 j4 j5 x : ℕ) : ℂ :=
  2 * (jbn r j1 j2 j4 j5 x / (2 * bz r x * bz r (x + 2)))

/-- The lower coefficient of the recurrence. -/
noncomputable def jC (r j1 j2 j4 j5 x : ℕ) : ℂ :=
  2 * (jNc r x (((j1 : ℤ) + j2 + x) / 2) (((j4 : ℤ) + j5 + x) / 2) / 2 /
    (bz r x * bz r (x + 1)))

set_option maxHeartbeats 800000 in
/-- **Detailed balance**: `ω(x) · A(x) = ω(x+2) · C(x+2)`. -/
theorem sixj_balance {r : ℕ} (hr : 2 ≤ r) {j1 j2 x j4 j5 : ℕ} (h1 : qAdm r j1 j2 x)
    (h1' : qAdm r j1 j2 (x + 2)) (h4 : qAdm r j4 j5 x) (h4' : qAdm r j4 j5 (x + 2)) :
    (jOmega r j1 j2 j4 j5 x : ℂ) * jA r j1 j2 j4 j5 x
      = (jOmega r j1 j2 j4 j5 (x + 2) : ℂ) * jC r j1 j2 j4 j5 (x + 2) := by
  have st1 := qDelta_sq_step hr h1 h1'
  have st2 := qDelta_sq_step hr h4 h4'
  unfold qAdm Lightlike.Pentagon.Tri at h1 h1' h4 h4'
  have hd := uC_sub_ne hr
  have nz : ∀ n : ℕ, 0 < n → n < r → ((qnum r n : ℝ) : ℂ) ≠ 0 := fun n h0 h1 =>
    Complex.ofReal_ne_zero.mpr (qnum_ne hr h0 h1)
  unfold jOmega jA jC jNa jNc
  have e1 : (((j1 : ℤ) + j2 + x) / 2) - j2 + 1 = (((j1 + j2 + x) / 2 - j2 + 1 : ℕ) : ℤ) := by omega
  have e2 : (((j1 : ℤ) + j2 + x) / 2) - j1 + 1 = (((j1 + j2 + x) / 2 - j1 + 1 : ℕ) : ℤ) := by omega
  have e3 : (((j4 : ℤ) + j5 + x) / 2) - j4 + 1 = (((j4 + j5 + x) / 2 - j4 + 1 : ℕ) : ℤ) := by omega
  have e4 : (((j4 : ℤ) + j5 + x) / 2) - j5 + 1 = (((j4 + j5 + x) / 2 - j5 + 1 : ℕ) : ℤ) := by omega
  have f1 : (((j1 : ℤ) + j2 + ((x + 2 : ℕ) : ℤ)) / 2) + 1 = (((j1 + j2 + x) / 2 + 2 : ℕ) : ℤ) := by omega
  have f2 : (((j4 : ℤ) + j5 + ((x + 2 : ℕ) : ℤ)) / 2) + 1 = (((j4 + j5 + x) / 2 + 2 : ℕ) : ℤ) := by omega
  have f3 : (((j1 : ℤ) + j2 + ((x + 2 : ℕ) : ℤ)) / 2) - ((x + 2 : ℕ) : ℤ) + 1
      = (((j1 + j2 + x) / 2 - x : ℕ) : ℤ) := by omega
  have f4 : (((j4 : ℤ) + j5 + ((x + 2 : ℕ) : ℤ)) / 2) - ((x + 2 : ℕ) : ℤ) + 1
      = (((j4 + j5 + x) / 2 - x : ℕ) : ℤ) := by omega
  have g1 : ((x + 1 : ℕ) : ℤ) = (x : ℤ) + 1 := by push_cast; ring
  rw [e1, e2, e3, e4, f1, f2, f3, f4]
  rw [show (((x + 2 : ℕ) : ℤ) + 1) = ((x + 3 : ℕ) : ℤ) by push_cast; ring,
    show ((x : ℤ) + 1) = ((x + 1 : ℕ) : ℤ) by push_cast; ring,
    show ((x : ℤ) + 2) = ((x + 2 : ℕ) : ℤ) by push_cast; ring]
  simp only [bz_nat hr]
  have c1 : (((qDelta r j1 j2 (x + 2) ^ 2 : ℝ)) : ℂ) *
      (((qnum r ((j1 + j2 + x) / 2 - x) : ℝ) : ℂ) * ((qnum r ((j1 + j2 + x) / 2 + 2) : ℝ) : ℂ))
      = ((qDelta r j1 j2 x ^ 2 : ℝ) : ℂ) *
        (((qnum r ((j1 + j2 + x) / 2 - j1 + 1) : ℝ) : ℂ) *
          ((qnum r ((j1 + j2 + x) / 2 - j2 + 1) : ℝ) : ℂ)) := by exact_mod_cast st1
  have c2 : (((qDelta r j4 j5 (x + 2) ^ 2 : ℝ)) : ℂ) *
      (((qnum r ((j4 + j5 + x) / 2 - x) : ℝ) : ℂ) * ((qnum r ((j4 + j5 + x) / 2 + 2) : ℝ) : ℂ))
      = ((qDelta r j4 j5 x ^ 2 : ℝ) : ℂ) *
        (((qnum r ((j4 + j5 + x) / 2 - j4 + 1) : ℝ) : ℂ) *
          ((qnum r ((j4 + j5 + x) / 2 - j5 + 1) : ℝ) : ℂ)) := by exact_mod_cast st2
  push_cast
  have n1 := nz (x + 1) (by omega) (by omega)
  have n2 := nz (x + 2) (by omega) (by omega)
  have n3 := nz (x + 3) (by omega) (by omega)
  have n4 := nz ((j1 + j2 + x) / 2 + 2) (by omega) (by omega)
  have n5 := nz ((j4 + j5 + x) / 2 + 2) (by omega) (by omega)
  have n6 := nz ((j1 + j2 + x) / 2 - x) (by omega) (by omega)
  have n7 := nz ((j4 + j5 + x) / 2 - x) (by omega) (by omega)
  push_cast at c1 c2
  field_simp
  linear_combination
    (-((uC r ^ 2 - 1) ^ 2 / uC r ^ 2)
        * (((qDelta r j4 j5 x : ℝ) : ℂ) ^ 2 * ((qnum r ((j4 + j5 + x) / 2 - j4 + 1) : ℝ) : ℂ) *
          ((qnum r ((j4 + j5 + x) / 2 - j5 + 1) : ℝ) : ℂ))) * c1
    + (-((uC r ^ 2 - 1) ^ 2 / uC r ^ 2)
        * (((qDelta r j1 j2 (x + 2) : ℝ) : ℂ) ^ 2 * ((qnum r ((j1 + j2 + x) / 2 - x) : ℝ) : ℂ) *
          ((qnum r ((j1 + j2 + x) / 2 + 2) : ℝ) : ℂ))) * c2

end Lightlike.TV.Refl
