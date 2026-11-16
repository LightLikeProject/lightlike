import Lightlike.TuraevViro.Reflect.EndRowLow

/-!
# The row of the recurrence at the highest third colour `x = r - 2`

For `x = r - 2` the denominator `[x + 2] = [r]` of the recurrence of `SixJRow` vanishes together with
the coefficient of the middle term. The row that holds instead is the plain identity
`bz(1)² Sj(r-4) - cz(j₁+1) cz(j₄+1) Sj(r-2) = cz(1) cz(1+q) Sj(r-2)`.
With `j₁ = k₂+k₄`, `j₂ = k₁+k₃`, `j₄ = k₁+k₄`, `j₅ = k₂+k₃`, `q = k₃+k₄` and `k₁+k₂+k₃+k₄ = r-2`,
the sum at `x = r-2` is one term and the sum at `x = r-4` has two, so the row reduces to the identity
`end_trig_top` of the quantum integers of the `kᵢ`.
-/

set_option maxHeartbeats 400000
set_option maxRecDepth 100000

namespace Lightlike.TV.Refl

open Lightlike.TV Finset

/-- The common factor of the top endpoint sums (`P + 1 = k₁+k₂+k₃+k₄`). -/
noncomputable def endH (r P k1 k2 k3 k4 : ℕ) : ℝ :=
  (-1) ^ P * qfact r (P + 1) * (invQFact r k1 * invQFact r k2 * invQFact r k3 * invQFact r k4)

/-- The sum at `x = r - 2`: one term. -/
lemma sr_top {r : ℕ} (P k1 k2 k3 k4 : ℕ) (hP : k1 + k2 + k3 + k4 = P + 1) :
    SR r ((P + 1 : ℕ) : ℤ) ((k2 + k3 + k4 : ℕ) : ℤ) ((k1 + k3 + k4 : ℕ) : ℤ) ((P + 1 : ℕ) : ℤ)
      ((P + 1 : ℕ) : ℤ) ((P + 1 + k3 : ℕ) : ℤ) ((P + 1 + k4 : ℕ) : ℤ) =
      -(endH r P k1 k2 k3 k4) * qnum r (P + 2) := by
  unfold SR
  rw [Finset.sum_eq_single (P + 1)]
  · unfold qRacahTerm endH
    have d0 : ((P + 1 : ℕ) : ℤ) - ((P + 1 : ℕ) : ℤ) = 0 := by omega
    have d1 : ((P + 1 : ℕ) : ℤ) - ((k2 + k3 + k4 : ℕ) : ℤ) = (k1 : ℤ) := by omega
    have d2 : ((P + 1 : ℕ) : ℤ) - ((k1 + k3 + k4 : ℕ) : ℤ) = (k2 : ℤ) := by omega
    have d3 : ((P + 1 + k3 : ℕ) : ℤ) - ((P + 1 : ℕ) : ℤ) = (k3 : ℤ) := by omega
    have d4 : ((P + 1 + k4 : ℕ) : ℤ) - ((P + 1 : ℕ) : ℤ) = (k4 : ℤ) := by omega
    rw [d0, d1, d2, d3, d4, invQ_zero, qfact_succ' r (P + 1)]
    have hq : qnum r (P + 1 + 1) = qnum r (P + 2) := rfl
    rw [hq]
    ring
  · intro z _ hz
    exact qRacahTerm_zero_of_out (by intro h; omega)
  · intro h; exfalso; apply h
    simp only [Finset.mem_range]; omega

/-- The sum at `x = r - 4`: two terms. -/
lemma sr_top_two {r : ℕ} (hr : 2 ≤ r) (P k1 k2 k3 k4 : ℕ) (hP : k1 + k2 + k3 + k4 = P + 1)
    (hPr : P + 2 ≤ r) :
    SR r (P : ℤ) ((k2 + k3 + k4 : ℕ) : ℤ) ((k1 + k3 + k4 : ℕ) : ℤ) (P : ℤ)
      ((P + 1 : ℕ) : ℤ) ((P + k3 : ℕ) : ℤ) ((P + k4 : ℕ) : ℤ) =
      endH r P k1 k2 k3 k4 *
        (qnum r k1 * qnum r k2 - qnum r (P + 2) * (qnum r k3 * qnum r k4)) := by
  rw [SR_two P (fun z h1 h2 => by intro h; omega)]
  unfold qRacahTerm endH
  have a0 : (P : ℤ) - (P : ℤ) = 0 := by omega
  have a1 : (P : ℤ) - ((k2 + k3 + k4 : ℕ) : ℤ) = (k1 : ℤ) - 1 := by omega
  have a2 : (P : ℤ) - ((k1 + k3 + k4 : ℕ) : ℤ) = (k2 : ℤ) - 1 := by omega
  have a3 : ((P + 1 : ℕ) : ℤ) - (P : ℤ) = ((1 : ℕ) : ℤ) := by omega
  have a4 : ((P + k3 : ℕ) : ℤ) - (P : ℤ) = (k3 : ℤ) := by omega
  have a5 : ((P + k4 : ℕ) : ℤ) - (P : ℤ) = (k4 : ℤ) := by omega
  have b1 : ((P + 1 : ℕ) : ℤ) - ((k2 + k3 + k4 : ℕ) : ℤ) = (k1 : ℤ) := by omega
  have b2 : ((P + 1 : ℕ) : ℤ) - ((k1 + k3 + k4 : ℕ) : ℤ) = (k2 : ℤ) := by omega
  have b0 : ((P + 1 : ℕ) : ℤ) - ((P + 1 : ℕ) : ℤ) = 0 := by omega
  have b4 : ((P + k3 : ℕ) : ℤ) - ((P + 1 : ℕ) : ℤ) = (k3 : ℤ) - 1 := by omega
  have b5 : ((P + k4 : ℕ) : ℤ) - ((P + 1 : ℕ) : ℤ) = (k4 : ℤ) - 1 := by omega
  rw [a0, a1, a2, a3, a4, a5, b1, b2, b0, b4, b5, invQ_zero, Nat.cast_one, invQ_one hr,
    invQ_pred hr k1 (by omega), invQ_pred hr k2 (by omega), invQ_pred hr k3 (by omega),
    invQ_pred hr k4 (by omega), qfact_succ' r (P + 1)]
  have hq : qnum r (P + 1 + 1) = qnum r (P + 2) := rfl
  rw [hq]
  ring

/-- **The row of the recurrence at the highest third colour `x = r - 2`.** -/
theorem endrow_top {r : ℕ} (hr : 3 ≤ r) (j1 j2 j4 j5 q : ℕ) (hs1 : j1 + j2 + 2 = r)
    (hs2 : j4 + j5 + 2 = r) (h1 : qAdm r j1 j5 q) (h2 : qAdm r j4 j2 q) :
    bz r 1 ^ 2 * (Sj r j1 j2 j4 j5 q ((r : ℤ) - 4) : ℂ)
      - cz r ((j1 : ℤ) + 1) * cz r ((j4 : ℤ) + 1) * (Sj r j1 j2 j4 j5 q ((r : ℤ) - 2) : ℂ)
      = cz r 1 * cz r (1 + q) * (Sj r j1 j2 j4 j5 q ((r : ℤ) - 2) : ℂ) := by
  have hr2 : 2 ≤ r := by omega
  unfold qAdm Lightlike.Pentagon.Tri at h1 h2
  obtain ⟨k1, k2, k3, k4, e1, e2, e3, e4, e5⟩ : ∃ k1 k2 k3 k4 : ℕ, j1 = k2 + k4 ∧ j2 = k1 + k3 ∧
      j4 = k1 + k4 ∧ j5 = k2 + k3 ∧ q = k3 + k4 :=
    ⟨(j4 + j2 - q) / 2, (j1 + j5 - q) / 2, (j2 + q - j4) / 2, (j1 + q - j5) / 2, by omega,
      by omega, by omega, by omega, by omega⟩
  subst e1 e2 e3 e4 e5
  obtain ⟨P, rfl⟩ : ∃ P, r = P + 3 := ⟨r - 3, by omega⟩
  have hP : k1 + k2 + k3 + k4 = P + 1 := by omega
  have hq1 : qnum (P + 3) (P + 2) = 1 := by
    have := qnum_sub (r := P + 3) (n := 1) hr2 (by omega)
    simpa [qnum_one hr2] using this
  have S1 : Sj (P + 3) (k2 + k4) (k1 + k3) (k1 + k4) (k2 + k3) (k3 + k4)
      (((P + 3 : ℕ) : ℤ) - 2) = -(endH (P + 3) P k1 k2 k3 k4) := by
    have := sr_top (r := P + 3) P k1 k2 k3 k4 hP
    rw [hq1, mul_one] at this
    rw [← this]; unfold Sj; congr 1 <;> omega
  have S2 : Sj (P + 3) (k2 + k4) (k1 + k3) (k1 + k4) (k2 + k3) (k3 + k4)
      (((P + 3 : ℕ) : ℤ) - 4) = endH (P + 3) P k1 k2 k3 k4 *
        (qnum (P + 3) k1 * qnum (P + 3) k2 - qnum (P + 3) k3 * qnum (P + 3) k4) := by
    have := sr_top_two (r := P + 3) hr2 P k1 k2 k3 k4 hP (by omega)
    rw [hq1, one_mul] at this
    rw [← this]; unfold Sj; congr 1 <;> omega
  rw [S1, S2]
  have T := end_trig_top hr2 k1 k2 k3 k4 (by omega)
  have b1 := bz_nat hr2 1
  have b2 := bz_nat hr2 k1
  have b3 := bz_nat hr2 k2
  have b4 := bz_nat hr2 k3
  have b5 := bz_nat hr2 k4
  rw [b2, b3, b4, b5] at T
  have c1 : (((k2 + k4 : ℕ) : ℤ) + 1) = ((k2 + k4 + 1 : ℕ) : ℤ) := by push_cast; ring
  have c2 : (((k1 + k4 : ℕ) : ℤ) + 1) = ((k1 + k4 + 1 : ℕ) : ℤ) := by push_cast; ring
  have c3 : (1 + ((k3 + k4 : ℕ) : ℤ)) = ((k3 + k4 + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [c1, c2, c3]
  simp only [Nat.cast_one, qnum_one hr2] at b1
  rw [b1]
  push_cast at T ⊢
  linear_combination (-((endH (P + 3) P k1 k2 k3 k4 : ℝ) : ℂ)) * T

end Lightlike.TV.Refl
