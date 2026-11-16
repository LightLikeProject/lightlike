import Lightlike.TuraevViro.Reflect.EndRowTrig
import Lightlike.TuraevViro.Reflect.SixJEnd
import Lightlike.TuraevViro.Reflect.SixJBalance

/-!
# The row of the recurrence at the lowest third colour `x = 0`

For `x = 0` the recurrence of `SixJRow` is `0/0`: both the denominator `[x]` and the coefficient of the
middle term vanish. The row that holds instead is a plain identity, in which the middle coefficient
`cz(B+1) cz(E+1) / cz 1` does not depend on the sixth colour `q`:
`bz(1)² Sj(2) + cz(B+1) cz(E+1) Sj(0) = cz(1) cz(1+q) Sj(0)`.
The sum at `x = 0` is one term and the sum at `x = 2` has two, so after division by the first term the
row is the identity `end_trig` of the quantum integers of the exponents.
-/

set_option maxHeartbeats 400000
set_option maxRecDepth 100000

namespace Lightlike.TV.Refl

open Lightlike.TV Finset

lemma invQ_nat (r n : ℕ) : invQFact r (n : ℤ) = (qfact r n)⁻¹ := by simp [invQFact]

lemma invQ_neg (r : ℕ) {u : ℤ} (h : u < 0) : invQFact r u = 0 := by
  simp [invQFact, not_le.mpr h]

lemma invQ_zero (r : ℕ) : invQFact r 0 = 1 := by simp [invQFact, qfact]

lemma invQ_one {r : ℕ} (hr : 2 ≤ r) : invQFact r 1 = 1 := by
  have : invQFact r ((1 : ℕ) : ℤ) = 1 := by
    rw [invQ_nat]; simp [qfact, qnum_one hr]
  simpa using this

/-- `[n-1]!⁻¹ = [n] · [n]!⁻¹` for `n < r`. -/
lemma invQ_pred {r : ℕ} (hr : 2 ≤ r) (n : ℕ) (hn : n < r) :
    invQFact r ((n : ℤ) - 1) = qnum r n * invQFact r n := by
  rcases n with _ | m
  · simp only [qnum_zero, zero_mul]; exact invQ_neg r (by norm_num)
  · have e : (((m + 1 : ℕ) : ℤ) - 1) = (m : ℤ) := by push_cast; ring
    rw [e, invQ_nat, invQ_nat, qfact_succ']
    have h1 := qnum_ne hr (Nat.succ_pos m) hn
    have h2 := (qfact_pos hr (by omega : m < r)).ne'
    field_simp

/-- The common factor of the endpoint sums. -/
noncomputable def endF (r n1 n2 n3 : ℕ) : ℝ :=
  (-1) ^ (n1 + n2 + n3) * qfact r (n1 + n2 + n3 + 1) *
    (invQFact r n1 * invQFact r n2 * invQFact r n3)

/-- The sum at `x = 0` is the single term `endF`. -/
lemma sr_low {r : ℕ} (n1 n2 n3 : ℕ) :
    SR r ((n2 + n3 : ℕ) : ℤ) ((n1 + n2 + n3 : ℕ) : ℤ) ((n1 + n2 + n3 : ℕ) : ℤ)
      ((n1 + n3 : ℕ) : ℤ) ((n1 + n2 + 2 * n3 : ℕ) : ℤ) ((n1 + n2 + n3 : ℕ) : ℤ)
      ((n1 + n2 + n3 : ℕ) : ℤ) = endF r n1 n2 n3 := by
  unfold SR
  rw [Finset.sum_eq_single (n1 + n2 + n3)]
  · unfold qRacahTerm endF
    have e1 : ((n1 + n2 + n3 : ℕ) : ℤ) - ((n2 + n3 : ℕ) : ℤ) = (n1 : ℤ) := by omega
    have e2 : ((n1 + n2 + n3 : ℕ) : ℤ) - ((n1 + n3 : ℕ) : ℤ) = (n2 : ℤ) := by omega
    have e3 : ((n1 + n2 + 2 * n3 : ℕ) : ℤ) - ((n1 + n2 + n3 : ℕ) : ℤ) = (n3 : ℤ) := by omega
    have e0 : ((n1 + n2 + n3 : ℕ) : ℤ) - ((n1 + n2 + n3 : ℕ) : ℤ) = 0 := by omega
    rw [e1, e2, e3, e0, invQ_zero]
    ring
  · intro z _ hz
    exact qRacahTerm_zero_of_out (by intro h; omega)
  · intro h; exfalso; apply h
    simp only [Finset.mem_range]; omega

/-- An `SR` whose only possibly nonzero terms are `z = P` and `z = P + 1`. -/
lemma SR_two {r : ℕ} {a1 a2 a3 a4 b1 b2 b3 : ℤ} (P : ℕ)
    (hz : ∀ z : ℕ, z ≠ P → z ≠ P + 1 →
      ¬ (a1 ≤ z ∧ a2 ≤ z ∧ a3 ≤ z ∧ a4 ≤ z ∧ (z : ℤ) ≤ b1 ∧ (z : ℤ) ≤ b2 ∧ (z : ℤ) ≤ b3)) :
    SR r a1 a2 a3 a4 b1 b2 b3 =
      qRacahTerm r a1 a2 a3 a4 b1 b2 b3 P + qRacahTerm r a1 a2 a3 a4 b1 b2 b3 (P + 1) := by
  unfold SR
  have h1 : ∑ z ∈ range (b1.toNat + 1), qRacahTerm r a1 a2 a3 a4 b1 b2 b3 z =
      ∑ z ∈ range (b1.toNat + P + 3), qRacahTerm r a1 a2 a3 a4 b1 b2 b3 z :=
    Finset.sum_subset (Finset.range_mono (by omega)) (fun z hz hz' =>
      qRacahTerm_zero_of_out (by
        intro h; simp only [Finset.mem_range] at hz hz'; omega))
  have h2 : ∑ z ∈ ({P, P + 1} : Finset ℕ), qRacahTerm r a1 a2 a3 a4 b1 b2 b3 z =
      ∑ z ∈ range (b1.toNat + P + 3), qRacahTerm r a1 a2 a3 a4 b1 b2 b3 z :=
    Finset.sum_subset (by intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton,
        Finset.mem_range] at hz ⊢; omega)
      (fun z _ hz' => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz'
        exact qRacahTerm_zero_of_out (hz z hz'.1 hz'.2))
  rw [h1, ← h2, Finset.sum_pair (by omega)]

/-- The sum at `x = 2`: two terms. -/
lemma sr_two {r : ℕ} (hr : 2 ≤ r) (n1 n2 n3 : ℕ) (hP : n1 + n2 + n3 + 2 ≤ r) :
    SR r ((n2 + n3 + 1 : ℕ) : ℤ) ((n1 + n2 + n3 : ℕ) : ℤ) ((n1 + n2 + n3 : ℕ) : ℤ)
      ((n1 + n3 + 1 : ℕ) : ℤ) ((n1 + n2 + 2 * n3 : ℕ) : ℤ) ((n1 + n2 + n3 + 1 : ℕ) : ℤ)
      ((n1 + n2 + n3 + 1 : ℕ) : ℤ) =
      endF r n1 n2 n3 * (qnum r n1 * qnum r n2 - qnum r (n1 + n2 + n3 + 2) * qnum r n3) := by
  rw [SR_two (n1 + n2 + n3) (fun z h1 h2 => by intro h; omega)]
  unfold qRacahTerm endF
  have e1 : ((n1 + n2 + n3 : ℕ) : ℤ) - ((n2 + n3 + 1 : ℕ) : ℤ) = (n1 : ℤ) - 1 := by omega
  have e2 : ((n1 + n2 + n3 : ℕ) : ℤ) - ((n1 + n3 + 1 : ℕ) : ℤ) = (n2 : ℤ) - 1 := by omega
  have e3 : ((n1 + n2 + 2 * n3 : ℕ) : ℤ) - ((n1 + n2 + n3 : ℕ) : ℤ) = (n3 : ℤ) := by omega
  have e0 : ((n1 + n2 + n3 : ℕ) : ℤ) - ((n1 + n2 + n3 : ℕ) : ℤ) = 0 := by omega
  have e4 : ((n1 + n2 + n3 + 1 : ℕ) : ℤ) - ((n1 + n2 + n3 : ℕ) : ℤ) = ((1 : ℕ) : ℤ) := by omega
  have f1 : (((n1 + n2 + n3 + 1 : ℕ) : ℤ)) - ((n2 + n3 + 1 : ℕ) : ℤ) = (n1 : ℤ) := by omega
  have f2 : (((n1 + n2 + n3 + 1 : ℕ) : ℤ)) - ((n1 + n3 + 1 : ℕ) : ℤ) = (n2 : ℤ) := by omega
  have f3 : ((n1 + n2 + 2 * n3 : ℕ) : ℤ) - ((n1 + n2 + n3 + 1 : ℕ) : ℤ) = (n3 : ℤ) - 1 := by omega
  have f0 : ((n1 + n2 + n3 + 1 : ℕ) : ℤ) - ((n1 + n2 + n3 + 1 : ℕ) : ℤ) = 0 := by omega
  have f4 : ((n1 + n2 + n3 + 1 : ℕ) : ℤ) - ((n1 + n2 + n3 : ℕ) : ℤ) = ((1 : ℕ) : ℤ) := by omega
  have g0 : ((n1 + n2 + n3 : ℕ) : ℤ) - ((n1 + n2 + n3 + 1 : ℕ) : ℤ) = -1 := by omega
  rw [e1, e2, e3, e0, f1, f2, f3, f0, invQ_zero, invQ_pred hr n1 (by omega),
    invQ_pred hr n2 (by omega), invQ_pred hr n3 (by omega)]
  rw [e4, Nat.cast_one, invQ_one hr, qfact_succ' r (n1 + n2 + n3 + 1)]
  have hq : qnum r (n1 + n2 + n3 + 1 + 1) = qnum r (n1 + n2 + n3 + 2) := rfl
  rw [hq]
  ring

/-- **The row of the recurrence at the lowest third colour `x = 0`.** Here `j₁ = j₂ = B` and
`j₄ = j₅ = E`, and the middle coefficient `cz(B+1) cz(E+1) / cz 1` does not depend on `q`. -/
theorem endrow_low {r : ℕ} (hr : 2 ≤ r) (B E q : ℕ) (h1 : qAdm r B E q) (h2 : qAdm r E B q) :
    bz r 1 ^ 2 * (Sj r B B E E q 2 : ℂ)
      + cz r ((B : ℤ) + 1) * cz r ((E : ℤ) + 1) * (Sj r B B E E q 0 : ℂ)
      = cz r 1 * cz r (1 + q) * (Sj r B B E E q 0 : ℂ) := by
  unfold qAdm Lightlike.Pentagon.Tri at h1 h2
  obtain ⟨n1, n2, n3, hB, hE, hq⟩ : ∃ n1 n2 n3 : ℕ, B = n2 + n3 ∧ E = n1 + n3 ∧ q = n1 + n2 :=
    ⟨(E + q - B) / 2, (B + q - E) / 2, (B + E - q) / 2, by omega, by omega, by omega⟩
  subst hB hE hq
  have S0 : Sj r (n2 + n3) (n2 + n3) (n1 + n3) (n1 + n3) (n1 + n2) 0 = endF r n1 n2 n3 := by
    rw [← sr_low n1 n2 n3]; unfold Sj; congr 1 <;> omega
  have S2 : Sj r (n2 + n3) (n2 + n3) (n1 + n3) (n1 + n3) (n1 + n2) 2 =
      endF r n1 n2 n3 * (qnum r n1 * qnum r n2 - qnum r (n1 + n2 + n3 + 2) * qnum r n3) := by
    rw [← sr_two hr n1 n2 n3 (by omega)]; unfold Sj; congr 1 <;> omega
  rw [S0, S2]
  have T := end_trig r n1 n2 n3
  have b1 := bz_nat hr 1
  have b2 := bz_nat hr n1
  have b3 := bz_nat hr n2
  have b4 := bz_nat hr n3
  have b5 := bz_nat hr (n1 + n2 + n3 + 2)
  rw [b2, b3, b4, b5] at T
  have c1 : (((n2 + n3 : ℕ) : ℤ) + 1) = ((n2 + n3 + 1 : ℕ) : ℤ) := by push_cast; ring
  have c2 : (((n1 + n3 : ℕ) : ℤ) + 1) = ((n1 + n3 + 1 : ℕ) : ℤ) := by push_cast; ring
  have c3 : (1 + ((n1 + n2 : ℕ) : ℤ)) = ((n1 + n2 + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [c1, c2, c3]
  simp only [Nat.cast_one, qnum_one hr] at b1
  rw [b1]
  push_cast at T ⊢
  linear_combination (((endF r n1 n2 n3 : ℝ) : ℂ)) * T

end Lightlike.TV.Refl


