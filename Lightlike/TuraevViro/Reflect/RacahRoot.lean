import Lightlike.TuraevViro.Reflect.RacahRec
import Lightlike.TuraevViro.QSixJ

/-!
# The q-Racah recurrence at `q = e^{iπ/r}`

Instantiates the field-level recurrence (`RacahRec.pointwise`) at `u = e^{iπ/r} ∈ ℂ`: the quantum
integer `[k] = (u^k - u^-k)/(u - u⁻¹)` is `sin(kπ/r)/sin(π/r)`, the truncated inverse q-factorial
`invQFact` satisfies the step relation `Fi n = [n+1] Fi (n+1)` for `n ≤ r - 2`, and the q-factorial
`qfact` satisfies `Pn (n+1) = [n+1] Pn n`.
-/

set_option maxRecDepth 100000

open Real
open Lightlike.TV

namespace Lightlike.TV.Refl

/-- `u = e^{iπ/r}`. -/
noncomputable def uC (r : ℕ) : ℂ := Complex.exp (Complex.I * ((π / r : ℝ) : ℂ))

/-- The quantum integer `sin(kπ/r)/sin(π/r)` for an integer `k`. -/
noncomputable def qZ (r : ℕ) (k : ℤ) : ℝ := sin (k * π / r) / sin (π / r)

lemma uC_ne_zero (r : ℕ) : uC r ≠ 0 := Complex.exp_ne_zero _

lemma uC_zpow (r : ℕ) (k : ℤ) : uC r ^ k = Complex.exp (Complex.I * (((k * π / r : ℝ)) : ℂ)) := by
  unfold uC
  rw [← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

lemma bk_uC (r : ℕ) (k : ℤ) :
    bk (uC r ^ k) = 2 * Complex.I * (sin (k * π / r) : ℝ) := by
  rw [uC_zpow, bk, ← Complex.exp_neg, Complex.ofReal_sin, Complex.sin]
  have : -(Complex.I * ((k * π / r : ℝ) : ℂ)) = -(((k * π / r : ℝ) : ℂ)) * Complex.I := by ring
  rw [this]
  have h2 : Complex.I * ((k * π / r : ℝ) : ℂ) = ((k * π / r : ℝ) : ℂ) * Complex.I := by ring
  rw [h2]
  ring_nf
  rw [Complex.I_sq]
  ring

lemma bk_uC_div {r : ℕ} (hr : 2 ≤ r) (k : ℤ) :
    bk (uC r ^ k) / (uC r - (uC r)⁻¹) = ((qZ r k : ℝ) : ℂ) := by
  have h1 : bk (uC r ^ (1 : ℤ)) = uC r - (uC r)⁻¹ := by simp [bk]
  have hs : ((sin (π / r) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (sin_pi_div_pos hr).ne'
  rw [← h1, bk_uC, bk_uC, qZ]
  push_cast
  field_simp

/-- The step relation of the truncated inverse q-factorial, in `ℝ`, for `n ≤ r - 2`. -/
lemma invQFact_step {r : ℕ} (hr : 2 ≤ r) (n : ℤ) (hn : n ≤ (r : ℤ) - 2) :
    invQFact r n = qZ r (n + 1) * invQFact r (n + 1) := by
  rcases lt_trichotomy n (-1) with h | h | h
  · have h1 : ¬ (0 ≤ n) := by omega
    have h2 : ¬ (0 ≤ n + 1) := by omega
    simp [invQFact, h1, h2]
  · subst h
    simp [invQFact, qZ]
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, by omega⟩
    have hm : m + 1 < r := by omega
    have hq : 0 < qnum r (m + 1) := qnum_pos hr (by omega) hm
    have hqf : 0 < qfact r m := qfact_pos hr (by omega)
    have e : qZ r ((m : ℤ) + 1) = qnum r (m + 1) := by
      simp [qZ, qnum]
    have hs : qfact r (m + 1) = qfact r m * qnum r (m + 1) := by
      unfold qfact; rw [Finset.prod_range_succ]
    have h1 : (0 : ℤ) ≤ m := by omega
    have h2 : (0 : ℤ) ≤ (m : ℤ) + 1 := by omega
    simp only [invQFact, h1, h2, ite_true, Int.toNat_natCast]
    rw [show ((m : ℤ) + 1).toNat = m + 1 by omega, e, hs]
    field_simp

/-- The q-factorial as a function on `ℤ`. -/
noncomputable def PnR (r : ℕ) (n : ℤ) : ℝ := if 0 ≤ n then qfact r n.toNat else 0

lemma PnR_step (r : ℕ) (n : ℤ) (hn : 0 ≤ n) : PnR r (n + 1) = qZ r (n + 1) * PnR r n := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, by omega⟩
  have e : qZ r ((m : ℤ) + 1) = qnum r (m + 1) := by simp [qZ, qnum]
  have h2 : (0 : ℤ) ≤ (m : ℤ) + 1 := by omega
  simp only [PnR, hn, h2, ite_true, Int.toNat_natCast]
  rw [show ((m : ℤ) + 1).toNat = m + 1 by omega, e]
  unfold qfact; rw [Finset.prod_range_succ]; ring

/-- Complex inverse q-factorial. -/
noncomputable def FiC (r : ℕ) (n : ℤ) : ℂ := ((invQFact r n : ℝ) : ℂ)

/-- Complex q-factorial. -/
noncomputable def PnC (r : ℕ) (n : ℤ) : ℂ := ((PnR r n : ℝ) : ℂ)

/-- Step hypothesis `hF` of the recurrence at `u = e^{iπ/r}`, for `n ≤ r - 2`. -/
lemma FiC_step {r : ℕ} (hr : 2 ≤ r) :
    ∀ n : ℤ, n ≤ (r : ℤ) - 2 →
      FiC r n = bk (uC r ^ (n + 1)) / (uC r - (uC r)⁻¹) * FiC r (n + 1) := by
  intro n hn
  rw [bk_uC_div hr (n + 1)]
  unfold FiC
  rw [invQFact_step hr n hn]
  push_cast
  ring

/-- Step hypothesis `hP` at `u = e^{iπ/r}`, for `0 ≤ n`. -/
lemma PnC_step (r : ℕ) (hr : 2 ≤ r) (n : ℤ) (hn : 0 ≤ n) :
    PnC r (n + 1) = bk (uC r ^ (n + 1)) / (uC r - (uC r)⁻¹) * PnC r n := by
  rw [bk_uC_div hr (n + 1)]
  unfold PnC
  rw [PnR_step r n hn]
  push_cast
  ring

/-- The Racah term of the recurrence, at `u = e^{iπ/r}`, is the real q-Racah term. -/
lemma tt_eq_qRacahTerm (r : ℕ) (A1 A2 A3 A4 B1 B2 B3 : ℤ) (z : ℕ) :
    tt (Fi := FiC r) (Pn := PnC r) A1 A2 A3 A4 B1 B2 B3 (z : ℤ) =
      ((qRacahTerm r A1 A2 A3 A4 B1 B2 B3 z : ℝ) : ℂ) := by
  have h : PnC r ((z : ℤ) + 1) = ((qfact r (z + 1) : ℝ) : ℂ) := by
    unfold PnC PnR
    have : (0 : ℤ) ≤ (z : ℤ) + 1 := by omega
    simp [this]
  unfold tt qRacahTerm
  rw [h]
  simp only [FiC, zpow_natCast]
  push_cast
  ring

end Lightlike.TV.Refl
