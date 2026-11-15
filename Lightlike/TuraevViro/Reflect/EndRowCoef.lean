import Lightlike.TuraevViro.Reflect.EndRowTop
import Lightlike.TuraevViro.Reflect.SixJRow

/-!
# The endpoint rows in the form of the recurrence coefficients

At `x = 0` the upper coefficient `jA` and at `x = r - 2` the lower coefficient `jC` are regular and
equal to `bz(1)² / cz(1)`. Only the middle coefficient has to be replaced by `± cz(j₁+1) cz(j₄+1) /
cz(1)`. This file states the two endpoint rows with the regular coefficients.
-/

set_option maxHeartbeats 400000
set_option maxRecDepth 100000

namespace Lightlike.TV.Refl

open Lightlike.TV Finset

lemma bz_two (r : ℕ) : bz r 2 = bz r 1 * cz r 1 := by
  unfold bz cz bk ck
  have : uC r ^ (2 : ℤ) = uC r * uC r := zpow_two _
  rw [this, zpow_one, mul_inv]
  ring

lemma bz_one_ne {r : ℕ} (hr : 2 ≤ r) : bz r 1 ≠ 0 := by
  have h := bz_nat hr 1
  simp only [Nat.cast_one, qnum_one hr, Complex.ofReal_one, mul_one] at h
  rw [h]; exact uC_sub_ne hr

lemma cz_one_eq {r : ℕ} (hr : 2 ≤ r) : cz r 1 = ((qnum r 2 : ℝ) : ℂ) := by
  have h2 := bz_nat hr 2
  have h1 := bz_nat hr 1
  simp only [Nat.cast_one, qnum_one hr, Complex.ofReal_one, mul_one] at h1
  have h2' : bz r 2 = (uC r - (uC r)⁻¹) * ((qnum r 2 : ℝ) : ℂ) := by exact_mod_cast h2
  rw [bz_two, h1] at h2'
  exact mul_left_cancel₀ (uC_sub_ne hr) h2'

lemma cz_one_ne {r : ℕ} (hr : 3 ≤ r) : cz r 1 ≠ 0 := by
  rw [cz_one_eq (by omega)]
  exact Complex.ofReal_ne_zero.mpr (qnum_ne (by omega) (by omega) (by omega))

/-- The upper coefficient at `x = 0` for `j₁ = j₂`, `j₄ = j₅`. -/
lemma jA_low {r : ℕ} (hr : 3 ≤ r) (B E : ℕ) : jA r B B E E 0 = bz r 1 ^ 2 / cz r 1 := by
  have h1 := bz_one_ne (by omega : 2 ≤ r)
  have h2 := cz_one_ne hr
  unfold jA jNa
  simp only [Nat.cast_zero, add_zero, zero_add,
    show ((B : ℤ) + B) / 2 - B + 1 = 1 by omega, show ((E : ℤ) + E) / 2 - E + 1 = 1 by omega]
  rw [bz_two]
  field_simp

/-- The lower coefficient at `x = r - 2`, where `r = P + 3` and `j₁ + j₂ = j₄ + j₅ = P + 1`. -/
lemma jC_top {P : ℕ} (hr : 3 ≤ P + 3) (j1 j2 j4 j5 : ℕ) (hs1 : j1 + j2 = P + 1)
    (hs2 : j4 + j5 = P + 1) :
    jC (P + 3) j1 j2 j4 j5 (P + 1) = bz (P + 3) 1 ^ 2 / cz (P + 3) 1 := by
  have hr2 : 2 ≤ P + 3 := by omega
  have hb1 := bz_one_ne hr2
  have hc1 := cz_one_ne hr
  have hq1 : qnum (P + 3) (P + 2) = 1 := by
    have := qnum_sub (r := P + 3) (n := 1) hr2 (by omega)
    simpa [qnum_one hr2] using this
  have hq2 : qnum (P + 3) (P + 1) = qnum (P + 3) 2 := by
    have := qnum_sub (r := P + 3) (n := 2) hr2 (by omega)
    simpa using this
  have hqne : qnum (P + 3) (P + 1) ≠ 0 := qnum_ne hr2 (by omega) (by omega)
  have hs : ((j1 : ℤ) + j2 + ((P + 1 : ℕ) : ℤ)) / 2 = ((P + 1 : ℕ) : ℤ) := by omega
  have ht : ((j4 : ℤ) + j5 + ((P + 1 : ℕ) : ℤ)) / 2 = ((P + 1 : ℕ) : ℤ) := by omega
  have c1 : ((P + 1 : ℕ) : ℤ) + 1 = ((P + 2 : ℕ) : ℤ) := by push_cast; ring
  unfold jC jNc
  rw [hs, ht, sub_self, zero_add, c1]
  have b1 := bz_nat hr2 1
  simp only [Nat.cast_one, qnum_one hr2, Complex.ofReal_one, mul_one] at b1
  have b2 := bz_nat hr2 (P + 1)
  have b3 := bz_nat hr2 (P + 2)
  rw [b2, b3, hq1, b1]
  rw [cz_one_eq hr2, ← hq2]
  have hd := uC_sub_ne hr2
  have hqc : ((qnum (P + 3) (P + 1) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hqne
  push_cast
  field_simp

/-- The row at `x = 0`, with the regular upper coefficient. -/
theorem row_low {r : ℕ} (hr : 3 ≤ r) (B E q : ℕ) (h1 : qAdm r B E q) (h2 : qAdm r E B q) :
    jA r B B E E 0 * (Sj r B B E E q 2 : ℂ)
      + (cz r ((B : ℤ) + 1) * cz r ((E : ℤ) + 1) / cz r 1) * (Sj r B B E E q 0 : ℂ)
      = cz r (1 + q) * (Sj r B B E E q 0 : ℂ) := by
  have E' := endrow_low (by omega) B E q h1 h2
  have h3 := cz_one_ne hr
  rw [jA_low hr]
  field_simp
  linear_combination E'

/-- The row at `x = r - 2`, with the regular lower coefficient. -/
theorem row_top {P : ℕ} (hr : 3 ≤ P + 3) (j1 j2 j4 j5 q : ℕ) (hs1 : j1 + j2 + 2 = P + 3)
    (hs2 : j4 + j5 + 2 = P + 3) (h1 : qAdm (P + 3) j1 j5 q) (h2 : qAdm (P + 3) j4 j2 q) :
    jC (P + 3) j1 j2 j4 j5 (P + 1) * (Sj (P + 3) j1 j2 j4 j5 q (((P + 3 : ℕ) : ℤ) - 4) : ℂ)
      + (-(cz (P + 3) ((j1 : ℤ) + 1) * cz (P + 3) ((j4 : ℤ) + 1) / cz (P + 3) 1)) *
          (Sj (P + 3) j1 j2 j4 j5 q (((P + 3 : ℕ) : ℤ) - 2) : ℂ)
      = cz (P + 3) (1 + q) * (Sj (P + 3) j1 j2 j4 j5 q (((P + 3 : ℕ) : ℤ) - 2) : ℂ) := by
  have E' := endrow_top hr j1 j2 j4 j5 q hs1 hs2 h1 h2
  have h3 := cz_one_ne hr
  rw [jC_top hr j1 j2 j4 j5 (by omega) (by omega)]
  field_simp
  linear_combination E'

lemma bz_zero (r : ℕ) : bz r 0 = 0 := by unfold bz bk; simp

lemma bz_self {r : ℕ} (hr : 2 ≤ r) : bz r (r : ℤ) = 0 := by
  unfold bz bk
  rw [zpow_natCast, uC_pow_self hr]
  norm_num

/-- At `x = 0` the lower coefficient is the division by `bz 0 = 0`, hence zero. -/
lemma jC_zero (r j1 j2 j4 j5 : ℕ) : jC r j1 j2 j4 j5 0 = 0 := by
  unfold jC
  simp [bz_zero]

/-- At `x = r - 2` the upper coefficient is the division by `bz r = 0`, hence zero. -/
lemma jA_top {P : ℕ} (hr : 2 ≤ P + 3) (j1 j2 j4 j5 : ℕ) : jA (P + 3) j1 j2 j4 j5 (P + 1) = 0 := by
  unfold jA
  rw [show ((P + 1 : ℕ) : ℤ) + 2 = ((P + 3 : ℕ) : ℤ) by push_cast; ring, bz_self hr]
  simp

/-- The middle coefficient of the recurrence, with the value of the endpoint rows at `x = 0` and
`x = r - 2` in place of the division by zero. -/
noncomputable def jBsp (r j1 j2 j4 j5 x : ℕ) : ℂ :=
  if x = 0 then cz r ((j1 : ℤ) + 1) * cz r ((j4 : ℤ) + 1) / cz r 1
  else if x + 2 = r then -(cz r ((j1 : ℤ) + 1) * cz r ((j4 : ℤ) + 1) / cz r 1)
  else jB r j1 j2 j4 j5 x

/-- **The row of the recurrence at every admissible third colour**, endpoints included. -/
theorem row_at {r : ℕ} (hr : 3 ≤ r) (j1 j2 j4 j5 x q : ℕ) (h1 : qAdm r j1 j2 x)
    (h2 : qAdm r j1 j5 q) (h3 : qAdm r j4 j2 q) (h4 : qAdm r j4 j5 x) :
    jA r j1 j2 j4 j5 x * (Sj r j1 j2 j4 j5 q ((x : ℤ) + 2) : ℂ)
      + jBsp r j1 j2 j4 j5 x * (Sj r j1 j2 j4 j5 q (x : ℤ) : ℂ)
      + jC r j1 j2 j4 j5 x * (Sj r j1 j2 j4 j5 q ((x : ℤ) - 2) : ℂ)
      = cz r (1 + q) * (Sj r j1 j2 j4 j5 q (x : ℤ) : ℂ) := by
  have hx : x + 2 ≤ r := by unfold qAdm Lightlike.Pentagon.Tri at h1; omega
  by_cases h0 : x = 0
  · subst h0
    have hj : j2 = j1 ∧ j5 = j4 := by unfold qAdm Lightlike.Pentagon.Tri at h1 h4; omega
    obtain ⟨rfl, rfl⟩ := hj
    have R := row_low hr j2 j5 q h2 h3
    simpa [jBsp, jC_zero] using R
  · by_cases ht : x + 2 = r
    · obtain ⟨P, rfl⟩ : ∃ P, r = P + 3 := ⟨r - 3, by omega⟩
      have hxP : x = P + 1 := by omega
      subst hxP
      have hs : j1 + j2 + 2 = P + 3 ∧ j4 + j5 + 2 = P + 3 := by
        unfold qAdm Lightlike.Pentagon.Tri at h1 h4; omega
      have R := row_top hr j1 j2 j4 j5 q hs.1 hs.2 h2 h3
      have e2 : ((P + 3 : ℕ) : ℤ) - 2 = ((P + 1 : ℕ) : ℤ) := by push_cast; ring
      have e4 : ((P + 3 : ℕ) : ℤ) - 4 = ((P + 1 : ℕ) : ℤ) - 2 := by push_cast; ring
      rw [e2, e4] at R
      have hB : jBsp (P + 3) j1 j2 j4 j5 (P + 1)
          = -(cz (P + 3) ((j1 : ℤ) + 1) * cz (P + 3) ((j4 : ℤ) + 1) / cz (P + 3) 1) := by
        unfold jBsp; simp
      rw [jA_top (by omega), hB]
      linear_combination R
    · have R := sixj_row (by omega) j1 j2 x j4 j5 q h1 h2 h3 h4 (by omega) (by omega)
      have hB : jBsp r j1 j2 j4 j5 x = jB r j1 j2 j4 j5 x := by
        unfold jBsp; simp [h0, ht]
      rw [hB]
      unfold jA jB jC
      linear_combination R

/-- Non-vacuity of `row_at` at the lower endpoint: `r = 4`, all four outer colours `1`, `x = 0`,
`q = 0` satisfy the admissibility hypotheses. -/
example : jA 4 1 1 1 1 0 * (Sj 4 1 1 1 1 0 ((0 : ℕ) + 2 : ℤ) : ℂ)
    + jBsp 4 1 1 1 1 0 * (Sj 4 1 1 1 1 0 (0 : ℤ) : ℂ)
    + jC 4 1 1 1 1 0 * (Sj 4 1 1 1 1 0 ((0 : ℕ) - 2 : ℤ) : ℂ)
    = cz 4 (1 + 0) * (Sj 4 1 1 1 1 0 (0 : ℤ) : ℂ) :=
  row_at (by norm_num) 1 1 1 1 0 0
    (by unfold qAdm Lightlike.Pentagon.Tri; omega) (by unfold qAdm Lightlike.Pentagon.Tri; omega)
    (by unfold qAdm Lightlike.Pentagon.Tri; omega) (by unfold qAdm Lightlike.Pentagon.Tri; omega)

end Lightlike.TV.Refl
