import Lightlike.Recoupling.Intertwiner
import Lightlike.PonzanoRegge.BEZero
import Lightlike.Tests.SixJ

/-!
# Bing's house: the Racah sum rule and the iterated Ponzano–Regge sum

Barrett and Naish-Guzman (2009, §2.4): for Bing's house with two rooms (a 2-complex with no
interior vertex that is not collapsible) the Ponzano–Regge sum is
`Z = Σ_c Σ_b Σ_a (-1)^(a+b) (2a+1)(2b+1)(2c+1) {a c c; c c c} {b c c; c c c}`,
and it is not absolutely convergent. Summing over `a` and `b` first gives `Z = 1`, by the
sum rule (6) `Σ_{a=0}^{2c} (-1)^a (2a+1) {a c c; c c c} = δ_{c0}`.

Spins are doubled: `C = 2c` and `x = 2a`. In these units the sum rule is `racah_sum`, and the
iterated sum is `bingIterated_eq_one`. The sign `(-1)^((2C + x)/2)` is the Racah sign; it equals
`(-1)^a` for integer `c`, and for half-integer `c` it differs by a factor `-1` that cancels in the
product of the two factors `a` and `b`; both sums are `0` there anyway.

## Main results
* `racah_sum`: the sum rule (6), from the orthogonality of 6j symbols.
* `bingIterated_eq_one`: the sum over `a` and `b` first gives `1` for every cutoff in `c`.
* `bingCutoff`, `bingCutoff_two`: the simple cut-off with all doubled spins `≤ L` truncates the room
  sums before `2C`; at `L = 2` it drops the term `x = 4` for `C = 2` and the partial sum is `37/12`.
  The sum is not absolutely convergent (BNG §2.4), so this is a different summation, not a second
  value of the model; `Z_L` has no limit (BNG fig. 6; `scripts/spinfoam/bing_house_check.py` is
  numerical evidence only).
-/

open Lightlike.Pentagon Lightlike.Recoupling Finset PhyslibAlpha.Sl2

namespace Lightlike.SpinFoam

/-- One term of the sum rule (6), in doubled units: `(-1)^((2C+x)/2) (x+1) {x C C; C C C}`. -/
noncomputable def racahTerm (C x : ℕ) : ℝ :=
  (-1) ^ ((2 * C + x) / 2) * ((x : ℝ) + 1) * sixJSym x C C C C C

/-- **The sum rule (6)** (doubled units): `Σ_{x=0}^{2C} (-1)^((2C+x)/2) (x+1) {x C C; C C C}`
is `1` for `C = 0` and `0` otherwise. It is the orthogonality of the 6j symbols
`sixJSym_orth_all` between `{C C x; C C C}` and the zero-spin symbol `{C C x; C C 0}`. -/
theorem racah_sum (C : ℕ) :
    ∑ x ∈ range (2 * C + 1), racahTerm C x = if C = 0 then 1 else 0 := by
  have h := Lightlike.Recoupling.sixJSym_orth_all C C C C C 0
  have hC : ((C : ℝ) + 1) ≠ 0 := by positivity
  have hterm : ∀ x ∈ range (C + C + 1),
      ((x : ℝ) + 1) * ((C : ℝ) + 1) * (sixJSym C C x C C C * sixJSym C C x C C 0) =
        racahTerm C x := by
    intro x _
    have hB : sixJSym C C x C C C = sixJSym x C C C C C := by
      rw [← Lightlike.Pentagon.sj_swap13 C C x C C C]
    have hA : sixJSym C C x C C 0 = sixJSym 0 C C x C C := by
      rw [← Lightlike.Pentagon.sj_swap13 C C x C C 0, ← Lightlike.Pentagon.sj_flip12 x C C 0 C C]
    rw [hB, hA, Lightlike.Pentagon.sixJSym_zero_left]
    unfold racahTerm
    by_cases hT : Tri C C x
    · rw [ite_eq_left ⟨rfl, rfl, hT⟩]
      have hs : Real.sqrt ((C : ℝ) + 1) * Real.sqrt ((C : ℝ) + 1) = (C : ℝ) + 1 :=
        Real.mul_self_sqrt (by positivity)
      have : (-1 : ℝ) ^ ((C + C + x) / 2) = (-1) ^ ((2 * C + x) / 2) := by
        congr 2; omega
      rw [this, hs]
      field_simp
    · rw [ite_eq_right (fun h => hT h.2.2)]
      have : sixJSym x C C C C C = 0 := by
        by_contra hne
        exact hT (by
          have := (Lightlike.Pentagon.tri_of_sixJSym_ne_zero hne).1
          unfold Tri at this ⊢; omega)
      rw [this]; ring
  rw [sum_congr rfl hterm, show C + C = 2 * C by ring] at h
  rw [h]
  by_cases hC0 : C = 0
  · subst hC0; simp [Tri]
  · simp [hC0]

/-- The Bing's-house sum summed over the two room spins `a`, `b` first, for central spin
`C ≤ N` (doubled units): `Σ_C (C+1) (Σ_x racahTerm C x) (Σ_y racahTerm C y)`. -/
noncomputable def bingIterated (N : ℕ) : ℝ :=
  ∑ C ∈ range (N + 1), ((C : ℝ) + 1) *
    ((∑ x ∈ range (2 * C + 1), racahTerm C x) * ∑ y ∈ range (2 * C + 1), racahTerm C y)

/-- Summing over `a` and `b` first gives `Z = 1` for every cut-off `N` on the central spin. -/
theorem bingIterated_eq_one (N : ℕ) : bingIterated N = 1 := by
  unfold bingIterated
  rw [sum_eq_single 0]
  · rw [racah_sum]; simp
  · intro C _ hC; simp [racah_sum, hC]
  · intro h; simp at h

/-- The Bing's-house sum with one simple cut-off `L` on all doubled spins (`C ≤ L`, `x, y ≤ L`):
`Σ_{C ≤ L} (C+1) (Σ_{x ≤ min(2C, L)} racahTerm C x)²`. -/
noncomputable def bingCutoff (L : ℕ) : ℝ :=
  ∑ C ∈ range (L + 1), ((C : ℝ) + 1) *
    (∑ x ∈ range (min (2 * C) L + 1), racahTerm C x) ^ 2

set_option maxHeartbeats 8000000 in
/-- The 6j symbol `{4 2 2; 2 2 2}` in doubled units, that is `{2 1 1; 1 1 1} = 1/6`. -/
theorem sixJSym_4_2_2_2_2_2 : sixJSym 4 2 2 2 2 2 = 1 / 6 := by
  rw [Lightlike.SixJAudit.sixJSym_eq_triple]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Lightlike.SixJAudit.mTuple]
  norm_num (config := { maxSteps := 10000000 }) [sixJTerm, threeJ, Adm3, threeJR, reggeJ,
    Lightlike.SixJAudit.sixSum_eq_sum, Lightlike.SixJAudit.sum_Icc_int, sixTerm, invFact,
    Finset.sum_range_succ, Fin.prod_univ_three, Nat.factorial]
  ring_nf
  surd_finish

/-- **The simple cut-off truncates a room sum.** With doubled cut-off `2` the partial sum is `37/12`:
the cut-off removes the term `x = 4` of the sum rule for `C = 2`. This is the contrast with
`bingIterated_eq_one`. -/
theorem bingCutoff_two : bingCutoff 2 = 37 / 12 := by
  have t4 : racahTerm 2 4 = 5 / 6 := by
    unfold racahTerm; rw [sixJSym_4_2_2_2_2_2]; norm_num
  have t3 : racahTerm 2 3 = 0 := by
    unfold racahTerm
    have : sixJSym 3 2 2 2 2 2 = 0 := by
      by_contra hne
      have := (Lightlike.Pentagon.tri_of_sixJSym_ne_zero hne).1
      unfold Tri at this; omega
    rw [this]; ring
  have s2 := racah_sum 2
  have s1 := racah_sum 1
  have s0 := racah_sum 0
  simp only [show 2 * 2 + 1 = 5 from rfl, show 2 * 1 + 1 = 3 from rfl, show 2 * 0 + 1 = 1 from rfl,
    sum_range_succ, sum_range_zero, t3, t4] at s2 s1 s0
  simp only [bingCutoff, sum_range_succ, sum_range_zero]
  norm_num [sum_range_succ, Nat.min_def] at *
  nlinarith [s0, s1, s2]

/-- The cut-off sum differs from the iterated one: `bingCutoff 2 ≠ bingIterated 2`. -/
theorem bingCutoff_two_ne_iterated : bingCutoff 2 ≠ bingIterated 2 := by
  rw [bingCutoff_two, bingIterated_eq_one]; norm_num

end Lightlike.SpinFoam
