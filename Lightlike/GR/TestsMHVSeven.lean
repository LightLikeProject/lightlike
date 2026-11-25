import Lightlike.GR.MHVMax

/-!
# Non-vacuity of the Parke-Taylor theorem at seven gluons

An explicit rational seven-gluon point is in the maximal closed class `Gmax` for every position `j = 1, …, 5` of the second
negative gluon: every reduction of the induction (far step, cyclic step) satisfies its hypotheses, checked by `norm_num`
through the bracket formulas of `MHVBrackets.lean`. Together with `closedClass_Gmax`, the Parke-Taylor theorem for the
true amplitudes (`trueAmp_eq_ptN`) is therefore not vacuous at seven gluons.
-/

noncomputable section

namespace Lightlike.SpinorHelicity.Tests

open Lightlike.SpinorHelicity Finset

/-- Square spinors of the seven-gluon point. -/
def l7 : ℕ → Fin 2 → ℂ := fun t =>
  if t = 0 then ![(5 : ℂ), (-6 : ℂ)] else if t = 1 then ![(2 : ℂ), (-2 : ℂ)] else if t = 2 then ![(4 : ℂ), (6 : ℂ)]
  else if t = 3 then ![(5 : ℂ), (4 : ℂ)] else if t = 4 then ![(-4 : ℂ), (-5 : ℂ)] else if t = 5 then ![(-25/2 : ℂ), (157/12 : ℂ)] else ![(-18 : ℂ), (17/2 : ℂ)]

/-- Angle spinors of the seven-gluon point. -/
def lt7 : ℕ → Fin 2 → ℂ := fun t =>
  if t = 0 then ![(0 : ℂ), (-5 : ℂ)] else if t = 1 then ![(6 : ℂ), (-3 : ℂ)] else if t = 2 then ![(3 : ℂ), (0 : ℂ)]
  else if t = 3 then ![(-3 : ℂ), (-2 : ℂ)] else if t = 4 then ![(6 : ℂ), (-5 : ℂ)] else if t = 5 then ![(6 : ℂ), (-6 : ℂ)] else ![(-5 : ℂ), (3 : ℂ)]

/-- The seven-gluon point. -/
abbrev E0l : ℕ → Fin 2 → ℂ := l7

/-- The seven-gluon point. -/
abbrev E0t : ℕ → Fin 2 → ℂ := lt7

/-- Reduced or rotated kinematics. -/
def E1l : ℕ → Fin 2 → ℂ := rotLabels E0l 6

/-- Reduced or rotated kinematics. -/
def E1t : ℕ → Fin 2 → ℂ := rotLabels E0t 6

/-- Reduced or rotated kinematics. -/
def E2l : ℕ → Fin 2 → ℂ := redL E1l E1t

/-- Reduced or rotated kinematics. -/
def E2t : ℕ → Fin 2 → ℂ := redLt E1t

/-- Reduced or rotated kinematics. -/
def E3l : ℕ → Fin 2 → ℂ := redL E2l E2t

/-- Reduced or rotated kinematics. -/
def E3t : ℕ → Fin 2 → ℂ := redLt E2t

/-- Reduced or rotated kinematics. -/
def E4l : ℕ → Fin 2 → ℂ := redL E3l E3t

/-- Reduced or rotated kinematics. -/
def E4t : ℕ → Fin 2 → ℂ := redLt E3t

/-- Reduced or rotated kinematics. -/
def E5l : ℕ → Fin 2 → ℂ := redL E4l E4t

/-- Reduced or rotated kinematics. -/
def E5t : ℕ → Fin 2 → ℂ := redLt E4t

/-- Reduced or rotated kinematics. -/
def E6l : ℕ → Fin 2 → ℂ := redL E0l E0t

/-- Reduced or rotated kinematics. -/
def E6t : ℕ → Fin 2 → ℂ := redLt E0t

/-- Reduced or rotated kinematics. -/
def E7l : ℕ → Fin 2 → ℂ := rotLabels E6l 5

/-- Reduced or rotated kinematics. -/
def E7t : ℕ → Fin 2 → ℂ := rotLabels E6t 5

/-- Reduced or rotated kinematics. -/
def E8l : ℕ → Fin 2 → ℂ := redL E7l E7t

/-- Reduced or rotated kinematics. -/
def E8t : ℕ → Fin 2 → ℂ := redLt E7t

/-- Reduced or rotated kinematics. -/
def E9l : ℕ → Fin 2 → ℂ := redL E8l E8t

/-- Reduced or rotated kinematics. -/
def E9t : ℕ → Fin 2 → ℂ := redLt E8t

/-- Reduced or rotated kinematics. -/
def E10l : ℕ → Fin 2 → ℂ := redL E9l E9t

/-- Reduced or rotated kinematics. -/
def E10t : ℕ → Fin 2 → ℂ := redLt E9t

/-- Reduced or rotated kinematics. -/
def E11l : ℕ → Fin 2 → ℂ := redL E6l E6t

/-- Reduced or rotated kinematics. -/
def E11t : ℕ → Fin 2 → ℂ := redLt E6t

/-- Reduced or rotated kinematics. -/
def E12l : ℕ → Fin 2 → ℂ := rotLabels E11l 4

/-- Reduced or rotated kinematics. -/
def E12t : ℕ → Fin 2 → ℂ := rotLabels E11t 4

/-- Reduced or rotated kinematics. -/
def E13l : ℕ → Fin 2 → ℂ := redL E12l E12t

/-- Reduced or rotated kinematics. -/
def E13t : ℕ → Fin 2 → ℂ := redLt E12t

/-- Reduced or rotated kinematics. -/
def E14l : ℕ → Fin 2 → ℂ := redL E13l E13t

/-- Reduced or rotated kinematics. -/
def E14t : ℕ → Fin 2 → ℂ := redLt E13t

/-- Reduced or rotated kinematics. -/
def E15l : ℕ → Fin 2 → ℂ := redL E11l E11t

/-- Reduced or rotated kinematics. -/
def E15t : ℕ → Fin 2 → ℂ := redLt E11t

/-- Reduced or rotated kinematics. -/
def E16l : ℕ → Fin 2 → ℂ := rotLabels E15l 3

/-- Reduced or rotated kinematics. -/
def E16t : ℕ → Fin 2 → ℂ := rotLabels E15t 3

/-- Reduced or rotated kinematics. -/
def E17l : ℕ → Fin 2 → ℂ := redL E16l E16t

/-- Reduced or rotated kinematics. -/
def E17t : ℕ → Fin 2 → ℂ := redLt E16t

/-- Reduced or rotated kinematics. -/
def E18l : ℕ → Fin 2 → ℂ := redL E15l E15t

/-- Reduced or rotated kinematics. -/
def E18t : ℕ → Fin 2 → ℂ := redLt E15t

set_option maxHeartbeats 4000000 in
lemma rot_E0_4 : RotData 4 E0l E0t := by
  refine ⟨?_, ?_⟩
  · funext μ
    fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E0t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
  · intro d h1 h2
    rw [mdot_range_self]
    interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E0t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma gen_E0_4 : GenericAngles (fun i : Fin (3+4) => E0t i) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E0t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma far_E1_3_6 : FarData 3 6 E1l E1t := by
  have hz : ∀ d, zpole E1l E1t d = zpole E1l E1t d := fun _ => rfl
  have hz3 : zpole E1l E1t 3 = (-73/82 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E0t, E1t] <;> norm_num
  have hz4 : zpole E1l E1t 4 = (-3281/4092 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E0t, E1t] <;> norm_num
  have hz5 : zpole E1l E1t 5 = (-1/27 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E0t, E1t] <;> norm_num
  refine ⟨⟨![(-5 : ℂ), (-5 : ℂ)], ![(-5 : ℂ), (-5 : ℂ)], ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E0t, E1t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E0t, E1t] <;> norm_num
    · intro b h1 h2
      rw [shiftedMom_zero, mdot_range_ref]
      interval_cases b <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E0t, E1t] <;> norm_num)
    · intro a b hab hb ha1 hne
      rw [shiftedMom_zero, mdot_range_self]
      have ha : a ≤ 4 := by omega
      interval_cases a <;> interval_cases b <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E0t, E1t] <;> norm_num)
    · rw [shiftedMom_zero]
      funext μ
      fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E0t, E1t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E0t, E1t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E0t, E1t] <;> norm_num)
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E0t, E1t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E0t, E1t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E0t, E1t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E0t, E1t] <;> norm_num)
    · intro d h1 h2
      rw [shiftedMom_zero, mdot_range_self]
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E0t, E1t] <;> norm_num)
    · intro d d' h1 h2 h3 h4 h5
      rw [zpole_eq_sums, zpole_eq_sums] at h5
      interval_cases d <;> interval_cases d' <;> first | rfl | (exfalso; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E0t, E1t] at h5 <;> norm_num at h5)
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E0t, E1t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E0t, E1t] <;> norm_num
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E0t, E1t] <;> norm_num)
  · refine ⟨fun d => if d = 3 then ![(-231/41 : ℂ), (330/41 : ℂ)] else if d = 4 then ![(-28220/341 : ℂ), (56855/682 : ℂ)] else ![(-100/9 : ℂ), (40/3 : ℂ)], fun d => if d = 3 then ![(1 : ℂ), (4/33 : ℂ)] else if d = 4 then ![(1 : ℂ), (-378/415 : ℂ)] else ![(1 : ℂ), (-11/4 : ℂ)], ?_, ?_, ?_, ?_, ?_⟩
    · intro d h1 h2
      interval_cases d
      · rw [hz3]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E0t, E1t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
      · rw [hz4]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E0t, E1t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
      · rw [hz5]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E0t, E1t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E0t, E1t] <;> norm_num)
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E0t, E1t] <;> norm_num)
    · intro d h1 h2 hdj s hs1 hs2
      interval_cases d <;> interval_cases s <;> first | omega | (simp only [ltHat, hz3, hz4, hz5] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E0t, E1t] <;> norm_num)
    · intro d h1 h2 hjd
      refine ⟨fun s hs1 hs2 hsj => ?_, ?_⟩
      · interval_cases d <;> interval_cases s <;> first | omega | exact absurd rfl hsj | (simp only [ltHat, hz3, hz4, hz5] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E0t, E1t] <;> norm_num)
      · interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E0t, E1t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma far_E2_2_5 : FarData 2 5 E2l E2t := by
  have hz : ∀ d, zpole E2l E2t d = zpole E2l E2t d := fun _ => rfl
  have hz3 : zpole E2l E2t 3 = (-31151/13533 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E0t, E1t, E2t] <;> norm_num
  have hz4 : zpole E2l E2t 4 = (-61/94 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E0t, E1t, E2t] <;> norm_num
  refine ⟨⟨![(-5 : ℂ), (-5 : ℂ)], ![(-5 : ℂ), (-5 : ℂ)], ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E0t, E1t, E2t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E0t, E1t, E2t] <;> norm_num
    · intro b h1 h2
      rw [shiftedMom_zero, mdot_range_ref]
      interval_cases b <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E0t, E1t, E2t] <;> norm_num)
    · intro a b hab hb ha1 hne
      rw [shiftedMom_zero, mdot_range_self]
      have ha : a ≤ 3 := by omega
      interval_cases a <;> interval_cases b <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E0t, E1t, E2t] <;> norm_num)
    · rw [shiftedMom_zero]
      funext μ
      fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E0t, E1t, E2t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E0t, E1t, E2t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E0t, E1t, E2t] <;> norm_num)
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E0t, E1t, E2t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E0t, E1t, E2t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E0t, E1t, E2t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E0t, E1t, E2t] <;> norm_num)
    · intro d h1 h2
      rw [shiftedMom_zero, mdot_range_self]
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E0t, E1t, E2t] <;> norm_num)
    · intro d d' h1 h2 h3 h4 h5
      rw [zpole_eq_sums, zpole_eq_sums] at h5
      interval_cases d <;> interval_cases d' <;> first | rfl | (exfalso; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E0t, E1t, E2t] at h5 <;> norm_num at h5)
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E0t, E1t, E2t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E0t, E1t, E2t] <;> norm_num
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E0t, E1t, E2t] <;> norm_num)
  · refine ⟨fun d => if d = 3 then ![(-286348/4511 : ℂ), (576907/9022 : ℂ)] else ![(-285/47 : ℂ), (342/47 : ℂ)], fun d => if d = 3 then ![(1 : ℂ), (-4361/4211 : ℂ)] else ![(1 : ℂ), (-527/114 : ℂ)], ?_, ?_, ?_, ?_, ?_⟩
    · intro d h1 h2
      interval_cases d
      · rw [hz3]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E0t, E1t, E2t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
      · rw [hz4]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E0t, E1t, E2t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E0t, E1t, E2t] <;> norm_num)
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E0t, E1t, E2t] <;> norm_num)
    · intro d h1 h2 hdj s hs1 hs2
      interval_cases d <;> interval_cases s <;> first | omega | (simp only [ltHat, hz3, hz4] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E0t, E1t, E2t] <;> norm_num)
    · intro d h1 h2 hjd
      refine ⟨fun s hs1 hs2 hsj => ?_, ?_⟩
      · interval_cases d <;> interval_cases s <;> first | omega | exact absurd rfl hsj | (simp only [ltHat, hz3, hz4] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E0t, E1t, E2t] <;> norm_num)
      · interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E0t, E1t, E2t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma far_E3_1_4 : FarData 1 4 E3l E3t := by
  have hz : ∀ d, zpole E3l E3t d = zpole E3l E3t d := fun _ => rfl
  have hz3 : zpole E3l E3t 3 = (-43/2 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E0t, E1t, E2t, E3t] <;> norm_num
  refine ⟨⟨![(-5 : ℂ), (-5 : ℂ)], ![(-5 : ℂ), (-5 : ℂ)], ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E0t, E1t, E2t, E3t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E0t, E1t, E2t, E3t] <;> norm_num
    · intro b h1 h2
      rw [shiftedMom_zero, mdot_range_ref]
      interval_cases b <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E0t, E1t, E2t, E3t] <;> norm_num)
    · intro a b hab hb ha1 hne
      rw [shiftedMom_zero, mdot_range_self]
      have ha : a ≤ 2 := by omega
      interval_cases a <;> interval_cases b <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E0t, E1t, E2t, E3t] <;> norm_num)
    · rw [shiftedMom_zero]
      funext μ
      fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E0t, E1t, E2t, E3t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E0t, E1t, E2t, E3t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E0t, E1t, E2t, E3t] <;> norm_num)
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E0t, E1t, E2t, E3t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E0t, E1t, E2t, E3t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E0t, E1t, E2t, E3t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E0t, E1t, E2t, E3t] <;> norm_num)
    · intro d h1 h2
      rw [shiftedMom_zero, mdot_range_self]
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E0t, E1t, E2t, E3t] <;> norm_num)
    · intro d d' h1 h2 h3 h4 h5
      rw [zpole_eq_sums, zpole_eq_sums] at h5
      interval_cases d <;> interval_cases d' <;> first | rfl | (exfalso; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E0t, E1t, E2t, E3t] at h5 <;> norm_num at h5)
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E0t, E1t, E2t, E3t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E0t, E1t, E2t, E3t] <;> norm_num
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E0t, E1t, E2t, E3t] <;> norm_num)
  · refine ⟨fun d => ![(1005/4 : ℂ), (-603/2 : ℂ)], fun d => ![(1 : ℂ), (-161/402 : ℂ)], ?_, ?_, ?_, ?_, ?_⟩
    · intro d h1 h2
      interval_cases d
      · rw [hz3]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E0t, E1t, E2t, E3t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E0t, E1t, E2t, E3t] <;> norm_num)
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E0t, E1t, E2t, E3t] <;> norm_num)
    · intro d h1 h2 hdj s hs1 hs2
      interval_cases d <;> interval_cases s <;> first | omega | (simp only [ltHat, hz3] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E0t, E1t, E2t, E3t] <;> norm_num)
    · intro d h1 h2 hjd
      refine ⟨fun s hs1 hs2 hsj => ?_, ?_⟩
      · interval_cases d <;> interval_cases s <;> first | omega | exact absurd rfl hsj | (simp only [ltHat, hz3] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E0t, E1t, E2t, E3t] <;> norm_num)
      · interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E0t, E1t, E2t, E3t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma far_E4_0_3 : FarData 0 3 E4l E4t := by
  have hz : ∀ d, zpole E4l E4t d = zpole E4l E4t d := fun _ => rfl
  refine ⟨⟨![(-5 : ℂ), (-5 : ℂ)], ![(-5 : ℂ), (-5 : ℂ)], ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E0t, E1t, E2t, E3t, E4t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E0t, E1t, E2t, E3t, E4t] <;> norm_num
    · intro b h1 h2
      rw [shiftedMom_zero, mdot_range_ref]
      interval_cases b <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E0t, E1t, E2t, E3t, E4t] <;> norm_num)
    · intro a b hab hb ha1 hne
      rw [shiftedMom_zero, mdot_range_self]
      have ha : a ≤ 1 := by omega
      interval_cases a <;> interval_cases b <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E0t, E1t, E2t, E3t, E4t] <;> norm_num)
    · rw [shiftedMom_zero]
      funext μ
      fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E0t, E1t, E2t, E3t, E4t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E0t, E1t, E2t, E3t, E4t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E0t, E1t, E2t, E3t, E4t] <;> norm_num)
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E0t, E1t, E2t, E3t, E4t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E0t, E1t, E2t, E3t, E4t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E0t, E1t, E2t, E3t, E4t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E0t, E1t, E2t, E3t, E4t] <;> norm_num)
    · intro d h1 h2
      rw [shiftedMom_zero, mdot_range_self]
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E0t, E1t, E2t, E3t, E4t] <;> norm_num)
    · intro d d' h1 h2 h3 h4 h5
      rw [zpole_eq_sums, zpole_eq_sums] at h5
      interval_cases d <;> interval_cases d' <;> first | rfl | (exfalso; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E0t, E1t, E2t, E3t, E4t] at h5 <;> norm_num at h5)
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E0t, E1t, E2t, E3t, E4t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E0t, E1t, E2t, E3t, E4t] <;> norm_num
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E0t, E1t, E2t, E3t, E4t] <;> norm_num)
  · refine ⟨fun _ => ![0, 0], fun _ => ![0, 0], ?_, ?_, ?_, ?_, ?_⟩
    · intro d h1 h2
      interval_cases d
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E0t, E1t, E2t, E3t, E4t] <;> norm_num)
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E0t, E1t, E2t, E3t, E4t] <;> norm_num)
    · intro d h1 h2 hdj s hs1 hs2
      interval_cases d <;> interval_cases s <;> first | omega | (simp only [ltHat, hz] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E0t, E1t, E2t, E3t, E4t] <;> norm_num)
    · intro d h1 h2 hjd
      refine ⟨fun s hs1 hs2 hsj => ?_, ?_⟩
      · interval_cases d <;> interval_cases s <;> first | omega | exact absurd rfl hsj | (simp only [ltHat, hz] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E0t, E1t, E2t, E3t, E4t] <;> norm_num)
      · interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E0t, E1t, E2t, E3t, E4t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma gmax_E5_0_2 : Gmax 0 2 E5l E5t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_, ?_, ?_, ?_⟩
  · funext μ
    fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E0t, E1t, E2t, E3t, E4t, E5t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E0t, E1t, E2t, E3t, E4t, E5t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E0t, E1t, E2t, E3t, E4t, E5t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E0t, E1t, E2t, E3t, E4t, E5t] <;> norm_num

lemma gmax_E4_1_3 : Gmax 1 3 E4l E4t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rw [if_pos (by norm_num)]
  exact ⟨far_E4_0_3, gmax_E5_0_2⟩

lemma gmax_E3_2_4 : Gmax 2 4 E3l E3t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rw [if_pos (by norm_num)]
  exact ⟨far_E3_1_4, gmax_E4_1_3⟩

lemma gmax_E2_3_5 : Gmax 3 5 E2l E2t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rw [if_pos (by norm_num)]
  exact ⟨far_E2_2_5, gmax_E3_2_4⟩

lemma gmax_E0_4_1 : Gmax 4 1 E0l E0t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rw [if_neg (by norm_num)]
  exact ⟨rot_E0_4, gen_E0_4, far_E1_3_6, gmax_E2_3_5⟩

set_option maxHeartbeats 4000000 in
lemma far_E0_3_2 : FarData 3 2 E0l E0t := by
  have hz : ∀ d, zpole E0l E0t d = zpole E0l E0t d := fun _ => rfl
  have hz3 : zpole E0l E0t 3 = (-19/5 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E0t, E1t, E2t, E3t, E4t, E5t] <;> norm_num
  have hz4 : zpole E0l E0t 4 = (67/170 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E0t, E1t, E2t, E3t, E4t, E5t] <;> norm_num
  have hz5 : zpole E0l E0t 5 = (-131/38 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E0t, E1t, E2t, E3t, E4t, E5t] <;> norm_num
  refine ⟨⟨![(-5 : ℂ), (-5 : ℂ)], ![(-5 : ℂ), (-5 : ℂ)], ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E0t, E1t, E2t, E3t, E4t, E5t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E0t, E1t, E2t, E3t, E4t, E5t] <;> norm_num
    · intro b h1 h2
      rw [shiftedMom_zero, mdot_range_ref]
      interval_cases b <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E0t, E1t, E2t, E3t, E4t, E5t] <;> norm_num)
    · intro a b hab hb ha1 hne
      rw [shiftedMom_zero, mdot_range_self]
      have ha : a ≤ 4 := by omega
      interval_cases a <;> interval_cases b <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E0t, E1t, E2t, E3t, E4t, E5t] <;> norm_num)
    · rw [shiftedMom_zero]
      funext μ
      fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E0t, E1t, E2t, E3t, E4t, E5t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E0t, E1t, E2t, E3t, E4t, E5t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E0t, E1t, E2t, E3t, E4t, E5t] <;> norm_num)
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E0t, E1t, E2t, E3t, E4t, E5t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E0t, E1t, E2t, E3t, E4t, E5t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E0t, E1t, E2t, E3t, E4t, E5t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E0t, E1t, E2t, E3t, E4t, E5t] <;> norm_num)
    · intro d h1 h2
      rw [shiftedMom_zero, mdot_range_self]
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E0t, E1t, E2t, E3t, E4t, E5t] <;> norm_num)
    · intro d d' h1 h2 h3 h4 h5
      rw [zpole_eq_sums, zpole_eq_sums] at h5
      interval_cases d <;> interval_cases d' <;> first | rfl | (exfalso; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E0t, E1t, E2t, E3t, E4t, E5t] at h5 <;> norm_num at h5)
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E0t, E1t, E2t, E3t, E4t, E5t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E0t, E1t, E2t, E3t, E4t, E5t] <;> norm_num
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E0t, E1t, E2t, E3t, E4t, E5t] <;> norm_num)
  · refine ⟨fun d => if d = 3 then ![(9 : ℂ), (-6 : ℂ)] else if d = 4 then ![(-15 : ℂ), (-36 : ℂ)] else ![(-90 : ℂ), (85/2 : ℂ)], fun d => if d = 3 then ![(1 : ℂ), (-6 : ℂ)] else if d = 4 then ![(1 : ℂ), (-9/17 : ℂ)] else ![(1 : ℂ), (-47/95 : ℂ)], ?_, ?_, ?_, ?_, ?_⟩
    · intro d h1 h2
      interval_cases d
      · rw [hz3]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E0t, E1t, E2t, E3t, E4t, E5t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
      · rw [hz4]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E0t, E1t, E2t, E3t, E4t, E5t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
      · rw [hz5]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E0t, E1t, E2t, E3t, E4t, E5t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E0t, E1t, E2t, E3t, E4t, E5t] <;> norm_num)
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E0t, E1t, E2t, E3t, E4t, E5t] <;> norm_num)
    · intro d h1 h2 hdj s hs1 hs2
      interval_cases d <;> interval_cases s <;> first | omega | (simp only [ltHat, hz3, hz4, hz5] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E0t, E1t, E2t, E3t, E4t, E5t] <;> norm_num)
    · intro d h1 h2 hjd
      refine ⟨fun s hs1 hs2 hsj => ?_, ?_⟩
      · interval_cases d <;> interval_cases s <;> first | omega | exact absurd rfl hsj | (simp only [ltHat, hz3, hz4, hz5] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E0t, E1t, E2t, E3t, E4t, E5t] <;> norm_num)
      · interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E0t, E1t, E2t, E3t, E4t, E5t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma rot_E6_3 : RotData 3 E6l E6t := by
  refine ⟨?_, ?_⟩
  · funext μ
    fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
  · intro d h1 h2
    rw [mdot_range_self]
    interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E0t, E1t, E2t, E3t, E4t, E5t, E6t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma gen_E6_3 : GenericAngles (fun i : Fin (2+4) => E6t i) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E0t, E1t, E2t, E3t, E4t, E5t, E6t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma far_E7_2_5 : FarData 2 5 E7l E7t := by
  have hz : ∀ d, zpole E7l E7t d = zpole E7l E7t d := fun _ => rfl
  have hz3 : zpole E7l E7t 3 = (-7817/3885 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t] <;> norm_num
  have hz4 : zpole E7l E7t 4 = (-175/152 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t] <;> norm_num
  refine ⟨⟨![(-5 : ℂ), (-5 : ℂ)], ![(-5 : ℂ), (-5 : ℂ)], ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t] <;> norm_num
    · intro b h1 h2
      rw [shiftedMom_zero, mdot_range_ref]
      interval_cases b <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t] <;> norm_num)
    · intro a b hab hb ha1 hne
      rw [shiftedMom_zero, mdot_range_self]
      have ha : a ≤ 3 := by omega
      interval_cases a <;> interval_cases b <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t] <;> norm_num)
    · rw [shiftedMom_zero]
      funext μ
      fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t] <;> norm_num)
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t] <;> norm_num)
    · intro d h1 h2
      rw [shiftedMom_zero, mdot_range_self]
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t] <;> norm_num)
    · intro d d' h1 h2 h3 h4 h5
      rw [zpole_eq_sums, zpole_eq_sums] at h5
      interval_cases d <;> interval_cases d' <;> first | rfl | (exfalso; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t] at h5 <;> norm_num at h5)
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t] <;> norm_num
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t] <;> norm_num)
  · refine ⟨fun d => if d = 3 then ![(-21709/259 : ℂ), (157071/2590 : ℂ)] else ![(-1023/152 : ℂ), (297/38 : ℂ)], fun d => if d = 3 then ![(1 : ℂ), (-1295/1277 : ℂ)] else ![(1 : ℂ), (-152/33 : ℂ)], ?_, ?_, ?_, ?_, ?_⟩
    · intro d h1 h2
      interval_cases d
      · rw [hz3]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
      · rw [hz4]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t] <;> norm_num)
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t] <;> norm_num)
    · intro d h1 h2 hdj s hs1 hs2
      interval_cases d <;> interval_cases s <;> first | omega | (simp only [ltHat, hz3, hz4] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t] <;> norm_num)
    · intro d h1 h2 hjd
      refine ⟨fun s hs1 hs2 hsj => ?_, ?_⟩
      · interval_cases d <;> interval_cases s <;> first | omega | exact absurd rfl hsj | (simp only [ltHat, hz3, hz4] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t] <;> norm_num)
      · interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma far_E8_1_4 : FarData 1 4 E8l E8t := by
  have hz : ∀ d, zpole E8l E8t d = zpole E8l E8t d := fun _ => rfl
  have hz3 : zpole E8l E8t 3 = (-986/887 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t] <;> norm_num
  refine ⟨⟨![(-5 : ℂ), (-5 : ℂ)], ![(-5 : ℂ), (-5 : ℂ)], ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t] <;> norm_num
    · intro b h1 h2
      rw [shiftedMom_zero, mdot_range_ref]
      interval_cases b <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t] <;> norm_num)
    · intro a b hab hb ha1 hne
      rw [shiftedMom_zero, mdot_range_self]
      have ha : a ≤ 2 := by omega
      interval_cases a <;> interval_cases b <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t] <;> norm_num)
    · rw [shiftedMom_zero]
      funext μ
      fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t] <;> norm_num)
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t] <;> norm_num)
    · intro d h1 h2
      rw [shiftedMom_zero, mdot_range_self]
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t] <;> norm_num)
    · intro d d' h1 h2 h3 h4 h5
      rw [zpole_eq_sums, zpole_eq_sums] at h5
      interval_cases d <;> interval_cases d' <;> first | rfl | (exfalso; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t] at h5 <;> norm_num at h5)
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t] <;> norm_num
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t] <;> norm_num)
  · refine ⟨fun d => ![(-3255/887 : ℂ), (3780/887 : ℂ)], fun d => ![(1 : ℂ), (-887/105 : ℂ)], ?_, ?_, ?_, ?_, ?_⟩
    · intro d h1 h2
      interval_cases d
      · rw [hz3]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t] <;> norm_num)
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t] <;> norm_num)
    · intro d h1 h2 hdj s hs1 hs2
      interval_cases d <;> interval_cases s <;> first | omega | (simp only [ltHat, hz3] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t] <;> norm_num)
    · intro d h1 h2 hjd
      refine ⟨fun s hs1 hs2 hsj => ?_, ?_⟩
      · interval_cases d <;> interval_cases s <;> first | omega | exact absurd rfl hsj | (simp only [ltHat, hz3] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t] <;> norm_num)
      · interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma far_E9_0_3 : FarData 0 3 E9l E9t := by
  have hz : ∀ d, zpole E9l E9t d = zpole E9l E9t d := fun _ => rfl
  refine ⟨⟨![(-5 : ℂ), (-5 : ℂ)], ![(-5 : ℂ), (-5 : ℂ)], ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t] <;> norm_num
    · intro b h1 h2
      rw [shiftedMom_zero, mdot_range_ref]
      interval_cases b <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t] <;> norm_num)
    · intro a b hab hb ha1 hne
      rw [shiftedMom_zero, mdot_range_self]
      have ha : a ≤ 1 := by omega
      interval_cases a <;> interval_cases b <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t] <;> norm_num)
    · rw [shiftedMom_zero]
      funext μ
      fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t] <;> norm_num)
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t] <;> norm_num)
    · intro d h1 h2
      rw [shiftedMom_zero, mdot_range_self]
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t] <;> norm_num)
    · intro d d' h1 h2 h3 h4 h5
      rw [zpole_eq_sums, zpole_eq_sums] at h5
      interval_cases d <;> interval_cases d' <;> first | rfl | (exfalso; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t] at h5 <;> norm_num at h5)
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t] <;> norm_num
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t] <;> norm_num)
  · refine ⟨fun _ => ![0, 0], fun _ => ![0, 0], ?_, ?_, ?_, ?_, ?_⟩
    · intro d h1 h2
      interval_cases d
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t] <;> norm_num)
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t] <;> norm_num)
    · intro d h1 h2 hdj s hs1 hs2
      interval_cases d <;> interval_cases s <;> first | omega | (simp only [ltHat, hz] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t] <;> norm_num)
    · intro d h1 h2 hjd
      refine ⟨fun s hs1 hs2 hsj => ?_, ?_⟩
      · interval_cases d <;> interval_cases s <;> first | omega | exact absurd rfl hsj | (simp only [ltHat, hz] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t] <;> norm_num)
      · interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma gmax_E10_0_2 : Gmax 0 2 E10l E10t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_, ?_, ?_, ?_⟩
  · funext μ
    fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num

lemma gmax_E9_1_3 : Gmax 1 3 E9l E9t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rw [if_pos (by norm_num)]
  exact ⟨far_E9_0_3, gmax_E10_0_2⟩

lemma gmax_E8_2_4 : Gmax 2 4 E8l E8t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rw [if_pos (by norm_num)]
  exact ⟨far_E8_1_4, gmax_E9_1_3⟩

lemma gmax_E6_3_1 : Gmax 3 1 E6l E6t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rw [if_neg (by norm_num)]
  exact ⟨rot_E6_3, gen_E6_3, far_E7_2_5, gmax_E8_2_4⟩

lemma gmax_E0_4_2 : Gmax 4 2 E0l E0t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rw [if_pos (by norm_num)]
  exact ⟨far_E0_3_2, gmax_E6_3_1⟩

set_option maxHeartbeats 4000000 in
lemma far_E0_3_3 : FarData 3 3 E0l E0t := by
  have hz : ∀ d, zpole E0l E0t d = zpole E0l E0t d := fun _ => rfl
  have hz3 : zpole E0l E0t 3 = (-19/5 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num
  have hz4 : zpole E0l E0t 4 = (67/170 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num
  have hz5 : zpole E0l E0t 5 = (-131/38 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num
  refine ⟨⟨![(-5 : ℂ), (-5 : ℂ)], ![(-5 : ℂ), (-5 : ℂ)], ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num
    · intro b h1 h2
      rw [shiftedMom_zero, mdot_range_ref]
      interval_cases b <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num)
    · intro a b hab hb ha1 hne
      rw [shiftedMom_zero, mdot_range_self]
      have ha : a ≤ 4 := by omega
      interval_cases a <;> interval_cases b <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num)
    · rw [shiftedMom_zero]
      funext μ
      fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num)
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num)
    · intro d h1 h2
      rw [shiftedMom_zero, mdot_range_self]
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num)
    · intro d d' h1 h2 h3 h4 h5
      rw [zpole_eq_sums, zpole_eq_sums] at h5
      interval_cases d <;> interval_cases d' <;> first | rfl | (exfalso; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] at h5 <;> norm_num at h5)
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num)
  · refine ⟨fun d => if d = 3 then ![(9 : ℂ), (-6 : ℂ)] else if d = 4 then ![(-15 : ℂ), (-36 : ℂ)] else ![(-90 : ℂ), (85/2 : ℂ)], fun d => if d = 3 then ![(1 : ℂ), (-6 : ℂ)] else if d = 4 then ![(1 : ℂ), (-9/17 : ℂ)] else ![(1 : ℂ), (-47/95 : ℂ)], ?_, ?_, ?_, ?_, ?_⟩
    · intro d h1 h2
      interval_cases d
      · rw [hz3]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
      · rw [hz4]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
      · rw [hz5]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num)
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num)
    · intro d h1 h2 hdj s hs1 hs2
      interval_cases d <;> interval_cases s <;> first | omega | (simp only [ltHat, hz3, hz4, hz5] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num)
    · intro d h1 h2 hjd
      refine ⟨fun s hs1 hs2 hsj => ?_, ?_⟩
      · interval_cases d <;> interval_cases s <;> first | omega | exact absurd rfl hsj | (simp only [ltHat, hz3, hz4, hz5] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num)
      · interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma far_E6_2_2 : FarData 2 2 E6l E6t := by
  have hz : ∀ d, zpole E6l E6t d = zpole E6l E6t d := fun _ => rfl
  have hz3 : zpole E6l E6t 3 = (-7/86 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num
  have hz4 : zpole E6l E6t 4 = (769/1040 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num
  refine ⟨⟨![(-5 : ℂ), (-5 : ℂ)], ![(-5 : ℂ), (-5 : ℂ)], ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num
    · intro b h1 h2
      rw [shiftedMom_zero, mdot_range_ref]
      interval_cases b <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num)
    · intro a b hab hb ha1 hne
      rw [shiftedMom_zero, mdot_range_self]
      have ha : a ≤ 3 := by omega
      interval_cases a <;> interval_cases b <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num)
    · rw [shiftedMom_zero]
      funext μ
      fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num)
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num)
    · intro d h1 h2
      rw [shiftedMom_zero, mdot_range_self]
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num)
    · intro d d' h1 h2 h3 h4 h5
      rw [zpole_eq_sums, zpole_eq_sums] at h5
      interval_cases d <;> interval_cases d' <;> first | rfl | (exfalso; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] at h5 <;> norm_num at h5)
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num)
  · refine ⟨fun d => if d = 3 then ![(-15 : ℂ), (-36 : ℂ)] else ![(-90 : ℂ), (85/2 : ℂ)], fun d => if d = 3 then ![(1 : ℂ), (-58/129 : ℂ)] else ![(1 : ℂ), (-331/260 : ℂ)], ?_, ?_, ?_, ?_, ?_⟩
    · intro d h1 h2
      interval_cases d
      · rw [hz3]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
      · rw [hz4]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num)
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num)
    · intro d h1 h2 hdj s hs1 hs2
      interval_cases d <;> interval_cases s <;> first | omega | (simp only [ltHat, hz3, hz4] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num)
    · intro d h1 h2 hjd
      refine ⟨fun s hs1 hs2 hsj => ?_, ?_⟩
      · interval_cases d <;> interval_cases s <;> first | omega | exact absurd rfl hsj | (simp only [ltHat, hz3, hz4] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num)
      · interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma rot_E11_2 : RotData 2 E11l E11t := by
  refine ⟨?_, ?_⟩
  · funext μ
    fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
  · intro d h1 h2
    rw [mdot_range_self]
    interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma gen_E11_2 : GenericAngles (fun i : Fin (1+4) => E11t i) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma far_E12_1_4 : FarData 1 4 E12l E12t := by
  have hz : ∀ d, zpole E12l E12t d = zpole E12l E12t d := fun _ => rfl
  have hz3 : zpole E12l E12t 3 = (-2/363 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t] <;> norm_num
  refine ⟨⟨![(-5 : ℂ), (-5 : ℂ)], ![(-5 : ℂ), (-5 : ℂ)], ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t] <;> norm_num
    · intro b h1 h2
      rw [shiftedMom_zero, mdot_range_ref]
      interval_cases b <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t] <;> norm_num)
    · intro a b hab hb ha1 hne
      rw [shiftedMom_zero, mdot_range_self]
      have ha : a ≤ 2 := by omega
      interval_cases a <;> interval_cases b <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t] <;> norm_num)
    · rw [shiftedMom_zero]
      funext μ
      fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t] <;> norm_num)
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t] <;> norm_num)
    · intro d h1 h2
      rw [shiftedMom_zero, mdot_range_self]
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t] <;> norm_num)
    · intro d d' h1 h2 h3 h4 h5
      rw [zpole_eq_sums, zpole_eq_sums] at h5
      interval_cases d <;> interval_cases d' <;> first | rfl | (exfalso; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t] at h5 <;> norm_num at h5)
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t] <;> norm_num
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t] <;> norm_num)
  · refine ⟨fun d => ![(-1081/121 : ℂ), (736/121 : ℂ)], fun d => ![(1 : ℂ), (-317/69 : ℂ)], ?_, ?_, ?_, ?_, ?_⟩
    · intro d h1 h2
      interval_cases d
      · rw [hz3]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t] <;> norm_num)
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t] <;> norm_num)
    · intro d h1 h2 hdj s hs1 hs2
      interval_cases d <;> interval_cases s <;> first | omega | (simp only [ltHat, hz3] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t] <;> norm_num)
    · intro d h1 h2 hjd
      refine ⟨fun s hs1 hs2 hsj => ?_, ?_⟩
      · interval_cases d <;> interval_cases s <;> first | omega | exact absurd rfl hsj | (simp only [ltHat, hz3] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t] <;> norm_num)
      · interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma far_E13_0_3 : FarData 0 3 E13l E13t := by
  have hz : ∀ d, zpole E13l E13t d = zpole E13l E13t d := fun _ => rfl
  refine ⟨⟨![(-5 : ℂ), (-5 : ℂ)], ![(-5 : ℂ), (-5 : ℂ)], ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t] <;> norm_num
    · intro b h1 h2
      rw [shiftedMom_zero, mdot_range_ref]
      interval_cases b <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t] <;> norm_num)
    · intro a b hab hb ha1 hne
      rw [shiftedMom_zero, mdot_range_self]
      have ha : a ≤ 1 := by omega
      interval_cases a <;> interval_cases b <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t] <;> norm_num)
    · rw [shiftedMom_zero]
      funext μ
      fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t] <;> norm_num)
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t] <;> norm_num)
    · intro d h1 h2
      rw [shiftedMom_zero, mdot_range_self]
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t] <;> norm_num)
    · intro d d' h1 h2 h3 h4 h5
      rw [zpole_eq_sums, zpole_eq_sums] at h5
      interval_cases d <;> interval_cases d' <;> first | rfl | (exfalso; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t] at h5 <;> norm_num at h5)
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t] <;> norm_num
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t] <;> norm_num)
  · refine ⟨fun _ => ![0, 0], fun _ => ![0, 0], ?_, ?_, ?_, ?_, ?_⟩
    · intro d h1 h2
      interval_cases d
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t] <;> norm_num)
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t] <;> norm_num)
    · intro d h1 h2 hdj s hs1 hs2
      interval_cases d <;> interval_cases s <;> first | omega | (simp only [ltHat, hz] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t] <;> norm_num)
    · intro d h1 h2 hjd
      refine ⟨fun s hs1 hs2 hsj => ?_, ?_⟩
      · interval_cases d <;> interval_cases s <;> first | omega | exact absurd rfl hsj | (simp only [ltHat, hz] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t] <;> norm_num)
      · interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma gmax_E14_0_2 : Gmax 0 2 E14l E14t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_, ?_, ?_, ?_⟩
  · funext μ
    fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num

lemma gmax_E13_1_3 : Gmax 1 3 E13l E13t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rw [if_pos (by norm_num)]
  exact ⟨far_E13_0_3, gmax_E14_0_2⟩

lemma gmax_E11_2_1 : Gmax 2 1 E11l E11t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rw [if_neg (by norm_num)]
  exact ⟨rot_E11_2, gen_E11_2, far_E12_1_4, gmax_E13_1_3⟩

lemma gmax_E6_3_2 : Gmax 3 2 E6l E6t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rw [if_pos (by norm_num)]
  exact ⟨far_E6_2_2, gmax_E11_2_1⟩

lemma gmax_E0_4_3 : Gmax 4 3 E0l E0t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rw [if_pos (by norm_num)]
  exact ⟨far_E0_3_3, gmax_E6_3_2⟩

set_option maxHeartbeats 4000000 in
lemma far_E0_3_4 : FarData 3 4 E0l E0t := by
  have hz : ∀ d, zpole E0l E0t d = zpole E0l E0t d := fun _ => rfl
  have hz3 : zpole E0l E0t 3 = (-19/5 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num
  have hz4 : zpole E0l E0t 4 = (67/170 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num
  have hz5 : zpole E0l E0t 5 = (-131/38 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num
  refine ⟨⟨![(-5 : ℂ), (-5 : ℂ)], ![(-5 : ℂ), (-5 : ℂ)], ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num
    · intro b h1 h2
      rw [shiftedMom_zero, mdot_range_ref]
      interval_cases b <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num)
    · intro a b hab hb ha1 hne
      rw [shiftedMom_zero, mdot_range_self]
      have ha : a ≤ 4 := by omega
      interval_cases a <;> interval_cases b <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num)
    · rw [shiftedMom_zero]
      funext μ
      fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num)
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num)
    · intro d h1 h2
      rw [shiftedMom_zero, mdot_range_self]
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num)
    · intro d d' h1 h2 h3 h4 h5
      rw [zpole_eq_sums, zpole_eq_sums] at h5
      interval_cases d <;> interval_cases d' <;> first | rfl | (exfalso; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] at h5 <;> norm_num at h5)
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num)
  · refine ⟨fun d => if d = 3 then ![(9 : ℂ), (-6 : ℂ)] else if d = 4 then ![(-15 : ℂ), (-36 : ℂ)] else ![(-90 : ℂ), (85/2 : ℂ)], fun d => if d = 3 then ![(1 : ℂ), (-6 : ℂ)] else if d = 4 then ![(1 : ℂ), (-9/17 : ℂ)] else ![(1 : ℂ), (-47/95 : ℂ)], ?_, ?_, ?_, ?_, ?_⟩
    · intro d h1 h2
      interval_cases d
      · rw [hz3]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
      · rw [hz4]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
      · rw [hz5]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num)
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num)
    · intro d h1 h2 hdj s hs1 hs2
      interval_cases d <;> interval_cases s <;> first | omega | (simp only [ltHat, hz3, hz4, hz5] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num)
    · intro d h1 h2 hjd
      refine ⟨fun s hs1 hs2 hsj => ?_, ?_⟩
      · interval_cases d <;> interval_cases s <;> first | omega | exact absurd rfl hsj | (simp only [ltHat, hz3, hz4, hz5] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num)
      · interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma far_E6_2_3 : FarData 2 3 E6l E6t := by
  have hz : ∀ d, zpole E6l E6t d = zpole E6l E6t d := fun _ => rfl
  have hz3 : zpole E6l E6t 3 = (-7/86 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num
  have hz4 : zpole E6l E6t 4 = (769/1040 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num
  refine ⟨⟨![(-5 : ℂ), (-5 : ℂ)], ![(-5 : ℂ), (-5 : ℂ)], ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num
    · intro b h1 h2
      rw [shiftedMom_zero, mdot_range_ref]
      interval_cases b <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num)
    · intro a b hab hb ha1 hne
      rw [shiftedMom_zero, mdot_range_self]
      have ha : a ≤ 3 := by omega
      interval_cases a <;> interval_cases b <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num)
    · rw [shiftedMom_zero]
      funext μ
      fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num)
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num)
    · intro d h1 h2
      rw [shiftedMom_zero, mdot_range_self]
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num)
    · intro d d' h1 h2 h3 h4 h5
      rw [zpole_eq_sums, zpole_eq_sums] at h5
      interval_cases d <;> interval_cases d' <;> first | rfl | (exfalso; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] at h5 <;> norm_num at h5)
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num)
  · refine ⟨fun d => if d = 3 then ![(-15 : ℂ), (-36 : ℂ)] else ![(-90 : ℂ), (85/2 : ℂ)], fun d => if d = 3 then ![(1 : ℂ), (-58/129 : ℂ)] else ![(1 : ℂ), (-331/260 : ℂ)], ?_, ?_, ?_, ?_, ?_⟩
    · intro d h1 h2
      interval_cases d
      · rw [hz3]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
      · rw [hz4]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num)
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num)
    · intro d h1 h2 hdj s hs1 hs2
      interval_cases d <;> interval_cases s <;> first | omega | (simp only [ltHat, hz3, hz4] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num)
    · intro d h1 h2 hjd
      refine ⟨fun s hs1 hs2 hsj => ?_, ?_⟩
      · interval_cases d <;> interval_cases s <;> first | omega | exact absurd rfl hsj | (simp only [ltHat, hz3, hz4] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num)
      · interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma far_E11_1_2 : FarData 1 2 E11l E11t := by
  have hz : ∀ d, zpole E11l E11t d = zpole E11l E11t d := fun _ => rfl
  have hz3 : zpole E11l E11t 3 = (353/105 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num
  refine ⟨⟨![(-5 : ℂ), (-5 : ℂ)], ![(-5 : ℂ), (-5 : ℂ)], ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num
    · intro b h1 h2
      rw [shiftedMom_zero, mdot_range_ref]
      interval_cases b <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num)
    · intro a b hab hb ha1 hne
      rw [shiftedMom_zero, mdot_range_self]
      have ha : a ≤ 2 := by omega
      interval_cases a <;> interval_cases b <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num)
    · rw [shiftedMom_zero]
      funext μ
      fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num)
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num)
    · intro d h1 h2
      rw [shiftedMom_zero, mdot_range_self]
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num)
    · intro d d' h1 h2 h3 h4 h5
      rw [zpole_eq_sums, zpole_eq_sums] at h5
      interval_cases d <;> interval_cases d' <;> first | rfl | (exfalso; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] at h5 <;> norm_num at h5)
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num)
  · refine ⟨fun d => ![(-90 : ℂ), (85/2 : ℂ)], fun d => ![(1 : ℂ), (-59/105 : ℂ)], ?_, ?_, ?_, ?_, ?_⟩
    · intro d h1 h2
      interval_cases d
      · rw [hz3]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num)
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num)
    · intro d h1 h2 hdj s hs1 hs2
      interval_cases d <;> interval_cases s <;> first | omega | (simp only [ltHat, hz3] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num)
    · intro d h1 h2 hjd
      refine ⟨fun s hs1 hs2 hsj => ?_, ?_⟩
      · interval_cases d <;> interval_cases s <;> first | omega | exact absurd rfl hsj | (simp only [ltHat, hz3] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num)
      · interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma rot_E15_1 : RotData 1 E15l E15t := by
  refine ⟨?_, ?_⟩
  · funext μ
    fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
  · intro d h1 h2
    rw [mdot_range_self]
    interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma gen_E15_1 : GenericAngles (fun i : Fin (0+4) => E15t i) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma far_E16_0_3 : FarData 0 3 E16l E16t := by
  have hz : ∀ d, zpole E16l E16t d = zpole E16l E16t d := fun _ => rfl
  refine ⟨⟨![(-5 : ℂ), (-5 : ℂ)], ![(-5 : ℂ), (-5 : ℂ)], ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t] <;> norm_num
    · intro b h1 h2
      rw [shiftedMom_zero, mdot_range_ref]
      interval_cases b <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t] <;> norm_num)
    · intro a b hab hb ha1 hne
      rw [shiftedMom_zero, mdot_range_self]
      have ha : a ≤ 1 := by omega
      interval_cases a <;> interval_cases b <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t] <;> norm_num)
    · rw [shiftedMom_zero]
      funext μ
      fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t] <;> norm_num)
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t] <;> norm_num)
    · intro d h1 h2
      rw [shiftedMom_zero, mdot_range_self]
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t] <;> norm_num)
    · intro d d' h1 h2 h3 h4 h5
      rw [zpole_eq_sums, zpole_eq_sums] at h5
      interval_cases d <;> interval_cases d' <;> first | rfl | (exfalso; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t] at h5 <;> norm_num at h5)
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t] <;> norm_num
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t] <;> norm_num)
  · refine ⟨fun _ => ![0, 0], fun _ => ![0, 0], ?_, ?_, ?_, ?_, ?_⟩
    · intro d h1 h2
      interval_cases d
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t] <;> norm_num)
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t] <;> norm_num)
    · intro d h1 h2 hdj s hs1 hs2
      interval_cases d <;> interval_cases s <;> first | omega | (simp only [ltHat, hz] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t] <;> norm_num)
    · intro d h1 h2 hjd
      refine ⟨fun s hs1 hs2 hsj => ?_, ?_⟩
      · interval_cases d <;> interval_cases s <;> first | omega | exact absurd rfl hsj | (simp only [ltHat, hz] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t] <;> norm_num)
      · interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma gmax_E17_0_2 : Gmax 0 2 E17l E17t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_, ?_, ?_, ?_⟩
  · funext μ
    fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num

lemma gmax_E15_1_1 : Gmax 1 1 E15l E15t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rw [if_neg (by norm_num)]
  exact ⟨rot_E15_1, gen_E15_1, far_E16_0_3, gmax_E17_0_2⟩

lemma gmax_E11_2_2 : Gmax 2 2 E11l E11t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rw [if_pos (by norm_num)]
  exact ⟨far_E11_1_2, gmax_E15_1_1⟩

lemma gmax_E6_3_3 : Gmax 3 3 E6l E6t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rw [if_pos (by norm_num)]
  exact ⟨far_E6_2_3, gmax_E11_2_2⟩

lemma gmax_E0_4_4 : Gmax 4 4 E0l E0t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rw [if_pos (by norm_num)]
  exact ⟨far_E0_3_4, gmax_E6_3_3⟩

set_option maxHeartbeats 4000000 in
lemma far_E0_3_5 : FarData 3 5 E0l E0t := by
  have hz : ∀ d, zpole E0l E0t d = zpole E0l E0t d := fun _ => rfl
  have hz3 : zpole E0l E0t 3 = (-19/5 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num
  have hz4 : zpole E0l E0t 4 = (67/170 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num
  have hz5 : zpole E0l E0t 5 = (-131/38 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num
  refine ⟨⟨![(-5 : ℂ), (-5 : ℂ)], ![(-5 : ℂ), (-5 : ℂ)], ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num
    · intro b h1 h2
      rw [shiftedMom_zero, mdot_range_ref]
      interval_cases b <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)
    · intro a b hab hb ha1 hne
      rw [shiftedMom_zero, mdot_range_self]
      have ha : a ≤ 4 := by omega
      interval_cases a <;> interval_cases b <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)
    · rw [shiftedMom_zero]
      funext μ
      fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)
    · intro d h1 h2
      rw [shiftedMom_zero, mdot_range_self]
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)
    · intro d d' h1 h2 h3 h4 h5
      rw [zpole_eq_sums, zpole_eq_sums] at h5
      interval_cases d <;> interval_cases d' <;> first | rfl | (exfalso; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] at h5 <;> norm_num at h5)
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)
  · refine ⟨fun d => if d = 3 then ![(9 : ℂ), (-6 : ℂ)] else if d = 4 then ![(-15 : ℂ), (-36 : ℂ)] else ![(-90 : ℂ), (85/2 : ℂ)], fun d => if d = 3 then ![(1 : ℂ), (-6 : ℂ)] else if d = 4 then ![(1 : ℂ), (-9/17 : ℂ)] else ![(1 : ℂ), (-47/95 : ℂ)], ?_, ?_, ?_, ?_, ?_⟩
    · intro d h1 h2
      interval_cases d
      · rw [hz3]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
      · rw [hz4]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
      · rw [hz5]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)
    · intro d h1 h2 hdj s hs1 hs2
      interval_cases d <;> interval_cases s <;> first | omega | (simp only [ltHat, hz3, hz4, hz5] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)
    · intro d h1 h2 hjd
      refine ⟨fun s hs1 hs2 hsj => ?_, ?_⟩
      · interval_cases d <;> interval_cases s <;> first | omega | exact absurd rfl hsj | (simp only [ltHat, hz3, hz4, hz5] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)
      · interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma far_E6_2_4 : FarData 2 4 E6l E6t := by
  have hz : ∀ d, zpole E6l E6t d = zpole E6l E6t d := fun _ => rfl
  have hz3 : zpole E6l E6t 3 = (-7/86 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num
  have hz4 : zpole E6l E6t 4 = (769/1040 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num
  refine ⟨⟨![(-5 : ℂ), (-5 : ℂ)], ![(-5 : ℂ), (-5 : ℂ)], ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num
    · intro b h1 h2
      rw [shiftedMom_zero, mdot_range_ref]
      interval_cases b <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)
    · intro a b hab hb ha1 hne
      rw [shiftedMom_zero, mdot_range_self]
      have ha : a ≤ 3 := by omega
      interval_cases a <;> interval_cases b <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)
    · rw [shiftedMom_zero]
      funext μ
      fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)
    · intro d h1 h2
      rw [shiftedMom_zero, mdot_range_self]
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)
    · intro d d' h1 h2 h3 h4 h5
      rw [zpole_eq_sums, zpole_eq_sums] at h5
      interval_cases d <;> interval_cases d' <;> first | rfl | (exfalso; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] at h5 <;> norm_num at h5)
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)
  · refine ⟨fun d => if d = 3 then ![(-15 : ℂ), (-36 : ℂ)] else ![(-90 : ℂ), (85/2 : ℂ)], fun d => if d = 3 then ![(1 : ℂ), (-58/129 : ℂ)] else ![(1 : ℂ), (-331/260 : ℂ)], ?_, ?_, ?_, ?_, ?_⟩
    · intro d h1 h2
      interval_cases d
      · rw [hz3]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
      · rw [hz4]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)
    · intro d h1 h2 hdj s hs1 hs2
      interval_cases d <;> interval_cases s <;> first | omega | (simp only [ltHat, hz3, hz4] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)
    · intro d h1 h2 hjd
      refine ⟨fun s hs1 hs2 hsj => ?_, ?_⟩
      · interval_cases d <;> interval_cases s <;> first | omega | exact absurd rfl hsj | (simp only [ltHat, hz3, hz4] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)
      · interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma far_E11_1_3 : FarData 1 3 E11l E11t := by
  have hz : ∀ d, zpole E11l E11t d = zpole E11l E11t d := fun _ => rfl
  have hz3 : zpole E11l E11t 3 = (353/105 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num
  refine ⟨⟨![(-5 : ℂ), (-5 : ℂ)], ![(-5 : ℂ), (-5 : ℂ)], ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num
    · intro b h1 h2
      rw [shiftedMom_zero, mdot_range_ref]
      interval_cases b <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)
    · intro a b hab hb ha1 hne
      rw [shiftedMom_zero, mdot_range_self]
      have ha : a ≤ 2 := by omega
      interval_cases a <;> interval_cases b <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)
    · rw [shiftedMom_zero]
      funext μ
      fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)
    · intro d h1 h2
      rw [shiftedMom_zero, mdot_range_self]
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)
    · intro d d' h1 h2 h3 h4 h5
      rw [zpole_eq_sums, zpole_eq_sums] at h5
      interval_cases d <;> interval_cases d' <;> first | rfl | (exfalso; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] at h5 <;> norm_num at h5)
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)
  · refine ⟨fun d => ![(-90 : ℂ), (85/2 : ℂ)], fun d => ![(1 : ℂ), (-59/105 : ℂ)], ?_, ?_, ?_, ?_, ?_⟩
    · intro d h1 h2
      interval_cases d
      · rw [hz3]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)
    · intro d h1 h2 hdj s hs1 hs2
      interval_cases d <;> interval_cases s <;> first | omega | (simp only [ltHat, hz3] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)
    · intro d h1 h2 hjd
      refine ⟨fun s hs1 hs2 hsj => ?_, ?_⟩
      · interval_cases d <;> interval_cases s <;> first | omega | exact absurd rfl hsj | (simp only [ltHat, hz3] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)
      · interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma far_E15_0_2 : FarData 0 2 E15l E15t := by
  have hz : ∀ d, zpole E15l E15t d = zpole E15l E15t d := fun _ => rfl
  refine ⟨⟨![(-5 : ℂ), (-5 : ℂ)], ![(-5 : ℂ), (-5 : ℂ)], ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num
    · intro b h1 h2
      rw [shiftedMom_zero, mdot_range_ref]
      interval_cases b <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)
    · intro a b hab hb ha1 hne
      rw [shiftedMom_zero, mdot_range_self]
      have ha : a ≤ 1 := by omega
      interval_cases a <;> interval_cases b <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)
    · rw [shiftedMom_zero]
      funext μ
      fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)
    · intro d h1 h2
      rw [shiftedMom_zero, mdot_range_self]
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)
    · intro d d' h1 h2 h3 h4 h5
      rw [zpole_eq_sums, zpole_eq_sums] at h5
      interval_cases d <;> interval_cases d' <;> first | rfl | (exfalso; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] at h5 <;> norm_num at h5)
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)
  · refine ⟨fun _ => ![0, 0], fun _ => ![0, 0], ?_, ?_, ?_, ?_, ?_⟩
    · intro d h1 h2
      interval_cases d
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)
    · intro d h1 h2 hdj s hs1 hs2
      interval_cases d <;> interval_cases s <;> first | omega | (simp only [ltHat, hz] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)
    · intro d h1 h2 hjd
      refine ⟨fun s hs1 hs2 hsj => ?_, ?_⟩
      · interval_cases d <;> interval_cases s <;> first | omega | exact absurd rfl hsj | (simp only [ltHat, hz] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)
      · interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma gmax_E18_0_1 : Gmax 0 1 E18l E18t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_, ?_, ?_, ?_⟩
  · funext μ
    fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num

lemma gmax_E15_1_2 : Gmax 1 2 E15l E15t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rw [if_pos (by norm_num)]
  exact ⟨far_E15_0_2, gmax_E18_0_1⟩

lemma gmax_E11_2_3 : Gmax 2 3 E11l E11t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rw [if_pos (by norm_num)]
  exact ⟨far_E11_1_3, gmax_E15_1_2⟩

lemma gmax_E6_3_4 : Gmax 3 4 E6l E6t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rw [if_pos (by norm_num)]
  exact ⟨far_E6_2_4, gmax_E11_2_3⟩

lemma gmax_E0_4_5 : Gmax 4 5 E0l E0t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rw [if_pos (by norm_num)]
  exact ⟨far_E0_3_5, gmax_E6_3_4⟩

set_option maxHeartbeats 4000000 in
lemma far_E0_3_6 : FarData 3 6 E0l E0t := by
  have hz : ∀ d, zpole E0l E0t d = zpole E0l E0t d := fun _ => rfl
  have hz3 : zpole E0l E0t 3 = (-19/5 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
  have hz4 : zpole E0l E0t 4 = (67/170 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
  have hz5 : zpole E0l E0t 5 = (-131/38 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
  refine ⟨⟨![(-5 : ℂ), (-5 : ℂ)], ![(-5 : ℂ), (-5 : ℂ)], ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
    · intro b h1 h2
      rw [shiftedMom_zero, mdot_range_ref]
      interval_cases b <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)
    · intro a b hab hb ha1 hne
      rw [shiftedMom_zero, mdot_range_self]
      have ha : a ≤ 4 := by omega
      interval_cases a <;> interval_cases b <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)
    · rw [shiftedMom_zero]
      funext μ
      fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)
    · intro d h1 h2
      rw [shiftedMom_zero, mdot_range_self]
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)
    · intro d d' h1 h2 h3 h4 h5
      rw [zpole_eq_sums, zpole_eq_sums] at h5
      interval_cases d <;> interval_cases d' <;> first | rfl | (exfalso; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] at h5 <;> norm_num at h5)
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)
  · refine ⟨fun d => if d = 3 then ![(9 : ℂ), (-6 : ℂ)] else if d = 4 then ![(-15 : ℂ), (-36 : ℂ)] else ![(-90 : ℂ), (85/2 : ℂ)], fun d => if d = 3 then ![(1 : ℂ), (-6 : ℂ)] else if d = 4 then ![(1 : ℂ), (-9/17 : ℂ)] else ![(1 : ℂ), (-47/95 : ℂ)], ?_, ?_, ?_, ?_, ?_⟩
    · intro d h1 h2
      interval_cases d
      · rw [hz3]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
      · rw [hz4]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
      · rw [hz5]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)
    · intro d h1 h2 hdj s hs1 hs2
      interval_cases d <;> interval_cases s <;> first | omega | (simp only [ltHat, hz3, hz4, hz5] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)
    · intro d h1 h2 hjd
      refine ⟨fun s hs1 hs2 hsj => ?_, ?_⟩
      · interval_cases d <;> interval_cases s <;> first | omega | exact absurd rfl hsj | (simp only [ltHat, hz3, hz4, hz5] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)
      · interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma far_E6_2_5 : FarData 2 5 E6l E6t := by
  have hz : ∀ d, zpole E6l E6t d = zpole E6l E6t d := fun _ => rfl
  have hz3 : zpole E6l E6t 3 = (-7/86 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
  have hz4 : zpole E6l E6t 4 = (769/1040 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
  refine ⟨⟨![(-5 : ℂ), (-5 : ℂ)], ![(-5 : ℂ), (-5 : ℂ)], ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
    · intro b h1 h2
      rw [shiftedMom_zero, mdot_range_ref]
      interval_cases b <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)
    · intro a b hab hb ha1 hne
      rw [shiftedMom_zero, mdot_range_self]
      have ha : a ≤ 3 := by omega
      interval_cases a <;> interval_cases b <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)
    · rw [shiftedMom_zero]
      funext μ
      fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)
    · intro d h1 h2
      rw [shiftedMom_zero, mdot_range_self]
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)
    · intro d d' h1 h2 h3 h4 h5
      rw [zpole_eq_sums, zpole_eq_sums] at h5
      interval_cases d <;> interval_cases d' <;> first | rfl | (exfalso; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] at h5 <;> norm_num at h5)
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)
  · refine ⟨fun d => if d = 3 then ![(-15 : ℂ), (-36 : ℂ)] else ![(-90 : ℂ), (85/2 : ℂ)], fun d => if d = 3 then ![(1 : ℂ), (-58/129 : ℂ)] else ![(1 : ℂ), (-331/260 : ℂ)], ?_, ?_, ?_, ?_, ?_⟩
    · intro d h1 h2
      interval_cases d
      · rw [hz3]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
      · rw [hz4]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)
    · intro d h1 h2 hdj s hs1 hs2
      interval_cases d <;> interval_cases s <;> first | omega | (simp only [ltHat, hz3, hz4] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)
    · intro d h1 h2 hjd
      refine ⟨fun s hs1 hs2 hsj => ?_, ?_⟩
      · interval_cases d <;> interval_cases s <;> first | omega | exact absurd rfl hsj | (simp only [ltHat, hz3, hz4] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)
      · interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma far_E11_1_4 : FarData 1 4 E11l E11t := by
  have hz : ∀ d, zpole E11l E11t d = zpole E11l E11t d := fun _ => rfl
  have hz3 : zpole E11l E11t 3 = (353/105 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
  refine ⟨⟨![(-5 : ℂ), (-5 : ℂ)], ![(-5 : ℂ), (-5 : ℂ)], ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
    · intro b h1 h2
      rw [shiftedMom_zero, mdot_range_ref]
      interval_cases b <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)
    · intro a b hab hb ha1 hne
      rw [shiftedMom_zero, mdot_range_self]
      have ha : a ≤ 2 := by omega
      interval_cases a <;> interval_cases b <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)
    · rw [shiftedMom_zero]
      funext μ
      fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)
    · intro d h1 h2
      rw [shiftedMom_zero, mdot_range_self]
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)
    · intro d d' h1 h2 h3 h4 h5
      rw [zpole_eq_sums, zpole_eq_sums] at h5
      interval_cases d <;> interval_cases d' <;> first | rfl | (exfalso; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] at h5 <;> norm_num at h5)
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)
  · refine ⟨fun d => ![(-90 : ℂ), (85/2 : ℂ)], fun d => ![(1 : ℂ), (-59/105 : ℂ)], ?_, ?_, ?_, ?_, ?_⟩
    · intro d h1 h2
      interval_cases d
      · rw [hz3]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)
    · intro d h1 h2 hdj s hs1 hs2
      interval_cases d <;> interval_cases s <;> first | omega | (simp only [ltHat, hz3] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)
    · intro d h1 h2 hjd
      refine ⟨fun s hs1 hs2 hsj => ?_, ?_⟩
      · interval_cases d <;> interval_cases s <;> first | omega | exact absurd rfl hsj | (simp only [ltHat, hz3] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)
      · interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma far_E15_0_3 : FarData 0 3 E15l E15t := by
  have hz : ∀ d, zpole E15l E15t d = zpole E15l E15t d := fun _ => rfl
  refine ⟨⟨![(-5 : ℂ), (-5 : ℂ)], ![(-5 : ℂ), (-5 : ℂ)], ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
    · intro b h1 h2
      rw [shiftedMom_zero, mdot_range_ref]
      interval_cases b <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)
    · intro a b hab hb ha1 hne
      rw [shiftedMom_zero, mdot_range_self]
      have ha : a ≤ 1 := by omega
      interval_cases a <;> interval_cases b <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)
    · rw [shiftedMom_zero]
      funext μ
      fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)
    · intro d h1 h2
      rw [shiftedMom_zero, mdot_range_self]
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)
    · intro d d' h1 h2 h3 h4 h5
      rw [zpole_eq_sums, zpole_eq_sums] at h5
      interval_cases d <;> interval_cases d' <;> first | rfl | (exfalso; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] at h5 <;> norm_num at h5)
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)
  · refine ⟨fun _ => ![0, 0], fun _ => ![0, 0], ?_, ?_, ?_, ?_, ?_⟩
    · intro d h1 h2
      interval_cases d
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)
    · intro d h1 h2 hdj s hs1 hs2
      interval_cases d <;> interval_cases s <;> first | omega | (simp only [ltHat, hz] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)
    · intro d h1 h2 hjd
      refine ⟨fun s hs1 hs2 hsj => ?_, ?_⟩
      · interval_cases d <;> interval_cases s <;> first | omega | exact absurd rfl hsj | (simp only [ltHat, hz] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)
      · interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma gmax_E18_0_2 : Gmax 0 2 E18l E18t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_, ?_, ?_, ?_⟩
  · funext μ
    fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l7, lt7, E0l, E1l, E2l, E3l, E4l, E5l, E6l, E7l, E8l, E9l, E10l, E11l, E12l, E13l, E14l, E15l, E16l, E17l, E18l, E0t, E1t, E2t, E3t, E4t, E5t, E6t, E7t, E8t, E9t, E10t, E11t, E12t, E13t, E14t, E15t, E16t, E17t, E18t] <;> norm_num

lemma gmax_E15_1_3 : Gmax 1 3 E15l E15t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rw [if_pos (by norm_num)]
  exact ⟨far_E15_0_3, gmax_E18_0_2⟩

lemma gmax_E11_2_4 : Gmax 2 4 E11l E11t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rw [if_pos (by norm_num)]
  exact ⟨far_E11_1_4, gmax_E15_1_3⟩

lemma gmax_E6_3_5 : Gmax 3 5 E6l E6t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rw [if_pos (by norm_num)]
  exact ⟨far_E6_2_5, gmax_E11_2_4⟩

lemma gmax_E0_4_6 : Gmax 4 6 E0l E0t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rw [if_pos (by norm_num)]
  exact ⟨far_E0_3_6, gmax_E6_3_5⟩

/-- **Non-vacuity at seven gluons**: the point is in `Gmax 3 j` for every position `j` of the second negative gluon. -/
theorem gmax_seven (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ 6) : Gmax 4 j l7 lt7 := by
  interval_cases j
  · exact gmax_E0_4_1
  · exact gmax_E0_4_2
  · exact gmax_E0_4_3
  · exact gmax_E0_4_4
  · exact gmax_E0_4_5
  · exact gmax_E0_4_6

end Lightlike.SpinorHelicity.Tests
