import Lightlike.GR.MHVMax

/-!
# Non-vacuity of the Parke-Taylor theorem at six gluons

An explicit rational six-gluon point is in the maximal closed class `Gmax` for every position `j = 1, …, 5` of the second
negative gluon: every reduction of the induction (far step, cyclic step) satisfies its hypotheses, checked by `norm_num`
through the bracket formulas of `MHVBrackets.lean`. Together with `closedClass_Gmax`, the Parke-Taylor theorem for the
true amplitudes (`trueAmp_eq_ptN`) is therefore not vacuous at six gluons.
-/

noncomputable section

namespace Lightlike.SpinorHelicity.Tests

open Lightlike.SpinorHelicity Finset

/-- Square spinors of the six-gluon point. -/
def l6 : ℕ → Fin 2 → ℂ := fun t =>
  if t = 0 then ![(-4 : ℂ), (-3 : ℂ)] else if t = 1 then ![(-1 : ℂ), (6 : ℂ)] else if t = 2 then ![(3 : ℂ), (6 : ℂ)]
  else if t = 3 then ![(-4 : ℂ), (-1 : ℂ)] else if t = 4 then ![(-157/9 : ℂ), (-116/9 : ℂ)] else ![(-7/6 : ℂ), (-17/6 : ℂ)]

/-- Angle spinors of the six-gluon point. -/
def lt6 : ℕ → Fin 2 → ℂ := fun t =>
  if t = 0 then ![(-5 : ℂ), (4 : ℂ)] else if t = 1 then ![(0 : ℂ), (-2 : ℂ)] else if t = 2 then ![(2 : ℂ), (1 : ℂ)]
  else if t = 3 then ![(-6 : ℂ), (-1 : ℂ)] else if t = 4 then ![(3 : ℂ), (0 : ℂ)] else ![(-2 : ℂ), (-6 : ℂ)]

/-- The six-gluon point. -/
abbrev D0l : ℕ → Fin 2 → ℂ := l6

/-- The six-gluon point. -/
abbrev D0t : ℕ → Fin 2 → ℂ := lt6

/-- Reduced or rotated kinematics. -/
def D1l : ℕ → Fin 2 → ℂ := rotLabels D0l 5

/-- Reduced or rotated kinematics. -/
def D1t : ℕ → Fin 2 → ℂ := rotLabels D0t 5

/-- Reduced or rotated kinematics. -/
def D2l : ℕ → Fin 2 → ℂ := redL D1l D1t

/-- Reduced or rotated kinematics. -/
def D2t : ℕ → Fin 2 → ℂ := redLt D1t

/-- Reduced or rotated kinematics. -/
def D3l : ℕ → Fin 2 → ℂ := redL D2l D2t

/-- Reduced or rotated kinematics. -/
def D3t : ℕ → Fin 2 → ℂ := redLt D2t

/-- Reduced or rotated kinematics. -/
def D4l : ℕ → Fin 2 → ℂ := redL D3l D3t

/-- Reduced or rotated kinematics. -/
def D4t : ℕ → Fin 2 → ℂ := redLt D3t

/-- Reduced or rotated kinematics. -/
def D5l : ℕ → Fin 2 → ℂ := redL D0l D0t

/-- Reduced or rotated kinematics. -/
def D5t : ℕ → Fin 2 → ℂ := redLt D0t

/-- Reduced or rotated kinematics. -/
def D6l : ℕ → Fin 2 → ℂ := rotLabels D5l 4

/-- Reduced or rotated kinematics. -/
def D6t : ℕ → Fin 2 → ℂ := rotLabels D5t 4

/-- Reduced or rotated kinematics. -/
def D7l : ℕ → Fin 2 → ℂ := redL D6l D6t

/-- Reduced or rotated kinematics. -/
def D7t : ℕ → Fin 2 → ℂ := redLt D6t

/-- Reduced or rotated kinematics. -/
def D8l : ℕ → Fin 2 → ℂ := redL D7l D7t

/-- Reduced or rotated kinematics. -/
def D8t : ℕ → Fin 2 → ℂ := redLt D7t

/-- Reduced or rotated kinematics. -/
def D9l : ℕ → Fin 2 → ℂ := redL D5l D5t

/-- Reduced or rotated kinematics. -/
def D9t : ℕ → Fin 2 → ℂ := redLt D5t

/-- Reduced or rotated kinematics. -/
def D10l : ℕ → Fin 2 → ℂ := rotLabels D9l 3

/-- Reduced or rotated kinematics. -/
def D10t : ℕ → Fin 2 → ℂ := rotLabels D9t 3

/-- Reduced or rotated kinematics. -/
def D11l : ℕ → Fin 2 → ℂ := redL D10l D10t

/-- Reduced or rotated kinematics. -/
def D11t : ℕ → Fin 2 → ℂ := redLt D10t

/-- Reduced or rotated kinematics. -/
def D12l : ℕ → Fin 2 → ℂ := redL D9l D9t

/-- Reduced or rotated kinematics. -/
def D12t : ℕ → Fin 2 → ℂ := redLt D9t

set_option maxHeartbeats 4000000 in
lemma rot_D0_3 : RotData 3 D0l D0t := by
  refine ⟨?_, ?_⟩
  · funext μ
    fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D0t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
  · intro d h1 h2
    rw [mdot_range_self]
    interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D0t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma gen_D0_3 : GenericAngles (fun i : Fin (2+4) => D0t i) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D0t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma far_D1_2_5 : FarData 2 5 D1l D1t := by
  have hz : ∀ d, zpole D1l D1t d = zpole D1l D1t d := fun _ => rfl
  have hz3 : zpole D1l D1t 3 = (-35/432 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D0t, D1t] <;> norm_num
  have hz4 : zpole D1l D1t 4 = (-9/5 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D0t, D1t] <;> norm_num
  refine ⟨⟨![(-5 : ℂ), (-5 : ℂ)], ![(-5 : ℂ), (-5 : ℂ)], ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D0t, D1t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D0t, D1t] <;> norm_num
    · intro b h1 h2
      rw [shiftedMom_zero, mdot_range_ref]
      interval_cases b <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D0t, D1t] <;> norm_num)
    · intro a b hab hb ha1 hne
      rw [shiftedMom_zero, mdot_range_self]
      have ha : a ≤ 3 := by omega
      interval_cases a <;> interval_cases b <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D0t, D1t] <;> norm_num)
    · rw [shiftedMom_zero]
      funext μ
      fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D0t, D1t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D0t, D1t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D0t, D1t] <;> norm_num)
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D0t, D1t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D0t, D1t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D0t, D1t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D0t, D1t] <;> norm_num)
    · intro d h1 h2
      rw [shiftedMom_zero, mdot_range_self]
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D0t, D1t] <;> norm_num)
    · intro d d' h1 h2 h3 h4 h5
      rw [zpole_eq_sums, zpole_eq_sums] at h5
      interval_cases d <;> interval_cases d' <;> first | rfl | (exfalso; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D0t, D1t] at h5 <;> norm_num at h5)
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D0t, D1t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D0t, D1t] <;> norm_num
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D0t, D1t] <;> norm_num)
  · refine ⟨fun d => if d = 3 then ![(-67/3 : ℂ), (-62/3 : ℂ)] else ![(-20 : ℂ), (-15 : ℂ)], fun d => if d = 3 then ![(1 : ℂ), (-7/24 : ℂ)] else ![(1 : ℂ), (-4/25 : ℂ)], ?_, ?_, ?_, ?_, ?_⟩
    · intro d h1 h2
      interval_cases d
      · rw [hz3]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D0t, D1t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
      · rw [hz4]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D0t, D1t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D0t, D1t] <;> norm_num)
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D0t, D1t] <;> norm_num)
    · intro d h1 h2 hdj s hs1 hs2
      interval_cases d <;> interval_cases s <;> first | omega | (simp only [ltHat, hz3, hz4] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D0t, D1t] <;> norm_num)
    · intro d h1 h2 hjd
      refine ⟨fun s hs1 hs2 hsj => ?_, ?_⟩
      · interval_cases d <;> interval_cases s <;> first | omega | exact absurd rfl hsj | (simp only [ltHat, hz3, hz4] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D0t, D1t] <;> norm_num)
      · interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D0t, D1t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma far_D2_1_4 : FarData 1 4 D2l D2t := by
  have hz : ∀ d, zpole D2l D2t d = zpole D2l D2t d := fun _ => rfl
  have hz3 : zpole D2l D2t 3 = (-22/3 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D0t, D1t, D2t] <;> norm_num
  refine ⟨⟨![(-5 : ℂ), (-5 : ℂ)], ![(-5 : ℂ), (-5 : ℂ)], ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D0t, D1t, D2t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D0t, D1t, D2t] <;> norm_num
    · intro b h1 h2
      rw [shiftedMom_zero, mdot_range_ref]
      interval_cases b <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D0t, D1t, D2t] <;> norm_num)
    · intro a b hab hb ha1 hne
      rw [shiftedMom_zero, mdot_range_self]
      have ha : a ≤ 2 := by omega
      interval_cases a <;> interval_cases b <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D0t, D1t, D2t] <;> norm_num)
    · rw [shiftedMom_zero]
      funext μ
      fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D0t, D1t, D2t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D0t, D1t, D2t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D0t, D1t, D2t] <;> norm_num)
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D0t, D1t, D2t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D0t, D1t, D2t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D0t, D1t, D2t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D0t, D1t, D2t] <;> norm_num)
    · intro d h1 h2
      rw [shiftedMom_zero, mdot_range_self]
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D0t, D1t, D2t] <;> norm_num)
    · intro d d' h1 h2 h3 h4 h5
      rw [zpole_eq_sums, zpole_eq_sums] at h5
      interval_cases d <;> interval_cases d' <;> first | rfl | (exfalso; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D0t, D1t, D2t] at h5 <;> norm_num at h5)
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D0t, D1t, D2t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D0t, D1t, D2t] <;> norm_num
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D0t, D1t, D2t] <;> norm_num)
  · refine ⟨fun d => ![(-20 : ℂ), (-15 : ℂ)], fun d => ![(1 : ℂ), (-64/15 : ℂ)], ?_, ?_, ?_, ?_, ?_⟩
    · intro d h1 h2
      interval_cases d
      · rw [hz3]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D0t, D1t, D2t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D0t, D1t, D2t] <;> norm_num)
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D0t, D1t, D2t] <;> norm_num)
    · intro d h1 h2 hdj s hs1 hs2
      interval_cases d <;> interval_cases s <;> first | omega | (simp only [ltHat, hz3] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D0t, D1t, D2t] <;> norm_num)
    · intro d h1 h2 hjd
      refine ⟨fun s hs1 hs2 hsj => ?_, ?_⟩
      · interval_cases d <;> interval_cases s <;> first | omega | exact absurd rfl hsj | (simp only [ltHat, hz3] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D0t, D1t, D2t] <;> norm_num)
      · interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D0t, D1t, D2t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma far_D3_0_3 : FarData 0 3 D3l D3t := by
  have hz : ∀ d, zpole D3l D3t d = zpole D3l D3t d := fun _ => rfl
  refine ⟨⟨![(-5 : ℂ), (-5 : ℂ)], ![(-5 : ℂ), (-5 : ℂ)], ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D0t, D1t, D2t, D3t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D0t, D1t, D2t, D3t] <;> norm_num
    · intro b h1 h2
      rw [shiftedMom_zero, mdot_range_ref]
      interval_cases b <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D0t, D1t, D2t, D3t] <;> norm_num)
    · intro a b hab hb ha1 hne
      rw [shiftedMom_zero, mdot_range_self]
      have ha : a ≤ 1 := by omega
      interval_cases a <;> interval_cases b <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D0t, D1t, D2t, D3t] <;> norm_num)
    · rw [shiftedMom_zero]
      funext μ
      fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D0t, D1t, D2t, D3t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D0t, D1t, D2t, D3t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D0t, D1t, D2t, D3t] <;> norm_num)
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D0t, D1t, D2t, D3t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D0t, D1t, D2t, D3t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D0t, D1t, D2t, D3t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D0t, D1t, D2t, D3t] <;> norm_num)
    · intro d h1 h2
      rw [shiftedMom_zero, mdot_range_self]
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D0t, D1t, D2t, D3t] <;> norm_num)
    · intro d d' h1 h2 h3 h4 h5
      rw [zpole_eq_sums, zpole_eq_sums] at h5
      interval_cases d <;> interval_cases d' <;> first | rfl | (exfalso; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D0t, D1t, D2t, D3t] at h5 <;> norm_num at h5)
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D0t, D1t, D2t, D3t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D0t, D1t, D2t, D3t] <;> norm_num
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D0t, D1t, D2t, D3t] <;> norm_num)
  · refine ⟨fun _ => ![0, 0], fun _ => ![0, 0], ?_, ?_, ?_, ?_, ?_⟩
    · intro d h1 h2
      interval_cases d
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D0t, D1t, D2t, D3t] <;> norm_num)
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D0t, D1t, D2t, D3t] <;> norm_num)
    · intro d h1 h2 hdj s hs1 hs2
      interval_cases d <;> interval_cases s <;> first | omega | (simp only [ltHat, hz] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D0t, D1t, D2t, D3t] <;> norm_num)
    · intro d h1 h2 hjd
      refine ⟨fun s hs1 hs2 hsj => ?_, ?_⟩
      · interval_cases d <;> interval_cases s <;> first | omega | exact absurd rfl hsj | (simp only [ltHat, hz] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D0t, D1t, D2t, D3t] <;> norm_num)
      · interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D0t, D1t, D2t, D3t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma gmax_D4_0_2 : Gmax 0 2 D4l D4t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_, ?_, ?_, ?_⟩
  · funext μ
    fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D0t, D1t, D2t, D3t, D4t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D0t, D1t, D2t, D3t, D4t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D0t, D1t, D2t, D3t, D4t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D0t, D1t, D2t, D3t, D4t] <;> norm_num

lemma gmax_D3_1_3 : Gmax 1 3 D3l D3t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rw [if_pos (by norm_num)]
  exact ⟨far_D3_0_3, gmax_D4_0_2⟩

lemma gmax_D2_2_4 : Gmax 2 4 D2l D2t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rw [if_pos (by norm_num)]
  exact ⟨far_D2_1_4, gmax_D3_1_3⟩

lemma gmax_D0_3_1 : Gmax 3 1 D0l D0t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rw [if_neg (by norm_num)]
  exact ⟨rot_D0_3, gen_D0_3, far_D1_2_5, gmax_D2_2_4⟩

set_option maxHeartbeats 4000000 in
lemma far_D0_2_2 : FarData 2 2 D0l D0t := by
  have hz : ∀ d, zpole D0l D0t d = zpole D0l D0t d := fun _ => rfl
  have hz3 : zpole D0l D0t 3 = (-312/1037 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D0t, D1t, D2t, D3t, D4t] <;> norm_num
  have hz4 : zpole D0l D0t 4 = (-47/59 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D0t, D1t, D2t, D3t, D4t] <;> norm_num
  refine ⟨⟨![(-5 : ℂ), (-5 : ℂ)], ![(-5 : ℂ), (-5 : ℂ)], ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D0t, D1t, D2t, D3t, D4t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D0t, D1t, D2t, D3t, D4t] <;> norm_num
    · intro b h1 h2
      rw [shiftedMom_zero, mdot_range_ref]
      interval_cases b <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D0t, D1t, D2t, D3t, D4t] <;> norm_num)
    · intro a b hab hb ha1 hne
      rw [shiftedMom_zero, mdot_range_self]
      have ha : a ≤ 3 := by omega
      interval_cases a <;> interval_cases b <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D0t, D1t, D2t, D3t, D4t] <;> norm_num)
    · rw [shiftedMom_zero]
      funext μ
      fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D0t, D1t, D2t, D3t, D4t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D0t, D1t, D2t, D3t, D4t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D0t, D1t, D2t, D3t, D4t] <;> norm_num)
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D0t, D1t, D2t, D3t, D4t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D0t, D1t, D2t, D3t, D4t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D0t, D1t, D2t, D3t, D4t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D0t, D1t, D2t, D3t, D4t] <;> norm_num)
    · intro d h1 h2
      rw [shiftedMom_zero, mdot_range_self]
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D0t, D1t, D2t, D3t, D4t] <;> norm_num)
    · intro d d' h1 h2 h3 h4 h5
      rw [zpole_eq_sums, zpole_eq_sums] at h5
      interval_cases d <;> interval_cases d' <;> first | rfl | (exfalso; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D0t, D1t, D2t, D3t, D4t] at h5 <;> norm_num at h5)
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D0t, D1t, D2t, D3t, D4t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D0t, D1t, D2t, D3t, D4t] <;> norm_num
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D0t, D1t, D2t, D3t, D4t] <;> norm_num)
  · refine ⟨fun d => if d = 3 then ![(32670/1037 : ℂ), (9306/1037 : ℂ)] else ![(-3248/177 : ℂ), (-7888/177 : ℂ)], fun d => if d = 3 then ![(1 : ℂ), (49/198 : ℂ)] else ![(1 : ℂ), (-147/464 : ℂ)], ?_, ?_, ?_, ?_, ?_⟩
    · intro d h1 h2
      interval_cases d
      · rw [hz3]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D0t, D1t, D2t, D3t, D4t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
      · rw [hz4]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D0t, D1t, D2t, D3t, D4t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D0t, D1t, D2t, D3t, D4t] <;> norm_num)
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D0t, D1t, D2t, D3t, D4t] <;> norm_num)
    · intro d h1 h2 hdj s hs1 hs2
      interval_cases d <;> interval_cases s <;> first | omega | (simp only [ltHat, hz3, hz4] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D0t, D1t, D2t, D3t, D4t] <;> norm_num)
    · intro d h1 h2 hjd
      refine ⟨fun s hs1 hs2 hsj => ?_, ?_⟩
      · interval_cases d <;> interval_cases s <;> first | omega | exact absurd rfl hsj | (simp only [ltHat, hz3, hz4] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D0t, D1t, D2t, D3t, D4t] <;> norm_num)
      · interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D0t, D1t, D2t, D3t, D4t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma rot_D5_2 : RotData 2 D5l D5t := by
  refine ⟨?_, ?_⟩
  · funext μ
    fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D0t, D1t, D2t, D3t, D4t, D5t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
  · intro d h1 h2
    rw [mdot_range_self]
    interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D0t, D1t, D2t, D3t, D4t, D5t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma gen_D5_2 : GenericAngles (fun i : Fin (1+4) => D5t i) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D0t, D1t, D2t, D3t, D4t, D5t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma far_D6_1_4 : FarData 1 4 D6l D6t := by
  have hz : ∀ d, zpole D6l D6t d = zpole D6l D6t d := fun _ => rfl
  have hz3 : zpole D6l D6t 3 = (57/68 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D0t, D1t, D2t, D3t, D4t, D5t, D6t] <;> norm_num
  refine ⟨⟨![(-5 : ℂ), (-5 : ℂ)], ![(-5 : ℂ), (-5 : ℂ)], ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D0t, D1t, D2t, D3t, D4t, D5t, D6t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D0t, D1t, D2t, D3t, D4t, D5t, D6t] <;> norm_num
    · intro b h1 h2
      rw [shiftedMom_zero, mdot_range_ref]
      interval_cases b <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D0t, D1t, D2t, D3t, D4t, D5t, D6t] <;> norm_num)
    · intro a b hab hb ha1 hne
      rw [shiftedMom_zero, mdot_range_self]
      have ha : a ≤ 2 := by omega
      interval_cases a <;> interval_cases b <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D0t, D1t, D2t, D3t, D4t, D5t, D6t] <;> norm_num)
    · rw [shiftedMom_zero]
      funext μ
      fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D0t, D1t, D2t, D3t, D4t, D5t, D6t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D0t, D1t, D2t, D3t, D4t, D5t, D6t] <;> norm_num)
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D0t, D1t, D2t, D3t, D4t, D5t, D6t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D0t, D1t, D2t, D3t, D4t, D5t, D6t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D0t, D1t, D2t, D3t, D4t, D5t, D6t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D0t, D1t, D2t, D3t, D4t, D5t, D6t] <;> norm_num)
    · intro d h1 h2
      rw [shiftedMom_zero, mdot_range_self]
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D0t, D1t, D2t, D3t, D4t, D5t, D6t] <;> norm_num)
    · intro d d' h1 h2 h3 h4 h5
      rw [zpole_eq_sums, zpole_eq_sums] at h5
      interval_cases d <;> interval_cases d' <;> first | rfl | (exfalso; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D0t, D1t, D2t, D3t, D4t, D5t, D6t] at h5 <;> norm_num at h5)
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D0t, D1t, D2t, D3t, D4t, D5t, D6t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D0t, D1t, D2t, D3t, D4t, D5t, D6t] <;> norm_num
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D0t, D1t, D2t, D3t, D4t, D5t, D6t] <;> norm_num)
  · refine ⟨fun d => ![(-328/17 : ℂ), (-861/34 : ℂ)], fun d => ![(1 : ℂ), (-61/82 : ℂ)], ?_, ?_, ?_, ?_, ?_⟩
    · intro d h1 h2
      interval_cases d
      · rw [hz3]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D0t, D1t, D2t, D3t, D4t, D5t, D6t] <;> norm_num)
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D0t, D1t, D2t, D3t, D4t, D5t, D6t] <;> norm_num)
    · intro d h1 h2 hdj s hs1 hs2
      interval_cases d <;> interval_cases s <;> first | omega | (simp only [ltHat, hz3] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D0t, D1t, D2t, D3t, D4t, D5t, D6t] <;> norm_num)
    · intro d h1 h2 hjd
      refine ⟨fun s hs1 hs2 hsj => ?_, ?_⟩
      · interval_cases d <;> interval_cases s <;> first | omega | exact absurd rfl hsj | (simp only [ltHat, hz3] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D0t, D1t, D2t, D3t, D4t, D5t, D6t] <;> norm_num)
      · interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D0t, D1t, D2t, D3t, D4t, D5t, D6t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma far_D7_0_3 : FarData 0 3 D7l D7t := by
  have hz : ∀ d, zpole D7l D7t d = zpole D7l D7t d := fun _ => rfl
  refine ⟨⟨![(-5 : ℂ), (-5 : ℂ)], ![(-5 : ℂ), (-5 : ℂ)], ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t] <;> norm_num
    · intro b h1 h2
      rw [shiftedMom_zero, mdot_range_ref]
      interval_cases b <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t] <;> norm_num)
    · intro a b hab hb ha1 hne
      rw [shiftedMom_zero, mdot_range_self]
      have ha : a ≤ 1 := by omega
      interval_cases a <;> interval_cases b <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t] <;> norm_num)
    · rw [shiftedMom_zero]
      funext μ
      fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t] <;> norm_num)
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t] <;> norm_num)
    · intro d h1 h2
      rw [shiftedMom_zero, mdot_range_self]
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t] <;> norm_num)
    · intro d d' h1 h2 h3 h4 h5
      rw [zpole_eq_sums, zpole_eq_sums] at h5
      interval_cases d <;> interval_cases d' <;> first | rfl | (exfalso; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t] at h5 <;> norm_num at h5)
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t] <;> norm_num
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t] <;> norm_num)
  · refine ⟨fun _ => ![0, 0], fun _ => ![0, 0], ?_, ?_, ?_, ?_, ?_⟩
    · intro d h1 h2
      interval_cases d
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t] <;> norm_num)
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t] <;> norm_num)
    · intro d h1 h2 hdj s hs1 hs2
      interval_cases d <;> interval_cases s <;> first | omega | (simp only [ltHat, hz] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t] <;> norm_num)
    · intro d h1 h2 hjd
      refine ⟨fun s hs1 hs2 hsj => ?_, ?_⟩
      · interval_cases d <;> interval_cases s <;> first | omega | exact absurd rfl hsj | (simp only [ltHat, hz] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t] <;> norm_num)
      · interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma gmax_D8_0_2 : Gmax 0 2 D8l D8t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_, ?_, ?_, ?_⟩
  · funext μ
    fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num

lemma gmax_D7_1_3 : Gmax 1 3 D7l D7t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rw [if_pos (by norm_num)]
  exact ⟨far_D7_0_3, gmax_D8_0_2⟩

lemma gmax_D5_2_1 : Gmax 2 1 D5l D5t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rw [if_neg (by norm_num)]
  exact ⟨rot_D5_2, gen_D5_2, far_D6_1_4, gmax_D7_1_3⟩

lemma gmax_D0_3_2 : Gmax 3 2 D0l D0t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rw [if_pos (by norm_num)]
  exact ⟨far_D0_2_2, gmax_D5_2_1⟩

set_option maxHeartbeats 4000000 in
lemma far_D0_2_3 : FarData 2 3 D0l D0t := by
  have hz : ∀ d, zpole D0l D0t d = zpole D0l D0t d := fun _ => rfl
  have hz3 : zpole D0l D0t 3 = (-312/1037 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num
  have hz4 : zpole D0l D0t 4 = (-47/59 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num
  refine ⟨⟨![(-5 : ℂ), (-5 : ℂ)], ![(-5 : ℂ), (-5 : ℂ)], ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num
    · intro b h1 h2
      rw [shiftedMom_zero, mdot_range_ref]
      interval_cases b <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num)
    · intro a b hab hb ha1 hne
      rw [shiftedMom_zero, mdot_range_self]
      have ha : a ≤ 3 := by omega
      interval_cases a <;> interval_cases b <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num)
    · rw [shiftedMom_zero]
      funext μ
      fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num)
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num)
    · intro d h1 h2
      rw [shiftedMom_zero, mdot_range_self]
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num)
    · intro d d' h1 h2 h3 h4 h5
      rw [zpole_eq_sums, zpole_eq_sums] at h5
      interval_cases d <;> interval_cases d' <;> first | rfl | (exfalso; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] at h5 <;> norm_num at h5)
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num)
  · refine ⟨fun d => if d = 3 then ![(32670/1037 : ℂ), (9306/1037 : ℂ)] else ![(-3248/177 : ℂ), (-7888/177 : ℂ)], fun d => if d = 3 then ![(1 : ℂ), (49/198 : ℂ)] else ![(1 : ℂ), (-147/464 : ℂ)], ?_, ?_, ?_, ?_, ?_⟩
    · intro d h1 h2
      interval_cases d
      · rw [hz3]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
      · rw [hz4]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num)
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num)
    · intro d h1 h2 hdj s hs1 hs2
      interval_cases d <;> interval_cases s <;> first | omega | (simp only [ltHat, hz3, hz4] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num)
    · intro d h1 h2 hjd
      refine ⟨fun s hs1 hs2 hsj => ?_, ?_⟩
      · interval_cases d <;> interval_cases s <;> first | omega | exact absurd rfl hsj | (simp only [ltHat, hz3, hz4] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num)
      · interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma far_D5_1_2 : FarData 1 2 D5l D5t := by
  have hz : ∀ d, zpole D5l D5t d = zpole D5l D5t d := fun _ => rfl
  have hz3 : zpole D5l D5t 3 = (375/707 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num
  refine ⟨⟨![(-5 : ℂ), (-5 : ℂ)], ![(-5 : ℂ), (-5 : ℂ)], ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num
    · intro b h1 h2
      rw [shiftedMom_zero, mdot_range_ref]
      interval_cases b <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num)
    · intro a b hab hb ha1 hne
      rw [shiftedMom_zero, mdot_range_self]
      have ha : a ≤ 2 := by omega
      interval_cases a <;> interval_cases b <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num)
    · rw [shiftedMom_zero]
      funext μ
      fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num)
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num)
    · intro d h1 h2
      rw [shiftedMom_zero, mdot_range_self]
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num)
    · intro d d' h1 h2 h3 h4 h5
      rw [zpole_eq_sums, zpole_eq_sums] at h5
      interval_cases d <;> interval_cases d' <;> first | rfl | (exfalso; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] at h5 <;> norm_num at h5)
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num)
  · refine ⟨fun d => ![(-3272/303 : ℂ), (-55624/2121 : ℂ)], fun d => ![(1 : ℂ), (69/3272 : ℂ)], ?_, ?_, ?_, ?_, ?_⟩
    · intro d h1 h2
      interval_cases d
      · rw [hz3]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num)
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num)
    · intro d h1 h2 hdj s hs1 hs2
      interval_cases d <;> interval_cases s <;> first | omega | (simp only [ltHat, hz3] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num)
    · intro d h1 h2 hjd
      refine ⟨fun s hs1 hs2 hsj => ?_, ?_⟩
      · interval_cases d <;> interval_cases s <;> first | omega | exact absurd rfl hsj | (simp only [ltHat, hz3] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num)
      · interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma rot_D9_1 : RotData 1 D9l D9t := by
  refine ⟨?_, ?_⟩
  · funext μ
    fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
  · intro d h1 h2
    rw [mdot_range_self]
    interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma gen_D9_1 : GenericAngles (fun i : Fin (0+4) => D9t i) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma far_D10_0_3 : FarData 0 3 D10l D10t := by
  have hz : ∀ d, zpole D10l D10t d = zpole D10l D10t d := fun _ => rfl
  refine ⟨⟨![(-5 : ℂ), (-5 : ℂ)], ![(-5 : ℂ), (-5 : ℂ)], ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t] <;> norm_num
    · intro b h1 h2
      rw [shiftedMom_zero, mdot_range_ref]
      interval_cases b <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t] <;> norm_num)
    · intro a b hab hb ha1 hne
      rw [shiftedMom_zero, mdot_range_self]
      have ha : a ≤ 1 := by omega
      interval_cases a <;> interval_cases b <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t] <;> norm_num)
    · rw [shiftedMom_zero]
      funext μ
      fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t] <;> norm_num)
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t] <;> norm_num)
    · intro d h1 h2
      rw [shiftedMom_zero, mdot_range_self]
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t] <;> norm_num)
    · intro d d' h1 h2 h3 h4 h5
      rw [zpole_eq_sums, zpole_eq_sums] at h5
      interval_cases d <;> interval_cases d' <;> first | rfl | (exfalso; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t] at h5 <;> norm_num at h5)
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t] <;> norm_num
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t] <;> norm_num)
  · refine ⟨fun _ => ![0, 0], fun _ => ![0, 0], ?_, ?_, ?_, ?_, ?_⟩
    · intro d h1 h2
      interval_cases d
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t] <;> norm_num)
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t] <;> norm_num)
    · intro d h1 h2 hdj s hs1 hs2
      interval_cases d <;> interval_cases s <;> first | omega | (simp only [ltHat, hz] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t] <;> norm_num)
    · intro d h1 h2 hjd
      refine ⟨fun s hs1 hs2 hsj => ?_, ?_⟩
      · interval_cases d <;> interval_cases s <;> first | omega | exact absurd rfl hsj | (simp only [ltHat, hz] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t] <;> norm_num)
      · interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma gmax_D11_0_2 : Gmax 0 2 D11l D11t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_, ?_, ?_, ?_⟩
  · funext μ
    fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num

lemma gmax_D9_1_1 : Gmax 1 1 D9l D9t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rw [if_neg (by norm_num)]
  exact ⟨rot_D9_1, gen_D9_1, far_D10_0_3, gmax_D11_0_2⟩

lemma gmax_D5_2_2 : Gmax 2 2 D5l D5t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rw [if_pos (by norm_num)]
  exact ⟨far_D5_1_2, gmax_D9_1_1⟩

lemma gmax_D0_3_3 : Gmax 3 3 D0l D0t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rw [if_pos (by norm_num)]
  exact ⟨far_D0_2_3, gmax_D5_2_2⟩

set_option maxHeartbeats 4000000 in
lemma far_D0_2_4 : FarData 2 4 D0l D0t := by
  have hz : ∀ d, zpole D0l D0t d = zpole D0l D0t d := fun _ => rfl
  have hz3 : zpole D0l D0t 3 = (-312/1037 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num
  have hz4 : zpole D0l D0t 4 = (-47/59 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num
  refine ⟨⟨![(-5 : ℂ), (-5 : ℂ)], ![(-5 : ℂ), (-5 : ℂ)], ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num
    · intro b h1 h2
      rw [shiftedMom_zero, mdot_range_ref]
      interval_cases b <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num)
    · intro a b hab hb ha1 hne
      rw [shiftedMom_zero, mdot_range_self]
      have ha : a ≤ 3 := by omega
      interval_cases a <;> interval_cases b <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num)
    · rw [shiftedMom_zero]
      funext μ
      fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num)
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num)
    · intro d h1 h2
      rw [shiftedMom_zero, mdot_range_self]
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num)
    · intro d d' h1 h2 h3 h4 h5
      rw [zpole_eq_sums, zpole_eq_sums] at h5
      interval_cases d <;> interval_cases d' <;> first | rfl | (exfalso; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] at h5 <;> norm_num at h5)
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num)
  · refine ⟨fun d => if d = 3 then ![(32670/1037 : ℂ), (9306/1037 : ℂ)] else ![(-3248/177 : ℂ), (-7888/177 : ℂ)], fun d => if d = 3 then ![(1 : ℂ), (49/198 : ℂ)] else ![(1 : ℂ), (-147/464 : ℂ)], ?_, ?_, ?_, ?_, ?_⟩
    · intro d h1 h2
      interval_cases d
      · rw [hz3]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
      · rw [hz4]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num)
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num)
    · intro d h1 h2 hdj s hs1 hs2
      interval_cases d <;> interval_cases s <;> first | omega | (simp only [ltHat, hz3, hz4] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num)
    · intro d h1 h2 hjd
      refine ⟨fun s hs1 hs2 hsj => ?_, ?_⟩
      · interval_cases d <;> interval_cases s <;> first | omega | exact absurd rfl hsj | (simp only [ltHat, hz3, hz4] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num)
      · interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma far_D5_1_3 : FarData 1 3 D5l D5t := by
  have hz : ∀ d, zpole D5l D5t d = zpole D5l D5t d := fun _ => rfl
  have hz3 : zpole D5l D5t 3 = (375/707 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num
  refine ⟨⟨![(-5 : ℂ), (-5 : ℂ)], ![(-5 : ℂ), (-5 : ℂ)], ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num
    · intro b h1 h2
      rw [shiftedMom_zero, mdot_range_ref]
      interval_cases b <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num)
    · intro a b hab hb ha1 hne
      rw [shiftedMom_zero, mdot_range_self]
      have ha : a ≤ 2 := by omega
      interval_cases a <;> interval_cases b <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num)
    · rw [shiftedMom_zero]
      funext μ
      fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num)
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num)
    · intro d h1 h2
      rw [shiftedMom_zero, mdot_range_self]
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num)
    · intro d d' h1 h2 h3 h4 h5
      rw [zpole_eq_sums, zpole_eq_sums] at h5
      interval_cases d <;> interval_cases d' <;> first | rfl | (exfalso; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] at h5 <;> norm_num at h5)
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num)
  · refine ⟨fun d => ![(-3272/303 : ℂ), (-55624/2121 : ℂ)], fun d => ![(1 : ℂ), (69/3272 : ℂ)], ?_, ?_, ?_, ?_, ?_⟩
    · intro d h1 h2
      interval_cases d
      · rw [hz3]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num)
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num)
    · intro d h1 h2 hdj s hs1 hs2
      interval_cases d <;> interval_cases s <;> first | omega | (simp only [ltHat, hz3] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num)
    · intro d h1 h2 hjd
      refine ⟨fun s hs1 hs2 hsj => ?_, ?_⟩
      · interval_cases d <;> interval_cases s <;> first | omega | exact absurd rfl hsj | (simp only [ltHat, hz3] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num)
      · interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma far_D9_0_2 : FarData 0 2 D9l D9t := by
  have hz : ∀ d, zpole D9l D9t d = zpole D9l D9t d := fun _ => rfl
  refine ⟨⟨![(-5 : ℂ), (-5 : ℂ)], ![(-5 : ℂ), (-5 : ℂ)], ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num
    · intro b h1 h2
      rw [shiftedMom_zero, mdot_range_ref]
      interval_cases b <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num)
    · intro a b hab hb ha1 hne
      rw [shiftedMom_zero, mdot_range_self]
      have ha : a ≤ 1 := by omega
      interval_cases a <;> interval_cases b <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num)
    · rw [shiftedMom_zero]
      funext μ
      fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num)
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num)
    · intro d h1 h2
      rw [shiftedMom_zero, mdot_range_self]
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num)
    · intro d d' h1 h2 h3 h4 h5
      rw [zpole_eq_sums, zpole_eq_sums] at h5
      interval_cases d <;> interval_cases d' <;> first | rfl | (exfalso; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] at h5 <;> norm_num at h5)
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num)
  · refine ⟨fun _ => ![0, 0], fun _ => ![0, 0], ?_, ?_, ?_, ?_, ?_⟩
    · intro d h1 h2
      interval_cases d
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num)
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num)
    · intro d h1 h2 hdj s hs1 hs2
      interval_cases d <;> interval_cases s <;> first | omega | (simp only [ltHat, hz] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num)
    · intro d h1 h2 hjd
      refine ⟨fun s hs1 hs2 hsj => ?_, ?_⟩
      · interval_cases d <;> interval_cases s <;> first | omega | exact absurd rfl hsj | (simp only [ltHat, hz] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num)
      · interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma gmax_D12_0_1 : Gmax 0 1 D12l D12t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_, ?_, ?_, ?_⟩
  · funext μ
    fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num

lemma gmax_D9_1_2 : Gmax 1 2 D9l D9t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rw [if_pos (by norm_num)]
  exact ⟨far_D9_0_2, gmax_D12_0_1⟩

lemma gmax_D5_2_3 : Gmax 2 3 D5l D5t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rw [if_pos (by norm_num)]
  exact ⟨far_D5_1_3, gmax_D9_1_2⟩

lemma gmax_D0_3_4 : Gmax 3 4 D0l D0t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rw [if_pos (by norm_num)]
  exact ⟨far_D0_2_4, gmax_D5_2_3⟩

set_option maxHeartbeats 4000000 in
lemma far_D0_2_5 : FarData 2 5 D0l D0t := by
  have hz : ∀ d, zpole D0l D0t d = zpole D0l D0t d := fun _ => rfl
  have hz3 : zpole D0l D0t 3 = (-312/1037 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num
  have hz4 : zpole D0l D0t 4 = (-47/59 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num
  refine ⟨⟨![(-5 : ℂ), (-5 : ℂ)], ![(-5 : ℂ), (-5 : ℂ)], ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num
    · intro b h1 h2
      rw [shiftedMom_zero, mdot_range_ref]
      interval_cases b <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num)
    · intro a b hab hb ha1 hne
      rw [shiftedMom_zero, mdot_range_self]
      have ha : a ≤ 3 := by omega
      interval_cases a <;> interval_cases b <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num)
    · rw [shiftedMom_zero]
      funext μ
      fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num)
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num)
    · intro d h1 h2
      rw [shiftedMom_zero, mdot_range_self]
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num)
    · intro d d' h1 h2 h3 h4 h5
      rw [zpole_eq_sums, zpole_eq_sums] at h5
      interval_cases d <;> interval_cases d' <;> first | rfl | (exfalso; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] at h5 <;> norm_num at h5)
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num)
  · refine ⟨fun d => if d = 3 then ![(32670/1037 : ℂ), (9306/1037 : ℂ)] else ![(-3248/177 : ℂ), (-7888/177 : ℂ)], fun d => if d = 3 then ![(1 : ℂ), (49/198 : ℂ)] else ![(1 : ℂ), (-147/464 : ℂ)], ?_, ?_, ?_, ?_, ?_⟩
    · intro d h1 h2
      interval_cases d
      · rw [hz3]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
      · rw [hz4]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num)
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num)
    · intro d h1 h2 hdj s hs1 hs2
      interval_cases d <;> interval_cases s <;> first | omega | (simp only [ltHat, hz3, hz4] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num)
    · intro d h1 h2 hjd
      refine ⟨fun s hs1 hs2 hsj => ?_, ?_⟩
      · interval_cases d <;> interval_cases s <;> first | omega | exact absurd rfl hsj | (simp only [ltHat, hz3, hz4] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num)
      · interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma far_D5_1_4 : FarData 1 4 D5l D5t := by
  have hz : ∀ d, zpole D5l D5t d = zpole D5l D5t d := fun _ => rfl
  have hz3 : zpole D5l D5t 3 = (375/707 : ℂ) := by
    rw [zpole_eq_sums]; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num
  refine ⟨⟨![(-5 : ℂ), (-5 : ℂ)], ![(-5 : ℂ), (-5 : ℂ)], ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num
    · intro b h1 h2
      rw [shiftedMom_zero, mdot_range_ref]
      interval_cases b <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num)
    · intro a b hab hb ha1 hne
      rw [shiftedMom_zero, mdot_range_self]
      have ha : a ≤ 2 := by omega
      interval_cases a <;> interval_cases b <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num)
    · rw [shiftedMom_zero]
      funext μ
      fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num)
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num)
    · intro d h1 h2
      rw [shiftedMom_zero, mdot_range_self]
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num)
    · intro d d' h1 h2 h3 h4 h5
      rw [zpole_eq_sums, zpole_eq_sums] at h5
      interval_cases d <;> interval_cases d' <;> first | rfl | (exfalso; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] at h5 <;> norm_num at h5)
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num)
  · refine ⟨fun d => ![(-3272/303 : ℂ), (-55624/2121 : ℂ)], fun d => ![(1 : ℂ), (69/3272 : ℂ)], ?_, ?_, ?_, ?_, ?_⟩
    · intro d h1 h2
      interval_cases d
      · rw [hz3]
        funext μ
        fin_cases μ <;> simp [shiftedMom, momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num)
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num)
    · intro d h1 h2 hdj s hs1 hs2
      interval_cases d <;> interval_cases s <;> first | omega | (simp only [ltHat, hz3] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num)
    · intro d h1 h2 hjd
      refine ⟨fun s hs1 hs2 hsj => ?_, ?_⟩
      · interval_cases d <;> interval_cases s <;> first | omega | exact absurd rfl hsj | (simp only [ltHat, hz3] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num)
      · interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma far_D9_0_3 : FarData 0 3 D9l D9t := by
  have hz : ∀ d, zpole D9l D9t d = zpole D9l D9t d := fun _ => rfl
  refine ⟨⟨![(-5 : ℂ), (-5 : ℂ)], ![(-5 : ℂ), (-5 : ℂ)], ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num
    · intro b h1 h2
      rw [shiftedMom_zero, mdot_range_ref]
      interval_cases b <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num)
    · intro a b hab hb ha1 hne
      rw [shiftedMom_zero, mdot_range_self]
      have ha : a ≤ 1 := by omega
      interval_cases a <;> interval_cases b <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num)
    · rw [shiftedMom_zero]
      funext μ
      fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num)
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num
    · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num
    · intro t h1 h2 h3
      interval_cases t <;> first | omega | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num)
    · intro d h1 h2
      rw [shiftedMom_zero, mdot_range_self]
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num)
    · intro d d' h1 h2 h3 h4 h5
      rw [zpole_eq_sums, zpole_eq_sums] at h5
      interval_cases d <;> interval_cases d' <;> first | rfl | (exfalso; simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] at h5 <;> norm_num at h5)
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num)
  · refine ⟨fun _ => ![0, 0], fun _ => ![0, 0], ?_, ?_, ?_, ?_, ?_⟩
    · intro d h1 h2
      interval_cases d
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num)
    · intro d h1 h2
      interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num)
    · intro d h1 h2 hdj s hs1 hs2
      interval_cases d <;> interval_cases s <;> first | omega | (simp only [ltHat, hz] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num)
    · intro d h1 h2 hjd
      refine ⟨fun s hs1 hs2 hsj => ?_, ?_⟩
      · interval_cases d <;> interval_cases s <;> first | omega | exact absurd rfl hsj | (simp only [ltHat, hz] <;> simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num)
      · interval_cases d <;> (simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num)

set_option maxHeartbeats 4000000 in
lemma gmax_D12_0_2 : Gmax 0 2 D12l D12t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_, ?_, ?_, ?_⟩
  · funext μ
    fin_cases μ <;> simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t, nullMom, momOf] <;> field_simp <;> ring_nf <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num
  · simp [Finset.sum_Ico_succ_top, Finset.sum_range_succ, angleBr_eq, squareBr_eq, redL, redLt, rotLabels, l6, lt6, D0l, D1l, D2l, D3l, D4l, D5l, D6l, D7l, D8l, D9l, D10l, D11l, D12l, D0t, D1t, D2t, D3t, D4t, D5t, D6t, D7t, D8t, D9t, D10t, D11t, D12t] <;> norm_num

lemma gmax_D9_1_3 : Gmax 1 3 D9l D9t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rw [if_pos (by norm_num)]
  exact ⟨far_D9_0_3, gmax_D12_0_2⟩

lemma gmax_D5_2_4 : Gmax 2 4 D5l D5t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rw [if_pos (by norm_num)]
  exact ⟨far_D5_1_4, gmax_D9_1_3⟩

lemma gmax_D0_3_5 : Gmax 3 5 D0l D0t := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  rw [if_pos (by norm_num)]
  exact ⟨far_D0_2_5, gmax_D5_2_4⟩

/-- **Non-vacuity at six gluons**: the point is in `Gmax 3 j` for every position `j` of the second negative gluon. -/
theorem gmax_six (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ 5) : Gmax 3 j l6 lt6 := by
  interval_cases j
  · exact gmax_D0_3_1
  · exact gmax_D0_3_2
  · exact gmax_D0_3_3
  · exact gmax_D0_3_4
  · exact gmax_D0_3_5

end Lightlike.SpinorHelicity.Tests
