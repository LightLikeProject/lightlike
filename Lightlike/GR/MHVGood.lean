import Lightlike.GR.MHVPTStep
import Lightlike.GR.MHVStep

/-!
# The good-gauge amplitude by the recursion and the induction hypothesis

Given the evaluation of the channel `[1, 2]` and the induction hypothesis for the reduced kinematics, the true
amplitude in the good gauge (`|q] = |1]`, `⟨q'| = ⟨0|`) is the Parke-Taylor amplitude: the channels `[1, d]`, `d ≥ 3`,
vanish and the channel `[1, 2]` reproduces the recursion of the Parke-Taylor amplitudes.
-/

noncomputable section

namespace Lightlike.SpinorHelicity

/-- The shifted kinematics at `z = 0` are the unshifted ones. -/
lemma shiftedMom_zero (l lt : ℕ → Fin 2 → ℂ) : shiftedMom l lt 0 = fun t => nullMom (l t) (lt t) := by
  funext t
  by_cases h0 : t = 0 <;> by_cases h1 : t = 1 <;> simp [shiftedMom, h0, h1]

/-- The shifted polarizations at `z = 0` are those of the true amplitude with negative gluons `0` and `j`. -/
lemma shiftedPol_zero_eq (l lt : ℕ → Fin 2 → ℂ) (qs qa : Fin 2 → ℂ) (j : ℕ) (hj : 2 ≤ j) :
    shiftedPol l lt qs qa j 0 =
      polRef (fun t => t = 0 ∨ t = j) l lt (fun _ => qs) (fun _ => qa) := by
  have := shiftedPol_eq l lt qs qa j hj 0
  have hl : lHat l 0 = l := by funext t; by_cases h : t = 0 <;> simp [lHat, h]
  have hlt : ltHat lt 0 = lt := by funext t; by_cases h : t = 1 <;> simp [ltHat, h]
  rw [hl, hlt] at this
  exact funext this

/-- **The true amplitude in the good gauge is the Parke-Taylor amplitude**, given the vanishing data of the far
channels, the evaluation of the channel `[1, 2]` and the induction hypothesis for the reduced kinematics. -/
theorem trueAmp_good (m j : ℕ) (hj : 2 ≤ j) (l lt : ℕ → Fin 2 → ℂ) (qs0 qa0 : Fin 2 → ℂ)
    (K : TrueKin (m + 1) j l lt qs0 qa0) (h02 : angleBr (lt 0) (lt 2) ≠ 0) (h12 : squareBr (l 1) (l 2) ≠ 0)
    (hg : GenericAngles (fun i : Fin (m + 4) => lt i)) (lP ltP : ℕ → Fin 2 → ℂ)
    (hP : ∀ d, 3 ≤ d → d ≤ m + 2 →
      momRange (shiftedMom l lt (zpole l lt d)) 1 d = nullMom (lP d) (ltP d))
    (hq1 : ∀ d, 3 ≤ d → d ≤ m + 2 → angleBr (lt 0) (ltP d) ≠ 0)
    (hq2 : ∀ d, 3 ≤ d → d ≤ m + 2 → squareBr (l 1) (lP d) ≠ 0)
    (hA : ∀ d, 3 ≤ d → d ≤ m + 2 → d < j → ∀ s, 1 ≤ s → s ≤ d →
      angleBr (ltP d) (ltHat lt (zpole l lt d) s) ≠ 0)
    (hB : ∀ d, 3 ≤ d → d ≤ m + 2 → j ≤ d →
      (∀ s, 1 ≤ s → s ≤ d → s ≠ j → angleBr (lt j) (ltHat lt (zpole l lt d) s) ≠ 0) ∧
        angleBr (lt j) (ltP d) ≠ 0)
    (hd2 : (1 / mdot (momRange (shiftedMom l lt 0) 1 2) (momRange (shiftedMom l lt 0) 1 2)) *
        channelTerm (m + 1) (shiftedMom l lt (zpole l lt 2))
          (shiftedPol l lt (l 1) (lt 0) j (zpole l lt 2)) 1 2
          ((angleBr (lt 0) (lt 1) / angleBr (lt 0) (lt 2)) • l 1 + l 2) (lt 2) (l 1) (lt 0) =
      (squareBr (l 1) (l 2) / (angleBr (lt 0) (lt 1) / angleBr (lt 0) (lt 2))) /
          (angleBr (lt 1) (lt 2) * squareBr (l 1) (l 2)) *
        trueAmp m (j - 1) (redL l lt) (redLt lt) (l 1) (lt 0))
    (hIH : trueAmp m (j - 1) (redL l lt) (redLt lt) (l 1) (lt 0) = ptN m (j - 1) (redLt lt)) :
    trueAmp (m + 1) j l lt (l 1) (lt 0) = ptN (m + 1) j lt := by
  set c := angleBr (lt 0) (lt 1) / angleBr (lt 0) (lt 2) with hc
  set lP' : ℕ → Fin 2 → ℂ := fun d => if d = 2 then c • l 1 + l 2 else lP d with hlP'
  set ltP' : ℕ → Fin 2 → ℂ := fun d => if d = 2 then lt 2 else ltP d with hltP'
  have hrec := true_recursion (m + 1) j l lt qs0 qa0 K lP' ltP'
    (fun d hd1 hd2' => by
      by_cases h2 : d = 2
      · subst h2; simp only [hlP', hltP', if_true]; exact momRange_pole_two l lt h02 h12
      · simp only [hlP', hltP', h2, if_false]; exact hP d (by omega) (by omega))
    (fun d hd1 hd2' => by
      by_cases h2 : d = 2
      · subst h2; simp only [hltP', if_true]; exact h02
      · simp only [hltP', h2, if_false]; exact hq1 d (by omega) (by omega))
    (fun d hd1 hd2' => by
      by_cases h2 : d = 2
      · subst h2
        simp only [hlP', if_true]
        have : squareBr (l 1) (c • l 1 + l 2) = squareBr (l 1) (l 2) := by simp [squareBr_eq]; ring
        rw [this]; exact h12
      · simp only [hlP', h2, if_false]; exact hq2 d (by omega) (by omega))
  have hL : trueAmp (m + 1) j l lt (l 1) (lt 0) =
      bgAmplitude (m + 1) (shiftedMom l lt 0) (shiftedPol l lt (l 1) (lt 0) j 0) := by
    unfold trueAmp
    rw [shiftedMom_zero, shiftedPol_zero_eq l lt (l 1) (lt 0) j hj]
  rw [hL, hrec, Finset.sum_eq_single 2]
  · have h2 : lP' 2 = c • l 1 + l 2 := by simp [hlP']
    have h2' : ltP' 2 = lt 2 := by simp [hltP']
    rw [h2, h2', hd2, hIH, ptN_step m j hj (by have := K.hjm; omega) l lt hg h12]
    ring
  · intro d hd hd2'
    have hd' := Finset.mem_Icc.1 hd
    have hz := channelTerm_zero_far K (show 3 ≤ d by omega) hd'.2 (lP' d) (ltP' d)
      (by simp only [hlP', hltP', hd2', if_false]; exact hP d (by omega) (by omega))
      (by simp only [hltP', hd2', if_false]; exact hq1 d (by omega) (by omega))
      (fun h s h1 h2 => by simp only [hltP', hd2', if_false]; exact hA d (by omega) (by omega) h s h1 h2)
      (fun h => by
        obtain ⟨b1, b2⟩ := hB d (by omega) (by omega) h
        simp only [hltP', hd2', if_false]
        exact ⟨b1, b2⟩)
    rw [hz, mul_zero]
  · intro h
    exfalso; apply h
    exact Finset.mem_Icc.2 ⟨le_rfl, by omega⟩

end Lightlike.SpinorHelicity
