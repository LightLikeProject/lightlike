import Lightlike.GR.MHVReduce
import Lightlike.GR.MHVChannelTwoJ2

/-!
# One step of the BCFW induction for the true amplitudes

The contribution of the channel `[1, 2]` to the recursion, divided by its propagator, is the reduced true amplitude
times the factor `([12]/c) / (⟨12⟩[12])` of the Parke-Taylor recursion (Elvang-Huang (3.17)–(3.22)).
-/

noncomputable section

namespace Lightlike.SpinorHelicity

/-- `[P 1] = −[1 2]` for `|P] = c|1] + |2]`. -/
lemma squareBr_pole_left (c : ℂ) (a b : Fin 2 → ℂ) : squareBr (c • a + b) a = -squareBr a b := by
  simp [squareBr_eq]; ring

/-- The propagator of the channel `[1, 2]` before the shift is `⟨12⟩[12]`. -/
lemma mdot_momRange_two (l lt : ℕ → Fin 2 → ℂ) :
    mdot (momRange (shiftedMom l lt 0) 1 2) (momRange (shiftedMom l lt 0) 1 2) =
      angleBr (lt 1) (lt 2) * squareBr (l 1) (l 2) := by
  have hP : momRange (shiftedMom l lt 0) 1 2 = nullMom (l 1) (lt 1) + nullMom (l 2) (lt 2) := by
    rw [momRange_two]; simp [shiftedMom]
  rw [hP]
  simp only [mdot_add_left, mdot_add_right, mdot_nullMom_two]
  have a1 : angleBr (lt 1) (lt 1) = 0 := by rw [angleBr_eq]; ring
  have a2 : angleBr (lt 2) (lt 2) = 0 := by rw [angleBr_eq]; ring
  have s1 : squareBr (l 1) (l 1) = 0 := by rw [squareBr_eq]; ring
  have s2 : squareBr (l 2) (l 2) = 0 := by rw [squareBr_eq]; ring
  have hs : squareBr (l 2) (l 1) = -squareBr (l 1) (l 2) := squareBr_antisymm _ _
  have ha : angleBr (lt 2) (lt 1) = -angleBr (lt 1) (lt 2) := angleBr_antisymm _ _
  rw [a1, a2, s1, s2, hs, ha]
  ring

/-- **The channel `[1, 2]` for the negative gluons `0` and `2`**: its contribution to the recursion is the reduced
true amplitude times `([12]/c)/(⟨12⟩[12])`. -/
theorem step_two {m : ℕ} {l lt : ℕ → Fin 2 → ℂ} {qs0 qa0 : Fin 2 → ℂ} (K : TrueKin m 2 l lt qs0 qa0)
    (hm : 1 ≤ m) (h02 : angleBr (lt 0) (lt 2) ≠ 0) (h01 : angleBr (lt 0) (lt 1) ≠ 0) :
    (1 / mdot (momRange (shiftedMom l lt 0) 1 2) (momRange (shiftedMom l lt 0) 1 2)) *
        channelTerm m (shiftedMom l lt (zpole l lt 2)) (shiftedPol l lt (l 1) (lt 0) 2 (zpole l lt 2)) 1 2
          ((angleBr (lt 0) (lt 1) / angleBr (lt 0) (lt 2)) • l 1 + l 2) (lt 2) (l 1) (lt 0) =
      (squareBr (l 1) (l 2) / (angleBr (lt 0) (lt 1) / angleBr (lt 0) (lt 2))) /
          (angleBr (lt 1) (lt 2) * squareBr (l 1) (l 2)) *
        trueAmp (m - 1) 1 (redL l lt) (redLt lt) (l 1) (lt 0) := by
  have h12 : squareBr (l 1) (l 2) ≠ 0 := K.gj
  have hP := momRange_pole_two l lt h02 h12
  have hq1 : angleBr (lt 0) (lt 2) ≠ 0 := h02
  rw [channelTerm_two_j2 K hm _ _ hP hq1, mdot_momRange_two]
  have hR : bgAmplitude (m - (2 - 1)) (collapse (shiftedMom l lt (zpole l lt 2)) 1 2
        (momRange (shiftedMom l lt (zpole l lt 2)) 1 2))
        (collapse (shiftedPol l lt (l 1) (lt 0) 2 (zpole l lt 2)) 1 2
          (epsMinus ((angleBr (lt 0) (lt 1) / angleBr (lt 0) (lt 2)) • l 1 + l 2) (lt 2) (l 1))) =
      trueAmp (m - 1) 1 (redL l lt) (redLt lt) (l 1) (lt 0) := by
    unfold trueAmp
    rw [show m - (2 - 1) = m - 1 by omega]
    congr 1
    · funext t; exact collapse_pole_two l lt h02 h12 t
    · funext t
      have := collapse_pol_two l lt 2 le_rfl h02 h12 t
      simpa using this
  rw [hR]
  have hz : ltHat lt (zpole l lt 2) 1 = (angleBr (lt 0) (lt 1) / angleBr (lt 0) (lt 2)) • lt 2 := by
    rw [zpole_two l lt h02 h12]
    simp only [ltHat, if_true]
    exact sub_smul_eq_smul_two (lt 1) (lt 0) (lt 2) h02
  rw [hz, squareBr_pole_left, angleBr_neg_right', angleBr_smul_right']
  field_simp

end Lightlike.SpinorHelicity
