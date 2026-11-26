import Lightlike.GR.MHVStep

/-!
# One step of the BCFW induction, second negative gluon `j ≥ 3`

The channel `[1, 2]` for the negative gluons `0` and `j ≥ 3`: the left factor is the anti-MHV three-point amplitude
`A₃(1⁺, 2⁺, P⁻)`, and the right factor is the reduced true amplitude with the negative gluons `0` and `j − 1`
(Elvang-Huang (3.17)–(3.22)).
-/

noncomputable section

namespace Lightlike.SpinorHelicity

/-- **The channel `[1, 2]` for the negative gluons `0` and `j ≥ 3`**: its contribution to the recursion is the reduced
true amplitude times `([12]/c)/(⟨12⟩[12])`. -/
theorem step_far {m j : ℕ} {l lt : ℕ → Fin 2 → ℂ} {qs0 qa0 : Fin 2 → ℂ} (K : TrueKin m j l lt qs0 qa0)
    (hj3 : 3 ≤ j) (hm : 1 ≤ m) (h02 : angleBr (lt 0) (lt 2) ≠ 0) (h12 : squareBr (l 1) (l 2) ≠ 0) :
    (1 / mdot (momRange (shiftedMom l lt 0) 1 2) (momRange (shiftedMom l lt 0) 1 2)) *
        channelTerm m (shiftedMom l lt (zpole l lt 2)) (shiftedPol l lt (l 1) (lt 0) j (zpole l lt 2)) 1 2
          ((angleBr (lt 0) (lt 1) / angleBr (lt 0) (lt 2)) • l 1 + l 2) (lt 2) (l 1) (lt 0) =
      (squareBr (l 1) (l 2) / (angleBr (lt 0) (lt 1) / angleBr (lt 0) (lt 2))) /
          (angleBr (lt 1) (lt 2) * squareBr (l 1) (l 2)) *
        trueAmp (m - 1) (j - 1) (redL l lt) (redLt lt) (l 1) (lt 0) := by
  set z := zpole l lt 2 with hz
  have hP := momRange_pole_two l lt h02 h12
  have h01 : angleBr (lt 0) (lt 1) ≠ 0 := K.g1
  have hzl : ltHat lt z 1 = (angleBr (lt 0) (lt 1) / angleBr (lt 0) (lt 2)) • lt 2 := by
    rw [hz, zpole_two l lt h02 h12]
    simp only [ltHat, if_true]
    exact sub_smul_eq_smul_two (lt 1) (lt 0) (lt 2) h02
  have hy1 : angleBr (lt 0) (lt 1 - z • lt 0) ≠ 0 := by
    have := K.angle_zero_ltHat z 1 le_rfl (by omega) (by omega)
    simpa [ltHat] using this
  have hy2 : angleBr (lt 0) (ltHat lt z 2) ≠ 0 := K.angle_zero_ltHat z 2 (by omega) (by omega) (by omega)
  have hl2 : ltHat lt z 2 = lt 2 := by simp [ltHat]
  have hx : squareBr (l 1) ((angleBr (lt 0) (lt 1) / angleBr (lt 0) (lt 2)) • l 1 + l 2) ≠ 0 := by
    have : squareBr (l 1) ((angleBr (lt 0) (lt 1) / angleBr (lt 0) (lt 2)) • l 1 + l 2) = squareBr (l 1) (l 2) := by
      simp [squareBr_eq]; ring
    rw [this]; exact h12
  have hct := channelTerm_two_ppm m (shiftedMom l lt z) (shiftedPol l lt (l 1) (lt 0) j z) (lHat l z) (ltHat lt z)
    ((angleBr (lt 0) (lt 1) / angleBr (lt 0) (lt 2)) • l 1 + l 2) (lt 2) (l 1) (lt 0) rfl rfl hP
    (shiftedPol_pos l lt (l 1) (lt 0) j z 1 (by omega) (by omega))
    (shiftedPol_pos l lt (l 1) (lt 0) j z 2 (by omega) (by omega))
    (by simpa [ltHat] using hy1) (by rw [hl2] at hy2; simpa [ltHat] using hy2) hx
  rw [hct]
  have hR : bgAmplitude (m - (2 - 1)) (collapse (shiftedMom l lt z) 1 2 (momRange (shiftedMom l lt z) 1 2))
      (collapse (shiftedPol l lt (l 1) (lt 0) j z) 1 2
        (epsPlus ((angleBr (lt 0) (lt 1) / angleBr (lt 0) (lt 2)) • l 1 + l 2) (lt 2) (lt 0))) =
      trueAmp (m - 1) (j - 1) (redL l lt) (redLt lt) (l 1) (lt 0) := by
    unfold trueAmp
    rw [show m - (2 - 1) = m - 1 by omega]
    congr 1
    · funext t; exact collapse_pole_two l lt h02 h12 t
    · funext t
      have := collapse_pol_two l lt j (by omega) h02 h12 t
      simpa [show j ≠ 2 by omega] using this
  rw [hR, mdot_momRange_two]
  have hl1 : lHat l z 1 = l 1 := by simp [lHat]
  have hl2' : lHat l z 2 = l 2 := by simp [lHat]
  rw [hl1, hl2', hl2, angleBr_neg_right', neg_sq]
  have hy1' : angleBr (lt 0) (ltHat lt z 1) = angleBr (lt 0) (lt 1) := by
    rw [hzl, angleBr_smul_right']; field_simp
  rw [hy1']
  field_simp

end Lightlike.SpinorHelicity
