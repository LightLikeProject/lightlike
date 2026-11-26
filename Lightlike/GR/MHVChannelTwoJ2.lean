import Lightlike.GR.MHVChannelTwo

/-!
# The channel `[1, 2]` when the second negative gluon is `2`

For the second negative gluon at the position `2` the left factor of the channel `[1, 2]` has the gluons
`1⁺, 2⁻` and the internal leg. With the internal leg negative, the right factor has the single negative gluon `0`
and vanishes; with the internal leg positive, the left factor is the anti-MHV three-point amplitude
`A₃(1⁺, 2⁻, P⁺)`, obtained from `A₃(P⁺, 1⁺, 2⁻)` by cyclic symmetry (Elvang-Huang (3.15)–(3.18)).
-/

noncomputable section

namespace Lightlike.SpinorHelicity

/-- **The left three-point amplitude `A₃(1⁺, 2⁻, P⁺)` of the channel `[1, 2]`.** -/
theorem leftAmp_pmp_two (p ê : ℕ → Fin 4 → ℂ) (a ta b tb lP ltP qs qa : Fin 2 → ℂ) (ε : Fin 4 → ℂ)
    (hp1 : p 1 = nullMom a ta) (hp2 : p 2 = nullMom b tb) (hP : momRange p 1 2 = nullMom lP ltP)
    (he1 : ê 1 = epsPlus a ta qa) (he2 : ê 2 = epsMinus b tb qs) (hε : ε = epsPlus lP (-ltP) qa)
    (hy0 : angleBr qa (-ltP) ≠ 0) (hy1 : angleBr qa ta ≠ 0) (hx2 : squareBr qs b ≠ 0) :
    bgAmplitude 0 (leftMom p 1 2 (-momRange p 1 2)) (leftPol ê 1 2 ε) =
      squareBr lP a * angleBr qa tb ^ 2 / (angleBr qa (-ltP) * angleBr qa ta) := by
  have hc : Conserved3 ![lP, a, b] ![-ltP, ta, tb] := by
    rw [conserved3_iff]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, nullMom_neg_right]
    rw [← hp1, ← hp2, ← hP, momRange_two]; abel
  set O : ℕ → Fin 4 → ℂ := leftMom p 1 2 (-momRange p 1 2) with hO
  set OE : ℕ → Fin 4 → ℂ := leftPol ê 1 2 ε with hOE
  set Q : ℕ → Fin 4 → ℂ := fun t => if t = 0 then O 2 else if t = 1 then O 0 else O 1 with hQ
  set QE : ℕ → Fin 4 → ℂ := fun t => if t = 0 then OE 2 else if t = 1 then OE 0 else OE 1 with hQE
  have hO0 : O 0 = p 1 := by simp [hO, leftMom]
  have hO1 : O 1 = p 2 := by simp [hO, leftMom]
  have hO2 : O 2 = -momRange p 1 2 := by simp [hO, leftMom]
  have hQc : momRange Q 0 2 = 0 := by
    have : momRange Q 0 2 = Q 0 + Q 1 + Q 2 := by simp [momRange, Finset.sum_Ico_succ_top, Finset.sum_range_succ]
    rw [this]
    simp only [hQ, if_true, show (1 : ℕ) ≠ 0 by omega, if_false, show (2 : ℕ) ≠ 0 by omega,
      show (2 : ℕ) ≠ 1 by omega, hO0, hO1, hO2, hP, hp1, hp2]
    rw [← hp1, ← hp2, ← hP, momRange_two]; abel
  have hrot : bgAmplitude 0 (rotLabels Q 2) (rotLabels QE 2) = bgAmplitude 0 Q QE :=
    bgAmplitude_rotLabels 0 Q QE hQc (fun d h1 h2 => by omega)
  have key : ∀ (p p' e e' : ℕ → Fin 4 → ℂ), p 0 = p' 0 → p 1 = p' 1 → e 0 = e' 0 → e 1 = e' 1 → e 2 = e' 2 →
      bgAmplitude 0 p e = bgAmplitude 0 p' e' := by
    intro p p' e e' h0 h1 f0 f1 f2
    rw [bgAmplitude_three, bgAmplitude_three, h0, h1, f0, f1, f2]
  have hrQ : ∀ t, t < 2 → rotLabels Q 2 t = O t := by
    intro t ht
    interval_cases t
    · simp [rotLabels, hQ]
    · simp [rotLabels, hQ]
  have hrE : ∀ t, t ≤ 2 → rotLabels QE 2 t = OE t := by
    intro t ht
    interval_cases t
    · simp [rotLabels, hQE]
    · simp [rotLabels, hQE]
    · simp [rotLabels, hQE]
  have h1 : bgAmplitude 0 O OE = bgAmplitude 0 Q QE := by
    rw [← hrot]
    exact (key _ _ _ _ (hrQ 0 (by omega)) (hrQ 1 (by omega)) (hrE 0 (by omega)) (hrE 1 (by omega))
      (hrE 2 le_rfl)).symm
  rw [h1]
  refine (bgAmplitude_three_ppm_gen ![lP, a, b] ![-ltP, ta, tb] hc qs qa Q QE ?_ ?_ ?_ ?_ ?_ hy0 hy1 hx2).trans ?_
  · simp [hQ, hO2, nullMom_neg_right, hP]
  · simp [hQ, hO0, hp1]
  · simp [hQE, hOE, leftPol, hε]
  · simp [hQE, hOE, leftPol, he1]
  · simp [hQE, hOE, leftPol, he2]
  · simp

/-- **The channel term `[1, 2]` with the negative gluon `2` on the left** is the anti-MHV three-point amplitude times
the right amplitude with the internal gluon negative, once the right amplitude with the internal gluon positive
(a single negative gluon) vanishes. -/
theorem channelTerm_two_pmp (m : ℕ) (p ê : ℕ → Fin 4 → ℂ) (a ta b tb lP ltP qs qa : Fin 2 → ℂ)
    (hp1 : p 1 = nullMom a ta) (hp2 : p 2 = nullMom b tb) (hP : momRange p 1 2 = nullMom lP ltP)
    (he1 : ê 1 = epsPlus a ta qa) (he2 : ê 2 = epsMinus b tb qs)
    (hy0 : angleBr qa (-ltP) ≠ 0) (hy1 : angleBr qa ta ≠ 0) (hx2 : squareBr qs b ≠ 0)
    (hR : bgAmplitude (m - (2 - 1)) (collapse p 1 2 (momRange p 1 2))
      (collapse ê 1 2 (epsPlus lP ltP qa)) = 0) :
    channelTerm m p ê 1 2 lP ltP qs qa =
      squareBr lP a * angleBr qa tb ^ 2 / (angleBr qa (-ltP) * angleBr qa ta) *
        bgAmplitude (m - (2 - 1)) (collapse p 1 2 (momRange p 1 2)) (collapse ê 1 2 (epsMinus lP ltP qs)) := by
  unfold channelTerm
  show bgAmplitude (2 - 1 - 1) _ _ * _ + bgAmplitude (2 - 1 - 1) _ _ * _ = _
  rw [hR, leftAmp_pmp_two p ê a ta b tb lP ltP qs qa _ hp1 hp2 hP he1 he2 rfl hy0 hy1 hx2]
  ring

/-- **The channel `[1, 2]` at its pole for the negative gluons `0` and `2`** (true kinematics in the good gauge):
the anti-MHV three-point amplitude times the `(n−1)`-point amplitude with the internal gluon negative. -/
theorem channelTerm_two_j2 {m : ℕ} {l lt : ℕ → Fin 2 → ℂ} {qs0 qa0 : Fin 2 → ℂ} (K : TrueKin m 2 l lt qs0 qa0)
    (hm : 1 ≤ m) (lP ltP : Fin 2 → ℂ)
    (hP : momRange (shiftedMom l lt (zpole l lt 2)) 1 2 = nullMom lP ltP)
    (hq1 : angleBr (lt 0) ltP ≠ 0) :
    channelTerm m (shiftedMom l lt (zpole l lt 2)) (shiftedPol l lt (l 1) (lt 0) 2 (zpole l lt 2)) 1 2 lP ltP
        (l 1) (lt 0) =
      squareBr lP (l 1) * angleBr (lt 0) (lt 2) ^ 2 /
          (angleBr (lt 0) (-ltP) * angleBr (lt 0) (ltHat lt (zpole l lt 2) 1)) *
        bgAmplitude (m - (2 - 1)) (collapse (shiftedMom l lt (zpole l lt 2)) 1 2
          (momRange (shiftedMom l lt (zpole l lt 2)) 1 2))
          (collapse (shiftedPol l lt (l 1) (lt 0) 2 (zpole l lt 2)) 1 2 (epsMinus lP ltP (l 1))) := by
  set z := zpole l lt 2 with hz
  have hj2 := K.hj
  have hF := falloffData_spinor m 2 K.hj l lt qs0 qa0 K.hq1 K.hq0 K.hone K.hother
  have hconsz : momRange (shiftedMom l lt z) 0 (m + 2) = 0 := by
    have := hF.momRange_eq z 0 (m + 2)
    rw [this, K.hcons]; simp
  have hlt0 : ltHat lt z 0 = lt 0 := by simp [ltHat]
  have hpr : ∀ c e', c < e' → e' ≤ m + 1 → ¬ (c = 0 ∧ e' = m + 1) → ¬ (c = 1 ∧ e' = 2) →
      mdot (momRange (shiftedMom l lt z) c e') (momRange (shiftedMom l lt z) c e') ≠ 0 :=
    fun c e' h1 h2 h3 h4 => K.prop_at_pole le_rfl (by omega) c e' h1 h2 h3 h4
  have hR : bgAmplitude (m - (2 - 1)) (collapse (shiftedMom l lt z) 1 2 (momRange (shiftedMom l lt z) 1 2))
      (collapse (shiftedPol l lt (l 1) (lt 0) 2 z) 1 2 (epsPlus lP ltP (lt 0))) = 0 := by
    refine rightAmp_oneMinus m 2 le_rfl (by omega) (shiftedMom l lt z) (shiftedPol l lt (l 1) (lt 0) 2 z)
      (lHat l z) (ltHat lt z) lP ltP (l 1) (lt 0) _ (fun t _ => rfl) hP hconsz
      (shiftedPol_zero l lt (l 1) (lt 0) 2 z) ?_ rfl hpr ?_ ?_
    · intro t ht1 ht2
      exact shiftedPol_pos l lt (l 1) (lt 0) 2 z t (by omega) (by omega)
    · intro t ht1 ht2
      by_cases h : t = 1
      · simp only [h, if_true]; exact hq1
      · simp only [h, if_false]
        exact K.angle_zero_ltHat z (t + (2 - 1)) (by omega) (by omega) (by omega)
    · intro t ht1 ht2
      rw [hlt0]
      by_cases h : t = 1
      · simp only [h, if_true]; exact hq1
      · simp only [h, if_false]
        exact K.angle_zero_ltHat z (t + (2 - 1)) (by omega) (by omega) (by omega)
  have h1 := channelTerm_two_pmp m (shiftedMom l lt z) (shiftedPol l lt (l 1) (lt 0) 2 z) (l 1) (ltHat lt z 1)
    (l 2) (lt 2) lP ltP (l 1) (lt 0) rfl rfl hP
    (by rw [shiftedPol_pos l lt (l 1) (lt 0) 2 z 1 (by omega) (by omega)]; rfl)
    (by rw [shiftedPol_neg_j l lt (l 1) (lt 0) 2 le_rfl z]; simp [lHat, ltHat])
    (by rw [angleBr_neg_right']; exact neg_ne_zero.2 hq1)
    (K.angle_zero_ltHat z 1 le_rfl (by omega) (by omega)) K.gj hR
  rw [h1]

end Lightlike.SpinorHelicity
