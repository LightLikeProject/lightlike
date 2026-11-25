import Lightlike.GR.MHVChannels

/-!
# The channels `d ≥ 3` do not contribute to the recursion of the true amplitudes

At the pole of the channel `[1, d]` with `d ≥ 3` one of the two factors of every term of `channelTerm` is an amplitude
with at most one negative gluon, hence zero (`MHVVanishing.lean`, `MHVChannels.lean`).
-/

open Matrix

noncomputable section

namespace Lightlike.SpinorHelicity

/-- Auxiliary statement `angleBr_neg_right'` for the vanishing of the channels. -/
lemma angleBr_neg_right' (a b : Fin 2 → ℂ) : angleBr a (-b) = -angleBr a b := by
  rw [angleBr_eq, angleBr_eq]; simp; ring

/-- Auxiliary statement `angleBr_neg_left'` for the vanishing of the channels. -/
lemma angleBr_neg_left' (a b : Fin 2 → ℂ) : angleBr (-a) b = -angleBr a b := by
  rw [angleBr_eq, angleBr_eq]; simp; ring

/-- The shifted polarization of a positive gluon `t ∉ {0, j}`. -/
lemma shiftedPol_pos (l lt : ℕ → Fin 2 → ℂ) (qs qa : Fin 2 → ℂ) (j : ℕ) (z : ℂ) (t : ℕ) (h0 : t ≠ 0)
    (hj : t ≠ j) :
    shiftedPol l lt qs qa j z t = epsPlus (lHat l z t) (ltHat lt z t) qa := by
  unfold shiftedPol lHat ltHat
  by_cases h1 : t = 1
  · subst h1; simp [hj]
  · simp [h0, h1, hj]

/-- The shifted polarization of the negative gluon `j ≥ 2`. -/
lemma shiftedPol_neg_j (l lt : ℕ → Fin 2 → ℂ) (qs qa : Fin 2 → ℂ) (j : ℕ) (hj2 : 2 ≤ j) (z : ℂ) :
    shiftedPol l lt qs qa j z j = epsMinus (lHat l z j) (ltHat lt z j) qs := by
  unfold shiftedPol lHat ltHat
  simp [show j ≠ 0 by omega, show j ≠ 1 by omega]

/-- The shifted polarization of the negative gluon `0`. -/
lemma shiftedPol_zero (l lt : ℕ → Fin 2 → ℂ) (qs qa : Fin 2 → ℂ) (j : ℕ) (z : ℂ) :
    shiftedPol l lt qs qa j z 0 = epsMinus (lHat l z 0) (ltHat lt z 0) qs := by
  unfold shiftedPol lHat ltHat
  simp

/-- The bracket `⟨0 t̂⟩` of the shifted angle spinors is nonzero for every gluon `t ≠ 0, j` (good gauge). -/
lemma TrueKin.angle_zero_ltHat {m j : ℕ} {l lt : ℕ → Fin 2 → ℂ} {qs0 qa0 : Fin 2 → ℂ}
    (K : TrueKin m j l lt qs0 qa0) (z : ℂ) (s : ℕ) (h1 : 1 ≤ s) (hs : s ≤ m + 2) (hsj : s ≠ j) :
    angleBr (lt 0) (ltHat lt z s) ≠ 0 := by
  unfold ltHat
  by_cases hs1 : s = 1
  · subst hs1
    simp only [if_true, angleBr_sub_smul_right]
    have : angleBr (lt 0) (lt 0) = 0 := by rw [angleBr_eq]; ring
    simpa [this] using K.g1
  · simp only [hs1, if_false]
    exact K.gt s (by omega) hs hsj

/-- **The channels `[1, d]`, `d ≥ 3`, of the recursion for the true amplitudes vanish** (generic pole spinors). -/
theorem channelTerm_zero_far {m j : ℕ} {l lt : ℕ → Fin 2 → ℂ} {qs0 qa0 : Fin 2 → ℂ}
    (K : TrueKin m j l lt qs0 qa0) {d : ℕ} (hd3 : 3 ≤ d) (hdm : d ≤ m + 1) (lP ltP : Fin 2 → ℂ)
    (hP : momRange (shiftedMom l lt (zpole l lt d)) 1 d = nullMom lP ltP)
    (hq1 : angleBr (lt 0) ltP ≠ 0)
    (hA : d < j → ∀ s, 1 ≤ s → s ≤ d → angleBr ltP (ltHat lt (zpole l lt d) s) ≠ 0)
    (hB : j ≤ d → (∀ s, 1 ≤ s → s ≤ d → s ≠ j → angleBr (lt j) (ltHat lt (zpole l lt d) s) ≠ 0) ∧
      angleBr (lt j) ltP ≠ 0) :
    channelTerm m (shiftedMom l lt (zpole l lt d)) (shiftedPol l lt (l 1) (lt 0) j (zpole l lt d)) 1 d
      lP ltP (l 1) (lt 0) = 0 := by
  set z := zpole l lt d with hz
  have hd2 : 2 ≤ d := by omega
  have hdd : d - 1 - 1 = d - 2 := by omega
  have hprop : ∀ c e', 1 ≤ c → c < e' → e' ≤ d → ¬ (c = 1 ∧ e' = d) →
      mdot (momRange (shiftedMom l lt z) c e') (momRange (shiftedMom l lt z) c e') ≠ 0 := fun c e' hc hce he hne =>
    K.prop_at_pole hd2 hdm c e' hce (by omega) (by omega) hne
  have hlh : ∀ t, 1 ≤ t → t ≤ d → shiftedMom l lt z t = nullMom (lHat l z t) (ltHat lt z t) := fun t _ _ => rfl
  unfold channelTerm
  rw [hdd]
  by_cases hjd : d < j
  · -- negative gluon `j` on the right
    have hL1 : bgAmplitude (d - 2) (leftMom (shiftedMom l lt z) 1 d (-momRange (shiftedMom l lt z) 1 d))
        (leftPol (shiftedPol l lt (l 1) (lt 0) j z) 1 d (epsMinus lP (-ltP) (l 1))) = 0 := by
      refine leftAmp_oneMinus d hd2 d le_rfl (shiftedMom l lt z) (shiftedPol l lt (l 1) (lt 0) j z)
        (lHat l z) (ltHat lt z) lP ltP (l 1) (lt 0) _ (fun t ht1 ht2 => hlh t ht1 ht2) hP ?_ (by simp) hprop ?_ ?_
      · intro t ht
        rw [shiftedPol_pos l lt (l 1) (lt 0) j z (t + 1) (by omega) (by omega)]
        simp [show t ≠ d by omega]
      · intro t ht htk
        have ht' : t ≤ d - 1 := by omega
        simp only [ht', if_true]
        exact K.angle_zero_ltHat z (t + 1) (by omega) (by omega) (by omega)
      · intro t ht htk
        have ht' : t ≤ d - 1 := by omega
        have hn : ¬ d ≤ d - 1 := by omega
        simp only [ht', hn, if_true, if_false]
        have := hA hjd (t + 1) (by omega) (by omega)
        rw [angleBr_neg_left']
        exact neg_ne_zero.2 this
    have hL2 : bgAmplitude (d - 2) (leftMom (shiftedMom l lt z) 1 d (-momRange (shiftedMom l lt z) 1 d))
        (leftPol (shiftedPol l lt (l 1) (lt 0) j z) 1 d (epsPlus lP (-ltP) (lt 0))) = 0 := by
      refine leftAmp_allPlus d _ _ (lHat l z) (ltHat lt z) lP ltP (lt 0) _ ?_ rfl _
      intro t ht
      exact shiftedPol_pos l lt (l 1) (lt 0) j z (t + 1) (by omega) (by omega)
    rw [hL1, hL2]; simp
  · -- the negative gluon `j` is on the left
    have hjd' : j ≤ d := by omega
    obtain ⟨hB1, hB2⟩ := hB hjd'
    have hj2 := K.hj
    have hF := falloffData_spinor m j K.hj l lt qs0 qa0 K.hq1 K.hq0 K.hone K.hother
    have hconsz : momRange (shiftedMom l lt z) 0 (m + 2) = 0 := by
      have := hF.momRange_eq z 0 (m + 2)
      rw [this, K.hcons]; simp
    have hlt0 : ltHat lt z 0 = lt 0 := by simp [ltHat]
    have hR1 : bgAmplitude (m - (d - 1)) (collapse (shiftedMom l lt z) 1 d (momRange (shiftedMom l lt z) 1 d))
        (collapse (shiftedPol l lt (l 1) (lt 0) j z) 1 d (epsPlus lP ltP (lt 0))) = 0 := by
      refine rightAmp_oneMinus m d hd2 hdm (shiftedMom l lt z) (shiftedPol l lt (l 1) (lt 0) j z)
        (lHat l z) (ltHat lt z) lP ltP (l 1) (lt 0) _ (fun t _ => rfl) hP hconsz
        (shiftedPol_zero l lt (l 1) (lt 0) j z) ?_ rfl
        (fun c e' h1 h2 h3 h4 => K.prop_at_pole hd2 hdm c e' h1 h2 h3 h4) ?_ ?_
      · intro t ht1 ht2
        exact shiftedPol_pos l lt (l 1) (lt 0) j z t (by omega) (by omega)
      · intro t ht1 ht2
        by_cases h : t = 1
        · simp only [h, if_true]; exact hq1
        · simp only [h, if_false]
          exact K.angle_zero_ltHat z (t + (d - 1)) (by omega) (by omega) (by omega)
      · intro t ht1 ht2
        rw [hlt0]
        by_cases h : t = 1
        · simp only [h, if_true]; exact hq1
        · simp only [h, if_false]
          exact K.angle_zero_ltHat z (t + (d - 1)) (by omega) (by omega) (by omega)
    have hL2 : bgAmplitude (d - 2) (leftMom (shiftedMom l lt z) 1 d (-momRange (shiftedMom l lt z) 1 d))
        (leftPol (shiftedPol l lt (l 1) (lt 0) j z) 1 d (epsPlus lP (-ltP) (lt 0))) = 0 := by
      have hjj : j - 1 + 1 = j := by omega
      refine leftAmp_oneMinus d hd2 (j - 1) (by omega) (shiftedMom l lt z) (shiftedPol l lt (l 1) (lt 0) j z)
        (lHat l z) (ltHat lt z) lP ltP (l 1) (lt 0) _ (fun t ht1 ht2 => hlh t ht1 ht2) hP ?_
        (by simp [show j - 1 ≠ d by omega]) hprop ?_ ?_
      · intro t ht
        by_cases h : t = j - 1
        · subst h
          rw [if_pos rfl, hjj, shiftedPol_neg_j l lt (l 1) (lt 0) j hj2 z]
        · rw [if_neg h, shiftedPol_pos l lt (l 1) (lt 0) j z (t + 1) (by omega) (by omega)]
      · intro t ht htk
        by_cases h : t ≤ d - 1
        · simp only [h, if_true]
          exact K.angle_zero_ltHat z (t + 1) (by omega) (by omega) (by omega)
        · simp only [h, if_false, angleBr_neg_right']
          exact neg_ne_zero.2 hq1
      · intro t ht htk
        have hk1 : j - 1 ≤ d - 1 := by omega
        simp only [hk1, if_true, hjj]
        have hl : ltHat lt z j = lt j := by simp [ltHat, show j ≠ 1 by omega]
        rw [hl]
        by_cases h : t ≤ d - 1
        · simp only [h, if_true]
          exact hB1 (t + 1) (by omega) (by omega) (by omega)
        · simp only [h, if_false, angleBr_neg_right']
          exact neg_ne_zero.2 hB2
    rw [hR1, hL2]; simp

end Lightlike.SpinorHelicity
