import Lightlike.GR.MHVRecursion

/-!
# The factors of a channel term: vanishing of the left and right amplitudes

The left amplitude of the channel `[1, d]` has the gluons `1, …, d` and the internal gluon `−P`; the right amplitude has
`0`, the internal gluon `P` at position `1` and the gluons `d+1, …`. With the polarizations of the good gauge both are
amplitudes of the form `polRef`, so the vanishing theorems of `MHVVanishing.lean` apply.
-/

open Matrix

noncomputable section

namespace Lightlike.SpinorHelicity

/-- **The left amplitude of a channel with exactly one negative gluon vanishes.** The negative gluon is the leg `k`
(`k = d` is the internal gluon). -/
theorem leftAmp_oneMinus (d : ℕ) (hd : 2 ≤ d) (k : ℕ) (hk : k ≤ d) (p ê : ℕ → Fin 4 → ℂ)
    (lh lth : ℕ → Fin 2 → ℂ) (lP ltP : Fin 2 → ℂ) (qs qa : Fin 2 → ℂ) (ε : Fin 4 → ℂ)
    (hp : ∀ t, 1 ≤ t → t ≤ d → p t = nullMom (lh t) (lth t))
    (hP : momRange p 1 d = nullMom lP ltP)
    (hleg : ∀ t, t ≤ d - 1 → ê (t + 1) =
      if t = k then epsMinus (lh (t + 1)) (lth (t + 1)) qs else epsPlus (lh (t + 1)) (lth (t + 1)) qa)
    (hε : ε = if k = d then epsMinus lP (-ltP) qs else epsPlus lP (-ltP) qa)
    (hprop : ∀ c e', 1 ≤ c → c < e' → e' ≤ d → ¬ (c = 1 ∧ e' = d) →
      mdot (momRange p c e') (momRange p c e') ≠ 0)
    (hqa : ∀ t, t ≤ d → t ≠ k → angleBr qa (if t ≤ d - 1 then lth (t + 1) else -ltP) ≠ 0)
    (hkt : ∀ t, t ≤ d → t ≠ k →
      angleBr (if k ≤ d - 1 then lth (k + 1) else -ltP) (if t ≤ d - 1 then lth (t + 1) else -ltP) ≠ 0) :
    bgAmplitude (d - 2) (leftMom p 1 d (-momRange p 1 d)) (leftPol ê 1 d ε) = 0 := by
  have hd2 : d - 2 + 2 = d := by omega
  have hPP : momRange p 1 d = nullMom lP ltP := hP
  refine bgAmplitude_oneMinus (d - 2) k (by omega) (fun t => if t ≤ d - 1 then lh (t + 1) else lP)
    (fun t => if t ≤ d - 1 then lth (t + 1) else -ltP) qs qa _ _ ?_ ?_ ?_ ?_ ?_ ?_
  · intro t ht
    rw [hd2] at ht
    by_cases h1 : t ≤ d - 1
    · simp only [leftMom, show t ≤ d - 1 by omega, if_true, h1]
      rw [hp (t + 1) (by omega) (by omega)]
    · have : t = d := by omega
      subst this
      simp only [leftMom, show ¬ (t ≤ t - 1) by omega, if_false, h1, hPP]
      rw [nullMom_neg_right]
  · intro t ht
    rw [hd2] at ht
    by_cases h1 : t ≤ d - 1
    · simp only [leftPol, h1, if_true]
      rw [hleg t h1]
    · have : t = d := by omega
      subst this
      simp only [leftPol, h1, if_false, hε]
      by_cases hkd : k = t
      · subst hkd; simp
      · simp [hkd, Ne.symm hkd]
  · rw [show d - 2 + 2 = d by omega]
    generalize hPdef : momRange p 1 d = P
    show ∑ t ∈ Finset.Ico 0 (d + 1), leftMom p 1 d (-P) t = 0
    rw [Finset.sum_Ico_succ_top (by omega)]
    have h1 : ∑ t ∈ Finset.Ico 0 d, leftMom p 1 d (-P) t = ∑ t ∈ Finset.Ico 0 d, p (t + 1) :=
      Finset.sum_congr rfl fun t ht => by
        simp [leftMom, show t ≤ d - 1 by have := Finset.mem_Ico.1 ht; omega]
    rw [h1, Finset.sum_Ico_add' (fun t => p t) 0 d 1, ← hPdef]
    simp [leftMom, show ¬ (d ≤ d - 1) by omega, momRange]
  · intro c e' hce he' hne
    have hm : momRange (leftMom p 1 d (-momRange p 1 d)) c e' = momRange p (c + 1) (e' + 1) := by
      rw [← momRange_shift]
      exact momRange_congr fun t _ ht => by simp [leftMom, show t ≤ d - 1 by omega]
    rw [hm]
    exact hprop _ _ (by omega) (by omega) (by omega) (by omega)
  · intro t ht htk
    rw [show d - 2 + 2 = d by omega] at ht
    exact hqa t ht htk
  · intro t ht htk
    rw [show d - 2 + 2 = d by omega] at ht
    exact hkt t ht htk

/-- **The left amplitude of a channel with all positive gluons vanishes.** -/
theorem leftAmp_allPlus (d : ℕ) (p ê : ℕ → Fin 4 → ℂ) (lh lth : ℕ → Fin 2 → ℂ) (lP ltP : Fin 2 → ℂ)
    (qa : Fin 2 → ℂ) (ε : Fin 4 → ℂ)
    (hleg : ∀ t, t ≤ d - 1 → ê (t + 1) = epsPlus (lh (t + 1)) (lth (t + 1)) qa)
    (hε : ε = epsPlus lP (-ltP) qa) (P' : Fin 4 → ℂ) :
    bgAmplitude (d - 2) (leftMom p 1 d P') (leftPol ê 1 d ε) = 0 := by
  refine bgAmplitude_eq_zero_of_angle (d - 2) _ _ qa fun t ht => ?_
  by_cases h1 : t ≤ d - 1
  · simp only [leftPol, h1, if_true]
    rw [hleg t h1]; exact inV_epsPlus _ _ _
  · simp only [leftPol, h1, if_false]
    rw [hε]; exact inV_epsPlus _ _ _

/-- **The right amplitude of a channel whose only negative gluon is the leg `0` vanishes.** -/
theorem rightAmp_oneMinus (m d : ℕ) (hd : 2 ≤ d) (hdm : d ≤ m + 1) (p ê : ℕ → Fin 4 → ℂ)
    (lh lth : ℕ → Fin 2 → ℂ) (lP ltP : Fin 2 → ℂ) (qs qa : Fin 2 → ℂ) (ε : Fin 4 → ℂ)
    (hp : ∀ t, t ≤ m + 2 → p t = nullMom (lh t) (lth t)) (hP : momRange p 1 d = nullMom lP ltP)
    (hcons : momRange p 0 (m + 2) = 0)
    (he0 : ê 0 = epsMinus (lh 0) (lth 0) qs)
    (heR : ∀ t, d + 1 ≤ t → t ≤ m + 2 → ê t = epsPlus (lh t) (lth t) qa)
    (hε : ε = epsPlus lP ltP qa)
    (hother : ∀ c e', c < e' → e' ≤ m + 1 → ¬ (c = 0 ∧ e' = m + 1) → ¬ (c = 1 ∧ e' = d) →
      mdot (momRange p c e') (momRange p c e') ≠ 0)
    (hqa : ∀ t, 1 ≤ t → t ≤ m - (d - 1) + 2 →
      angleBr qa (if t = 1 then ltP else lth (t + (d - 1))) ≠ 0)
    (hkt : ∀ t, 1 ≤ t → t ≤ m - (d - 1) + 2 →
      angleBr (lth 0) (if t = 1 then ltP else lth (t + (d - 1))) ≠ 0) :
    bgAmplitude (m - (d - 1)) (collapse p 1 d (momRange p 1 d)) (collapse ê 1 d ε) = 0 := by
  refine bgAmplitude_oneMinus (m - (d - 1)) 0 (by omega)
    (fun t => if t = 0 then lh 0 else if t = 1 then lP else lh (t + (d - 1)))
    (fun t => if t = 0 then lth 0 else if t = 1 then ltP else lth (t + (d - 1))) qs qa _ _ ?_ ?_ ?_ ?_ ?_ ?_
  · intro t ht
    rcases Nat.lt_trichotomy t 1 with h | h | h
    · have : t = 0 := by omega
      subst this
      simp [collapse_of_lt _ _ (show 0 < 1 by omega), hp 0 (by omega)]
    · subst h; simp [hP]
    · rw [collapse_of_gt _ _ h, hp _ (by omega)]
      simp [show t ≠ 0 by omega, show t ≠ 1 by omega]
  · intro t ht
    rcases Nat.lt_trichotomy t 1 with h | h | h
    · have : t = 0 := by omega
      subst this
      simp [collapse_of_lt _ _ (show 0 < 1 by omega), he0]
    · subst h; simp [hε]
    · rw [collapse_of_gt _ _ h, heR _ (by omega) (by omega)]
      simp [show t ≠ 0 by omega, show t ≠ 1 by omega]
  · rw [momRange_collapse p (show 1 ≤ d by omega) (by omega) (by omega)]
    rw [show m - (d - 1) + 2 + (d - 1) = m + 2 by omega]; exact hcons
  · intro c e' hce he' hne
    exact mdot_momRange_collapse_ne m p (show 1 < d by omega) hdm (by omega) hother c e' hce
      (by omega) (by omega)
  · intro t ht htk
    have h1 : 1 ≤ t := by omega
    simpa [show t ≠ 0 by omega] using hqa t h1 ht
  · intro t ht htk
    have h1 : 1 ≤ t := by omega
    simpa [show t ≠ 0 by omega] using hkt t h1 ht

/-- At the pole `z_d` of the channel `[1, d]` all the other channel propagators are nonzero. -/
theorem TrueKin.prop_at_pole {m j : ℕ} {l lt : ℕ → Fin 2 → ℂ} {qs0 qa0 : Fin 2 → ℂ} (K : TrueKin m j l lt qs0 qa0)
    {d : ℕ} (hd : 2 ≤ d) (hdm : d ≤ m + 1) (c e' : ℕ) (hce : c < e') (he' : e' ≤ m + 1)
    (hne : ¬ (c = 0 ∧ e' = m + 1)) (hne2 : ¬ (c = 1 ∧ e' = d)) :
    mdot (momRange (shiftedMom l lt (zpole l lt d)) c e') (momRange (shiftedMom l lt (zpole l lt d)) c e') ≠ 0 := by
  have hF := falloffData_spinor m j K.hj l lt qs0 qa0 K.hq1 K.hq0 K.hone K.hother
  by_cases hc : c = 1
  · subst hc
    have hb : 2 ≤ e' := hce
    have hed : e' ≠ d := fun h => hne2 ⟨rfl, h⟩
    rw [hF.mdot_one hb]
    intro h0
    apply hed
    refine K.hinj e' d hb he' hd hdm ?_
    have hs : (-2 : ℂ) * mdot (momRange (shiftedMom l lt 0) 1 e') (nullMom (l 1) (lt 0)) ≠ 0 :=
      mul_ne_zero (by norm_num) (K.hone e' hb he')
    have hz : zpole l lt e' = -mdot (momRange (shiftedMom l lt 0) 1 e') (momRange (shiftedMom l lt 0) 1 e') /
        (-2 * mdot (momRange (shiftedMom l lt 0) 1 e') (nullMom (l 1) (lt 0))) := rfl
    rw [hz, div_eq_iff hs]
    linear_combination (-1 : ℂ) * h0
  · rw [hF.momRange_const hce hc]
    exact K.hother c e' hce he' hc hne

end Lightlike.SpinorHelicity
