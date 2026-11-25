import Lightlike.GR.MHVChannels

/-!
# The channel terms with `d ≥ 3` vanish

For the channel `[1, d]` with `d ≥ 3` of the recursion for the true amplitudes with negative gluons `0` and `j`, every
term of the channel residue contains a factor with at most one negative gluon, which vanishes by `MHVVanishing.lean`.
-/

open Matrix

noncomputable section

namespace Lightlike.SpinorHelicity

/-- **A channel term with `d ≥ 3` and the second negative gluon on the right (`d < j`) vanishes.** -/
theorem channelTerm_zero_of_lt (m d : ℕ) (hd : 3 ≤ d) (p ê : ℕ → Fin 4 → ℂ)
    (lh lth : ℕ → Fin 2 → ℂ) (lP ltP : Fin 2 → ℂ) (qs qa : Fin 2 → ℂ)
    (hp : ∀ t, 1 ≤ t → t ≤ d → p t = nullMom (lh t) (lth t))
    (hP : momRange p 1 d = nullMom lP ltP)
    (hleg : ∀ t, t ≤ d - 1 → ê (t + 1) = epsPlus (lh (t + 1)) (lth (t + 1)) qa)
    (hprop : ∀ c e', 1 ≤ c → c < e' → e' ≤ d → ¬ (c = 1 ∧ e' = d) →
      mdot (momRange p c e') (momRange p c e') ≠ 0)
    (hqa : ∀ t, t ≤ d → t ≠ d → angleBr qa (if t ≤ d - 1 then lth (t + 1) else -ltP) ≠ 0)
    (hkt : ∀ t, t ≤ d → t ≠ d →
      angleBr (if d ≤ d - 1 then lth (d + 1) else -ltP) (if t ≤ d - 1 then lth (t + 1) else -ltP) ≠ 0) :
    channelTerm m p ê 1 d lP ltP qs qa = 0 := by
  have h1 : d - 1 - 1 = d - 2 := by omega
  unfold channelTerm
  rw [h1]
  have hA : bgAmplitude (d - 2) (leftMom p 1 d (-momRange p 1 d))
      (leftPol ê 1 d (epsMinus lP (-ltP) qs)) = 0 :=
    leftAmp_oneMinus d (by omega) d le_rfl p ê lh lth lP ltP qs qa _ hp hP
      (fun t ht => by simp [show t ≠ d by omega, hleg t ht]) (by simp) hprop hqa hkt
  have hB : bgAmplitude (d - 2) (leftMom p 1 d (-momRange p 1 d))
      (leftPol ê 1 d (epsPlus lP (-ltP) qa)) = 0 :=
    leftAmp_allPlus d p ê lh lth lP ltP qa _ hleg rfl _
  rw [hA, hB]; simp

/-- **A channel term with `d ≥ 3` and the second negative gluon on the left (`j ≤ d`) vanishes.** The negative gluon
`j` is the left leg `k = j - 1`. -/
theorem channelTerm_zero_of_le (m d k : ℕ) (hd : 3 ≤ d) (hk : k ≤ d - 1) (hdm : d ≤ m + 1) (p ê : ℕ → Fin 4 → ℂ)
    (lh lth : ℕ → Fin 2 → ℂ) (lP ltP : Fin 2 → ℂ) (qs qa : Fin 2 → ℂ)
    (hp : ∀ t, t ≤ m + 2 → p t = nullMom (lh t) (lth t))
    (hP : momRange p 1 d = nullMom lP ltP)
    (hcons : momRange p 0 (m + 2) = 0)
    (he0 : ê 0 = epsMinus (lh 0) (lth 0) qs)
    (hleg : ∀ t, t ≤ d - 1 → ê (t + 1) =
      if t = k then epsMinus (lh (t + 1)) (lth (t + 1)) qs else epsPlus (lh (t + 1)) (lth (t + 1)) qa)
    (heR : ∀ t, d + 1 ≤ t → t ≤ m + 2 → ê t = epsPlus (lh t) (lth t) qa)
    (hpropL : ∀ c e', 1 ≤ c → c < e' → e' ≤ d → ¬ (c = 1 ∧ e' = d) →
      mdot (momRange p c e') (momRange p c e') ≠ 0)
    (hqaL : ∀ t, t ≤ d → t ≠ k → angleBr qa (if t ≤ d - 1 then lth (t + 1) else -ltP) ≠ 0)
    (hktL : ∀ t, t ≤ d → t ≠ k →
      angleBr (if k ≤ d - 1 then lth (k + 1) else -ltP) (if t ≤ d - 1 then lth (t + 1) else -ltP) ≠ 0)
    (hother : ∀ c e', c < e' → e' ≤ m + 1 → ¬ (c = 0 ∧ e' = m + 1) → ¬ (c = 1 ∧ e' = d) →
      mdot (momRange p c e') (momRange p c e') ≠ 0)
    (hqaR : ∀ t, 1 ≤ t → t ≤ m - (d - 1) + 2 →
      angleBr qa (if t = 1 then ltP else lth (t + (d - 1))) ≠ 0)
    (hktR : ∀ t, 1 ≤ t → t ≤ m - (d - 1) + 2 →
      angleBr (lth 0) (if t = 1 then ltP else lth (t + (d - 1))) ≠ 0) :
    channelTerm m p ê 1 d lP ltP qs qa = 0 := by
  have h1 : d - 1 - 1 = d - 2 := by omega
  unfold channelTerm
  rw [h1]
  have hA : bgAmplitude (m - (d - 1)) (collapse p 1 d (momRange p 1 d))
      (collapse ê 1 d (epsPlus lP ltP qa)) = 0 :=
    rightAmp_oneMinus m d (by omega) hdm p ê lh lth lP ltP qs qa _ hp hP hcons he0 heR rfl hother hqaR hktR
  have hB : bgAmplitude (d - 2) (leftMom p 1 d (-momRange p 1 d))
      (leftPol ê 1 d (epsPlus lP (-ltP) qa)) = 0 :=
    leftAmp_oneMinus d (by omega) k (by omega) p ê lh lth lP ltP qs qa _ (fun t _ ht' => hp t (by omega))
      hP hleg (by simp [show k ≠ d by omega]) hpropL hqaL hktL
  rw [hA, hB]; simp

end Lightlike.SpinorHelicity
