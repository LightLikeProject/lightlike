import Lightlike.GR.MHVVanishing
import Lightlike.GR.MHVThreeGen

/-!
# The Feynman amplitude does not depend on the reference spinors

Changing the reference spinor of the polarization of one gluon shifts it by a multiple of its momentum
(`epsPlus_sub_epsPlus`, `epsMinus_sub_epsMinus`), and the amplitude is invariant under such a shift
(`bgAmplitude_update_add_mom`: multilinearity and the Ward identity). Doing this leg by leg shows that the amplitude
with the polarizations `ε_±(p_t; q_t)` is independent of the references (`bgAmplitude_refs`), for conserved null
momenta, nonvanishing channel propagators and nonvanishing reference brackets.
-/

open Matrix

noncomputable section

namespace Lightlike.SpinorHelicity

/-- The polarizations with the helicity pattern `neg` and the reference spinors `qS` (for negative legs, `|q]`) and `qA`
(for positive legs, `⟨q|`). -/
def polRef (neg : ℕ → Prop) [DecidablePred neg] (l lt qS qA : ℕ → Fin 2 → ℂ) (t : ℕ) : Fin 4 → ℂ :=
  if neg t then epsMinus (l t) (lt t) (qS t) else epsPlus (l t) (lt t) (qA t)

/-- Auxiliary statement `bgCurrent_congr_le` for the true MHV amplitudes. -/
lemma bgCurrent_congr_le (p e e' : ℕ → Fin 4 → ℂ) (N : ℕ) (h : ∀ t ≤ N, e t = e' t) :
    ∀ n a b, b - a ≤ n → a ≤ b → b ≤ N → bgCurrent p e a b = bgCurrent p e' a b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hn hab hbN
    rcases Nat.lt_or_ge a b with hlt | hge
    · rw [bgCurrent_of_lt p e hlt, bgCurrent_of_lt p e' hlt]
      congr 1
      refine bgVertexSum_congr p a b fun c d hac hcd hdb hlen => ?_
      exact ih (d - c) (by omega) c d le_rfl hcd (by omega)
    · have : a = b := le_antisymm hab hge
      subst this
      rw [bgCurrent_self, bgCurrent_self]; exact h a hbN

/-- Auxiliary statement `bgAmplitude_congr_le` for the true MHV amplitudes. -/
lemma bgAmplitude_congr_le (m : ℕ) (p : ℕ → Fin 4 → ℂ) {e e' : ℕ → Fin 4 → ℂ} (h : ∀ t ≤ m + 2, e t = e' t) :
    bgAmplitude m p e = bgAmplitude m p e' := by
  unfold bgAmplitude
  rw [h (m + 2) le_rfl]
  congr 1
  refine bgVertexSum_congr p 0 (m + 1) fun c d hac hcd hdb hlen => ?_
  exact bgCurrent_congr_le p e e' (m + 2) h (d - c) c d le_rfl hcd (by omega)

/-- **Reference independence of the Feynman amplitude.** -/
theorem bgAmplitude_refs (m : ℕ) (neg : ℕ → Prop) [DecidablePred neg] (l lt qS qA qS' qA' : ℕ → Fin 2 → ℂ)
    (p : ℕ → Fin 4 → ℂ) (hp : ∀ t, p t = nullMom (l t) (lt t)) (hcons : momRange p 0 (m + 2) = 0)
    (hprop : ∀ c d, c < d → d ≤ m + 1 → ¬ (c = 0 ∧ d = m + 1) →
      mdot (momRange p c d) (momRange p c d) ≠ 0)
    (hS : ∀ t ≤ m + 2, neg t → squareBr (qS t) (l t) ≠ 0 ∧ squareBr (qS' t) (l t) ≠ 0)
    (hA : ∀ t ≤ m + 2, ¬ neg t → angleBr (qA t) (lt t) ≠ 0 ∧ angleBr (qA' t) (lt t) ≠ 0) :
    bgAmplitude m p (polRef neg l lt qS qA) = bgAmplitude m p (polRef neg l lt qS' qA') := by
  classical
  have hnull : ∀ t ≤ m + 2, mdot (p t) (p t) = 0 := fun t _ => by rw [hp]; exact mdot_nullMom_self _ _
  set e := polRef neg l lt qS qA with he
  set eS : Finset ℕ → ℕ → Fin 4 → ℂ := fun S t => if t ∈ S then polRef neg l lt qS' qA' t else e t with heS
  have htrS : ∀ S : Finset ℕ, ∀ s, mdot (eS S s) (p s) = 0 := fun S s => by
    simp only [heS, he, polRef]
    rw [hp]
    by_cases hs : s ∈ S
    · rw [if_pos hs]
      by_cases hn : neg s
      · rw [if_pos hn, mdot_comm]; exact mdot_epsMinus _ _ _
      · rw [if_neg hn, mdot_comm]; exact mdot_epsPlus _ _ _
    · rw [if_neg hs]
      by_cases hn : neg s
      · rw [if_pos hn, mdot_comm]; exact mdot_epsMinus _ _ _
      · rw [if_neg hn, mdot_comm]; exact mdot_epsPlus _ _ _
  have key : ∀ S : Finset ℕ, (∀ t ∈ S, t ≤ m + 2) → bgAmplitude m p (eS S) = bgAmplitude m p e := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro _; congr 1
    | insert t S ht ih =>
      intro hSS
      have ht' : t ≤ m + 2 := hSS t (Finset.mem_insert_self _ _)
      have ih' := ih fun s hs => hSS s (Finset.mem_insert_of_mem hs)
      have hshift : ∃ c : ℂ, polRef neg l lt qS' qA' t = polRef neg l lt qS qA t + c • p t := by
        by_cases hn : neg t
        · have := epsMinus_sub_epsMinus (l t) (lt t) (qS t) (qS' t) (hS t ht' hn).1 (hS t ht' hn).2
          refine ⟨-((Real.sqrt 2 : ℝ) : ℂ) * squareBr (qS t) (qS' t) / (squareBr (qS t) (l t) * squareBr (qS' t) (l t)), ?_⟩
          rw [hp, polRef, polRef, if_pos hn, if_pos hn, ← this]; abel
        · have := epsPlus_sub_epsPlus (l t) (lt t) (qA t) (qA' t) (hA t ht' hn).1 (hA t ht' hn).2
          refine ⟨-((Real.sqrt 2 : ℝ) : ℂ) * angleBr (qA t) (qA' t) / (angleBr (qA t) (lt t) * angleBr (qA' t) (lt t)), ?_⟩
          rw [hp, polRef, polRef, if_neg hn, if_neg hn, ← this]; abel
      obtain ⟨c, hc⟩ := hshift
      have hnew : eS (insert t S) = Function.update (eS S) t (eS S t + c • p t) := by
        funext s
        by_cases hst : s = t
        · subst hst
          simp only [heS, Finset.mem_insert_self, if_true, Function.update_self, ht, if_false]
          rw [hc]
        · simp only [heS, Finset.mem_insert, hst, false_or, Function.update_of_ne hst]
      rw [hnew, bgAmplitude_update_add_mom m p (eS S) ht' hnull hcons hprop (fun s _ _ => htrS S s), ih']
  have h := key (Finset.range (m + 3)) fun t ht => by have := Finset.mem_range.1 ht; omega
  rw [← h]
  exact (bgAmplitude_congr_le m p (fun t ht => by
    simp only [heS, Finset.mem_range]; rw [if_pos (by omega)])).symm

end Lightlike.SpinorHelicity
