import Lightlike.GR.MHVBase
import Lightlike.GR.FeynmanWard

/-!
# Adjacent negative gluons by cyclic symmetry

The true amplitude with the negative gluons `0` and `1` is, after the cyclic relabelling `t ↦ t + 1`, the true
amplitude with negative gluons `0` and `m + 2` (Elvang-Huang p. 25, property 1).
-/

noncomputable section

namespace Lightlike.SpinorHelicity

/-- **Cyclic symmetry of the true amplitude** with adjacent negative gluons `0, 1`: relabelling by `t ↦ t + 1` gives
the negative gluons `0` and `m + 2`. -/
theorem trueAmp_rot (m : ℕ) (l lt : ℕ → Fin 2 → ℂ) (qs qa : Fin 2 → ℂ)
    (hcons : momRange (fun t => nullMom (l t) (lt t)) 0 (m + 2) = 0)
    (hprop : ∀ d, 1 ≤ d → d ≤ m → mdot (momRange (fun t => nullMom (l t) (lt t)) 0 d)
      (momRange (fun t => nullMom (l t) (lt t)) 0 d) ≠ 0) :
    trueAmp m 1 l lt qs qa = trueAmp m (m + 2) (rotLabels l (m + 2)) (rotLabels lt (m + 2)) qs qa := by
  unfold trueAmp
  rw [← bgAmplitude_rotLabels m _ _ hcons hprop]
  congr 1
  · funext t
    simp only [rotLabels]
    split_ifs <;> rfl
  · funext t
    simp only [rotLabels, polRef]
    by_cases h1 : t < m + 2
    · by_cases h0 : t = 0
      · subst h0; simp
      · simp [h1, h0, show t + 1 ≠ 0 by omega, show t + 1 ≠ 1 by omega, show t ≠ m + 2 by omega]
    · by_cases h2 : t = m + 2
      · subst h2; simp
      · simp [h1, h2, show t ≠ 0 by omega, show t ≠ 1 by omega]

/-- **Cyclic symmetry of the Parke-Taylor amplitude** for the relabelling `t ↦ t + 1`. -/
theorem ptN_rot (m : ℕ) (lt : ℕ → Fin 2 → ℂ) :
    ptN m 1 lt = ptN m (m + 2) (rotLabels lt (m + 2)) := by
  unfold ptN
  have hs : (fun i : Fin (m + 3) => rotLabels lt (m + 2) i) = (fun i : Fin (m + 3) => lt i) ∘ finRotate (m + 3) := by
    funext i
    simp only [Function.comp_apply, rotLabels]
    by_cases h : (i : ℕ) < m + 2
    · rw [if_pos h]
      congr 1
      rw [coe_finRotate_of_ne_last (by rw [Ne, Fin.ext_iff]; simp; omega)]
    · have : i = Fin.last (m + 2) := Fin.ext (by simp; omega)
      subst this
      simp [rotLabels]
  rw [hs, parkeTaylor_rotate]
  simp only [rotLabels, show (0 : ℕ) < m + 2 by omega, if_true, show m + 2 = m + 2 from rfl, lt_irrefl, if_false,
    if_true]
  unfold parkeTaylor
  have : angleBr (lt 1) (lt 0) ^ 4 = angleBr (lt 0) (lt 1) ^ 4 := by
    rw [angleBr_antisymm (lt 1) (lt 0)]; ring
  rw [zero_add, this]

end Lightlike.SpinorHelicity
