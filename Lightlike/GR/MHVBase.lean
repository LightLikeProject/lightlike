import Lightlike.GR.MHVRefs
import Lightlike.GR.MHVTrue
import Lightlike.GR.ColourOrdered

/-!
# The three-point case of the true amplitudes against Parke-Taylor

The base of the induction for the true MHV amplitudes: for three gluons the Feynman amplitude with negative gluons
`0` and `j ∈ {1, 2}` is the Parke-Taylor amplitude `⟨0j⟩⁴/(⟨01⟩⟨12⟩⟨20⟩)` for any generic references.
-/

noncomputable section

namespace Lightlike.SpinorHelicity

/-- **The true amplitude** with negative gluons `0` and `j`, spinors `l`, `lt` and references `qs`, `qa`. -/
def trueAmp (m j : ℕ) (l lt : ℕ → Fin 2 → ℂ) (qs qa : Fin 2 → ℂ) : ℂ :=
  bgAmplitude m (fun t => nullMom (l t) (lt t))
    (polRef (fun t => t = 0 ∨ t = j) l lt (fun _ => qs) (fun _ => qa))

/-- **The Parke-Taylor amplitude** of `m + 3` gluons with negative gluons `0` and `j`, from the angle spinors. -/
def ptN (m j : ℕ) (lt : ℕ → Fin 2 → ℂ) : ℂ := parkeTaylor (lt 0) (lt j) (fun i : Fin (m + 3) => lt i)

/-- The Parke-Taylor denominator of three gluons. -/
lemma cycDen_threeLegs (s : Fin 3 → Fin 2 → ℂ) :
    cycDen s = angleBr (s 0) (s 1) * angleBr (s 1) (s 2) * angleBr (s 2) (s 0) := by
  have h0 : finRotate 3 0 = 1 := by decide
  have h1 : finRotate 3 1 = 2 := by decide
  have h2 : finRotate 3 2 = 0 := by decide
  simp [cycDen, Fin.prod_univ_three, h0, h1, h2]

/-- **The three-point true amplitude is the Parke-Taylor amplitude** (negative gluons `0` and `j ∈ {1, 2}`). -/
theorem trueAmp_zero (j : ℕ) (hj : j = 1 ∨ j = 2) (l lt : ℕ → Fin 2 → ℂ) (qs qa : Fin 2 → ℂ)
    (hcons : momRange (fun t => nullMom (l t) (lt t)) 0 2 = 0)
    (a01 : angleBr (lt 0) (lt 1) ≠ 0) (a12 : angleBr (lt 1) (lt 2) ≠ 0) (a20 : angleBr (lt 2) (lt 0) ≠ 0)
    (hS : ∀ t ≤ 2, (t = 0 ∨ t = j) → squareBr qs (l t) ≠ 0)
    (hA : ∀ t ≤ 2, ¬ (t = 0 ∨ t = j) → angleBr qa (lt t) ≠ 0) :
    trueAmp 0 j l lt qs qa = ptN 0 j lt := by
  have hc : Conserved3 (fun i : Fin 3 => l i) (fun i : Fin 3 => lt i) := by
    rw [conserved3_iff]
    have : momRange (fun t => nullMom (l t) (lt t)) 0 2 =
        nullMom (l 0) (lt 0) + nullMom (l 1) (lt 1) + nullMom (l 2) (lt 2) := by
      simp [momRange, Finset.sum_range_succ]
    rw [this] at hcons
    simpa using hcons
  have a02 : angleBr (lt 0) (lt 2) ≠ 0 := by
    intro h; apply a20; rw [angleBr_antisymm, h]; simp
  have a10 : angleBr (lt 1) (lt 0) ≠ 0 := by
    intro h; apply a01; rw [angleBr_antisymm, h]; simp
  unfold trueAmp ptN parkeTaylor
  rw [cycDen_threeLegs]
  rcases hj with rfl | rfl
  · rw [bgAmplitude_three_mmp (fun i : Fin 3 => l i) (fun i : Fin 3 => lt i) hc qs qa _ _ rfl rfl
      (by simp [polRef]) (by simp [polRef]) (by simp [polRef])
      (hS 0 (by omega) (Or.inl rfl)) (hS 1 (by omega) (Or.inr rfl)) (hA 2 le_rfl (by omega)) a12 a20]
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one]
    field_simp
  · rw [bgAmplitude_three_mpm (fun i : Fin 3 => l i) (fun i : Fin 3 => lt i) hc qs qa _ _ rfl rfl rfl
      (by simp [polRef]) (by simp [polRef]) (by simp [polRef])
      (hS 2 le_rfl (Or.inr rfl)) (hS 0 (by omega) (Or.inl rfl)) (hA 1 (by omega) (by omega)) a01 a12]
    simp only [Fin.isValue, Fin.val_zero, Fin.val_two]
    have h4 : angleBr (lt 0) (lt 2) = -angleBr (lt 2) (lt 0) := angleBr_antisymm _ _
    rw [h4]
    field_simp

end Lightlike.SpinorHelicity
