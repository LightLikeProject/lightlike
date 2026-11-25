import Lightlike.GR.MHVGood
import Lightlike.GR.MHVStepFar
import Lightlike.GR.MHVRotate

/-!
# The true MHV amplitudes are the Parke-Taylor amplitudes

The induction on the number of gluons: the true colour-ordered Feynman amplitude with negative gluons `0` and `j`
is the Parke-Taylor amplitude `⟨0j⟩⁴/(⟨01⟩ ⋯ ⟨n0⟩)` for kinematics in a class `G` closed under the reduction of the
channel `[1, 2]` (Elvang-Huang (3.17)–(3.22), (2.80)) and under the cyclic relabelling for adjacent negative gluons.
The class records the nonvanishing of the brackets and propagators that the recursion divides by.
-/

noncomputable section

namespace Lightlike.SpinorHelicity

/-- The data of the far step at the level `m + 1`, `2 ≤ j`: the genericity of the kinematics for the recursion
(spinor brackets, propagators, pole spinors of the channels `[1, d]`, `d ≥ 3`). -/
structure FarData (m j : ℕ) (l lt : ℕ → Fin 2 → ℂ) : Prop where
  /-- Generic references for the falloff and the recursion. -/
  K : ∃ qs0 qa0, TrueKin (m + 1) j l lt qs0 qa0
  /-- `⟨02⟩ ≠ 0`. -/
  h02 : angleBr (lt 0) (lt 2) ≠ 0
  /-- `[12] ≠ 0`. -/
  h12 : squareBr (l 1) (l 2) ≠ 0
  /-- All the angle brackets are nonzero (the Parke-Taylor denominators). -/
  hg : GenericAngles (fun i : Fin (m + 4) => lt i)
  /-- Pole spinors of the channels `[1, d]`, `d ≥ 3`, with the brackets that make their terms vanish. -/
  poles : ∃ lP ltP : ℕ → Fin 2 → ℂ,
    (∀ d, 3 ≤ d → d ≤ m + 2 →
      momRange (shiftedMom l lt (zpole l lt d)) 1 d = nullMom (lP d) (ltP d)) ∧
    (∀ d, 3 ≤ d → d ≤ m + 2 → angleBr (lt 0) (ltP d) ≠ 0) ∧
    (∀ d, 3 ≤ d → d ≤ m + 2 → squareBr (l 1) (lP d) ≠ 0) ∧
    (∀ d, 3 ≤ d → d ≤ m + 2 → d < j → ∀ s, 1 ≤ s → s ≤ d →
      angleBr (ltP d) (ltHat lt (zpole l lt d) s) ≠ 0) ∧
    (∀ d, 3 ≤ d → d ≤ m + 2 → j ≤ d →
      (∀ s, 1 ≤ s → s ≤ d → s ≠ j → angleBr (lt j) (ltHat lt (zpole l lt d) s) ≠ 0) ∧
        angleBr (lt j) (ltP d) ≠ 0)

/-- The data of the cyclic step at the level `m` for adjacent negative gluons: momentum conservation and the
nonvanishing of the cyclic propagators. -/
structure RotData (m : ℕ) (l lt : ℕ → Fin 2 → ℂ) : Prop where
  /-- Momentum conservation. -/
  hcons : momRange (fun t => nullMom (l t) (lt t)) 0 (m + 2) = 0
  /-- The propagators `P_{0..d}²` do not vanish. -/
  hprop : ∀ d, 1 ≤ d → d ≤ m → mdot (momRange (fun t => nullMom (l t) (lt t)) 0 d)
    (momRange (fun t => nullMom (l t) (lt t)) 0 d) ≠ 0

/-- **A class of kinematics closed under the reductions of the induction**: the position of the second negative
gluon, the three-point data, the far step, and the cyclic step. -/
def ClosedClass (G : ℕ → ℕ → (ℕ → Fin 2 → ℂ) → (ℕ → Fin 2 → ℂ) → Prop) : Prop :=
  (∀ m j l lt, G m j l lt → 1 ≤ j ∧ j ≤ m + 2) ∧
  (∀ j l lt, G 0 j l lt → momRange (fun t => nullMom (l t) (lt t)) 0 2 = 0 ∧ angleBr (lt 0) (lt 1) ≠ 0 ∧
    angleBr (lt 1) (lt 2) ≠ 0 ∧ angleBr (lt 2) (lt 0) ≠ 0) ∧
  (∀ m j l lt, G (m + 1) j l lt → 2 ≤ j → FarData m j l lt ∧ G m (j - 1) (redL l lt) (redLt lt)) ∧
  (∀ m l lt, G (m + 1) 1 l lt → RotData (m + 1) l lt ∧ GenericAngles (fun i : Fin (m + 4) => lt i) ∧
    G (m + 1) (m + 3) (rotLabels l (m + 3)) (rotLabels lt (m + 3)))

/-- **Reference independence in the good gauge**: the true amplitude with generic references is the one with the
good-gauge references `|q] = |1]`, `⟨q'| = ⟨0|`. -/
lemma trueAmp_refs_good (m j : ℕ) (hj : 2 ≤ j) (l lt : ℕ → Fin 2 → ℂ) (qs0 qa0 : Fin 2 → ℂ)
    (K : TrueKin (m + 1) j l lt qs0 qa0) (qs qa : Fin 2 → ℂ)
    (hS : ∀ t ≤ m + 3, (t = 0 ∨ t = j) → squareBr qs (l t) ≠ 0)
    (hA : ∀ t ≤ m + 3, ¬ (t = 0 ∨ t = j) → angleBr qa (lt t) ≠ 0) :
    trueAmp (m + 1) j l lt qs qa = trueAmp (m + 1) j l lt (l 1) (lt 0) := by
  have hcons : momRange (fun t => nullMom (l t) (lt t)) 0 (m + 1 + 2) = 0 := by
    have := K.hcons; rwa [shiftedMom_zero] at this
  unfold trueAmp
  refine bgAmplitude_refs (m + 1) (fun t => t = 0 ∨ t = j) l lt (fun _ => qs) (fun _ => qa) (fun _ => l 1)
    (fun _ => lt 0) _ (fun t => rfl) hcons ?_ ?_ ?_
  · intro c d hcd hd hne
    have h0 := shiftedMom_zero l lt
    by_cases hc1 : c = 1
    · subst hc1
      have := K.hP0 d (by omega) (by omega)
      rwa [h0] at this
    · have := K.hother c d hcd (by omega) hc1 hne
      rwa [h0] at this
  · intro t ht hneg
    rcases hneg with h0 | hjt
    · subst h0; exact ⟨hS 0 (by omega) (Or.inl rfl), K.g0⟩
    · subst hjt; exact ⟨hS t (by omega) (Or.inr rfl), K.gj⟩
  · intro t ht hneg
    have h1 : t ≠ 0 := fun h => hneg (Or.inl h)
    have h2 : t ≠ j := fun h => hneg (Or.inr h)
    refine ⟨hA t (by omega) hneg, ?_⟩
    by_cases h3 : t = 1
    · subst h3; exact K.g1
    · exact K.gt t (by omega) (by omega) h2

/-- The references `(|1], ⟨0|)` are generic for the reduced kinematics. -/
lemma refs_reduced (m j : ℕ) (hj : 2 ≤ j) (l lt : ℕ → Fin 2 → ℂ) (qs0 qa0 : Fin 2 → ℂ)
    (K : TrueKin (m + 1) j l lt qs0 qa0) (h12 : squareBr (l 1) (l 2) ≠ 0) :
    (∀ t ≤ m + 2, (t = 0 ∨ t = j - 1) → squareBr (l 1) (redL l lt t) ≠ 0) ∧
    (∀ t ≤ m + 2, ¬ (t = 0 ∨ t = j - 1) → angleBr (lt 0) (redLt lt t) ≠ 0) := by
  constructor
  · intro t ht hneg
    rcases hneg with h0 | hjt
    · subst h0
      have : squareBr (l 1) (redL l lt 0) = squareBr (l 1) (l 0) := by
        simp [redL, squareBr_eq]; ring
      rw [this]; exact K.g0
    · by_cases h2 : j = 2
      · subst h2
        have : t = 1 := by omega
        subst this
        have : squareBr (l 1) (redL l lt 1) = squareBr (l 1) (l 2) := by
          simp [redL, squareBr_eq]; ring
        rw [this]; exact h12
      · have h1 : t ≠ 0 := by omega
        have h1' : t ≠ 1 := by omega
        have e : redL l lt t = l j := by simp [redL, h1, h1']; congr 1; omega
        rw [e]; exact K.gj
  · intro t ht hneg
    have h1 : t ≠ 0 := fun h => hneg (Or.inl h)
    have h2 : t ≠ j - 1 := fun h => hneg (Or.inr h)
    have e : redLt lt t = lt (t + 1) := by simp [redLt, h1]
    rw [e]
    exact K.gt (t + 1) (by omega) (by omega) (by omega)

/-- **The far step of the induction**: the induction hypothesis for the reduced kinematics gives the
Parke-Taylor amplitude for the true amplitude with negative gluons `0` and `j ≥ 2`. -/
theorem trueAmp_far (m j : ℕ) (hj : 2 ≤ j) (l lt : ℕ → Fin 2 → ℂ) (F : FarData m j l lt)
    (IH : ∀ qs qa : Fin 2 → ℂ, (∀ t ≤ m + 2, (t = 0 ∨ t = j - 1) → squareBr qs (redL l lt t) ≠ 0) →
      (∀ t ≤ m + 2, ¬ (t = 0 ∨ t = j - 1) → angleBr qa (redLt lt t) ≠ 0) →
      trueAmp m (j - 1) (redL l lt) (redLt lt) qs qa = ptN m (j - 1) (redLt lt))
    (qs qa : Fin 2 → ℂ) (hS : ∀ t ≤ m + 3, (t = 0 ∨ t = j) → squareBr qs (l t) ≠ 0)
    (hA : ∀ t ≤ m + 3, ¬ (t = 0 ∨ t = j) → angleBr qa (lt t) ≠ 0) :
    trueAmp (m + 1) j l lt qs qa = ptN (m + 1) j lt := by
  obtain ⟨qs0, qa0, K⟩ := F.K
  obtain ⟨lP, ltP, hP, hq1, hq2, hA', hB⟩ := F.poles
  obtain ⟨hR1, hR2⟩ := refs_reduced m j hj l lt qs0 qa0 K F.h12
  have hIH := IH (l 1) (lt 0) hR1 hR2
  have hd2 : (1 / mdot (momRange (shiftedMom l lt 0) 1 2) (momRange (shiftedMom l lt 0) 1 2)) *
        channelTerm (m + 1) (shiftedMom l lt (zpole l lt 2))
          (shiftedPol l lt (l 1) (lt 0) j (zpole l lt 2)) 1 2
          ((angleBr (lt 0) (lt 1) / angleBr (lt 0) (lt 2)) • l 1 + l 2) (lt 2) (l 1) (lt 0) =
      (squareBr (l 1) (l 2) / (angleBr (lt 0) (lt 1) / angleBr (lt 0) (lt 2))) /
          (angleBr (lt 1) (lt 2) * squareBr (l 1) (l 2)) *
        trueAmp m (j - 1) (redL l lt) (redLt lt) (l 1) (lt 0) := by
    by_cases h2 : j = 2
    · subst h2
      simpa using step_two K (by omega) F.h02 K.g1
    · simpa using step_far K (by omega) (by omega) F.h02 F.h12
  rw [trueAmp_refs_good m j hj l lt qs0 qa0 K qs qa hS hA]
  exact trueAmp_good m j hj l lt qs0 qa0 K F.h02 F.h12 F.hg lP ltP hP hq1 hq2 hA' hB hd2 hIH

/-- **The true MHV amplitudes are the Parke-Taylor amplitudes** for kinematics in a class closed under the
reductions of the induction: for every such class `G`, the Feynman amplitude with the negative gluons `0` and `j`
and generic references equals `⟨0j⟩⁴/(⟨01⟩ ⋯ ⟨n0⟩)`. -/
theorem trueAmp_eq_ptN (G : ℕ → ℕ → (ℕ → Fin 2 → ℂ) → (ℕ → Fin 2 → ℂ) → Prop) (hG : ClosedClass G) :
    ∀ (m j : ℕ) (l lt : ℕ → Fin 2 → ℂ) (qs qa : Fin 2 → ℂ), G m j l lt →
      (∀ t ≤ m + 2, (t = 0 ∨ t = j) → squareBr qs (l t) ≠ 0) →
      (∀ t ≤ m + 2, ¬ (t = 0 ∨ t = j) → angleBr qa (lt t) ≠ 0) →
      trueAmp m j l lt qs qa = ptN m j lt := by
  intro m
  induction m with
  | zero =>
    intro j l lt qs qa hGj hS hA
    have hr := hG.1 0 j l lt hGj
    obtain ⟨hc, a01, a12, a20⟩ := hG.2.1 j l lt hGj
    exact trueAmp_zero j (by omega) l lt qs qa hc a01 a12 a20 hS hA
  | succ m ih =>
    have hfar : ∀ (j : ℕ) (l lt : ℕ → Fin 2 → ℂ) (qs qa : Fin 2 → ℂ), G (m + 1) j l lt → 2 ≤ j →
        (∀ t ≤ m + 1 + 2, (t = 0 ∨ t = j) → squareBr qs (l t) ≠ 0) →
        (∀ t ≤ m + 1 + 2, ¬ (t = 0 ∨ t = j) → angleBr qa (lt t) ≠ 0) →
        trueAmp (m + 1) j l lt qs qa = ptN (m + 1) j lt := by
      intro j l lt qs qa hGj hj hS hA
      obtain ⟨F, hred⟩ := hG.2.2.1 m j l lt hGj hj
      exact trueAmp_far m j hj l lt F (fun qs' qa' h1 h2 => ih (j - 1) (redL l lt) (redLt lt) qs' qa' hred h1 h2)
        qs qa hS hA
    intro j l lt qs qa hGj hS hA
    have hr := hG.1 (m + 1) j l lt hGj
    by_cases hj1 : j = 1
    · subst hj1
      obtain ⟨hRot, hgen, hG'⟩ := hG.2.2.2 m l lt hGj
      rw [trueAmp_rot (m + 1) l lt qs qa hRot.hcons hRot.hprop, ptN_rot (m + 1) lt]
      refine hfar (m + 3) _ _ qs qa hG' (by omega) ?_ ?_
      · intro t ht hneg
        rcases hneg with h0 | h1
        · subst h0
          simpa [rotLabels] using hS 1 (by omega) (Or.inr rfl)
        · subst h1
          simpa [rotLabels] using hS 0 (by omega) (Or.inl rfl)
      · intro t ht hneg
        have h1 : t < m + 3 := by omega
        have h2 : t ≠ 0 := fun h => hneg (Or.inl h)
        simpa [rotLabels, h1] using hA (t + 1) (by omega) (by omega)
    · exact hfar j l lt qs qa hGj (by omega) hS hA

end Lightlike.SpinorHelicity
