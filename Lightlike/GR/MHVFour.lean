import Lightlike.GR.MHVInduction
import Lightlike.GR.MHVStep

/-!
# Four gluons: the true amplitudes are the Parke-Taylor amplitudes for generic kinematics

For four gluons the genericity of the recursion is the nonvanishing of the brackets: the class of kinematics with
momentum conservation and all angle and square brackets nonzero is closed under the reductions of the induction, so
the Berends-Giele amplitude is the Parke-Taylor amplitude on this open set (the three-gluon case is the base of the
induction).
-/

noncomputable section

namespace Lightlike.SpinorHelicity

/-- The propagator of two adjacent gluons: `P_{a,a+1}² = ⟨a, a+1⟩[a, a+1]`. -/
lemma mdot_adjacent (l lt : ℕ → Fin 2 → ℂ) (a : ℕ) :
    mdot (momRange (fun t => nullMom (l t) (lt t)) a (a + 1)) (momRange (fun t => nullMom (l t) (lt t)) a (a + 1)) =
      angleBr (lt a) (lt (a + 1)) * squareBr (l a) (l (a + 1)) := by
  have hP : momRange (fun t => nullMom (l t) (lt t)) a (a + 1) = nullMom (l a) (lt a) + nullMom (l (a + 1)) (lt (a + 1)) := by
    simp [momRange, Finset.sum_Ico_succ_top]
  rw [hP]
  simp only [mdot_add_left, mdot_add_right, mdot_nullMom_two]
  have a1 : angleBr (lt a) (lt a) = 0 := by rw [angleBr_eq]; ring
  have a2 : angleBr (lt (a + 1)) (lt (a + 1)) = 0 := by rw [angleBr_eq]; ring
  have s1 : squareBr (l a) (l a) = 0 := by rw [squareBr_eq]; ring
  have s2 : squareBr (l (a + 1)) (l (a + 1)) = 0 := by rw [squareBr_eq]; ring
  have hs : squareBr (l (a + 1)) (l a) = -squareBr (l a) (l (a + 1)) := squareBr_antisymm _ _
  have ha : angleBr (lt (a + 1)) (lt a) = -angleBr (lt a) (lt (a + 1)) := angleBr_antisymm _ _
  rw [a1, a2, s1, s2, hs, ha]
  ring

/-- **Generic four-gluon kinematics satisfy the hypotheses of the recursion**: momentum conservation, nonzero angle
and square brackets and nonzero references. -/
theorem trueKin_four (j : ℕ) (hj : 2 ≤ j) (hj3 : j ≤ 3) (l lt : ℕ → Fin 2 → ℂ) (qs0 qa0 : Fin 2 → ℂ)
    (hcons : momRange (fun t => nullMom (l t) (lt t)) 0 3 = 0)
    (hA : ∀ a b, a ≤ 3 → b ≤ 3 → a ≠ b → angleBr (lt a) (lt b) ≠ 0)
    (hS : ∀ a b, a ≤ 3 → b ≤ 3 → a ≠ b → squareBr (l a) (l b) ≠ 0)
    (hqs : ∀ t ≤ 3, squareBr qs0 (l t) ≠ 0) (hqa : ∀ t ≤ 3, angleBr qa0 (lt t) ≠ 0) :
    TrueKin 1 j l lt qs0 qa0 := by
  have h0 := shiftedMom_zero l lt
  refine ⟨hj, by omega, hqs 1 (by omega), hqa 0 (by omega), ?_, ?_, ?_, hqs j hj3, ?_, hS 1 0 (by omega) (by omega)
    (by omega), hS 1 j (by omega) hj3 (by omega), hA 0 1 (by omega) (by omega) (by omega), ?_, ?_, ?_⟩
  · intro b hb1 hb2
    have : b = 2 := by omega
    subst this
    rw [h0, momRange_two]
    simp only [mdot_add_left, mdot_nullMom_two]
    have a1 : angleBr (lt 1) (lt 0) ≠ 0 := hA 1 0 (by omega) (by omega) (by omega)
    have s1 : squareBr (l 1) (l 1) = 0 := by rw [squareBr_eq]; ring
    have a2 : angleBr (lt 2) (lt 0) ≠ 0 := hA 2 0 (by omega) (by omega) (by omega)
    have s2 : squareBr (l 2) (l 1) ≠ 0 := hS 2 1 (by omega) (by omega) (by omega)
    rw [s1]
    simp only [mul_zero, zero_add]
    exact mul_ne_zero (mul_ne_zero (by norm_num) a2) s2
  · intro a b hab hb ha1 hne
    have ha : a = 0 := by omega
    subst ha
    have hb1 : b = 1 := by omega
    subst hb1
    rw [h0]
    have := mdot_adjacent l lt 0
    simp only [zero_add] at this
    rw [this]
    exact mul_ne_zero (hA 0 1 (by omega) (by omega) (by omega)) (hS 0 1 (by omega) (by omega) (by omega))
  · rw [h0]; exact hcons
  · intro t ht1 ht2 htj
    exact hqa t (by omega)
  · intro t ht1 ht2 htj
    exact hA 0 t (by omega) ht2 (by omega)
  · intro d hd1 hd2
    have : d = 2 := by omega
    subst this
    rw [mdot_momRange_two]
    exact mul_ne_zero (hA 1 2 (by omega) (by omega) (by omega)) (hS 1 2 (by omega) (by omega) (by omega))
  · intro d d' h1 h2 h3 h4 _
    omega

/-- **The class of generic kinematics of four gluons** (and the three-gluon kinematics of their reductions):
momentum conservation, all angle and square brackets nonzero, and generic references. -/
def Gen4 : ℕ → ℕ → (ℕ → Fin 2 → ℂ) → (ℕ → Fin 2 → ℂ) → Prop := fun m j l lt =>
  (m = 1 ∧ 1 ≤ j ∧ j ≤ 3 ∧ momRange (fun t => nullMom (l t) (lt t)) 0 3 = 0 ∧
    (∀ a b, a ≤ 3 → b ≤ 3 → a ≠ b → angleBr (lt a) (lt b) ≠ 0) ∧
    (∀ a b, a ≤ 3 → b ≤ 3 → a ≠ b → squareBr (l a) (l b) ≠ 0) ∧
    ∃ qs0 qa0 : Fin 2 → ℂ, (∀ t ≤ 3, squareBr qs0 (l t) ≠ 0) ∧ (∀ t ≤ 3, angleBr qa0 (lt t) ≠ 0)) ∨
  (m = 0 ∧ (j = 1 ∨ j = 2) ∧ momRange (fun t => nullMom (l t) (lt t)) 0 2 = 0 ∧ angleBr (lt 0) (lt 1) ≠ 0 ∧
    angleBr (lt 1) (lt 2) ≠ 0 ∧ angleBr (lt 2) (lt 0) ≠ 0)

/-- The reduced three-gluon kinematics of the channel `[1, 2]` of generic four-gluon kinematics. -/
lemma gen4_reduced (j : ℕ) (hj2 : 2 ≤ j) (hj3 : j ≤ 3) (l lt : ℕ → Fin 2 → ℂ)
    (hcons : momRange (fun t => nullMom (l t) (lt t)) 0 3 = 0)
    (hA : ∀ a b, a ≤ 3 → b ≤ 3 → a ≠ b → angleBr (lt a) (lt b) ≠ 0)
    (hS : ∀ a b, a ≤ 3 → b ≤ 3 → a ≠ b → squareBr (l a) (l b) ≠ 0) (qs0 qa0 : Fin 2 → ℂ)
    (hqs : ∀ t ≤ 3, squareBr qs0 (l t) ≠ 0) (hqa : ∀ t ≤ 3, angleBr qa0 (lt t) ≠ 0) :
    Gen4 0 (j - 1) (redL l lt) (redLt lt) := by
  right
  have K := trueKin_four j hj2 hj3 l lt qs0 qa0 hcons hA hS hqs hqa
  have h02 := hA 0 2 (by omega) (by omega) (by omega)
  have h12 := hS 1 2 (by omega) (by omega) (by omega)
  refine ⟨rfl, by omega, ?_, ?_, ?_, ?_⟩
  · have hF := falloffData_spinor 1 j hj2 l lt qs0 qa0 K.hq1 K.hq0 K.hone K.hother
    have hconsz : momRange (shiftedMom l lt (zpole l lt 2)) 0 (1 + 2) = 0 := by
      have := hF.momRange_eq (zpole l lt 2) 0 (1 + 2)
      rw [this, K.hcons]; simp
    have hc := momRange_collapse (shiftedMom l lt (zpole l lt 2)) (i := 1) (j := 2) (a := 0) (b := 2)
      (by omega) (by omega) (by omega)
    have hf : (fun t => nullMom (redL l lt t) (redLt lt t)) =
        collapse (shiftedMom l lt (zpole l lt 2)) 1 2 (momRange (shiftedMom l lt (zpole l lt 2)) 1 2) :=
      funext fun t => (collapse_pole_two l lt h02 h12 t).symm
    rw [hf, hc]
    simpa using hconsz
  · simpa [redLt] using hA 0 2 (by omega) (by omega) (by omega)
  · simpa [redLt] using hA 2 3 (by omega) (by omega) (by omega)
  · simpa [redLt] using hA 3 0 (by omega) (by omega) (by omega)

/-- The cyclic relabelling of generic four-gluon kinematics, for adjacent negative gluons. -/
lemma gen4_rot (l lt : ℕ → Fin 2 → ℂ)
    (hcons : momRange (fun t => nullMom (l t) (lt t)) 0 3 = 0)
    (hA : ∀ a b, a ≤ 3 → b ≤ 3 → a ≠ b → angleBr (lt a) (lt b) ≠ 0)
    (hS : ∀ a b, a ≤ 3 → b ≤ 3 → a ≠ b → squareBr (l a) (l b) ≠ 0) (qs0 qa0 : Fin 2 → ℂ)
    (hqs : ∀ t ≤ 3, squareBr qs0 (l t) ≠ 0) (hqa : ∀ t ≤ 3, angleBr qa0 (lt t) ≠ 0) :
    RotData 1 l lt ∧ GenericAngles (fun i : Fin (0 + 4) => lt i) ∧
      Gen4 1 3 (rotLabels l (0 + 3)) (rotLabels lt (0 + 3)) := by
  refine ⟨⟨hcons, ?_⟩, ?_, Or.inl ⟨rfl, by omega, le_rfl, ?_, ?_, ?_, qs0, qa0, ?_, ?_⟩⟩
  · intro d hd1 hd2
    have : d = 1 := by omega
    subst this
    have := mdot_adjacent l lt 0
    simp only [zero_add] at this
    rw [this]
    exact mul_ne_zero (hA 0 1 (by omega) (by omega) (by omega)) (hS 0 1 (by omega) (by omega) (by omega))
  · intro a b hab
    exact hA a b (by have := a.isLt; omega) (by have := b.isLt; omega) (fun e => hab (Fin.ext e))
  · rw [← hcons]
    simp [momRange, Finset.sum_range_succ, rotLabels]
    abel
  · intro a b ha hb hab
    interval_cases a <;> interval_cases b <;>
      first | exact absurd rfl hab | (simp [rotLabels]; exact hA _ _ (by omega) (by omega) (by omega))
  · intro a b ha hb hab
    interval_cases a <;> interval_cases b <;>
      first | exact absurd rfl hab | (simp [rotLabels]; exact hS _ _ (by omega) (by omega) (by omega))
  · intro t ht
    interval_cases t <;> simp [rotLabels] <;> exact hqs _ (by omega)
  · intro t ht
    interval_cases t <;> simp [rotLabels] <;> exact hqa _ (by omega)

/-- **The class of generic four-gluon kinematics is closed under the reductions of the induction.** -/
theorem Gen4_closed : ClosedClass Gen4 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m j l lt h
    rcases h with ⟨rfl, h1, h2, -⟩ | ⟨rfl, hj, -⟩
    · omega
    · omega
  · intro j l lt h
    rcases h with ⟨hm, -⟩ | ⟨-, -, h1, h2, h3, h4⟩
    · omega
    · exact ⟨h1, h2, h3, h4⟩
  · intro m j l lt h hj2
    rcases h with ⟨hm, h1, h3, hc, hA, hS, qs0, qa0, hqs, hqa⟩ | ⟨hm, -⟩
    · have hm0 : m = 0 := by omega
      subst hm0
      refine ⟨⟨⟨qs0, qa0, trueKin_four j hj2 h3 l lt qs0 qa0 hc hA hS hqs hqa⟩,
        hA 0 2 (by omega) (by omega) (by omega), hS 1 2 (by omega) (by omega) (by omega), ?_, ?_⟩,
        gen4_reduced j hj2 h3 l lt hc hA hS qs0 qa0 hqs hqa⟩
      · intro a b hab
        exact hA a b (by have := a.isLt; omega) (by have := b.isLt; omega) (fun e => hab (Fin.ext e))
      · exact ⟨fun _ => 0, fun _ => 0, fun d h1 h2 => by omega, fun d h1 h2 => by omega,
          fun d h1 h2 => by omega, fun d h1 h2 => by omega, fun d h1 h2 => by omega⟩
    · omega
  · intro m l lt h
    rcases h with ⟨hm, h1, h3, hc, hA, hS, qs0, qa0, hqs, hqa⟩ | ⟨hm, -⟩
    · have hm0 : m = 0 := by omega
      subst hm0
      exact gen4_rot l lt hc hA hS qs0 qa0 hqs hqa
    · omega

/-- **The Parke-Taylor formula for four gluons from the Feynman rules, for all generic kinematics**: momentum
conservation and nonzero angle and square brackets (and references with nonzero brackets). -/
theorem trueAmp_four (j : ℕ) (l lt : ℕ → Fin 2 → ℂ) (qs qa : Fin 2 → ℂ) (hj : 1 ≤ j) (hj3 : j ≤ 3)
    (hc : momRange (fun t => nullMom (l t) (lt t)) 0 3 = 0)
    (hA : ∀ a b, a ≤ 3 → b ≤ 3 → a ≠ b → angleBr (lt a) (lt b) ≠ 0)
    (hS : ∀ a b, a ≤ 3 → b ≤ 3 → a ≠ b → squareBr (l a) (l b) ≠ 0)
    (hqs : ∀ t ≤ 3, squareBr qs (l t) ≠ 0) (hqa : ∀ t ≤ 3, angleBr qa (lt t) ≠ 0) :
    trueAmp 1 j l lt qs qa = ptN 1 j lt :=
  trueAmp_eq_ptN Gen4 Gen4_closed 1 j l lt qs qa (Or.inl ⟨rfl, hj, hj3, hc, hA, hS, qs, qa, hqs, hqa⟩)
    (fun t ht _ => hqs t (by omega)) (fun t ht _ => hqa t (by omega))

end Lightlike.SpinorHelicity
