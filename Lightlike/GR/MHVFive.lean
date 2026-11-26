import Lightlike.GR.MHVFour
import Lightlike.GR.MHVStepFar

/-!
# Five gluons: the hypotheses of the recursion for explicit kinematics

The nonvanishing conditions of `TrueKin` for five gluons in terms of brackets: momentum conservation, nonzero angle and
square brackets, three nonzero three-particle propagators, one nonzero pole bracket and distinct poles.
-/

noncomputable section

namespace Lightlike.SpinorHelicity

/-- The propagator of three adjacent gluons: `P_{a..a+2}² = Σ ⟨st⟩[st]` over the three pairs. -/
lemma mdot_three (l lt : ℕ → Fin 2 → ℂ) (a : ℕ) :
    mdot (momRange (fun t => nullMom (l t) (lt t)) a (a + 2)) (momRange (fun t => nullMom (l t) (lt t)) a (a + 2)) =
      angleBr (lt a) (lt (a + 1)) * squareBr (l a) (l (a + 1)) +
        angleBr (lt a) (lt (a + 2)) * squareBr (l a) (l (a + 2)) +
        angleBr (lt (a + 1)) (lt (a + 2)) * squareBr (l (a + 1)) (l (a + 2)) := by
  have hP : momRange (fun t => nullMom (l t) (lt t)) a (a + 2) =
      nullMom (l a) (lt a) + nullMom (l (a + 1)) (lt (a + 1)) + nullMom (l (a + 2)) (lt (a + 2)) := by
    simp [momRange, Finset.sum_Ico_succ_top, add_assoc]
  rw [hP]
  simp only [mdot_add_left, mdot_add_right, mdot_nullMom_two]
  have za : ∀ x : Fin 2 → ℂ, angleBr x x = 0 := fun x => by rw [angleBr_eq]; ring
  have zs : ∀ x : Fin 2 → ℂ, squareBr x x = 0 := fun x => by rw [squareBr_eq]; ring
  have as : ∀ x y : Fin 2 → ℂ, angleBr y x = -angleBr x y := fun x y => angleBr_antisymm y x
  have ss : ∀ x y : Fin 2 → ℂ, squareBr y x = -squareBr x y := fun x y => squareBr_antisymm y x
  rw [za, za, za, zs, zs, zs, as (lt a) (lt (a + 1)), as (lt a) (lt (a + 2)), as (lt (a + 1)) (lt (a + 2)),
    ss (l a) (l (a + 1)), ss (l a) (l (a + 2)), ss (l (a + 1)) (l (a + 2))]
  ring

/-- The pole of the channel `[1, 3]`: `z = P_{123}² / (⟨20⟩[21] + ⟨30⟩[31])`. -/
lemma zpole_three (l lt : ℕ → Fin 2 → ℂ) :
    zpole l lt 3 =
      (angleBr (lt 1) (lt 2) * squareBr (l 1) (l 2) + angleBr (lt 1) (lt 3) * squareBr (l 1) (l 3) +
        angleBr (lt 2) (lt 3) * squareBr (l 2) (l 3)) /
        (angleBr (lt 2) (lt 0) * squareBr (l 2) (l 1) + angleBr (lt 3) (lt 0) * squareBr (l 3) (l 1)) := by
  have h0 := shiftedMom_zero l lt
  have hP : momRange (fun t => nullMom (l t) (lt t)) 1 3 =
      nullMom (l 1) (lt 1) + nullMom (l 2) (lt 2) + nullMom (l 3) (lt 3) := by
    simp [momRange, Finset.sum_Ico_succ_top, add_assoc]
  have h3 := mdot_three l lt 1
  rw [show (1 : ℕ) + 2 = 3 from rfl] at h3
  unfold zpole
  rw [h0, h3, hP]
  simp only [mdot_add_left, mdot_nullMom_two]
  have s1 : squareBr (l 1) (l 1) = 0 := by rw [squareBr_eq]; ring
  rw [s1]
  rw [show (-2 : ℂ) * (1 / 2 * angleBr (lt 1) (lt 0) * 0 + 1 / 2 * angleBr (lt 2) (lt 0) * squareBr (l 2) (l 1) +
      1 / 2 * angleBr (lt 3) (lt 0) * squareBr (l 3) (l 1)) =
      -(angleBr (lt 2) (lt 0) * squareBr (l 2) (l 1) + angleBr (lt 3) (lt 0) * squareBr (l 3) (l 1)) by ring]
  rw [neg_div_neg_eq]

/-- **Five-gluon kinematics satisfy the hypotheses of the recursion** under explicit bracket conditions. -/
theorem trueKin_five (j : ℕ) (hj : 2 ≤ j) (hj4 : j ≤ 4) (l lt : ℕ → Fin 2 → ℂ) (qs0 qa0 : Fin 2 → ℂ)
    (hcons : momRange (fun t => nullMom (l t) (lt t)) 0 4 = 0)
    (hA : ∀ a b, a ≤ 4 → b ≤ 4 → a ≠ b → angleBr (lt a) (lt b) ≠ 0)
    (hS : ∀ a b, a ≤ 4 → b ≤ 4 → a ≠ b → squareBr (l a) (l b) ≠ 0)
    (hqs : ∀ t ≤ 4, squareBr qs0 (l t) ≠ 0) (hqa : ∀ t ≤ 4, angleBr qa0 (lt t) ≠ 0)
    (h012 : angleBr (lt 0) (lt 1) * squareBr (l 0) (l 1) + angleBr (lt 0) (lt 2) * squareBr (l 0) (l 2) +
      angleBr (lt 1) (lt 2) * squareBr (l 1) (l 2) ≠ 0)
    (h123 : angleBr (lt 1) (lt 2) * squareBr (l 1) (l 2) + angleBr (lt 1) (lt 3) * squareBr (l 1) (l 3) +
      angleBr (lt 2) (lt 3) * squareBr (l 2) (l 3) ≠ 0)
    (hone3 : angleBr (lt 2) (lt 0) * squareBr (l 2) (l 1) + angleBr (lt 3) (lt 0) * squareBr (l 3) (l 1) ≠ 0)
    (hinj : zpole l lt 2 ≠ zpole l lt 3) :
    TrueKin 2 j l lt qs0 qa0 := by
  have h0 := shiftedMom_zero l lt
  refine ⟨hj, by omega, hqs 1 (by omega), hqa 0 (by omega), ?_, ?_, ?_, hqs j hj4, ?_,
    hS 1 0 (by omega) (by omega) (by omega), hS 1 j (by omega) hj4 (by omega),
    hA 0 1 (by omega) (by omega) (by omega), ?_, ?_, ?_⟩
  · intro b hb1 hb2
    rw [h0]
    have a1 : angleBr (lt 1) (lt 0) ≠ 0 := hA 1 0 (by omega) (by omega) (by omega)
    have s1 : squareBr (l 1) (l 1) = 0 := by rw [squareBr_eq]; ring
    rcases (by omega : b = 2 ∨ b = 3) with rfl | rfl
    · rw [momRange_two]
      simp only [mdot_add_left, mdot_nullMom_two]
      rw [s1]
      simp only [mul_zero, zero_add]
      exact mul_ne_zero (mul_ne_zero (by norm_num) (hA 2 0 (by omega) (by omega) (by omega)))
        (hS 2 1 (by omega) (by omega) (by omega))
    · have hP : momRange (fun t => nullMom (l t) (lt t)) 1 3 =
          nullMom (l 1) (lt 1) + nullMom (l 2) (lt 2) + nullMom (l 3) (lt 3) := by
        simp [momRange, Finset.sum_Ico_succ_top, add_assoc]
      rw [hP]
      simp only [mdot_add_left, mdot_nullMom_two]
      rw [s1]
      intro h
      apply hone3
      linear_combination 2 * h
  · intro a b hab hb ha1 hne
    rw [h0]
    have ha : a = 0 ∨ a = 2 := by omega
    rcases ha with rfl | rfl
    · rcases (by omega : b = 1 ∨ b = 2) with rfl | rfl
      · have := mdot_adjacent l lt 0
        simp only [zero_add] at this
        rw [this]
        exact mul_ne_zero (hA 0 1 (by omega) (by omega) (by omega)) (hS 0 1 (by omega) (by omega) (by omega))
      · rw [mdot_three l lt 0]
        simpa using h012
    · have hb3 : b = 3 := by omega
      subst hb3
      exact (mdot_adjacent l lt 2).symm ▸
        mul_ne_zero (hA 2 3 (by omega) (by omega) (by omega)) (hS 2 3 (by omega) (by omega) (by omega))
  · rw [h0]; exact hcons
  · intro t ht1 ht2 htj
    exact hqa t (by omega)
  · intro t ht1 ht2 htj
    exact hA 0 t (by omega) (by omega) (by omega)
  · intro d hd1 hd2
    rw [h0]
    rcases (by omega : d = 2 ∨ d = 3) with rfl | rfl
    · rw [← h0, mdot_momRange_two]
      exact mul_ne_zero (hA 1 2 (by omega) (by omega) (by omega)) (hS 1 2 (by omega) (by omega) (by omega))
    · rw [mdot_three l lt 1]
      simpa using h123
  · intro d d' h1 h2 h3 h4 h5
    rcases (by omega : d = 2 ∨ d = 3) with rfl | rfl <;> rcases (by omega : d' = 2 ∨ d' = 3) with rfl | rfl
    · rfl
    · exact absurd h5 hinj
    · exact absurd h5.symm hinj
    · rfl

/-- **Generic five-gluon kinematics**: the bracket conditions of `trueKin_five`, and the nonvanishing of the square
brackets and the existence of generic references for the reduced four-gluon kinematics of the channel `[1, 2]`. -/
structure Five (l lt : ℕ → Fin 2 → ℂ) : Prop where
  /-- Momentum conservation. -/
  cons : momRange (fun t => nullMom (l t) (lt t)) 0 4 = 0
  /-- All angle brackets are nonzero. -/
  hA : ∀ a b, a ≤ 4 → b ≤ 4 → a ≠ b → angleBr (lt a) (lt b) ≠ 0
  /-- All square brackets are nonzero. -/
  hS : ∀ a b, a ≤ 4 → b ≤ 4 → a ≠ b → squareBr (l a) (l b) ≠ 0
  /-- Generic references. -/
  refs : ∃ qs0 qa0 : Fin 2 → ℂ, (∀ t ≤ 4, squareBr qs0 (l t) ≠ 0) ∧ (∀ t ≤ 4, angleBr qa0 (lt t) ≠ 0)
  /-- `P_{012}² ≠ 0`. -/
  h012 : angleBr (lt 0) (lt 1) * squareBr (l 0) (l 1) + angleBr (lt 0) (lt 2) * squareBr (l 0) (l 2) +
    angleBr (lt 1) (lt 2) * squareBr (l 1) (l 2) ≠ 0
  /-- `P_{123}² ≠ 0`. -/
  h123 : angleBr (lt 1) (lt 2) * squareBr (l 1) (l 2) + angleBr (lt 1) (lt 3) * squareBr (l 1) (l 3) +
    angleBr (lt 2) (lt 3) * squareBr (l 2) (l 3) ≠ 0
  /-- `P_{123} · r ≠ 0`. -/
  hone3 : angleBr (lt 2) (lt 0) * squareBr (l 2) (l 1) + angleBr (lt 3) (lt 0) * squareBr (l 3) (l 1) ≠ 0
  /-- The poles of the channels `[1,2]` and `[1,3]` are distinct. -/
  hinj : zpole l lt 2 ≠ zpole l lt 3
  /-- The square brackets of the reduced kinematics are nonzero. -/
  hredS : ∀ a b, a ≤ 3 → b ≤ 3 → a ≠ b → squareBr (redL l lt a) (redL l lt b) ≠ 0
  /-- Generic references for the reduced kinematics. -/
  hredQ : ∃ qs0 qa0 : Fin 2 → ℂ, (∀ t ≤ 3, squareBr qs0 (redL l lt t) ≠ 0) ∧
    (∀ t ≤ 3, angleBr qa0 (redLt lt t) ≠ 0)

/-- The pole spinors of the channel `[1, 3]` of five gluons, with the brackets that make its term vanish. -/
def PolesData (j : ℕ) (l lt : ℕ → Fin 2 → ℂ) : Prop :=
  ∃ lP ltP : ℕ → Fin 2 → ℂ,
    (∀ d, 3 ≤ d → d ≤ 1 + 2 → momRange (shiftedMom l lt (zpole l lt d)) 1 d = nullMom (lP d) (ltP d)) ∧
    (∀ d, 3 ≤ d → d ≤ 1 + 2 → angleBr (lt 0) (ltP d) ≠ 0) ∧
    (∀ d, 3 ≤ d → d ≤ 1 + 2 → squareBr (l 1) (lP d) ≠ 0) ∧
    (∀ d, 3 ≤ d → d ≤ 1 + 2 → d < j → ∀ s, 1 ≤ s → s ≤ d →
      angleBr (ltP d) (ltHat lt (zpole l lt d) s) ≠ 0) ∧
    (∀ d, 3 ≤ d → d ≤ 1 + 2 → j ≤ d →
      (∀ s, 1 ≤ s → s ≤ d → s ≠ j → angleBr (lt j) (ltHat lt (zpole l lt d) s) ≠ 0) ∧
        angleBr (lt j) (ltP d) ≠ 0)

/-- The class of generic kinematics of three, four and five gluons. -/
def Gen5 : ℕ → ℕ → (ℕ → Fin 2 → ℂ) → (ℕ → Fin 2 → ℂ) → Prop := fun m j l lt =>
  Gen4 m j l lt ∨
    (m = 2 ∧ 1 ≤ j ∧ j ≤ 4 ∧ Five l lt ∧ (2 ≤ j → PolesData j l lt) ∧
      (j = 1 → Five (rotLabels l 4) (rotLabels lt 4) ∧ PolesData 4 (rotLabels l 4) (rotLabels lt 4)))

/-- The reduced four-gluon kinematics of the channel `[1, 2]` of generic five-gluon kinematics. -/
lemma gen5_reduced (j : ℕ) (hj2 : 2 ≤ j) (hj4 : j ≤ 4) (l lt : ℕ → Fin 2 → ℂ) (F : Five l lt) :
    Gen4 1 (j - 1) (redL l lt) (redLt lt) := by
  obtain ⟨qs0, qa0, hqs, hqa⟩ := F.refs
  have K := trueKin_five j hj2 hj4 l lt qs0 qa0 F.cons F.hA F.hS hqs hqa F.h012 F.h123 F.hone3 F.hinj
  have h02 := F.hA 0 2 (by omega) (by omega) (by omega)
  have h12 := F.hS 1 2 (by omega) (by omega) (by omega)
  left
  refine ⟨rfl, by omega, by omega, ?_, ?_, F.hredS, F.hredQ⟩
  · have hF := falloffData_spinor 2 j hj2 l lt qs0 qa0 K.hq1 K.hq0 K.hone K.hother
    have hconsz : momRange (shiftedMom l lt (zpole l lt 2)) 0 (2 + 2) = 0 := by
      have := hF.momRange_eq (zpole l lt 2) 0 (2 + 2)
      rw [this, K.hcons]; simp
    have hc := momRange_collapse (shiftedMom l lt (zpole l lt 2)) (i := 1) (j := 2) (a := 0) (b := 3)
      (by omega) (by omega) (by omega)
    have hf : (fun t => nullMom (redL l lt t) (redLt lt t)) =
        collapse (shiftedMom l lt (zpole l lt 2)) 1 2 (momRange (shiftedMom l lt (zpole l lt 2)) 1 2) :=
      funext fun t => (collapse_pole_two l lt h02 h12 t).symm
    rw [hf, hc]
    simpa using hconsz
  · intro a b ha hb hab
    simp only [redLt]
    by_cases h0 : a = 0
    · subst h0
      have hb0 : b ≠ 0 := fun h => hab (by omega)
      simpa [hb0] using F.hA 0 (b + 1) (by omega) (by omega) (by omega)
    · by_cases hb0 : b = 0
      · subst hb0
        simpa [h0] using F.hA (a + 1) 0 (by omega) (by omega) (by omega)
      · simpa [h0, hb0] using F.hA (a + 1) (b + 1) (by omega) (by omega) (by omega)

/-- **The class of generic kinematics of up to five gluons is closed under the reductions of the induction.** -/
theorem Gen5_closed : ClosedClass Gen5 := by
  obtain ⟨c1, c2, c3, c4⟩ := Gen4_closed
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m j l lt h
    rcases h with h | ⟨rfl, h1, h2, -⟩
    · exact c1 m j l lt h
    · omega
  · intro j l lt h
    rcases h with h | ⟨hm, -⟩
    · exact c2 j l lt h
    · omega
  · intro m j l lt h hj2
    rcases h with h | ⟨hm, h1, h4, F, hP, -⟩
    · obtain ⟨hF, hG⟩ := c3 m j l lt h hj2
      exact ⟨hF, Or.inl hG⟩
    · have hm1 : m = 1 := by omega
      subst hm1
      obtain ⟨qs0, qa0, hqs, hqa⟩ := F.refs
      refine ⟨⟨⟨qs0, qa0, trueKin_five j hj2 h4 l lt qs0 qa0 F.cons F.hA F.hS hqs hqa F.h012 F.h123
        F.hone3 F.hinj⟩, F.hA 0 2 (by omega) (by omega) (by omega),
        F.hS 1 2 (by omega) (by omega) (by omega), ?_, hP hj2⟩, Or.inl (gen5_reduced j hj2 h4 l lt F)⟩
      intro a b hab
      exact F.hA a b (by have := a.isLt; omega) (by have := b.isLt; omega) (fun e => hab (Fin.ext e))
  · intro m l lt h
    rcases h with h | ⟨hm, h1, h4, F, -, hR⟩
    · obtain ⟨hR, hg, hG⟩ := c4 m l lt h
      exact ⟨hR, hg, Or.inl hG⟩
    · have hm1 : m = 1 := by omega
      subst hm1
      obtain ⟨F', P'⟩ := hR rfl
      refine ⟨⟨F.cons, ?_⟩, ?_, Or.inr ⟨rfl, by omega, le_rfl, F', fun _ => P', fun h => absurd h (by omega)⟩⟩
      · intro d hd1 hd2
        rcases (by omega : d = 1 ∨ d = 2) with rfl | rfl
        · have := mdot_adjacent l lt 0
          simp only [zero_add] at this
          rw [this]
          exact mul_ne_zero (F.hA 0 1 (by omega) (by omega) (by omega)) (F.hS 0 1 (by omega) (by omega) (by omega))
        · rw [show (2 : ℕ) = 0 + 2 from rfl, mdot_three l lt 0]
          simpa using F.h012
      · intro a b hab
        exact F.hA a b (by have := a.isLt; omega) (by have := b.isLt; omega) (fun e => hab (Fin.ext e))

end Lightlike.SpinorHelicity
