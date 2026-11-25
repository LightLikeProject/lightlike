import Mathlib
import Lightlike.PL.Polygon
import Lightlike.PL.Chain
import Lightlike.PL.SimpleChain
import Lightlike.PL.ChainCarrier

/-!
# The ray-crossing count is additive under subdividing an edge

Row G3-188 (PL5), ring cells.  For a point `m = u + t (v - u)` of the edge `[u, v]`, the horizontal ray from `x` crosses
`[u, v]` exactly when it crosses one of `[u, m]`, `[m, v]` (`ind_crossesRay_split`); this is the algebra behind inserting a
vertex into an edge of a polygon.
-/

open Set

namespace Lightlike.PL

lemma xAt_split_left {u v : ℝ × ℝ} {t h : ℝ} (ht : 0 < t) (hab : u.2 ≠ v.2) :
    xAt u (u + t • (v - u)) h = xAt u v h := by
  have hba : v.2 - u.2 ≠ 0 := sub_ne_zero.2 hab.symm
  unfold xAt
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.snd_sub, Prod.smul_snd, Prod.fst_sub, smul_eq_mul]
  field_simp
  ring

lemma xAt_split_right {u v : ℝ × ℝ} {t h : ℝ} (ht : t < 1) (hab : u.2 ≠ v.2) :
    xAt (u + t • (v - u)) v h = xAt u v h := by
  have hba : v.2 - u.2 ≠ 0 := sub_ne_zero.2 hab.symm
  have h1 : 1 - t ≠ 0 := by linarith
  unfold xAt
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.snd_sub, Prod.smul_snd, Prod.fst_sub, smul_eq_mul]
  have : v.2 - (u.2 + t * (v.2 - u.2)) = (1 - t) * (v.2 - u.2) := by ring
  rw [this]
  field_simp
  ring

lemma ind_add_of_excl (A B C X : Prop) (hC : C ↔ A ∨ B) (hAB : ¬ (A ∧ B)) :
    ind (A ∧ X) + ind (B ∧ X) = ind (C ∧ X) := by
  by_cases hX : X
  · by_cases hA : A
    · have hB : ¬ B := fun hB => hAB ⟨hA, hB⟩
      have hC' : C := hC.2 (Or.inl hA)
      simp [ind, hA, hB, hC', hX]
    · by_cases hB : B
      · have hC' : C := hC.2 (Or.inr hB)
        simp [ind, hA, hB, hC', hX]
      · have hC' : ¬ C := fun h => by rcases hC.1 h with h | h <;> contradiction
        simp [ind, hA, hB, hC', hX]
  · simp [ind, hX]

/-- **Subdividing an edge keeps the crossing count.** -/
lemma ind_crossesRay_split {u v x : ℝ × ℝ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ind (CrossesRay u (u + t • (v - u)) x) + ind (CrossesRay (u + t • (v - u)) v x) = ind (CrossesRay u v x) := by
  rcases ht0.eq_or_lt with rfl | ht0
  · have h : CrossesRay u (u + (0 : ℝ) • (v - u)) x ↔ False := by
      simp only [zero_smul, add_zero, CrossesRay]
      constructor
      · rintro ⟨h | h, -⟩ <;> linarith [h.1, h.2]
      · exact False.elim
    rw [Polygon.ind_congr h]
    simp only [zero_smul, add_zero]
    simp [ind]
  rcases ht1.eq_or_lt with rfl | ht1
  · have h : CrossesRay (u + (1 : ℝ) • (v - u)) v x ↔ False := by
      simp only [one_smul, add_sub_cancel, CrossesRay]
      constructor
      · rintro ⟨h | h, -⟩ <;> linarith [h.1, h.2]
      · exact False.elim
    rw [Polygon.ind_congr h]
    simp only [one_smul, add_sub_cancel]
    simp [ind]
  by_cases hab : u.2 = v.2
  · have hm : (u + t • (v - u)).2 = u.2 := by simp [hab]
    have h1 : CrossesRay u (u + t • (v - u)) x ↔ False := by
      unfold CrossesRay; rw [hm]
      constructor
      · rintro ⟨h | h, -⟩ <;> linarith [h.1, h.2]
      · exact False.elim
    have h2 : CrossesRay (u + t • (v - u)) v x ↔ False := by
      unfold CrossesRay; rw [hm, ← hab]
      constructor
      · rintro ⟨h | h, -⟩ <;> linarith [h.1, h.2]
      · exact False.elim
    have h3 : CrossesRay u v x ↔ False := by
      unfold CrossesRay; rw [← hab]
      constructor
      · rintro ⟨h | h, -⟩ <;> linarith [h.1, h.2]
      · exact False.elim
    rw [Polygon.ind_congr h1, Polygon.ind_congr h2, Polygon.ind_congr h3]
    simp [ind]
  · have hm : (u + t • (v - u)).2 = u.2 + t * (v.2 - u.2) := by simp
    rw [CrossesRay, CrossesRay, CrossesRay, xAt_split_left ht0 hab, xAt_split_right ht1 hab]
    apply ind_add_of_excl
    · rcases lt_or_gt_of_ne hab with hlt | hgt
      · have hac : u.2 < (u + t • (v - u)).2 := by rw [hm]; nlinarith
        have hcb : (u + t • (v - u)).2 < v.2 := by rw [hm]; nlinarith
        constructor
        · rintro (h | h)
          · by_cases hx : x.2 < (u + t • (v - u)).2
            · exact Or.inl (Or.inl ⟨h.1, hx⟩)
            · exact Or.inr (Or.inl ⟨not_lt.1 hx, h.2⟩)
          · exfalso; linarith [h.1, h.2]
        · rintro ((h | h) | (h | h))
          · exact Or.inl ⟨h.1, by linarith [h.2]⟩
          · exfalso; linarith [h.1, h.2]
          · exact Or.inl ⟨by linarith [h.1], h.2⟩
          · exfalso; linarith [h.1, h.2]
      · have hac : (u + t • (v - u)).2 < u.2 := by rw [hm]; nlinarith
        have hcb : v.2 < (u + t • (v - u)).2 := by rw [hm]; nlinarith
        constructor
        · rintro (h | h)
          · exfalso; linarith [h.1, h.2]
          · by_cases hx : x.2 < (u + t • (v - u)).2
            · exact Or.inr (Or.inr ⟨h.1, hx⟩)
            · exact Or.inl (Or.inr ⟨not_lt.1 hx, h.2⟩)
        · rintro ((h | h) | (h | h))
          · exfalso; linarith [h.1, h.2]
          · exact Or.inr ⟨by linarith [h.1], h.2⟩
          · exfalso; linarith [h.1, h.2]
          · exact Or.inr ⟨h.1, by linarith [h.2]⟩
    · rintro ⟨(h1 | h1), (h2 | h2)⟩ <;> rcases lt_or_gt_of_ne hab with hlt | hgt <;>
        first
        | (have hac : u.2 < (u + t • (v - u)).2 := by rw [hm]; nlinarith
           have hcb : (u + t • (v - u)).2 < v.2 := by rw [hm]; nlinarith
           linarith [h1.1, h1.2, h2.1, h2.2])
        | (have hac : (u + t • (v - u)).2 < u.2 := by rw [hm]; nlinarith
           have hcb : v.2 < (u + t • (v - u)).2 := by rw [hm]; nlinarith
           linarith [h1.1, h1.2, h2.1, h2.2])

/-- **Inserting a point of an edge into a chain keeps its parity.** -/
lemma chainParity_insert (x : ℝ × ℝ) (l₁ l₂ : List (ℝ × ℝ)) (a b : ℝ × ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    chainParity x (l₁ ++ a :: (a + t • (b - a)) :: b :: l₂) = chainParity x (l₁ ++ a :: b :: l₂) := by
  rw [chainParity_append x l₁ a ((a + t • (b - a)) :: b :: l₂), chainParity_append x l₁ a (b :: l₂),
    chainParity_cons_cons, chainParity_cons_cons, chainParity_cons_cons, ← add_assoc (ind _) (ind _),
    ind_crossesRay_split ht0 ht1]

/-- A segment is the union of the two parts cut at one of its points. -/
lemma segment_split_union (a b : ℝ × ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    segment ℝ a (a + t • (b - a)) ∪ segment ℝ (a + t • (b - a)) b = segment ℝ a b := by
  have hm : a + t • (b - a) ∈ segment ℝ a b := by
    rw [segment_eq_image']; exact ⟨t, ⟨ht0, ht1⟩, rfl⟩
  apply Set.Subset.antisymm
  · rintro z (hz | hz)
    · exact (convex_segment a b).segment_subset (left_mem_segment ℝ a b) hm hz
    · exact (convex_segment a b).segment_subset hm (right_mem_segment ℝ a b) hz
  · intro z hz
    rw [segment_eq_image'] at hz
    obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := hz
    rcases le_total s t with hst | hst
    · left
      rcases ht0.eq_or_lt with rfl | htp
      · have : s = 0 := le_antisymm hst hs0
        subst this
        simpa using left_mem_segment ℝ a (a + (0 : ℝ) • (b - a))
      · rw [segment_eq_image']
        refine ⟨s / t, ⟨div_nonneg hs0 ht0, (div_le_one htp).2 hst⟩, ?_⟩
        simp only []
        rw [show a + t • (b - a) - a = t • (b - a) by abel, smul_smul, div_mul_cancel₀ _ htp.ne']
    · right
      rcases ht1.eq_or_lt with rfl | htp
      · have : s = 1 := le_antisymm hs1 hst
        subst this
        simpa using right_mem_segment ℝ (a + (1 : ℝ) • (b - a)) b
      · rw [segment_eq_image']
        have h1 : 0 < 1 - t := by linarith
        refine ⟨(s - t) / (1 - t), ⟨div_nonneg (by linarith) h1.le, (div_le_one h1).2 (by linarith)⟩, ?_⟩
        simp only []
        have : b - (a + t • (b - a)) = (1 - t) • (b - a) := by module
        rw [this, smul_smul, div_mul_cancel₀ _ h1.ne']
        module

/-- Inserting a point of an edge into a chain does not change its set. -/
lemma chainSet_insert (l₁ l₂ : List (ℝ × ℝ)) (a b : ℝ × ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    chainSet (l₁ ++ a :: (a + t • (b - a)) :: b :: l₂) = chainSet (l₁ ++ a :: b :: l₂) := by
  rw [chainSet_append l₁ a ((a + t • (b - a)) :: b :: l₂), chainSet_append l₁ a (b :: l₂)]
  congr 1
  simp only [chainSet]
  rw [← segment_split_union a b ht0 ht1]
  ext z; simp only [mem_union]; tauto

lemma carrier_ofList_closed (L : List (ℝ × ℝ)) [NeZero L.length] (h2 : 2 ≤ L.length) :
    (Polygon.ofList L).carrier = chainSet (L ++ [L.getD 0 0]) := by
  obtain ⟨a, l, z, rfl⟩ : ∃ a l z, L = a :: l ++ [z] := by
    match L, h2 with
    | a :: t, h =>
      rcases List.eq_nil_or_concat t with rfl | ⟨l, z, rfl⟩
      · simp at h
      · exact ⟨a, l, z, by simp⟩
  rw [carrier_ofList]
  have e : (a :: l ++ [z]).getD 0 0 = a := by simp
  have e2 : chainSet ((a :: l ++ [z]) ++ [a]) = chainSet (a :: l ++ [z]) ∪ segment ℝ z a := by
    have := chainSet_append (a :: l) z [a]
    rw [chainSet_pair z a] at this
    simpa using this
  rw [e, e2]

/-- **Inserting a point of an edge as a vertex does not change the carrier or the inside of the polygon.** -/
theorem ofList_insert (l₁ l₂ : List (ℝ × ℝ)) (a b : ℝ × ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    [NeZero (l₁ ++ a :: b :: l₂).length] [NeZero (l₁ ++ a :: (a + t • (b - a)) :: b :: l₂).length] :
    (Polygon.ofList (l₁ ++ a :: (a + t • (b - a)) :: b :: l₂)).carrier = (Polygon.ofList (l₁ ++ a :: b :: l₂)).carrier ∧
    (Polygon.ofList (l₁ ++ a :: (a + t • (b - a)) :: b :: l₂)).inside = (Polygon.ofList (l₁ ++ a :: b :: l₂)).inside := by
  have h2 : 2 ≤ (l₁ ++ a :: b :: l₂).length := by simp only [List.length_append, List.length_cons]; omega
  have h2' : 2 ≤ (l₁ ++ a :: (a + t • (b - a)) :: b :: l₂).length := by simp only [List.length_append, List.length_cons]; omega
  have hh : (l₁ ++ a :: (a + t • (b - a)) :: b :: l₂).getD 0 0 = (l₁ ++ a :: b :: l₂).getD 0 0 := by
    cases l₁ <;> simp
  constructor
  · have e1 := carrier_ofList_closed (l₁ ++ a :: b :: l₂) h2
    have e2 := carrier_ofList_closed (l₁ ++ a :: (a + t • (b - a)) :: b :: l₂) h2'
    rw [e2, e1, hh]
    have := chainSet_insert l₁ (l₂ ++ [(l₁ ++ a :: b :: l₂).getD 0 0]) a b ht0 ht1
    simpa using this
  · ext y
    simp only [Polygon.inside, mem_ofPred_eq]
    have hc : (Polygon.ofList (l₁ ++ a :: (a + t • (b - a)) :: b :: l₂)).carrier =
        (Polygon.ofList (l₁ ++ a :: b :: l₂)).carrier := by
      have e1 := carrier_ofList_closed (l₁ ++ a :: b :: l₂) h2
      have e2 := carrier_ofList_closed (l₁ ++ a :: (a + t • (b - a)) :: b :: l₂) h2'
      rw [e2, e1, hh]
      have := chainSet_insert l₁ (l₂ ++ [(l₁ ++ a :: b :: l₂).getD 0 0]) a b ht0 ht1
      simpa using this
    have hp1 := Polygon.parity_ofList (l₁ ++ a :: b :: l₂) y 0 h2
    have hp2 := Polygon.parity_ofList (l₁ ++ a :: (a + t • (b - a)) :: b :: l₂) y 0 h2'
    have hpar : (Polygon.ofList (l₁ ++ a :: (a + t • (b - a)) :: b :: l₂)).parity y =
        (Polygon.ofList (l₁ ++ a :: b :: l₂)).parity y := by
      rw [hp1, hp2, hh]
      have := chainParity_insert y l₁ (l₂ ++ [(l₁ ++ a :: b :: l₂).getD 0 0]) a b ht0 ht1
      simpa using this
    rw [hc, hpar]

end Lightlike.PL
