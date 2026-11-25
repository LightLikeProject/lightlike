import Mathlib
import Lightlike.PL.Schoenflies.GoodQuad
import Lightlike.PL.Schoenflies.Glue
import Lightlike.PL.Schoenflies.QuadSplit
import Lightlike.PL.Schoenflies.CycPolygon
import Lightlike.PL.ChainCarrier
import Lightlike.PL.Schoenflies.RegionExtension

/-!
# Boundary maps of good cells

Row G3-188 (PL5), ring cells.  `quad_boundary_bijOn`: given a continuous bijection on each of the four sides of a good
cell onto the corresponding side of another good cell, agreeing at the corners, the four maps glue to a
continuous bijection of the boundary `α ∪ σ' ∪ β ∪ σ` onto the boundary of the other cell.
-/

open Set

namespace Lightlike.PL.Schoenflies

open Lightlike.PL

lemma isCompact_chainSet' : ∀ l : List (ℝ × ℝ), IsCompact (chainSet l)
  | [] => by simp [chainSet]
  | [a] => by simp [chainSet]
  | a :: b :: l => by
    simp only [chainSet]
    exact (isCompact_segment' a b).union (isCompact_chainSet' (b :: l))

lemma glue_two {f g : ℝ × ℝ → ℝ × ℝ} {A B A' B' S S' : Set (ℝ × ℝ)} (hA : BijOn f A A') (hB : BijOn g B B')
    (hAB : A ∩ B = S) (hAB' : A' ∩ B' = S') (hfg : ∀ x ∈ S, f x = g x) (hS : S' ⊆ g '' S) :
    ∃ F : ℝ × ℝ → ℝ × ℝ, BijOn F (A ∪ B) (A' ∪ B') ∧ EqOn F f A ∧ EqOn F g B := by
  refine exists_bijOn_union_glue hA hB (fun x hx => hfg x (hAB ▸ hx)) ?_
  rw [hAB, hAB']; exact hS

theorem quad_boundary_bijOn {w w' v v' w₂ w₂' v₂ v₂' : ℝ × ℝ} {α β α₂ β₂ : List (ℝ × ℝ)}
    (hQ : GoodQuad w w' v v' α β) (hQ₂ : GoodQuad w₂ w₂' v₂ v₂' α₂ β₂)
    {fa fb fs fs' : ℝ × ℝ → ℝ × ℝ}
    (ha : BijOn fa (chainSet α) (chainSet α₂)) (hb : BijOn fb (chainSet β) (chainSet β₂))
    (hs : BijOn fs (segment ℝ w v) (segment ℝ w₂ v₂))
    (hs' : BijOn fs' (segment ℝ w' v') (segment ℝ w₂' v₂'))
    (haw : fa w = w₂) (haw' : fa w' = w₂') (hbv : fb v = v₂) (hbv' : fb v' = v₂')
    (hsw : fs w = w₂) (hsv : fs v = v₂) (hsw' : fs' w' = w₂') (hsv' : fs' v' = v₂') :
    ∃ F : ℝ × ℝ → ℝ × ℝ,
      BijOn F (chainSet α ∪ segment ℝ w' v' ∪ chainSet β ∪ segment ℝ w v)
        (chainSet α₂ ∪ segment ℝ w₂' v₂' ∪ chainSet β₂ ∪ segment ℝ w₂ v₂) ∧
      EqOn F fa (chainSet α) ∧ EqOn F fb (chainSet β) ∧ EqOn F fs (segment ℝ w v) ∧
      EqOn F fs' (segment ℝ w' v') := by
  have wα : w ∈ chainSet α := mem_chainSet_of_head hQ.headα
  have w'α : w' ∈ chainSet α := mem_chainSet_of_getLast hQ.lastα
  have vβ : v ∈ chainSet β := mem_chainSet_of_head hQ.headβ
  have v'β : v' ∈ chainSet β := mem_chainSet_of_getLast hQ.lastβ
  have wα₂ : w₂ ∈ chainSet α₂ := mem_chainSet_of_head hQ₂.headα
  have w'α₂ : w₂' ∈ chainSet α₂ := mem_chainSet_of_getLast hQ₂.lastα
  have vβ₂ : v₂ ∈ chainSet β₂ := mem_chainSet_of_head hQ₂.headβ
  have v'β₂ : v₂' ∈ chainSet β₂ := mem_chainSet_of_getLast hQ₂.lastβ
  have eps : ∀ {a b : ℝ × ℝ}, a ∈ segment ℝ a b ∧ b ∈ segment ℝ a b :=
    fun {a b} => ⟨left_mem_segment ℝ a b, right_mem_segment ℝ a b⟩
  -- step 1: `α ∪ σ'`
  have i1 : chainSet α ∩ segment ℝ w' v' = {w'} := by rw [inter_comm]; exact hQ.sw'
  have i1' : chainSet α₂ ∩ segment ℝ w₂' v₂' = {w₂'} := by rw [inter_comm]; exact hQ₂.sw'
  obtain ⟨F1, hF1, hF1a, hF1s⟩ := glue_two ha hs' i1 i1'
    (by intro x hx; rw [mem_singleton_iff.1 hx, haw', hsw'])
    (by rintro y hy; rw [mem_singleton_iff.1 hy]; exact ⟨w', rfl, hsw'⟩)
  -- step 2: `(α ∪ σ') ∪ β`
  have i2 : (chainSet α ∪ segment ℝ w' v') ∩ chainSet β = {v'} := by
    ext x; constructor
    · rintro ⟨hx | hx, hxb⟩
      · have : x ∈ chainSet α ∩ chainSet β := ⟨hx, hxb⟩
        rw [hQ.disj] at this; exact this.elim
      · have : x ∈ segment ℝ w' v' ∩ chainSet β := ⟨hx, hxb⟩
        rw [hQ.sv'] at this; exact this
    · intro hx; rw [mem_singleton_iff.1 hx]; exact ⟨Or.inr eps.2, v'β⟩
  have i2' : (chainSet α₂ ∪ segment ℝ w₂' v₂') ∩ chainSet β₂ = {v₂'} := by
    ext x; constructor
    · rintro ⟨hx | hx, hxb⟩
      · have : x ∈ chainSet α₂ ∩ chainSet β₂ := ⟨hx, hxb⟩
        rw [hQ₂.disj] at this; exact this.elim
      · have : x ∈ segment ℝ w₂' v₂' ∩ chainSet β₂ := ⟨hx, hxb⟩
        rw [hQ₂.sv'] at this; exact this
    · intro hx; rw [mem_singleton_iff.1 hx]; exact ⟨Or.inr eps.2, v'β₂⟩
  obtain ⟨F2, hF2, hF2a, hF2b⟩ := glue_two hF1 hb i2 i2'
    (by intro x hx; rw [mem_singleton_iff.1 hx, hbv', hF1s eps.2, hsv'])
    (by rintro y hy; rw [mem_singleton_iff.1 hy]; exact ⟨v', rfl, hbv'⟩)
  -- step 3: `((α ∪ σ') ∪ β) ∪ σ`
  have i3 : ((chainSet α ∪ segment ℝ w' v') ∪ chainSet β) ∩ segment ℝ w v = {w, v} := by
    ext x; constructor
    · rintro ⟨(hx | hx) | hx, hxs⟩
      · have : x ∈ segment ℝ w v ∩ chainSet α := ⟨hxs, hx⟩
        rw [hQ.sw] at this; exact Or.inl this
      · exact (Set.disjoint_left.1 hQ.ss hxs hx).elim
      · have : x ∈ segment ℝ w v ∩ chainSet β := ⟨hxs, hx⟩
        rw [hQ.sv] at this; exact Or.inr this
    · rintro (rfl | rfl)
      · exact ⟨Or.inl (Or.inl wα), eps.1⟩
      · exact ⟨Or.inr vβ, eps.2⟩
  have i3' : ((chainSet α₂ ∪ segment ℝ w₂' v₂') ∪ chainSet β₂) ∩ segment ℝ w₂ v₂ = {w₂, v₂} := by
    ext x; constructor
    · rintro ⟨(hx | hx) | hx, hxs⟩
      · have : x ∈ segment ℝ w₂ v₂ ∩ chainSet α₂ := ⟨hxs, hx⟩
        rw [hQ₂.sw] at this; exact Or.inl this
      · exact (Set.disjoint_left.1 hQ₂.ss hxs hx).elim
      · have : x ∈ segment ℝ w₂ v₂ ∩ chainSet β₂ := ⟨hxs, hx⟩
        rw [hQ₂.sv] at this; exact Or.inr this
    · rintro (rfl | rfl)
      · exact ⟨Or.inl (Or.inl wα₂), eps.1⟩
      · exact ⟨Or.inr vβ₂, eps.2⟩
  obtain ⟨F3, hF3, hF3a, hF3s⟩ := glue_two hF2 hs i3 i3'
    (by
      rintro x (rfl | rfl)
      · rw [hsw, hF2a (Or.inl wα), hF1a wα, haw]
      · rw [hsv, hF2b vβ, hbv])
    (by rintro y (rfl | rfl)
        · exact ⟨w, Or.inl rfl, hsw⟩
        · exact ⟨v, Or.inr rfl, hsv⟩)
  refine ⟨F3, hF3, ?_, ?_, hF3s, ?_⟩
  · intro x hx; rw [hF3a (Or.inl (Or.inl hx)), hF2a (Or.inl hx), hF1a hx]
  · intro x hx; rw [hF3a (Or.inr hx), hF2b hx]
  · intro x hx; rw [hF3a (Or.inl (Or.inr hx)), hF2a (Or.inr hx), hF1s hx]

/-- **A continuous bijection of compact sets is a homeomorphism.** -/
theorem exists_homeo_of_bijOn {A A' : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℝ × ℝ} (hA : IsCompact A)
    (hc : ContinuousOn F A) (hb : BijOn F A A') :
    ∃ e : A ≃ₜ A', ∀ (x : ℝ × ℝ) (hx : x ∈ A), (e ⟨x, hx⟩ : ℝ × ℝ) = F x := by
  have hcont : Continuous (hb.mapsTo.restrict F _ _) := hc.mapsToRestrict hb.mapsTo
  have : CompactSpace A := isCompact_iff_compactSpace.1 hA
  exact ⟨hcont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ hb.bijective), fun x hx => rfl⟩

/-- **The polygon of a good cell is simple, with the four sides as carrier.** -/
theorem GoodQuad.polygon {w w' v v' : ℝ × ℝ} {α β : List (ℝ × ℝ)} (h : GoodQuad w w' v v' α β)
    [NeZero (quadList α β).length] :
    3 ≤ (quadList α β).length ∧ (Polygon.ofList (quadList α β)).IsSimple ∧
      (Polygon.ofList (quadList α β)).carrier =
        chainSet α ∪ segment ℝ w' v' ∪ chainSet β ∪ segment ℝ w v := by
  have hrev1 : ((β).reverse).head? = some v' := by rw [List.head?_reverse]; exact h.lastβ
  have hA := simple_append_spoke (w := w') (v := v') h.simpα (isSimpleChain_reverse h.simpβ) h.lastα hrev1
    h.sw' (by rw [chainSet_reverse]; exact h.sv') (by rw [chainSet_reverse]; exact h.disj)
  rw [chainSet_reverse] at hA
  obtain ⟨hs, hset⟩ := hA
  have wα : w ∈ chainSet α := mem_chainSet_of_head h.headα
  have vβ : v ∈ chainSet β := mem_chainSet_of_head h.headβ
  have hwv : w ≠ v := by
    intro e
    have : w ∈ chainSet α ∩ chainSet β := ⟨wα, e ▸ vβ⟩
    rw [h.disj] at this; exact this
  have hhead : (α ++ β.reverse).head? = some w := by
    have := h.headα
    cases α with
    | nil => simp at this
    | cons x t => simpa using this
  have hlast : (α ++ β.reverse).getLast? = some v := by
    rw [List.getLast?_append_of_ne_nil]
    · rw [List.getLast?_reverse]; exact h.headβ
    · intro e
      have hb := h.headβ
      have e' : β = [] := by simpa using e
      subst e'; simp at hb
  obtain ⟨l, hl⟩ := eq_cons_append_of hhead hlast hwv
  have hcl : segment ℝ v w ∩ chainSet (w :: l ++ [v]) = {w, v} := by
    rw [← hl, hset, segment_symm ℝ v w]
    ext x; constructor
    · rintro ⟨hxs, (hx | hx) | hx⟩
      · have : x ∈ segment ℝ w v ∩ chainSet α := ⟨hxs, hx⟩
        rw [h.sw] at this; exact Or.inl this
      · exact (Set.disjoint_left.1 h.ss hxs hx).elim
      · have : x ∈ segment ℝ w v ∩ chainSet β := ⟨hxs, hx⟩
        rw [h.sv] at this; exact Or.inr this
    · rintro (rfl | rfl)
      · exact ⟨left_mem_segment ℝ _ _, Or.inl (Or.inl wα)⟩
      · exact ⟨right_mem_segment ℝ _ _, Or.inr vβ⟩
  have hlen : 3 ≤ (w :: l ++ [v]).length := by
    have : (w :: l ++ [v]).length = (α ++ β.reverse).length := by rw [← hl]
    rw [this]
    have h1 : 2 ≤ (α ++ β.reverse).length := by
      by_contra hlt
      push Not at hlt
      have : (w :: l ++ [v]).length ≥ 2 := by simp
      omega
    rcases h1.eq_or_lt with h2 | h3
    · exfalso
      have hαne : α ≠ [] := by intro e; have := h.headα; rw [e] at this; simp at this
      have hβne : β ≠ [] := by intro e; have := h.headβ; rw [e] at this; simp at this
      have hαpos : 0 < α.length := List.length_pos_iff.2 hαne
      have hβpos : 0 < β.length := List.length_pos_iff.2 hβne
      have hlen2 : α.length + β.length = 2 := by simpa using h2.symm
      obtain ⟨a₀, rfl⟩ : ∃ a₀, α = [a₀] := List.length_eq_one_iff.1 (by omega)
      have e1 : a₀ = w := by simpa using h.headα
      have e2 : a₀ = w' := by simpa using h.lastα
      have : w ∈ segment ℝ w v := left_mem_segment ℝ w v
      have : w ∈ segment ℝ w' v' := by rw [← e1, e2]; exact left_mem_segment ℝ w' v'
      exact Set.disjoint_left.1 h.ss (left_mem_segment ℝ w v) this
    · exact h3
  have hsimple := isSimple_ofList (l := l) (a := w) (b := v) hlen (by rw [← hl]; exact hs) hwv hcl
  have e : quadList α β = w :: l ++ [v] := hl
  have iA : NeZero (w :: l ++ [v]).length := ⟨by simp⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [quadList, hl]; exact hlen
  · rw [quadList, hl]; exact hsimple
  · rw [quadList, hl, carrier_ofList]
    rw [← hl, hset, segment_symm ℝ v w]

/-- **A good cell is mapped homeomorphically onto another by any compatible maps of its four sides.** The
homeomorphism restricts to the given map on each of the four sides. -/
theorem GoodQuad.extend' {w w' v v' w₂ w₂' v₂ v₂' : ℝ × ℝ} {α β α₂ β₂ : List (ℝ × ℝ)}
    (hQ : GoodQuad w w' v v' α β) (hQ₂ : GoodQuad w₂ w₂' v₂ v₂' α₂ β₂)
    [NeZero (quadList α β).length] [NeZero (quadList α₂ β₂).length]
    {fa fb fs fs' : ℝ × ℝ → ℝ × ℝ}
    (ha : BijOn fa (chainSet α) (chainSet α₂)) (hb : BijOn fb (chainSet β) (chainSet β₂))
    (hs : BijOn fs (segment ℝ w v) (segment ℝ w₂ v₂))
    (hs' : BijOn fs' (segment ℝ w' v') (segment ℝ w₂' v₂'))
    (hca : ContinuousOn fa (chainSet α)) (hcb : ContinuousOn fb (chainSet β))
    (hcs : ContinuousOn fs (segment ℝ w v)) (hcs' : ContinuousOn fs' (segment ℝ w' v'))
    (haw : fa w = w₂) (haw' : fa w' = w₂') (hbv : fb v = v₂) (hbv' : fb v' = v₂')
    (hsw : fs w = w₂) (hsv : fs v = v₂) (hsw' : fs' w' = w₂') (hsv' : fs' v' = v₂') :
    ∃ E : region (Polygon.ofList (quadList α β)) ≃ₜ region (Polygon.ofList (quadList α₂ β₂)),
      (∀ x (hx : x ∈ region (Polygon.ofList (quadList α β))), x ∈ chainSet α → (E ⟨x, hx⟩ : ℝ × ℝ) = fa x) ∧
      (∀ x (hx : x ∈ region (Polygon.ofList (quadList α β))), x ∈ chainSet β → (E ⟨x, hx⟩ : ℝ × ℝ) = fb x) ∧
      (∀ x (hx : x ∈ region (Polygon.ofList (quadList α β))), x ∈ segment ℝ w v → (E ⟨x, hx⟩ : ℝ × ℝ) = fs x) ∧
      (∀ x (hx : x ∈ region (Polygon.ofList (quadList α β))), x ∈ segment ℝ w' v' →
        (E ⟨x, hx⟩ : ℝ × ℝ) = fs' x) := by
  obtain ⟨hn, hsimp, hcar⟩ := hQ.polygon
  obtain ⟨hn₂, hsimp₂, hcar₂⟩ := hQ₂.polygon
  obtain ⟨F, hF, hFa, hFb, hFs, hFs'⟩ := quad_boundary_bijOn hQ hQ₂ ha hb hs hs' haw haw' hbv hbv' hsw hsv hsw' hsv'
  have cα := isCompact_chainSet' α
  have cβ := isCompact_chainSet' β
  have cσ := isCompact_segment' w v
  have cσ' := isCompact_segment' w' v'
  have hcF : ContinuousOn F (chainSet α ∪ segment ℝ w' v' ∪ chainSet β ∪ segment ℝ w v) := by
    refine ((((hca.congr hFa).union_of_isClosed (hcs'.congr hFs') cα.isClosed cσ'.isClosed).union_of_isClosed
      (hcb.congr hFb) (cα.union cσ').isClosed cβ.isClosed).union_of_isClosed (hcs.congr hFs)
      ((cα.union cσ').union cβ).isClosed cσ.isClosed)
  obtain ⟨ψ, hψ⟩ := exists_homeo_of_bijOn (((cα.union cσ').union cβ).union cσ) hcF hF
  have e1 : (Polygon.ofList (quadList α β)).carrier = chainSet α ∪ segment ℝ w' v' ∪ chainSet β ∪ segment ℝ w v := hcar
  have e2 : (Polygon.ofList (quadList α₂ β₂)).carrier =
      chainSet α₂ ∪ segment ℝ w₂' v₂' ∪ chainSet β₂ ∪ segment ℝ w₂ v₂ := hcar₂
  obtain ⟨E, hE⟩ := boundary_homeo_extends hn hn₂ hsimp hsimp₂
    ((Homeomorph.setCongr e1).trans (ψ.trans (Homeomorph.setCongr e2.symm)))
  have key : ∀ (x : ℝ × ℝ) (hx : x ∈ region (Polygon.ofList (quadList α β))),
      x ∈ chainSet α ∪ segment ℝ w' v' ∪ chainSet β ∪ segment ℝ w v → (E ⟨x, hx⟩ : ℝ × ℝ) = F x := by
    intro x hx hxK
    have hx' : x ∈ (Polygon.ofList (quadList α β)).carrier := by rw [e1]; exact hxK
    have := hE x hx'
    have e : (⟨x, hx⟩ : region (Polygon.ofList (quadList α β))) = ⟨x, carrier_subset_region _ hx'⟩ := rfl
    rw [e, this]
    simp only [Homeomorph.trans_apply]
    show (ψ ⟨x, _⟩ : ℝ × ℝ) = F x
    exact hψ x hxK
  refine ⟨E, fun x hx hxa => ?_, fun x hx hxb => ?_, fun x hx hxs => ?_, fun x hx hxs => ?_⟩
  · rw [key x hx (Or.inl (Or.inl (Or.inl hxa))), hFa hxa]
  · rw [key x hx (Or.inl (Or.inr hxb)), hFb hxb]
  · rw [key x hx (Or.inr hxs), hFs hxs]
  · rw [key x hx (Or.inl (Or.inl (Or.inr hxs))), hFs' hxs]

end Lightlike.PL.Schoenflies
