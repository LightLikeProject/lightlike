import Lightlike.PL.TwoArcs
import Lightlike.PL.Theta
import Lightlike.PL.Interlaced
import Lightlike.PL.Schoenflies.EarSplit

/-!
# Splitting a simple polygon along a polygonal chord

Row G3-188, milestone PL5 (third pass), item 5c (annulus lemma, step 2).  `Polygon.inside_split` cuts a
simple polygon along a straight diagonal between two vertices.  Here the chord is a simple polygonal
arc `E` from `a` to `b`: the polygon `C` is made of two simple arcs `A₁` (from `a` to `b`) and `A₂` (from
`b` to `a`), the arcs meet only in `a, b`, and `E` meets `A₁ ∪ A₂` only in `a, b`, with the open chord
inside `C`.  Then `C₁ = A₁ ∪ E` and `C₂ = A₂ ∪ E` are simple polygons, their insides are disjoint, and
`inside C = inside C₁ ∪ inside C₂ ∪ (E \ {a, b})`.

* `inside_split_chain`: the statement above.
* `region_split_chain`: the closed regions satisfy `region C = region C₁ ∪ region C₂`.
-/

open Set Lightlike.PL.Polygon

namespace Lightlike.PL.Schoenflies

open Lightlike.PL

/-- **Splitting the inside of a simple polygon along a polygonal chord.** -/
theorem inside_split_chain {a b : ℝ × ℝ} {m₁ m₂ mₑ : List (ℝ × ℝ)} (hab : a ≠ b)
    (h₁ : IsSimpleChain (a :: m₁ ++ [b])) (h₂ : IsSimpleChain (b :: m₂ ++ [a]))
    (hₑ : IsSimpleChain (a :: mₑ ++ [b]))
    (h₁₂ : chainSet (a :: m₁ ++ [b]) ∩ chainSet (b :: m₂ ++ [a]) = {a, b})
    (h₁ₑ : chainSet (a :: m₁ ++ [b]) ∩ chainSet (a :: mₑ ++ [b]) = {a, b})
    (h₂ₑ : chainSet (b :: m₂ ++ [a]) ∩ chainSet (a :: mₑ ++ [b]) = {a, b})
    (hD : chainSet (a :: mₑ ++ [b]) \ {a, b} ⊆ (Polygon.ofList (a :: m₁ ++ b :: m₂)).inside) :
    Disjoint (Polygon.ofList (a :: m₁ ++ b :: mₑ.reverse)).inside
        (Polygon.ofList (b :: m₂ ++ a :: mₑ)).inside ∧
      (Polygon.ofList (a :: m₁ ++ b :: m₂)).inside =
        (Polygon.ofList (a :: m₁ ++ b :: mₑ.reverse)).inside ∪
          (Polygon.ofList (b :: m₂ ++ a :: mₑ)).inside ∪ (chainSet (a :: mₑ ++ [b]) \ {a, b}) := by
  classical
  set A₁ := chainSet (a :: m₁ ++ [b]) with hA₁
  set A₂ := chainSet (b :: m₂ ++ [a]) with hA₂
  set E := chainSet (a :: mₑ ++ [b]) with hE
  set C := Polygon.ofList (a :: m₁ ++ b :: m₂) with hC
  set L := Polygon.ofList (a :: m₁ ++ b :: mₑ.reverse) with hL
  set R := Polygon.ofList (b :: m₂ ++ a :: mₑ) with hR
  have iC : NeZero (a :: m₁ ++ b :: m₂).length := ⟨by simp⟩
  have iL : NeZero (a :: m₁ ++ b :: mₑ.reverse).length := ⟨by simp⟩
  have iR : NeZero (b :: m₂ ++ a :: mₑ).length := ⟨by simp⟩
  have hrev : (a :: mₑ ++ [b]).reverse = b :: mₑ.reverse ++ [a] := by simp
  have hEr : IsSimpleChain (b :: mₑ.reverse ++ [a]) := hrev ▸ isSimpleChain_reverse hₑ
  have hEs : chainSet (b :: mₑ.reverse ++ [a]) = E := by
    rw [← hrev, chainSet_reverse]
  have sC : C.IsSimple := isSimple_two_arcs h₁ h₂ h₁₂ hab
  have sL : L.IsSimple := isSimple_two_arcs h₁ hEr (by rw [hEs]; exact h₁ₑ) hab
  have sR : R.IsSimple := isSimple_two_arcs (a := b) (b := a) h₂ hₑ
    (by rw [Set.pair_comm]; exact h₂ₑ) hab.symm
  have cC : C.carrier = A₁ ∪ A₂ := carrier_two_arcs a b m₁ m₂
  have cL : L.carrier = A₁ ∪ E := by
    have := carrier_two_arcs a b m₁ mₑ.reverse
    rw [hEs] at this; exact this
  have cR : R.carrier = A₂ ∪ E := carrier_two_arcs b a m₂ mₑ
  have hadd : ∀ x, L.parity x + R.parity x = C.parity x := fun z => parity_theta a b z m₁ m₂ mₑ
  have haA₁ : a ∈ A₁ := mem_chainSet_head a _
  have hbA₁ : b ∈ A₁ := mem_chainSet_last (a :: m₁) b
  have hEab : E ⊆ (E \ {a, b}) ∪ A₁ := by
    intro x hx
    by_cases h : x ∈ ({a, b} : Set (ℝ × ℝ))
    · exact Or.inr (by rcases h with rfl | rfl <;> assumption)
    · exact Or.inl ⟨hx, h⟩
  have hz : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  have hoff : ∀ x, x ∉ C.carrier → x ∉ E \ {a, b} → x ∉ L.carrier ∧ x ∉ R.carrier := by
    intro x hx1 hx2
    rw [cC, mem_union, not_or] at hx1
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [cL] at h
      rcases h with h | h
      · exact hx1.1 h
      · rcases hEab h with h' | h'
        · exact hx2 h'
        · exact hx1.1 h'
    · rw [cR] at h
      rcases h with h | h
      · exact hx1.2 h
      · rcases hEab h with h' | h'
        · exact hx2 h'
        · exact hx1.1 h'
  have hCL : ∀ x, x ∈ C.carrier → x ∈ L.carrier ∨ x ∈ R.carrier := by
    intro x hx
    rw [cC] at hx
    rcases hx with h | h
    · exact Or.inl (by rw [cL]; exact Or.inl h)
    · exact Or.inr (by rw [cR]; exact Or.inl h)
  have hLC : ∀ x, x ∈ L.carrier → x ∈ C.carrier ∨ x ∈ E \ {a, b} := by
    intro x hx
    rw [cL] at hx
    rcases hx with h | h
    · exact Or.inl (by rw [cC]; exact Or.inl h)
    · rcases hEab h with h' | h'
      · exact Or.inr h'
      · exact Or.inl (by rw [cC]; exact Or.inl h')
  have hRC : ∀ x, x ∈ R.carrier → x ∈ C.carrier ∨ x ∈ E \ {a, b} := by
    intro x hx
    rw [cR] at hx
    rcases hx with h | h
    · exact Or.inl (by rw [cC]; exact Or.inr h)
    · rcases hEab h with h' | h'
      · exact Or.inr h'
      · exact Or.inl (by rw [cC]; exact Or.inl h')
  -- the open chord is off the carriers of the two parts only through `E`; it lies in `C.inside`
  have hbothin : ∀ x, x ∈ L.inside → x ∈ R.inside → x ∈ C.outside := by
    intro x h1 h2
    have hxc : x ∉ C.carrier := fun hc => by
      rcases hCL x hc with h | h
      · exact h1.1 h
      · exact h2.1 h
    refine ⟨hxc, ?_⟩
    rw [← hadd, h1.2, h2.2]; decide
  have hout : ∀ x, x ∈ C.outside → (x ∈ L.outside ∧ x ∈ R.outside) ∨
      (x ∈ L.inside ∧ x ∈ R.inside) := by
    intro x hx
    have hxD : x ∉ E \ {a, b} := fun h =>
      (Set.disjoint_left.1 (Polygon.disjoint_outside_inside C)) hx (hD h)
    obtain ⟨hxL, hxR⟩ := hoff x hx.1 hxD
    have hadd' := hadd x
    rw [hx.2] at hadd'
    rcases hz (L.parity x) with h1 | h1 <;> rcases hz (R.parity x) with h2 | h2
    · exact Or.inl ⟨⟨hxL, h1⟩, ⟨hxR, h2⟩⟩
    · rw [h1, h2] at hadd'; exact absurd hadd' (by decide)
    · rw [h1, h2] at hadd'; exact absurd hadd' (by decide)
    · exact Or.inr ⟨⟨hxL, h1⟩, ⟨hxR, h2⟩⟩
  have hdisj : Disjoint L.inside R.inside := by
    rw [Set.disjoint_left]
    intro x hxL hxR
    have hpre : IsPreconnected C.outside := Polygon.isPreconnected_outside sC
    have hO : IsOpen (L.outside ∩ R.outside) :=
      (Polygon.isOpen_outside L).inter (Polygon.isOpen_outside R)
    have hW : IsOpen (L.inside ∩ R.inside) :=
      (Polygon.isOpen_inside L).inter (Polygon.isOpen_inside R)
    have hdj : Disjoint (L.outside ∩ R.outside) (L.inside ∩ R.inside) := by
      rw [Set.disjoint_left]
      rintro y ⟨hy1, -⟩ ⟨hy2, -⟩
      exact (Set.disjoint_left.1 (Polygon.disjoint_outside_inside L)) hy1 hy2
    have hcov : C.outside ⊆ (L.outside ∩ R.outside) ∪ (L.inside ∩ R.inside) := fun y hy => by
      rcases hout y hy with h | h
      · exact Or.inl h
      · exact Or.inr h
    rcases hpre.subset_or_subset hO hW hdj hcov with h | h
    · exact (Set.disjoint_left.1 (Polygon.disjoint_outside_inside L))
        ((h (hbothin x hxL hxR)).1) hxL
    · exact Polygon.not_isBounded_outside C
        ((Polygon.isBounded_inside L).subset (fun y hy => (h hy).1))
  have hcross1 : ∀ y, y ∈ L.inside → y ∉ R.carrier := by
    intro y hy hyc
    have hcl := Polygon.carrier_subset_closure_class sR 1 hyc
    obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 hcl _ (Polygon.isOpen_inside L) hy
    exact Set.disjoint_left.1 hdisj hz1 hz2
  have hcross2 : ∀ y, y ∈ R.inside → y ∉ L.carrier := by
    intro y hy hyc
    have hcl := Polygon.carrier_subset_closure_class sL 1 hyc
    obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 hcl _ (Polygon.isOpen_inside R) hy
    exact Set.disjoint_left.1 hdisj hz2 hz1
  refine ⟨hdisj, ?_⟩
  ext x
  constructor
  · intro hx
    by_cases hxD : x ∈ E \ {a, b}
    · exact Or.inr hxD
    · obtain ⟨hxL, hxR⟩ := hoff x hx.1 hxD
      have hadd' := hadd x
      rw [hx.2] at hadd'
      rcases hz (L.parity x) with h1 | h1 <;> rcases hz (R.parity x) with h2 | h2
      · rw [h1, h2] at hadd'; exact absurd hadd' (by decide)
      · exact Or.inl (Or.inr ⟨hxR, h2⟩)
      · exact Or.inl (Or.inl ⟨hxL, h1⟩)
      · rw [h1, h2] at hadd'; exact absurd hadd' (by decide)
  · rintro ((hx | hx) | hx)
    · have hxR : x ∉ R.carrier := hcross1 x hx
      have hxp : x ∉ C.carrier := fun hc => by
        rcases hCL x hc with h | h
        · exact hx.1 h
        · exact hxR h
      refine ⟨hxp, ?_⟩
      have hr0 : R.parity x = 0 := by
        rcases hz (R.parity x) with h | h
        · exact h
        · exact absurd ⟨hxR, h⟩ (fun hh => Set.disjoint_left.1 hdisj hx hh)
      rw [← hadd, hx.2, hr0]; decide
    · have hxL : x ∉ L.carrier := hcross2 x hx
      have hxp : x ∉ C.carrier := fun hc => by
        rcases hCL x hc with h | h
        · exact hxL h
        · exact hx.1 h
      refine ⟨hxp, ?_⟩
      have hl0 : L.parity x = 0 := by
        rcases hz (L.parity x) with h | h
        · exact h
        · exact absurd ⟨hxL, h⟩ (fun hh => Set.disjoint_left.1 hdisj hh hx)
      rw [← hadd, hx.2, hl0]; decide
    · exact hD hx

/-- **Splitting the closed region of a simple polygon along a polygonal chord.** The closed region of `C`
is the union of the closed regions of the two parts, and these meet exactly in the closed chord. -/
theorem region_split_chain {a b : ℝ × ℝ} {m₁ m₂ mₑ : List (ℝ × ℝ)} (hab : a ≠ b)
    (h₁ : IsSimpleChain (a :: m₁ ++ [b])) (h₂ : IsSimpleChain (b :: m₂ ++ [a]))
    (hₑ : IsSimpleChain (a :: mₑ ++ [b]))
    (h₁₂ : chainSet (a :: m₁ ++ [b]) ∩ chainSet (b :: m₂ ++ [a]) = {a, b})
    (h₁ₑ : chainSet (a :: m₁ ++ [b]) ∩ chainSet (a :: mₑ ++ [b]) = {a, b})
    (h₂ₑ : chainSet (b :: m₂ ++ [a]) ∩ chainSet (a :: mₑ ++ [b]) = {a, b})
    (hD : chainSet (a :: mₑ ++ [b]) \ {a, b} ⊆ (Polygon.ofList (a :: m₁ ++ b :: m₂)).inside) :
    region (Polygon.ofList (a :: m₁ ++ b :: m₂)) =
        region (Polygon.ofList (a :: m₁ ++ b :: mₑ.reverse)) ∪
          region (Polygon.ofList (b :: m₂ ++ a :: mₑ)) ∧
      region (Polygon.ofList (a :: m₁ ++ b :: mₑ.reverse)) ∩
          region (Polygon.ofList (b :: m₂ ++ a :: mₑ)) = chainSet (a :: mₑ ++ [b]) := by
  classical
  obtain ⟨hdisj, hin⟩ := inside_split_chain hab h₁ h₂ hₑ h₁₂ h₁ₑ h₂ₑ hD
  have hrev : (a :: mₑ ++ [b]).reverse = b :: mₑ.reverse ++ [a] := by simp
  have hEr : IsSimpleChain (b :: mₑ.reverse ++ [a]) := hrev ▸ isSimpleChain_reverse hₑ
  have hEs : chainSet (b :: mₑ.reverse ++ [a]) = chainSet (a :: mₑ ++ [b]) := by
    rw [← hrev, chainSet_reverse]
  have iL : NeZero (a :: m₁ ++ b :: mₑ.reverse).length := ⟨by simp⟩
  have iR : NeZero (b :: m₂ ++ a :: mₑ).length := ⟨by simp⟩
  have sL := isSimple_two_arcs h₁ hEr (by rw [hEs]; exact h₁ₑ) hab
  have sR := isSimple_two_arcs (a := b) (b := a) h₂ hₑ (by rw [Set.pair_comm]; exact h₂ₑ) hab.symm
  have cC := carrier_two_arcs a b m₁ m₂
  have cL : (Polygon.ofList (a :: m₁ ++ b :: mₑ.reverse)).carrier =
      chainSet (a :: m₁ ++ [b]) ∪ chainSet (a :: mₑ ++ [b]) := by
    have := carrier_two_arcs a b m₁ mₑ.reverse
    rw [hEs] at this; exact this
  have cR := carrier_two_arcs b a m₂ mₑ
  have haA₁ : a ∈ chainSet (a :: m₁ ++ [b]) := mem_chainSet_head a _
  have hbA₁ : b ∈ chainSet (a :: m₁ ++ [b]) := mem_chainSet_last (a :: m₁) b
  have hEsub : chainSet (a :: mₑ ++ [b]) ⊆
      (chainSet (a :: mₑ ++ [b]) \ {a, b}) ∪ chainSet (a :: m₁ ++ [b]) := by
    intro x hx
    by_cases h : x ∈ ({a, b} : Set (ℝ × ℝ))
    · exact Or.inr (by rcases h with rfl | rfl <;> assumption)
    · exact Or.inl ⟨hx, h⟩
  have hDin : ∀ x ∈ chainSet (a :: mₑ ++ [b]), x ∈ (Polygon.ofList (a :: m₁ ++ b :: m₂)).inside ∨
      x ∈ (Polygon.ofList (a :: m₁ ++ b :: m₂)).carrier := by
    intro x hx
    rcases hEsub hx with h | h
    · exact Or.inl (hD h)
    · exact Or.inr (by rw [cC]; exact Or.inl h)
  constructor
  · ext x
    simp only [region, mem_union]
    constructor
    · rintro (hx | hx)
      · rw [hin] at hx
        rcases hx with (hx | hx) | hx
        · exact Or.inl (Or.inl hx)
        · exact Or.inr (Or.inl hx)
        · exact Or.inl (Or.inr (by rw [cL]; exact Or.inr hx.1))
      · rw [cC] at hx
        rcases hx with hx | hx
        · exact Or.inl (Or.inr (by rw [cL]; exact Or.inl hx))
        · exact Or.inr (Or.inr (by rw [cR]; exact Or.inl hx))
    · rintro ((hx | hx) | (hx | hx))
      · exact Or.inl (by rw [hin]; exact Or.inl (Or.inl hx))
      · rw [cL] at hx
        rcases hx with hx | hx
        · exact Or.inr (by rw [cC]; exact Or.inl hx)
        · exact hDin x hx
      · exact Or.inl (by rw [hin]; exact Or.inl (Or.inr hx))
      · rw [cR] at hx
        rcases hx with hx | hx
        · exact Or.inr (by rw [cC]; exact Or.inr hx)
        · exact hDin x hx
  · ext x
    simp only [region, mem_union, mem_inter_iff]
    constructor
    · rintro ⟨hx | hx, hy | hy⟩
      · exact absurd hy (Set.disjoint_left.1 hdisj hx)
      · exfalso
        have hcl := Polygon.carrier_subset_closure_class sR 1 hy
        obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 hcl _ (Polygon.isOpen_inside _) hx
        exact Set.disjoint_left.1 hdisj hz1 hz2
      · exfalso
        have hcl := Polygon.carrier_subset_closure_class sL 1 hx
        obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 hcl _ (Polygon.isOpen_inside _) hy
        exact Set.disjoint_left.1 hdisj hz2 hz1
      · rw [cL] at hx
        rw [cR] at hy
        rcases hx with hx | hx
        · rcases hy with hy | hy
          · have : x ∈ chainSet (a :: m₁ ++ [b]) ∩ chainSet (b :: m₂ ++ [a]) := ⟨hx, hy⟩
            rw [h₁₂] at this
            rcases this with rfl | rfl
            · exact mem_chainSet_head _ _
            · exact mem_chainSet_last (a :: mₑ) _
          · exact hy
        · exact hx
    · intro hx
      have h1 : x ∈ (Polygon.ofList (a :: m₁ ++ b :: mₑ.reverse)).carrier := by
        rw [cL]; exact Or.inr hx
      have h2 : x ∈ (Polygon.ofList (b :: m₂ ++ a :: mₑ)).carrier := by
        rw [cR]; exact Or.inr hx
      exact ⟨Or.inr h1, Or.inr h2⟩

end Lightlike.PL.Schoenflies
