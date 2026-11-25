import Mathlib
import Lightlike.PL.Schoenflies.ChordSplit
import Lightlike.PL.Schoenflies.RegionGlue
import Lightlike.PL.Schoenflies.OfListRot

/-!
# Splitting a quadrilateral cell of a ring along a spoke

Row G3-188 (PL5), ring cells.  A *cell* between an inner chain `α` (from `w` to `w'`) and an outer chain `β`
(from `v` to `v'`) is the polygon on the list `α ++ β.reverse`; its two closing edges are the spokes `[w', v']`
and `[v, w]`.  A spoke `[x, y]` joining a vertex `x` of `α` to a vertex `y` of `β` cuts the cell into the cell
between the parts of the chains after `x`, `y` and the cell between the parts up to `x`, `y`
(`quad_split_region`).
-/

open Set

namespace Lightlike.PL.Schoenflies

open Lightlike.PL

/-- The cell between an inner chain `α` and an outer chain `β`. -/
def quadList (α β : List (ℝ × ℝ)) : List (ℝ × ℝ) := α ++ β.reverse

lemma region_ofList_congr {l l' : List (ℝ × ℝ)} [NeZero l.length] [NeZero l'.length] (h : l = l') :
    region (Polygon.ofList l) = region (Polygon.ofList l') := by
  subst h; rfl

lemma region_ofList_rotate (l₁ l₂ : List (ℝ × ℝ)) [NeZero (l₁ ++ l₂).length] [NeZero (l₂ ++ l₁).length] :
    region (Polygon.ofList (l₂ ++ l₁)) = region (Polygon.ofList (l₁ ++ l₂)) := by
  unfold region
  rw [ofList_rotate_inside, ofList_rotate_carrier]

theorem quad_split_region {pa qa pb qb : List (ℝ × ℝ)} {x y : ℝ × ℝ} (hxy : x ≠ y)
    (h₁ : IsSimpleChain (x :: (qa ++ qb.reverse) ++ [y]))
    (h₂ : IsSimpleChain (y :: (pb.reverse ++ pa) ++ [x]))
    (h₁₂ : chainSet (x :: (qa ++ qb.reverse) ++ [y]) ∩ chainSet (y :: (pb.reverse ++ pa) ++ [x]) = {x, y})
    (h₁ₑ : chainSet (x :: (qa ++ qb.reverse) ++ [y]) ∩ segment ℝ x y = {x, y})
    (h₂ₑ : chainSet (y :: (pb.reverse ++ pa) ++ [x]) ∩ segment ℝ x y = {x, y})
    (hD : segment ℝ x y \ {x, y} ⊆
      (Polygon.ofList (x :: (qa ++ qb.reverse) ++ y :: (pb.reverse ++ pa))).inside) :
    region (Polygon.ofList (x :: (qa ++ qb.reverse) ++ y :: (pb.reverse ++ pa))) =
        region (Polygon.ofList (quadList (x :: qa) (y :: qb))) ∪
          region (Polygon.ofList (quadList (pa ++ [x]) (pb ++ [y]))) ∧
      region (Polygon.ofList (quadList (x :: qa) (y :: qb))) ∩
          region (Polygon.ofList (quadList (pa ++ [x]) (pb ++ [y]))) = segment ℝ x y := by
  have hE : IsSimpleChain (x :: ([] : List (ℝ × ℝ)) ++ [y]) := by
    simp only [List.nil_append, List.cons_append]; refine ⟨hxy, ?_, trivial⟩
    simp only [chainSet]
    exact Set.inter_eq_right.2 (singleton_subset_iff.2 (right_mem_segment ℝ x y))
  have hEs : chainSet (x :: ([] : List (ℝ × ℝ)) ++ [y]) = segment ℝ x y := by
    simpa using chainSet_pair x y
  obtain ⟨hU, hI⟩ := region_split_chain (a := x) (b := y) (m₁ := qa ++ qb.reverse)
    (m₂ := pb.reverse ++ pa) (mₑ := []) hxy h₁ h₂ hE h₁₂ (by rw [hEs]; exact h₁ₑ)
    (by rw [hEs]; exact h₂ₑ) (by rw [hEs]; exact hD)
  rw [hEs] at hI
  have iA : NeZero (x :: (qa ++ qb.reverse) ++ y :: ([] : List (ℝ × ℝ)).reverse).length := ⟨by simp⟩
  have iB : NeZero (y :: (pb.reverse ++ pa) ++ x :: ([] : List (ℝ × ℝ))).length := ⟨by simp⟩
  have iQ1 : NeZero (quadList (x :: qa) (y :: qb)).length := ⟨by simp [quadList]⟩
  have iQ2 : NeZero (quadList (pa ++ [x]) (pb ++ [y])).length := ⟨by simp [quadList]⟩
  have iQ2' : NeZero ((y :: pb.reverse) ++ (pa ++ [x])).length := ⟨by simp⟩
  have iQ2'' : NeZero ((pa ++ [x]) ++ (y :: pb.reverse)).length := ⟨by simp⟩
  have e1 : region (Polygon.ofList (x :: (qa ++ qb.reverse) ++ y :: ([] : List (ℝ × ℝ)).reverse)) =
      region (Polygon.ofList (quadList (x :: qa) (y :: qb))) := by
    apply region_ofList_congr; simp [quadList]
  have e2 : region (Polygon.ofList (y :: (pb.reverse ++ pa) ++ x :: ([] : List (ℝ × ℝ)))) =
      region (Polygon.ofList (quadList (pa ++ [x]) (pb ++ [y]))) := by
    have h1 : region (Polygon.ofList (y :: (pb.reverse ++ pa) ++ x :: ([] : List (ℝ × ℝ)))) =
        region (Polygon.ofList ((y :: pb.reverse) ++ (pa ++ [x]))) := by
      apply region_ofList_congr; simp
    rw [h1, region_ofList_rotate (pa ++ [x]) (y :: pb.reverse)]
    apply region_ofList_congr; simp [quadList]
  rw [e1, e2] at hU
  refine ⟨hU, ?_⟩
  rw [e1, e2] at hI
  exact hI

lemma quad_region_left (qa qb : List (ℝ × ℝ)) (x y : ℝ × ℝ) :
    region (Polygon.ofList (x :: (qa ++ qb.reverse) ++ y :: ([] : List (ℝ × ℝ)).reverse)) =
      region (Polygon.ofList (quadList (x :: qa) (y :: qb))) := by
  have iA : NeZero (x :: (qa ++ qb.reverse) ++ y :: ([] : List (ℝ × ℝ)).reverse).length := ⟨by simp⟩
  have iQ1 : NeZero (quadList (x :: qa) (y :: qb)).length := ⟨by simp [quadList]⟩
  apply region_ofList_congr; simp [quadList]

lemma quad_region_right (pa pb : List (ℝ × ℝ)) (x y : ℝ × ℝ) :
    region (Polygon.ofList (y :: (pb.reverse ++ pa) ++ x :: ([] : List (ℝ × ℝ)))) =
      region (Polygon.ofList (quadList (pa ++ [x]) (pb ++ [y]))) := by
  have iB : NeZero (y :: (pb.reverse ++ pa) ++ x :: ([] : List (ℝ × ℝ))).length := ⟨by simp⟩
  have iQ2 : NeZero (quadList (pa ++ [x]) (pb ++ [y])).length := ⟨by simp [quadList]⟩
  have iQ2' : NeZero ((y :: pb.reverse) ++ (pa ++ [x])).length := ⟨by simp⟩
  have iQ2'' : NeZero ((pa ++ [x]) ++ (y :: pb.reverse)).length := ⟨by simp⟩
  have h1 : region (Polygon.ofList (y :: (pb.reverse ++ pa) ++ x :: ([] : List (ℝ × ℝ)))) =
      region (Polygon.ofList ((y :: pb.reverse) ++ (pa ++ [x]))) := by
    apply region_ofList_congr; simp
  rw [h1, region_ofList_rotate (pa ++ [x]) (y :: pb.reverse)]
  apply region_ofList_congr; simp [quadList]

/-- **Gluing homeomorphisms of the two cells obtained by cutting a cell along a spoke.** -/
theorem quad_split_homeo {pa qa pb qb : List (ℝ × ℝ)} {x y : ℝ × ℝ} (hxy : x ≠ y)
    (h₁ : IsSimpleChain (x :: (qa ++ qb.reverse) ++ [y]))
    (h₂ : IsSimpleChain (y :: (pb.reverse ++ pa) ++ [x]))
    (h₁₂ : chainSet (x :: (qa ++ qb.reverse) ++ [y]) ∩ chainSet (y :: (pb.reverse ++ pa) ++ [x]) = {x, y})
    (h₁ₑ : chainSet (x :: (qa ++ qb.reverse) ++ [y]) ∩ segment ℝ x y = {x, y})
    (h₂ₑ : chainSet (y :: (pb.reverse ++ pa) ++ [x]) ∩ segment ℝ x y = {x, y})
    (hD : segment ℝ x y \ {x, y} ⊆
      (Polygon.ofList (x :: (qa ++ qb.reverse) ++ y :: (pb.reverse ++ pa))).inside)
    {A' B' : Set (ℝ × ℝ)}
    (e₁ : region (Polygon.ofList (quadList (x :: qa) (y :: qb))) ≃ₜ A')
    (e₂ : region (Polygon.ofList (quadList (pa ++ [x]) (pb ++ [y]))) ≃ₜ B')
    (h : ∀ (z : ℝ × ℝ) (hz1 : z ∈ region (Polygon.ofList (quadList (x :: qa) (y :: qb))))
      (hz2 : z ∈ region (Polygon.ofList (quadList (pa ++ [x]) (pb ++ [y])))),
      (e₁ ⟨z, hz1⟩ : ℝ × ℝ) = e₂ ⟨z, hz2⟩)
    (hAB : ∀ w, w ∈ A' → w ∈ B' → ∃ (z : ℝ × ℝ)
      (_ : z ∈ region (Polygon.ofList (quadList (x :: qa) (y :: qb))))
      (hz2 : z ∈ region (Polygon.ofList (quadList (pa ++ [x]) (pb ++ [y])))), (e₂ ⟨z, hz2⟩ : ℝ × ℝ) = w) :
    ∃ E : region (Polygon.ofList (x :: (qa ++ qb.reverse) ++ y :: (pb.reverse ++ pa))) ≃ₜ
        (A' ∪ B' : Set (ℝ × ℝ)),
      (∀ (z : ℝ × ℝ) (hz : z ∈ region (Polygon.ofList (quadList (x :: qa) (y :: qb)))),
        (E ⟨z, (quad_split_region hxy h₁ h₂ h₁₂ h₁ₑ h₂ₑ hD).1 ▸ Or.inl hz⟩ : ℝ × ℝ) = e₁ ⟨z, hz⟩) ∧
      (∀ (z : ℝ × ℝ) (hz : z ∈ region (Polygon.ofList (quadList (pa ++ [x]) (pb ++ [y])))),
        (E ⟨z, (quad_split_region hxy h₁ h₂ h₁₂ h₁ₑ h₂ₑ hD).1 ▸ Or.inr hz⟩ : ℝ × ℝ) = e₂ ⟨z, hz⟩) := by
  have hE : IsSimpleChain (x :: ([] : List (ℝ × ℝ)) ++ [y]) := by
    simp only [List.nil_append, List.cons_append]
    refine ⟨hxy, ?_, trivial⟩
    simp only [chainSet]
    exact Set.inter_eq_right.2 (singleton_subset_iff.2 (right_mem_segment ℝ x y))
  have hEs : chainSet (x :: ([] : List (ℝ × ℝ)) ++ [y]) = segment ℝ x y := by
    simpa using chainSet_pair x y
  have eL := quad_region_left qa qb x y
  have eR := quad_region_right pa pb x y
  obtain ⟨E, hE1, hE2⟩ := region_split_homeo (a := x) (b := y) (m₁ := qa ++ qb.reverse)
    (m₂ := pb.reverse ++ pa) (mₑ := []) hxy h₁ h₂ hE h₁₂ (by rw [hEs]; exact h₁ₑ)
    (by rw [hEs]; exact h₂ₑ) (by rw [hEs]; exact hD)
    ((Homeomorph.setCongr eL).trans e₁) ((Homeomorph.setCongr eR).trans e₂)
    (fun z hzA hzB => h z (eL ▸ hzA) (eR ▸ hzB))
    (fun w hwA hwB => by
      obtain ⟨z, hz1, hz2, hz⟩ := hAB w hwA hwB
      exact ⟨z, eL ▸ hz1, eR ▸ hz2, hz⟩)
  refine ⟨E, fun z hz => ?_, fun z hz => ?_⟩
  · exact hE1 z (eL ▸ hz)
  · exact hE2 z (eR ▸ hz)

end Lightlike.PL.Schoenflies
