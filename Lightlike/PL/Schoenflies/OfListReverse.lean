import Mathlib
import Lightlike.PL.Schoenflies.RaySplit

/-!
# Reversing the vertex list of a polygon

Row G3-188 (PL5), nested ring.  The polygon on the reversed list has the same carrier and inside
(`ofList_reverse_carrier`, `ofList_reverse_inside`).
-/

open Set

namespace Lightlike.PL.Schoenflies

open Lightlike.PL

lemma ofList_reverse_data (a : ℝ × ℝ) (t : List (ℝ × ℝ)) (ht : t ≠ []) :
    ∃ (u : List (ℝ × ℝ)) (z : ℝ × ℝ), t = u ++ [z] := by
  rcases List.eq_nil_or_concat t with h | ⟨u, z, h⟩
  · exact absurd h ht
  · exact ⟨u, z, by simpa using h⟩

lemma chainParity_ofList_reverse (x : ℝ × ℝ) (a : ℝ × ℝ) (u : List (ℝ × ℝ)) (z : ℝ × ℝ) :
    chainParity x ((a :: u ++ [z]).reverse ++ [(a :: u ++ [z]).reverse.getD 0 0]) =
      chainParity x ((a :: u ++ [z]) ++ [(a :: u ++ [z]).getD 0 0]) := by
  have e1 : (a :: u ++ [z]).reverse.getD 0 0 = z := by simp
  have e2 : (a :: u ++ [z]).getD 0 0 = a := by simp
  rw [e1, e2]
  have h1 : (a :: u ++ [z]).reverse ++ [z] = (z :: (a :: u ++ [z])).reverse := by simp
  rw [h1, chainParity_reverse]
  have h2 : (a :: u ++ [z]) ++ [a] = (a :: u) ++ z :: [a] := by simp
  rw [h2, chainParity_append x (a :: u) z [a]]
  have h3 : z :: (a :: u ++ [z]) = z :: a :: (u ++ [z]) := rfl
  rw [h3, chainParity_cons_cons x z a (u ++ [z]), chainParity_cons_cons x z a [], chainParity_singleton, add_zero]
  have h4 : a :: (u ++ [z]) = (a :: u) ++ [z] := rfl
  rw [h4, add_comm]

/-- **The polygon on the reversed list has the same carrier and inside.** -/
theorem ofList_reverse (a : ℝ × ℝ) (u : List (ℝ × ℝ)) (z : ℝ × ℝ)
    [NeZero (a :: u ++ [z]).length] [NeZero (a :: u ++ [z]).reverse.length] :
    (Polygon.ofList (a :: u ++ [z]).reverse).carrier = (Polygon.ofList (a :: u ++ [z])).carrier ∧
    (Polygon.ofList (a :: u ++ [z]).reverse).inside = (Polygon.ofList (a :: u ++ [z])).inside := by
  have h2 : 2 ≤ (a :: u ++ [z]).length := by simp only [List.length_append, List.length_cons]; omega
  have h2' : 2 ≤ (a :: u ++ [z]).reverse.length := by simpa using h2
  have hc : (Polygon.ofList (a :: u ++ [z]).reverse).carrier = (Polygon.ofList (a :: u ++ [z])).carrier := by
    rw [carrier_ofList_closed _ h2', carrier_ofList_closed _ h2]
    have e1 : (a :: u ++ [z]).reverse.getD 0 0 = z := by simp
    have e2 : (a :: u ++ [z]).getD 0 0 = a := by simp
    rw [e1, e2]
    have h1 : (a :: u ++ [z]).reverse ++ [z] = (z :: (a :: u ++ [z])).reverse := by simp
    rw [h1, chainSet_reverse]
    have h3 : (a :: u ++ [z]) ++ [a] = (a :: u) ++ z :: [a] := by simp
    rw [h3, chainSet_append, chainSet_pair z a]
    have h4 : z :: (a :: u ++ [z]) = z :: a :: (u ++ [z]) := rfl
    rw [h4]
    simp only [chainSet]
    have h5 : a :: (u ++ [z]) = (a :: u) ++ [z] := rfl
    rw [h5, union_comm]
  refine ⟨hc, ?_⟩
  ext y
  simp only [Polygon.inside, mem_ofPred_eq]
  have hp1 := Polygon.parity_ofList (a :: u ++ [z]).reverse y 0 h2'
  have hp2 := Polygon.parity_ofList (a :: u ++ [z]) y 0 h2
  rw [hc, hp1, hp2, chainParity_ofList_reverse]

end Lightlike.PL.Schoenflies
