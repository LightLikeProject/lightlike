import Mathlib
import Lightlike.PL.PolygonSplit
import Lightlike.PL.Chain
import Lightlike.PL.SimpleChain

/-!
# Rotating the vertex list of a polygon

Row G3-188 (PL5), ring cells.  The polygon on a list and the polygon on a rotation of the list have the same
carrier and inside, and one is simple exactly when the other is (`ofList_rotate_inside`, `ofList_rotate_carrier`,
`ofList_rotate_isSimple`).
-/

open Set

namespace Lightlike.PL.Schoenflies

open Lightlike.PL

/-- Two polygons with the same cyclic vertex function have the same inside, carrier and simplicity. -/
lemma polygon_congr {n m : ℕ} [NeZero n] [NeZero m] (p : Polygon n) (q : Polygon m) (h : n = m)
    (hpq : ∀ i, p.cyc i = q.cyc i) :
    p.inside = q.inside ∧ p.carrier = q.carrier ∧ (p.IsSimple ↔ q.IsSimple) := by
  subst h
  have : p = q := by
    funext i
    have := hpq i.val
    rwa [Polygon.cyc_of_lt p i.2, Polygon.cyc_of_lt q i.2] at this
  subst this
  exact ⟨rfl, rfl, Iff.rfl⟩

lemma ofList_rotate_data (l₁ l₂ : List (ℝ × ℝ)) [NeZero (l₁ ++ l₂).length] [NeZero (l₂ ++ l₁).length] :
    ∃ β : Fin (l₁ ++ l₂).length, ∀ i, (Polygon.ofList (l₂ ++ l₁)).cyc i =
      ((Polygon.ofList (l₁ ++ l₂)).rot β).cyc i := by
  have hn : 0 < (l₁ ++ l₂).length := NeZero.pos _
  refine ⟨⟨l₁.length % (l₁ ++ l₂).length, Nat.mod_lt _ hn⟩, fun i => ?_⟩
  have hn' : NeZero (l₂ ++ l₁).length := ⟨by simp [Nat.add_comm]; simpa [Nat.add_comm] using hn.ne'⟩
  have : NeZero (l₂ ++ l₁).length := hn'
  rw [Polygon.rot_cyc, Polygon.ofList_cyc _ (0 : ℝ × ℝ), Polygon.ofList_cyc _ (0 : ℝ × ℝ)]
  have hrot : (l₁ ++ l₂).rotate l₁.length = l₂ ++ l₁ := List.rotate_append_length_eq l₁ l₂
  have hlen : (l₂ ++ l₁).length = (l₁ ++ l₂).length := by simp [Nat.add_comm]
  have hk1 : i % (l₂ ++ l₁).length < (l₂ ++ l₁).length := Nat.mod_lt _ (NeZero.pos _)
  have hk2 : (i + l₁.length % (l₁ ++ l₂).length) % (l₁ ++ l₂).length < (l₁ ++ l₂).length :=
    Nat.mod_lt _ hn
  rw [List.getD_eq_getElem (l₂ ++ l₁) 0 hk1, List.getD_eq_getElem (l₁ ++ l₂) 0 hk2]
  have h3 : (l₂ ++ l₁)[i % (l₂ ++ l₁).length] =
      ((l₁ ++ l₂).rotate l₁.length)[i % (l₂ ++ l₁).length]'(by rw [List.length_rotate]; exact hk1.trans_eq hlen) := by
    simp only [hrot]
  rw [h3, List.getElem_rotate]
  congr 1
  rw [hlen]
  simp [Nat.add_mod]

lemma ofList_rotate_inside (l₁ l₂ : List (ℝ × ℝ)) [NeZero (l₁ ++ l₂).length] [NeZero (l₂ ++ l₁).length] :
    (Polygon.ofList (l₂ ++ l₁)).inside = (Polygon.ofList (l₁ ++ l₂)).inside := by
  obtain ⟨β, hβ⟩ := ofList_rotate_data l₁ l₂
  have := (polygon_congr (Polygon.ofList (l₂ ++ l₁)) ((Polygon.ofList (l₁ ++ l₂)).rot β)
    (by simp [Nat.add_comm]) hβ).1
  rw [this, Polygon.inside_rot]

lemma ofList_rotate_carrier (l₁ l₂ : List (ℝ × ℝ)) [NeZero (l₁ ++ l₂).length] [NeZero (l₂ ++ l₁).length] :
    (Polygon.ofList (l₂ ++ l₁)).carrier = (Polygon.ofList (l₁ ++ l₂)).carrier := by
  obtain ⟨β, hβ⟩ := ofList_rotate_data l₁ l₂
  have := (polygon_congr (Polygon.ofList (l₂ ++ l₁)) ((Polygon.ofList (l₁ ++ l₂)).rot β)
    (by simp [Nat.add_comm]) hβ).2.1
  rw [this, Polygon.carrier_rot]

lemma ofList_rotate_isSimple (l₁ l₂ : List (ℝ × ℝ)) [NeZero (l₁ ++ l₂).length] [NeZero (l₂ ++ l₁).length]
    (h : (Polygon.ofList (l₁ ++ l₂)).IsSimple) : (Polygon.ofList (l₂ ++ l₁)).IsSimple := by
  obtain ⟨β, hβ⟩ := ofList_rotate_data l₁ l₂
  have := (polygon_congr (Polygon.ofList (l₂ ++ l₁)) ((Polygon.ofList (l₁ ++ l₂)).rot β)
    (by simp [Nat.add_comm]) hβ).2.2
  exact this.2 (Polygon.isSimple_rot h β)

end Lightlike.PL.Schoenflies
