import Mathlib
import Lightlike.PL.PolygonSplit
import Lightlike.PL.Schoenflies.ConvexSplit

/-!
# Strict convex position is invariant under rotation of the vertex list

Piece 11 of the polygonal Schoenflies theorem (row G3-188, milestone PL5).  The ear induction rotates
the polygon so that an ear sits at the vertex `0`; the convex polygon must be rotated by the same
amount.  Strict convex position of `c` is the positivity of `det3` on all cyclically ordered
triples; hence it survives `Polygon.rot`.
-/

namespace Lightlike.PL.Schoenflies

open Set

lemma cyc_add_mul {n : ℕ} [NeZero n] (c : Polygon n) (q i : ℕ) : c.cyc (n * q + i) = c.cyc i := by
  simp [Polygon.cyc]

/-- Cyclic version of strict convex position, for `i < n`. -/
lemma scp_cyc_aux {n : ℕ} [NeZero n] {c : Polygon n} (hc : StrictConvexPos c) {i j k : ℕ}
    (hi : i < n) (hij : i < j) (hjk : j < k) (hk : k < i + n) :
    0 < det3 (c.cyc i) (c.cyc j) (c.cyc k) := by
  by_cases hkn : k < n
  · exact scp_cyc hc hij hjk hkn.le (Or.inl hkn)
  · have e : c.cyc k = c.cyc (k - n) := by
      have := c.cyc_self_add (k - n)
      rw [show n + (k - n) = k by omega] at this
      exact this
    by_cases hjn : j < n
    · -- `k - n < i < j`
      rw [e, ← det3_cyc (c.cyc i) (c.cyc j) (c.cyc (k - n))]
      have := scp_cyc hc (i := k - n) (j := i) (k := j) (by omega) hij hjn.le (Or.inl hjn)
      rwa [det3_cyc] at this
    · have ej : c.cyc j = c.cyc (j - n) := by
        have := c.cyc_self_add (j - n)
        rw [show n + (j - n) = j by omega] at this
        exact this
      rw [e, ej]
      have := scp_cyc hc (i := j - n) (j := k - n) (k := i) (by omega) (by omega) hi.le
        (Or.inl hi)
      rw [det3_cyc] at this
      exact this

/-- Strict convex position, read cyclically on all natural numbers: every `i < j < k < i + n`. -/
lemma scp_cyc_gen {n : ℕ} [NeZero n] {c : Polygon n} (hc : StrictConvexPos c) {i j k : ℕ}
    (hij : i < j) (hjk : j < k) (hk : k < i + n) :
    0 < det3 (c.cyc i) (c.cyc j) (c.cyc k) := by
  have hn := NeZero.pos n
  have hq : n * (i / n) ≤ i := Nat.mul_div_le i n
  have hr : i % n < n := Nat.mod_lt _ hn
  have hi' : i = n * (i / n) + i % n := (Nat.div_add_mod i n).symm
  have e1 : c.cyc i = c.cyc (i % n) := (c.cyc_mod i).symm
  have e2 : c.cyc j = c.cyc (j - n * (i / n)) := by
    rw [← cyc_add_mul c (i / n) (j - n * (i / n)), show n * (i / n) + (j - n * (i / n)) = j by omega]
  have e3 : c.cyc k = c.cyc (k - n * (i / n)) := by
    rw [← cyc_add_mul c (i / n) (k - n * (i / n)), show n * (i / n) + (k - n * (i / n)) = k by omega]
  rw [e1, e2, e3]
  exact scp_cyc_aux hc hr (by omega) (by omega) (by omega)

/-- **Rotating the vertex list keeps strict convex position.** -/
lemma scp_rot {n : ℕ} [NeZero n] {c : Polygon n} (hc : StrictConvexPos c) (β : Fin n) :
    StrictConvexPos (c.rot β) := by
  intro i j k hij hjk
  have h : ∀ m : Fin n, c.rot β m = c.cyc (m + β) := fun m => by
    rw [show c.rot β m = (c.rot β).cyc m from ((c.rot β).cyc_of_lt m.2).symm, Polygon.rot_cyc]
  rw [h, h, h]
  have hij' : (i : ℕ) < j := hij
  have hjk' : (j : ℕ) < k := hjk
  have := k.2
  exact scp_cyc_gen hc (by omega) (by omega) (by omega)

/-- Rotating the vertex list does not change the set of vertices. -/
lemma range_rot {n : ℕ} [NeZero n] (c : Polygon n) (β : Fin n) : range (c.rot β) = range c := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩; exact ⟨i + β, rfl⟩
  · rintro ⟨i, rfl⟩; exact ⟨i - β, by simp [Polygon.rot]⟩

/-- The unit square, counterclockwise. -/
private def sq : Polygon 4 := ![(0, 0), (1, 0), (1, 1), (0, 1)]

/-- Non-vacuity: rotating the unit square by one vertex is still strictly convex. -/
example : StrictConvexPos (sq.rot 1) :=
  scp_rot (by
    intro i j k hij hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all [sq, det3, cross]) 1

end Lightlike.PL.Schoenflies
