import Lightlike.PL.PolygonDiagonal3

/-!
# Splitting a polygon along a diagonal

The crossing test of the horizontal ray does not depend on the direction in which an edge is
traversed. This is what makes the parities of the two polygons obtained by cutting along a
diagonal add up to the parity of the original polygon: the diagonal is an edge of both, traversed
in opposite directions, and contributes twice.

## Main results

* `Lightlike.PL.crossesRay_symm`: the ray crosses `[u, v]` exactly when it crosses `[v, u]`
-/

namespace Lightlike.PL

/-- The abscissa of the line through two points at a given height does not depend on the order of
the points, when they are at different heights. -/
lemma xAt_symm {u v : ℝ × ℝ} (h : u.2 ≠ v.2) (t : ℝ) : xAt u v t = xAt v u t := by
  unfold xAt
  have h1 : v.2 - u.2 ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  have h2 : u.2 - v.2 ≠ 0 := sub_ne_zero.2 h
  field_simp
  ring

/-- **The ray crosses an edge independently of the direction of the edge.** -/
theorem crossesRay_symm (u v x : ℝ × ℝ) : CrossesRay u v x ↔ CrossesRay v u x := by
  unfold CrossesRay
  by_cases h : u.2 = v.2
  · constructor <;> rintro ⟨h1 | h1, -⟩ <;> exfalso <;> linarith [h1.1, h1.2]
  · rw [xAt_symm h]
    exact and_congr_left' (or_comm)

/-- The successor of an index in `Fin m` as a natural number. -/
lemma finRotate_val {m : ℕ} (hm : 2 ≤ m) (i : Fin m) :
    ((finRotate m i : Fin m) : ℕ) = (i + 1) % m := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [finRotate_apply, Fin.val_add]
  have h1 : ((1 : Fin (m' + 1)) : ℕ) = 1 := by
    simp [Nat.mod_eq_of_lt (show 1 < m' + 1 by omega)]
  rw [h1]

namespace Polygon

variable {n : ℕ} [NeZero n] (p : Polygon n)

/-- The vertices of a polygon read cyclically, as a function on all natural numbers. -/
def cyc (i : ℕ) : ℝ × ℝ := p ⟨i % n, Nat.mod_lt _ (NeZero.pos n)⟩

lemma cyc_of_lt {i : ℕ} (hi : i < n) : p.cyc i = p ⟨i, hi⟩ := by
  simp [cyc, Nat.mod_eq_of_lt hi]

lemma cyc_mod (i : ℕ) : p.cyc (i % n) = p.cyc i := by simp [cyc]

lemma cyc_self_add (i : ℕ) : p.cyc (n + i) = p.cyc i := by
  simp [cyc]

/-- The part of the polygon from the vertex `0` to the vertex `b`, closed by the diagonal from
`b` back to `0`. -/
def left (b : ℕ) : Polygon (b + 1) := fun i => p.cyc i

/-- The part of the polygon from the vertex `b` to the vertex `0` (that is `n`), closed by the
diagonal from `0` back to `b`. -/
def right (b : ℕ) : Polygon (n - b + 1) := fun j => p.cyc (b + j)

/-- One summand of the parity: the ray crosses the edge from the vertex `i` to the vertex `i+1`,
read cyclically. -/
noncomputable def crossTerm (x : ℝ × ℝ) (i : ℕ) : ZMod 2 :=
  ind (CrossesRay (p.cyc i) (p.cyc (i + 1)) x)

/-- The parity as a sum over the natural numbers below `n`. -/
lemma parity_eq_sum_range (hn : 2 ≤ n) (x : ℝ × ℝ) :
    p.parity x = ∑ i ∈ Finset.range n, p.crossTerm x i := by
  unfold parity
  rw [← Fin.sum_univ_eq_sum_range (fun i => p.crossTerm x i) n]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : p i = p.cyc i := by rw [p.cyc_of_lt i.2]
  have h2 : p (finRotate n i) = p.cyc (i + 1) := by
    simp only [cyc]; congr 1; ext; exact finRotate_val hn i
  rw [crossTerm, ← h1, ← h2]

/-- The parity of the left part. -/
lemma parity_left {b : ℕ} (hb : 1 ≤ b) (x : ℝ × ℝ) :
    (p.left b).parity x =
      ∑ i ∈ Finset.range b, p.crossTerm x i + ind (CrossesRay (p.cyc b) (p.cyc 0) x) := by
  have hb2 : 2 ≤ b + 1 := by omega
  have h1 : (p.left b).parity x =
      ∑ i : Fin (b + 1), ind (CrossesRay (p.cyc i) (p.cyc ((i + 1) % (b + 1))) x) := by
    unfold parity
    refine Finset.sum_congr rfl fun i _ => ?_
    have : (p.left b) (finRotate (b + 1) i) = p.cyc ((i + 1) % (b + 1)) := by
      show p.cyc ((finRotate (b + 1) i : Fin (b + 1)) : ℕ) = _
      rw [finRotate_val hb2]
    rw [this]; rfl
  rw [h1, Fin.sum_univ_eq_sum_range
    (fun i => ind (CrossesRay (p.cyc i) (p.cyc ((i + 1) % (b + 1))) x)) (b + 1),
    Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    have : (i + 1) % (b + 1) = i + 1 := Nat.mod_eq_of_lt (by have := Finset.mem_range.1 hi; omega)
    simp only [crossTerm, this]
  · simp

/-- The parity of the right part. -/
lemma parity_right {b : ℕ} (hbn : b < n) (x : ℝ × ℝ) :
    (p.right b).parity x =
      ∑ i ∈ Finset.range (n - b), p.crossTerm x (b + i) +
        ind (CrossesRay (p.cyc 0) (p.cyc b) x) := by
  have hb2 : 2 ≤ n - b + 1 := by omega
  have h1 : (p.right b).parity x =
      ∑ i : Fin (n - b + 1), ind (CrossesRay (p.cyc (b + i))
        (p.cyc (b + (i + 1) % (n - b + 1))) x) := by
    unfold parity
    refine Finset.sum_congr rfl fun i _ => ?_
    have : (p.right b) (finRotate (n - b + 1) i) = p.cyc (b + (i + 1) % (n - b + 1)) := by
      show p.cyc (b + ((finRotate (n - b + 1) i : Fin (n - b + 1)) : ℕ)) = _
      rw [finRotate_val hb2]
    rw [this]; rfl
  rw [h1, Fin.sum_univ_eq_sum_range
    (fun i => ind (CrossesRay (p.cyc (b + i)) (p.cyc (b + (i + 1) % (n - b + 1))) x)) (n - b + 1),
    Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    have : (i + 1) % (n - b + 1) = i + 1 := Nat.mod_eq_of_lt (by have := Finset.mem_range.1 hi; omega)
    simp only [crossTerm, this, Nat.add_assoc]
  · have e1 : b + (n - b) = n + 0 := by omega
    have e2 : (n - b + 1) % (n - b + 1) = 0 := Nat.mod_self _
    rw [e1, e2, p.cyc_self_add 0, Nat.add_zero]

/-- **The parities of the two parts add up to the parity of the polygon.** The diagonal is an
edge of both parts, traversed in opposite directions, so it is counted twice. -/
theorem parity_left_add_right {b : ℕ} (hb : 1 ≤ b) (hbn : b < n) (x : ℝ × ℝ) :
    (p.left b).parity x + (p.right b).parity x = p.parity x := by
  have hn : 2 ≤ n := by omega
  rw [parity_left p hb, parity_right p hbn, p.parity_eq_sum_range hn]
  have hsplit := Finset.sum_range_add (fun i => p.crossTerm x i) b (n - b)
  rw [Nat.add_sub_cancel' hbn.le] at hsplit
  rw [hsplit]
  have hd : ind (CrossesRay (p.cyc b) (p.cyc 0) x) = ind (CrossesRay (p.cyc 0) (p.cyc b) x) :=
    ind_congr (crossesRay_symm _ _ _)
  rw [hd]
  have h2 := CharTwo.add_self_eq_zero (ind (CrossesRay (p.cyc 0) (p.cyc b) x))
  linear_combination h2

end Polygon

end Lightlike.PL
