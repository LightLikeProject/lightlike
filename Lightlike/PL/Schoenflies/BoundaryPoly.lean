import Lightlike.PL.Schoenflies.LatticePoly
import Lightlike.PL.Schoenflies.LatticeCycle
import Lightlike.PL.Schoenflies.LatticeBoxes

/-!
# The boundary polygon of a union of inflated grid squares

Row G3-188, milestone PL5 (third pass), item 5b, route A.  For a finite family `F` of grid squares the
boundary graph of `sqSet F` (`LatticeGraph`) has a cycle through every boundary edge
(`exists_boundary_cycle`); this cycle is a simple polygon (`exists_boundary_polygon`), and its carrier
misses the open inflated squares (`bdEdge_not_mem_openBox`), all in units of `δ / 4`.

* `openBoxU q`: the open inflated grid square `q`, in units of `δ / 4`.
* `bdAdj_horiz`, `bdAdj_vert`: a unit segment that is a boundary edge, in normal form.
* `bdEdge_not_mem_openBox`: a boundary edge of `sqSet F` meets no open inflated square of `F`.
* `exists_boundary_polygon`: boundary cycle that is a simple polygon.
-/

namespace Lightlike.PL.Schoenflies

open Set

/-- The open inflated grid square `q`, in units of `δ / 4`. -/
def openBoxU (q : ℤ × ℤ) : Set (ℝ × ℝ) :=
  {z | 4 * (q.1 : ℝ) - 1 < z.1 ∧ z.1 < 4 * q.1 + 5 ∧ 4 * (q.2 : ℝ) - 1 < z.2 ∧ z.2 < 4 * q.2 + 5}

/-- A boundary edge between `(x,y)` and `(x+1,y)` is a horizontal boundary edge. -/
lemma bdAdj_horiz {S : Set (ℤ × ℤ)} {a b : ℤ × ℤ} {x y : ℤ} (hab : BdAdj S a b)
    (h : ({a, b} : Set (ℤ × ℤ)) = {(x, y), (x + 1, y)}) : HB S x y := by
  rcases Set.pair_eq_pair_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases (bdAdj_iff S x y (x + 1) y).1 hab with h1 | h1 | h1 | h1
    · exact h1.2.2
    · omega
    · omega
    · omega
  · have := (show BdAdj S (x, y) (x + 1, y) from SimpleGraph.Adj.symm (G := bdGraph S) hab)
    rcases (bdAdj_iff S x y (x + 1) y).1 this with h1 | h1 | h1 | h1
    · exact h1.2.2
    · omega
    · omega
    · omega

/-- A boundary edge between `(x,y)` and `(x,y+1)` is a vertical boundary edge. -/
lemma bdAdj_vert {S : Set (ℤ × ℤ)} {a b : ℤ × ℤ} {x y : ℤ} (hab : BdAdj S a b)
    (h : ({a, b} : Set (ℤ × ℤ)) = {(x, y), (x, y + 1)}) : VB S x y := by
  rcases Set.pair_eq_pair_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases (bdAdj_iff S x y x (y + 1)).1 hab with h1 | h1 | h1 | h1
    · omega
    · omega
    · exact h1.2.2
    · omega
  · have := (show BdAdj S (x, y) (x, y + 1) from SimpleGraph.Adj.symm (G := bdGraph S) hab)
    rcases (bdAdj_iff S x y x (y + 1)).1 this with h1 | h1 | h1 | h1
    · omega
    · omega
    · exact h1.2.2
    · omega

/-- **A boundary edge of `sqSet F` meets no open inflated square of `F`.** -/
theorem bdEdge_not_mem_openBox {F : Finset (ℤ × ℤ)} {a b : ℤ × ℤ} (hab : BdAdj (sqSet F) a b)
    {z : ℝ × ℝ} (hz : z ∈ segment ℝ (pt a) (pt b)) {q : ℤ × ℤ} (hq : q ∈ F) :
    z ∉ openBoxU q := by
  intro hzq
  obtain ⟨h1, h2, h3, h4⟩ := hzq
  obtain ⟨x, y, ⟨he, hy, hx1, hx2⟩ | ⟨he, hx, hy1, hy2⟩⟩ := seg_unit hab.unitStep hz
  · have hB := bdAdj_horiz hab he
    rw [hy] at h3 h4
    have a1 : 4 * q.1 - 1 < x + 1 := by
      have : (4 * (q.1 : ℝ) - 1) < x + 1 := by linarith
      exact_mod_cast this
    have a2 : x < 4 * q.1 + 5 := by
      have : (x : ℝ) < 4 * q.1 + 5 := by linarith
      exact_mod_cast this
    have a3 : 4 * q.2 - 1 < y := by exact_mod_cast h3
    have a4 : y < 4 * q.2 + 5 := by exact_mod_cast h4
    have m1 : (x, y) ∈ sqSet F := mem_sqSet.2 ⟨q, hq, mem_boxSq.2 ⟨by omega, by omega, by omega, by omega⟩⟩
    have m2 : (x, y - 1) ∈ sqSet F :=
      mem_sqSet.2 ⟨q, hq, mem_boxSq.2 ⟨by omega, by omega, by omega, by omega⟩⟩
    unfold HB at hB
    tauto
  · have hB := bdAdj_vert hab he
    rw [hx] at h1 h2
    have a1 : 4 * q.1 - 1 < x := by exact_mod_cast h1
    have a2 : x < 4 * q.1 + 5 := by exact_mod_cast h2
    have a3 : 4 * q.2 - 1 < y + 1 := by
      have : (4 * (q.2 : ℝ) - 1) < y + 1 := by linarith
      exact_mod_cast this
    have a4 : y < 4 * q.2 + 5 := by
      have : (y : ℝ) < 4 * q.2 + 5 := by linarith
      exact_mod_cast this
    have m1 : (x, y) ∈ sqSet F := mem_sqSet.2 ⟨q, hq, mem_boxSq.2 ⟨by omega, by omega, by omega, by omega⟩⟩
    have m2 : (x - 1, y) ∈ sqSet F :=
      mem_sqSet.2 ⟨q, hq, mem_boxSq.2 ⟨by omega, by omega, by omega, by omega⟩⟩
    unfold VB at hB
    tauto

/-- **The boundary cycle of a finite union of inflated grid squares is a simple polygon.**  Through every
boundary edge `a b` of `sqSet F` there is a simple lattice polygon `latticePoly v` with all edges boundary
edges, having `a b` as an edge. -/
theorem exists_boundary_polygon (F : Finset (ℤ × ℤ)) {a b : ℤ × ℤ}
    (hab : (bdGraph (sqSet F)).Adj a b) :
    ∃ (n : ℕ) (v : Fin n → ℤ × ℤ), 3 ≤ n ∧ Function.Injective v ∧
      (∀ i, BdAdj (sqSet F) (v i) (v (finRotate n i))) ∧ (latticePoly v).IsSimple ∧
      ∃ i, (v i = a ∧ v (finRotate n i) = b) ∨ (v i = b ∧ v (finRotate n i) = a) := by
  obtain ⟨n, v, hn, hv, hadj, hi⟩ :=
    exists_boundary_cycle (noPinch_sqSet F) (sqSet_finite F) hab
  exact ⟨n, v, hn, hv, hadj, latticePoly_isSimple hn hv (fun i => (hadj i).unitStep), hi⟩

/-- **The carrier of the boundary polygon misses the open inflated squares of `F`.** -/
theorem carrier_not_mem_openBox {F : Finset (ℤ × ℤ)} {n : ℕ} {v : Fin n → ℤ × ℤ}
    (hadj : ∀ i, BdAdj (sqSet F) (v i) (v (finRotate n i))) {q : ℤ × ℤ} (hq : q ∈ F) :
    Disjoint (latticePoly v).carrier (openBoxU q) := by
  rw [Set.disjoint_left]
  intro z hz hzq
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz
  exact bdEdge_not_mem_openBox (hadj i) hi hq hzq

end Lightlike.PL.Schoenflies
