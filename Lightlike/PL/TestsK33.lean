import Lightlike.PL.K33

/-!
# Non-vacuity of the polygonal drawing of `K₃,₃`

`no_PL_K33` is not vacuous: the hypotheses of `PLDrawing` are satisfiable for the graph `K₃,₃`
without one edge. This file builds a drawing of `K₃,₃ − (2, 2)` with straight segments:
the square `u₀ v₀ u₁ v₁` with corners `(0,0) (2,0) (2,2) (0,2)`, the point `v₂ = (1,1)` in the
middle joined to the opposite corners `u₀`, `u₁`, and the point `u₂ = (4,4)` outside joined to the
other two corners `v₀`, `v₁`. The edge `(2, 2)` is the only one missing.

The scope is the one of `no_PL_K33`: polygonal arcs in `ℝ²`.
-/

open Set

namespace Lightlike.PL

namespace TestsK33

/-- A point of a segment, in coordinates. -/
lemma mem_seg {a b z : ℝ × ℝ} (h : z ∈ segment ℝ a b) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ z.1 = a.1 + s * (b.1 - a.1) ∧ z.2 = a.2 + s * (b.2 - a.2) := by
  obtain ⟨x, y, hx, hy, hxy, rfl⟩ := h
  obtain rfl : x = 1 - y := by linarith
  refine ⟨y, hy, by linarith, ?_, ?_⟩ <;> simp <;> ring

set_option hygiene false in
/-- Two segments meet only in the allowed points. -/
local macro "segpair" : tactic =>
  `(tactic| (
    rintro ⟨x, y⟩ ⟨h1, h2⟩
    obtain ⟨s, hs0, hs1, hs2, hs3⟩ := mem_seg h1
    obtain ⟨t, ht0, ht1, ht2, ht3⟩ := mem_seg h2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff] at *
    norm_num at *
    first
    | (left; constructor <;> linarith)
    | (right; constructor <;> linarith)))

/-- The six points. -/
def u : Fin 3 → ℝ × ℝ := ![(0, 0), (2, 2), (4, 4)]
/-- The six points. -/
def v : Fin 3 → ℝ × ℝ := ![(2, 0), (0, 2), (1, 1)]

/-- The graph: `K₃,₃` without the edge `(2, 2)`. -/
def E : Set (Fin 3 × Fin 3) := Set.univ \ {(2, 2)}

/-- The arcs, each a single segment. -/
def arc : Fin 3 → Fin 3 → List (ℝ × ℝ)
  | 0, 0 => [u 0, v 0] | 0, 1 => [u 0, v 1] | 0, 2 => [u 0, v 2]
  | 1, 0 => [u 1, v 0] | 1, 1 => [u 1, v 1] | 1, 2 => [u 1, v 2]
  | 2, 0 => [u 2, v 0] | 2, 1 => [u 2, v 1] | 2, 2 => []

lemma mem_E {i j : Fin 3} (h : (i, j) ∈ E) : ¬ (i = 2 ∧ j = 2) := by
  rintro ⟨rfl, rfl⟩; simp [E] at h

lemma seg_simple (a b : ℝ × ℝ) (h : a ≠ b) : IsSimpleChain [a, b] := by
  refine ⟨h, ?_, trivial⟩
  have : chainSet [b] = {b} := by simp [chainSet]
  rw [this]
  exact Set.inter_eq_right.2 (Set.singleton_subset_iff.2 (right_mem_segment ℝ a b))

lemma chainSet2 (a b : ℝ × ℝ) : chainSet [a, b] = segment ℝ a b := by
  simp [chainSet]
  exact right_mem_segment ℝ a b

/-- **A polygonal drawing of `K₃,₃ − (2, 2)`**: `PLDrawing E` is inhabited. -/
def drawing : PLDrawing E where
  u := u
  v := v
  arc := arc
  simple i j h := by
    have := mem_E h
    fin_cases i <;> fin_cases j <;> simp_all [arc] <;>
      exact seg_simple _ _ (by simp [u, v, Prod.ext_iff])
  head i j h := by
    have := mem_E h
    fin_cases i <;> fin_cases j <;> simp_all [arc]
  last i j h := by
    have := mem_E h
    fin_cases i <;> fin_cases j <;> simp_all [arc]
  length_ge i j h := by
    have := mem_E h
    fin_cases i <;> fin_cases j <;> simp_all [arc]
  disj i j i' j' h h' hne := by
    have hA := mem_E h
    have hB := mem_E h'
    fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;>
      first
      | (exfalso; apply hA; exact ⟨rfl, rfl⟩)
      | (exfalso; apply hB; exact ⟨rfl, rfl⟩)
      | exact absurd rfl hne
      | (simp [arc, u, v, chainSet2]
         constructor <;> segpair)
  inj_u := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [u, Prod.ext_iff]
  inj_v := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [v, Prod.ext_iff]
  uv_ne i j := by
    fin_cases i <;> fin_cases j <;> simp [u, v, Prod.ext_iff]

/-- Trust check (wrong model): the two diagonals of the square cross at `(1, 1)`, which is not an
endpoint of either, so two such arcs would violate the disjointness field of `PLDrawing`. -/
example : ((1 : ℝ), (1 : ℝ)) ∈ segment ℝ ((0 : ℝ), (0 : ℝ)) (2, 2) ∩ segment ℝ ((2 : ℝ), (0 : ℝ)) (0, 2) ∧
    ((1 : ℝ), (1 : ℝ)) ∉ ({((0 : ℝ), (0 : ℝ)), (2, 2)} : Set (ℝ × ℝ)) := by
  refine ⟨⟨⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩,
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩⟩, ?_⟩
  · ext <;> simp
  · ext <;> simp
  · simp [Prod.ext_iff]

/-- Consistency with the theorem: the drawing of `K₃,₃ − (2, 2)` exists while that of `K₃,₃`
does not. -/
example : Nonempty (PLDrawing E) ∧ ¬ Nonempty (PLDrawing Set.univ) :=
  ⟨⟨drawing⟩, fun ⟨d⟩ => no_PL_K33 d⟩

end TestsK33

end Lightlike.PL
