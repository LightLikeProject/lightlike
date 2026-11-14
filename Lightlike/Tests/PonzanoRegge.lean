module

public import Lightlike.PonzanoRegge.Amplitude
public import Lightlike.PonzanoRegge.GaugeFixed
public import Lightlike.PonzanoRegge.Parity

/-!
# Tests for the Ponzano–Regge amplitude and the 2-3 move

`weight_move23` takes, as a hypothesis, the single instance `BEAt` of the Biedenharn–Elliott
identity that a given colouring needs. These tests check that the conditional theorem is not
vacuous:

* `move23_example` - on the complex `{0123, 0124}` (two tetrahedra sharing the triangle `012`),
  coloured with spin 1 on `01, 12, 20` and spin ½ elsewhere, the 2-3 move holds
  **unconditionally**, from the proven instance `biedenharnElliott_instance`.
* `weight_example_ne_zero` - and the identity is not `0 = 0`: the weight is nonzero (each
  tetrahedron carries `{1 1 1; ½ ½ ½} = -1/3`).

* `move14_example` - the 1-4 move on the single tetrahedron `0123` with new vertex `4` (the
  hypotheses of `weight_move14` are satisfiable), and `weight_K1_ne_zero`: that weight is nonzero.

* `gf_move14_example`, `gf_move23_example`, `gf_chain_example`: the gauge-fixed amplitude's
  invariance theorems apply (hypotheses satisfiable); `gf_weight_example`: at spin 0 on the new
  gauge edge the 1-4 identity has factor 1, on a colouring with nonzero weight.
* `isMaxTree_K1`, `isMaxTree_K`, `gf_tree_move14_example`, `gf_tree_move23_example`,
  `gf_tree_chain_example`: maximal-tree gauge sets exist on the test complexes, and the
  maximal-tree versions of the invariance theorems apply to them.

Independent numerical evidence (SymPy, exact arithmetic) for the 2-3 move with these weights:
`scripts/pr23_check.py` (all 262 144 colourings with spins ≤ 3/2, 1 495 nontrivial; and a control
run with a wrong edge sign, which fails).
-/

@[expose] public section

open Finset

namespace Lightlike.PR.Test

/-- Two tetrahedra `0123` and `0124` glued along the triangle `012`. -/
def K : Complex3 (Fin 5) := ⟨{{0, 1, 2, 3}, {0, 1, 2, 4}}, by decide⟩

theorem hmove : IsMove23 K 0 1 2 3 4 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Spin 1 (doubled `2`) on the triangle `012`, spin ½ (doubled `1`) on every other pair. -/
def col : Colouring (Fin 5) := fun s => if s = {0, 1} ∨ s = {1, 2} ∨ s = {2, 0} then 2 else 1

lemma col_vals : col {0, 3} = 1 ∧ col {0, 4} = 1 ∧ col {1, 4} = 1 ∧ col {1, 3} = 1 ∧
    col {2, 3} = 1 ∧ col {2, 4} = 1 ∧ col {0, 1} = 2 ∧ col {1, 2} = 2 ∧ col {2, 0} = 2 := by
  decide

/-- **An unconditional 2-3 move**: no Biedenharn–Elliott hypothesis, only the proven instance. -/
theorem move23_example :
    weight K col = ∑ x ∈ range 3, weight (move23 K hmove) (Function.update col {3, 4} x) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := col_vals
  have hBE : BEAt col 0 1 2 3 4 := by
    unfold BEAt
    rw [h1, h2, h3, h4, h5, h6, h7, h8, h9]
    exact biedenharnElliott_instance
  have := weight_move23 K hmove col hBE
  rwa [h1, h2] at this

lemma edgeW_ne_zero (J : ℕ) : edgeW J ≠ 0 := by
  unfold edgeW
  exact mul_ne_zero (by positivity) (pow_ne_zero _ (by norm_num))

/-- The test is not `0 = 0`: the weight of `K` is nonzero. -/
theorem weight_example_ne_zero : weight K col ≠ 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := col_vals
  have ht1 : tetW col {0, 1, 2, 3} = -1 / 3 := by
    rw [tetW_eq_tetAmp col (by decide) (p := ![3, 2, 0, 1]) (by decide)
      (by intro i; fin_cases i <;> decide), tetAmp_eq]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [show ({2, 1} : Finset (Fin 5)) = {1, 2} by decide, show ({3, 2} : Finset (Fin 5)) = {2, 3}
      by decide, show ({3, 0} : Finset (Fin 5)) = {0, 3} by decide,
      show ({3, 1} : Finset (Fin 5)) = {1, 3} by decide, h7, h8, h9, h5, h1, h4]
    exact Lightlike.SixJAudit.sixJ_111_hhh
  have ht2 : tetW col {0, 1, 2, 4} = -1 / 3 := by
    rw [tetW_eq_tetAmp col (by decide) (p := ![4, 2, 0, 1]) (by decide)
      (by intro i; fin_cases i <;> decide), tetAmp_eq]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [show ({2, 1} : Finset (Fin 5)) = {1, 2} by decide, show ({4, 2} : Finset (Fin 5)) = {2, 4}
      by decide, show ({4, 0} : Finset (Fin 5)) = {0, 4} by decide,
      show ({4, 1} : Finset (Fin 5)) = {1, 4} by decide, h7, h8, h9, h6, h2, h3]
    exact Lightlike.SixJAudit.sixJ_111_hhh
  unfold weight
  refine mul_ne_zero (mul_ne_zero (prod_ne_zero_iff.mpr fun e _ => edgeW_ne_zero _)
    (prod_ne_zero_iff.mpr fun f _ => pow_ne_zero _ (by norm_num))) ?_
  refine prod_ne_zero_iff.mpr fun t ht => ?_
  have : t = {0, 1, 2, 3} ∨ t = {0, 1, 2, 4} := by simpa [K] using ht
  rcases this with rfl | rfl
  · rw [ht1]; norm_num
  · rw [ht2]; norm_num

/-! ### The 1-4 move -/

/-- A single tetrahedron `0123`; vertex `4` is unused. -/
def K1 : Complex3 (Fin 5) := ⟨{{0, 1, 2, 3}}, by decide⟩

theorem hmove14 : IsMove14 K1 0 1 2 3 4 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩

/-- **A 1-4 move** on `0123` with new vertex `4` and spin ½ on the new edge `34`: summing the
other three new edges gives `(2·½ + 1)² = 4` times the old weight. -/
theorem move14_example :
    ∑ a ∈ range (col {0, 3} + 1 + 1), ∑ b ∈ range (col {1, 3} + 1 + 1),
      ∑ c ∈ range (col {2, 3} + 1 + 1),
        weight (move14 K1 hmove14) (upd14 (Function.update col {3, 4} 1) 0 1 2 4 a b c) =
      4 * weight K1 col := by
  rw [weight_move14]
  norm_num

/-- The 1-4 test is not `0 = 0`: the weight of the single tetrahedron is `-1/3 · (nonzero)`. -/
theorem weight_K1_ne_zero : weight K1 col ≠ 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := col_vals
  have ht1 : tetW col {0, 1, 2, 3} = -1 / 3 := by
    rw [tetW_eq_tetAmp col (by decide) (p := ![3, 2, 0, 1]) (by decide)
      (by intro i; fin_cases i <;> decide), tetAmp_eq]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [show ({2, 1} : Finset (Fin 5)) = {1, 2} by decide, show ({3, 2} : Finset (Fin 5)) = {2, 3}
      by decide, show ({3, 0} : Finset (Fin 5)) = {0, 3} by decide,
      show ({3, 1} : Finset (Fin 5)) = {1, 3} by decide, h7, h8, h9, h5, h1, h4]
    exact Lightlike.SixJAudit.sixJ_111_hhh
  unfold weight
  refine mul_ne_zero (mul_ne_zero (prod_ne_zero_iff.mpr fun e _ => edgeW_ne_zero _)
    (prod_ne_zero_iff.mpr fun f _ => pow_ne_zero _ (by norm_num))) ?_
  rw [show K1.tets = {{0, 1, 2, 3}} from rfl, prod_singleton, ht1]
  norm_num

/-! ### The gauge-fixed amplitude -/

/-- 1-4 move on `0123` with the new edge `34` gauge-fixed, cutoff spin ½ everywhere. -/
theorem gf_move14_example :
    amplitudeGF (move14 K1 hmove14) (insert {3, 4} ∅) (fun _ => 1) =
      amplitudeGF K1 ∅ (fun _ => 1) :=
  amplitudeGF_move14 K1 hmove14 ∅ (empty_subset _) _ le_rfl le_rfl le_rfl

/-- Cutoffs for the 2-3 move on `{0123, 0124}`: the new edge `34` gets `≥ cut 03 + cut 04`. -/
def cut23 : Finset (Fin 5) → ℕ := fun e => if e = {3, 4} then 4 else 2

/-- The gauge-fixed 2-3 theorem applies on `{0123, 0124}` (its cutoff hypothesis is satisfiable). -/
theorem gf_move23_example : amplitudeGF (move23 K hmove) ∅ cut23 = amplitudeGF K ∅ cut23 :=
  amplitudeGF_move23 K hmove ∅ (empty_subset _) cut23 (by decide)

/-- A (one-step) chain in the equivalence closure. -/
theorem gf_chain_example :
    Relation.EqvGen GFStep (K1, ∅, fun _ => 1) (move14 K1 hmove14, insert {3, 4} ∅, fun _ => 1) :=
  .rel _ _ (.move14 hmove14 (empty_subset _) le_rfl le_rfl le_rfl)

/-- With spin 0 on the gauge edge `34`, the 1-4 move has factor 1, and the weight is nonzero. -/
theorem gf_weight_example :
    ∑ a ∈ range (col {0, 3} + 0 + 1), ∑ b ∈ range (col {1, 3} + 0 + 1),
      ∑ c ∈ range (col {2, 3} + 0 + 1),
        weight (move14 K1 hmove14) (upd14 (Function.update col {3, 4} 0) 0 1 2 4 a b c) =
      weight K1 col ∧ weight K1 col ≠ 0 := by
  refine ⟨(weight_move14 K1 hmove14 col 0).trans ?_, weight_K1_ne_zero⟩
  norm_num

/-! ### Maximal-tree gauge sets (non-vacuity of `IsMaxTree`) -/

/-- A star (every vertex joined to a centre `c`) connects its vertex set. -/
lemma conn_star {V : Type*} [DecidableEq V] {W : Finset V} {T : Finset (Finset V)} {c : V}
    (h : ∀ w ∈ W, w = c ∨ ({c, w} : Finset V) ∈ T) :
    ∀ u ∈ W, ∀ v ∈ W, Relation.ReflTransGen (fun x y => ({x, y} : Finset V) ∈ T) u v := by
  intro u hu v hv
  have to_c : Relation.ReflTransGen (fun x y => ({x, y} : Finset V) ∈ T) u c := by
    rcases h u hu with rfl | hu'
    · exact .refl
    · exact .single (by rw [pair_comm]; exact hu')
  have from_c : Relation.ReflTransGen (fun x y => ({x, y} : Finset V) ∈ T) c v := by
    rcases h v hv with rfl | hv'
    · exact .refl
    · exact .single hv'
  exact to_c.trans from_c

/-- The star at vertex `0` is a maximal tree of the one-tetrahedron complex `K1`. -/
theorem isMaxTree_K1 : IsMaxTree K1 {{0, 1}, {0, 2}, {0, 3}} :=
  ⟨by decide, ⟨by decide, conn_star (c := 0) (by decide), by decide⟩⟩

/-- The star at vertex `0` is a maximal tree of the two-tetrahedron complex `K`. -/
theorem isMaxTree_K : IsMaxTree K {{0, 1}, {0, 2}, {0, 3}, {0, 4}} :=
  ⟨by decide, ⟨by decide, conn_star (c := 0) (by decide), by decide⟩⟩

/-- 1-4 move with a maximal tree: the new gauge set `T ∪ {34}` is a maximal tree of the new
complex and the gauge-fixed amplitude is unchanged. -/
theorem gf_tree_move14_example :
    IsMaxTree (move14 K1 hmove14) (insert {3, 4} {{0, 1}, {0, 2}, {0, 3}}) ∧
      amplitudeGF (move14 K1 hmove14) (insert {3, 4} {{0, 1}, {0, 2}, {0, 3}}) (fun _ => 1) =
        amplitudeGF K1 {{0, 1}, {0, 2}, {0, 3}} (fun _ => 1) :=
  amplitudeGF_move14_tree K1 hmove14 isMaxTree_K1 _ le_rfl le_rfl le_rfl

/-- 2-3 move with a maximal tree. -/
theorem gf_tree_move23_example :
    IsMaxTree (move23 K hmove) {{0, 1}, {0, 2}, {0, 3}, {0, 4}} ∧
      amplitudeGF (move23 K hmove) {{0, 1}, {0, 2}, {0, 3}, {0, 4}} cut23 =
        amplitudeGF K {{0, 1}, {0, 2}, {0, 3}, {0, 4}} cut23 :=
  amplitudeGF_move23_tree K hmove isMaxTree_K cut23 (by decide)

/-- A tree-restricted chain step. -/
theorem gf_tree_chain_example :
    Relation.EqvGen GFTreeStep (K1, {{0, 1}, {0, 2}, {0, 3}}, fun _ => 1)
      (move14 K1 hmove14, insert {3, 4} {{0, 1}, {0, 2}, {0, 3}}, fun _ => 1) :=
  .rel _ _ (.move14 hmove14 isMaxTree_K1 le_rfl le_rfl le_rfl)

/-- The example tree is a tree in Mathlib's sense. -/
example : (treeGraph K1.verts {{0, 1}, {0, 2}, {0, 3}}).IsTree := isMaxTree_K1.2.isTree

/-! ### Odd perimeters: the `ℕ` division in the triangle weight is never seen -/

/-- Known value: the 6j symbol with three odd doubled perimeters vanishes (here every triad has
perimeter `3`), by `sixJSym_eq_zero_of_odd`. -/
example : PhyslibAlpha.Sl2.sixJSym 1 1 1 1 1 1 = 0 := sixJSym_eq_zero_of_odd (Or.inl (by decide))

/-- Every doubled spin `1` (spin ½): each triangle has perimeter `3`, so the weight is `0`. -/
theorem weight_odd_example : weight K (fun _ => 1) = 0 := by
  unfold weight
  have h : tetW (fun _ : Finset (Fin 5) => 1) {0, 1, 2, 3} = 0 :=
    tetW_eq_zero_of_odd _ (f := {0, 1, 2}) (by decide) (by decide) (by decide) (by decide)
  rw [prod_eq_zero (i := {0, 1, 2, 3}) (by simp [K]) h, mul_zero]

/-- On this colouring every triangle of `K` has an odd perimeter, so the triangle weight may be
replaced by any function (here the constant `5`) without changing the weight. -/
theorem weightWith_odd_example : weightWith (fun _ => 5) K (fun _ => 1) = weight K (fun _ => 1) :=
  weightWith_eq_weight _ _ _ fun f hf h => by
    obtain ⟨t, -, hft, hcard⟩ := Complex3.mem_tris.mp hf
    simp [sum_const, card_powersetCard, hcard] at h

/-- **Wrong model.** On the nonzero weight of `col`, where every triangle of `K` has an *even*
perimeter, replacing `triW` by `-triW` changes the weight: the hypothesis of
`weightWith_eq_weight` (agreement on even-perimeter triangles) is needed. `K` has seven
triangles, so the sign is `(-1)⁷`. -/
theorem weightWith_wrong_model : weightWith (fun f => -triW col f) K col ≠ weight K col := by
  have h7 : K.tris.card = 7 := by decide
  have h : weightWith (fun f => -triW col f) K col = -weight K col := by
    unfold weightWith weight
    have : ∏ f ∈ K.tris, -triW col f = -∏ f ∈ K.tris, triW col f := by
      rw [prod_congr rfl fun f _ => (neg_one_mul (triW col f)).symm, prod_mul_distrib, prod_const, h7,
        show ((-1 : ℝ)) ^ 7 = -1 by norm_num, neg_one_mul]
    rw [this]; ring
  rw [h]
  intro h'
  exact weight_example_ne_zero (by linarith)


end Lightlike.PR.Test
