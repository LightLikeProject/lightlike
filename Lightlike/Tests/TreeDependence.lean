module

public import Lightlike.PonzanoRegge.Forcing
public import Lightlike.PonzanoRegge.SphereInvariants

/-!
# The gauge-fixed amplitude depends on the maximal tree (a counterexample)

`R` is a ring of three tetrahedra `0123`, `2345`, `4501`, each sharing an edge with the next. Its
loop `0 → 2 → 4 → 0` cannot be contracted. `T1` (the star at `0`) and `T2` (`01, 02, 03, 04, 25`)
are both maximal trees, they are not related by triangle exchanges, and with cutoff `½` on every
edge the gauge-fixed amplitudes differ:

* `amplitudeGF_R_T1 : amplitudeGF R T1 half = -7`,
* `amplitudeGF_R_T2 : amplitudeGF R T2 half = -15`,
* `amplitudeGF_tree_dependent`: so independence of the maximal tree fails for this complex.

`R` is not a 3-manifold (`not_isCombManifold_R`): its tetrahedra meet only along edges. The
counterexample therefore lies outside the assumptions of Freidel–Louapre's tree independence
(*Nucl. Phys. B* 662 (2003) 279; *Class. Quantum Grav.* 21 (2004) 5685): a triangulated 3-manifold,
boundary spins fixed, a tree through bulk vertices, and no cutoff. The gauge fixing used here, spin
`0` on the edges of a maximal tree, matches their translational gauge fixing. Whether tree
independence fails on a closed combinatorial 3-manifold is open.

Proof: the gauge set forces spin `0` on the edges `12, 13, 23, 14, 15, 45` (for `T1`) or
`12, 13, 23, 14, 35` (for `T2`) (`amplitudeGF_force`). On the remaining 4 (or 5) edges only two
colourings have admissible triangles: all spins `0` (weight `1`) and all spins `½` (weight `-8`,
resp. `-16`); every other colouring has a triangle with an odd perimeter
(`weight_eq_zero_of_not_Tri`). The two weights are computed from the edge and triangle factors and
the 6j symbols `{0 ½ ½; 0 ½ ½} = -½` and `{0 0 0; ½ ½ ½} = -1/√2` (`sixJSym_zero_left`).
-/

@[expose] public section

open Finset Lightlike.Pentagon PhyslibAlpha.Sl2

namespace Lightlike.PR.Test.Ring

set_option maxRecDepth 20000

/-- Three tetrahedra in a ring, each sharing an edge with the next. -/
def R : Complex3 (Fin 6) := ⟨{{0, 1, 2, 3}, {2, 3, 4, 5}, {4, 5, 0, 1}}, by decide⟩

/-- Cutoff `½` (doubled `1`) on every edge. -/
def half : Finset (Fin 6) → ℕ := fun _ => 1

/-- The star tree at `0`. -/
def T1 : Finset (Finset (Fin 6)) := {{0, 1}, {0, 2}, {0, 3}, {0, 4}, {0, 5}}

/-- A second maximal tree: `01, 02, 03, 04, 25`. -/
def T2 : Finset (Finset (Fin 6)) := {{0, 1}, {0, 2}, {0, 3}, {0, 4}, {2, 5}}

/-- `T1` is a maximal tree of `R`. -/
theorem isMaxTree_T1 : IsMaxTree R T1 := by
  refine ⟨by decide, ⟨by decide, ?_, by decide⟩⟩
  intro u hu v hv
  have to0 : ∀ w ∈ R.verts, Relation.ReflTransGen (fun x y => ({x, y} : Finset (Fin 6)) ∈ T1) w 0 := by
    intro w hw
    fin_cases w
    · exact .refl
    all_goals exact .single (by decide)
  have from0 : ∀ w ∈ R.verts, Relation.ReflTransGen (fun x y => ({x, y} : Finset (Fin 6)) ∈ T1) 0 w := by
    intro w hw
    fin_cases w
    · exact .refl
    all_goals exact .single (by decide)
  exact (to0 u hu).trans (from0 v hv)

/-- `T2` is a maximal tree of `R` (the vertex `5` is joined to `0` through `2`). -/
theorem isMaxTree_T2 : IsMaxTree R T2 := by
  refine ⟨by decide, ⟨by decide, ?_, by decide⟩⟩
  intro u hu v hv
  have to0 : ∀ w ∈ R.verts, Relation.ReflTransGen (fun x y => ({x, y} : Finset (Fin 6)) ∈ T2) w 0 := by
    intro w hw
    fin_cases w
    · exact .refl
    · exact .single (by decide)
    · exact .single (by decide)
    · exact .single (by decide)
    · exact .single (by decide)
    · exact .head (b := 2) (by decide) (.single (by decide))
  have from0 : ∀ w ∈ R.verts, Relation.ReflTransGen (fun x y => ({x, y} : Finset (Fin 6)) ∈ T2) 0 w := by
    intro w hw
    fin_cases w
    · exact .refl
    · exact .single (by decide)
    · exact .single (by decide)
    · exact .single (by decide)
    · exact .single (by decide)
    · exact .tail (b := 2) (.single (by decide)) (by decide)
  exact (to0 u hu).trans (from0 v hv)

/-! ## Summing over four free edges -/

/-- The sum over spins on four edges, as four nested sums (all other edges have spin `0`). -/
lemma sum_pi_four {V : Type*} [DecidableEq V] {a b c d : Finset V}
    (ha : a ∉ (insert b (insert c (insert d ∅)) : Finset (Finset V)))
    (hb : b ∉ (insert c (insert d ∅) : Finset (Finset V)))
    (hc : c ∉ (insert d ∅ : Finset (Finset V))) (t : Finset V → Finset ℕ)
    (F : Colouring V → ℝ) :
    ∑ σ ∈ (insert a (insert b (insert c (insert d ∅))) : Finset (Finset V)).pi t,
        F (extS (insert a (insert b (insert c (insert d ∅)))) σ) =
      ∑ w ∈ t d, ∑ z ∈ t c, ∑ y ∈ t b, ∑ x ∈ t a,
        F (Function.update (Function.update (Function.update (Function.update (fun _ => 0) d w)
          c z) b y) a x) := by
  rw [sum_pi_insert ha]
  have hb' := sum_pi_insert hb t (fun col => ∑ x ∈ t a, F (Function.update col a x))
  beta_reduce at hb'
  rw [hb']
  have hc' := sum_pi_insert hc t
    (fun col => ∑ y ∈ t b, ∑ x ∈ t a, F (Function.update (Function.update col b y) a x))
  beta_reduce at hc'
  rw [hc']
  have hd' := sum_pi_insert (notMem_empty d) t (fun col => ∑ z ∈ t c, ∑ y ∈ t b, ∑ x ∈ t a,
    F (Function.update (Function.update (Function.update col c z) b y) a x))
  beta_reduce at hd'
  rw [hd', pi_empty, sum_singleton]
  have h0 : extS (∅ : Finset (Finset V)) (Pi.empty _) = fun _ => 0 :=
    funext fun e => extS_of_not_mem (notMem_empty e)
  rw [h0]

/-! ## The star tree `T1`: amplitude `-7` -/

/-- Spins `x, y, z, w` on `24, 25, 34, 35`, and `0` on every other edge. -/
def c1 (x y z w : ℕ) : Colouring (Fin 6) :=
  Function.update (Function.update (Function.update (Function.update (fun _ => 0) {3, 5} w)
    {3, 4} z) {2, 5} y) {2, 4} x

/-- `T1` forces `12, 13, 23, 14, 15, 45`, which leaves `24, 25, 34, 35` free (for every cutoff). -/
theorem T1_force (cut : Finset (Fin 6) → ℕ) : amplitudeGF R T1 cut =
    amplitudeGF R (insert {4, 5} (insert {1, 5} (insert {1, 4} (insert {2, 3} (insert {1, 3}
      (insert {1, 2} T1)))))) cut := by
  rw [← amplitudeGF_force R (T := T1) (p := 1) (q := 2) (r := 0) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide),
    ← amplitudeGF_force R (T := insert {1, 2} T1) (p := 1) (q := 3) (r := 0) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    ← amplitudeGF_force R (T := insert {1, 3} (insert {1, 2} T1)) (p := 2) (q := 3) (r := 0)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    ← amplitudeGF_force R (T := insert {2, 3} (insert {1, 3} (insert {1, 2} T1))) (p := 1) (q := 4)
      (r := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    ← amplitudeGF_force R (T := insert {1, 4} (insert {2, 3} (insert {1, 3} (insert {1, 2} T1))))
      (p := 1) (q := 5) (r := 0) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide),
    ← amplitudeGF_force R
      (T := insert {1, 5} (insert {1, 4} (insert {2, 3} (insert {1, 3} (insert {1, 2} T1)))))
      (p := 4) (q := 5) (r := 0) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]

/-- The all-`½` colouring of the four free edges has weight `-8`: the four edge factors give
`(-2)^4 = 16`, the triangle signs cancel, and the tetrahedron `2345` gives `{0 ½ ½; 0 ½ ½} = -½`. -/
theorem weight_c1_one : weight R (c1 1 1 1 1) = -8 := by
  have hE : (∏ e ∈ R.edges, edgeW (c1 1 1 1 1 e)) =
      ((∏ e ∈ R.edges, (((c1 1 1 1 1 e : ℤ) + 1) * (-1) ^ (c1 1 1 1 1 e)) : ℤ) : ℝ) := by
    push_cast [edgeW]
    rfl
  have hE' : (∏ e ∈ R.edges, (((c1 1 1 1 1 e : ℤ) + 1) * (-1) ^ (c1 1 1 1 1 e))) = 16 := by
    decide
  have hF : (∏ f ∈ R.tris, triW (c1 1 1 1 1) f) =
      ((∏ f ∈ R.tris, (-1 : ℤ) ^ ((∑ e ∈ f.powersetCard 2, c1 1 1 1 1 e) / 2) : ℤ) : ℝ) := by
    push_cast [triW]
    rfl
  have hF' : (∏ f ∈ R.tris, (-1 : ℤ) ^ ((∑ e ∈ f.powersetCard 2, c1 1 1 1 1 e) / 2)) = 1 := by
    decide
  have hT : (∏ t ∈ R.tets, tetW (c1 1 1 1 1) t) = -1 / 2 := by
    rw [show R.tets = {{0, 1, 2, 3}, {2, 3, 4, 5}, {4, 5, 0, 1}} from rfl,
      prod_insert (by decide), prod_insert (by decide), prod_singleton,
      tetW_eq_tetAmp _ (by decide) (p := ![0, 1, 2, 3]) (by decide) (by decide),
      tetW_eq_tetAmp _ (by decide) (p := ![4, 5, 2, 3]) (by decide) (by decide),
      tetW_eq_tetAmp _ (by decide) (p := ![4, 5, 0, 1]) (by decide) (by decide),
      tetAmp_eq, tetAmp_eq, tetAmp_eq]
    have v : ∀ s : Finset (Fin 6), c1 1 1 1 1 s =
        if s = {2, 4} ∨ s = {2, 5} ∨ s = {3, 4} ∨ s = {3, 5} then 1 else 0 := by decide
    simp only [v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    simp (config := { decide := true }) only [ite_true, ite_false]
    simp only [sixJSym_zero_left]
    norm_num [Tri, Real.mul_self_sqrt]
  rw [weight, hE, hE', hF, hF', hT]
  norm_num

-- `done` makes `first` try the next triangle when `simp` cannot close the goal.
set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 4000000 in
/-- The weight of a colouring of the four free edges of `T1`: `1` for all spins `0`, `-8` for all
spins `½`, and `0` otherwise (some triangle of `2345` then has an odd perimeter). -/
theorem weight_c1 {x y z w : ℕ} (hx : x < 2) (hy : y < 2) (hz : z < 2) (hw : w < 2) :
    weight R (c1 x y z w) =
      if x = 1 ∧ y = 1 ∧ z = 1 ∧ w = 1 then -8 else if x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0 then 1
      else 0 := by
  interval_cases x <;> interval_cases y <;> interval_cases z <;> interval_cases w <;>
    simp only [and_self, and_false, false_and, ite_true, ite_false, one_ne_zero, zero_ne_one] <;>
    first
    | exact weight_c1_one
    | (rw [show c1 0 0 0 0 = fun _ => 0 by simp [c1]]; exact weight_zero R)
    | (refine weight_eq_zero_of_not_Tri (K := R) (p := 2) (q := 3) (r := 4) ?_ ?_ ?_ ?_ ?_ <;>
        first | decide |
          (simp (config := { decide := true }) [c1, Function.update_apply, Tri]; done))
    | (refine weight_eq_zero_of_not_Tri (K := R) (p := 2) (q := 3) (r := 5) ?_ ?_ ?_ ?_ ?_ <;>
        first | decide |
          (simp (config := { decide := true }) [c1, Function.update_apply, Tri]; done))
    | (refine weight_eq_zero_of_not_Tri (K := R) (p := 2) (q := 4) (r := 5) ?_ ?_ ?_ ?_ ?_ <;>
        first | decide |
          (simp (config := { decide := true }) [c1, Function.update_apply, Tri]; done))

/-- **With the star tree `T1` and cutoff `½`, the gauge-fixed amplitude of the ring is `-7`.** -/
theorem amplitudeGF_R_T1 : amplitudeGF R T1 half = -7 := by
  rw [T1_force]
  simp only [amplitudeGF]
  rw [show R.edges \ insert {4, 5} (insert {1, 5} (insert {1, 4} (insert {2, 3} (insert {1, 3}
      (insert {1, 2} T1))))) = insert {2, 4} (insert {2, 5} (insert {3, 4} (insert {3, 5} ∅)))
      from by decide,
    sum_pi_four (by decide) (by decide) (by decide)]
  change ∑ w ∈ _, ∑ z ∈ _, ∑ y ∈ _, ∑ x ∈ _, weight R (c1 x y z w) = -7
  have key : ∀ w ∈ range (half {3, 5} + 1), ∀ z ∈ range (half {3, 4} + 1),
      ∀ y ∈ range (half {2, 5} + 1), ∀ x ∈ range (half {2, 4} + 1),
      weight R (c1 x y z w) =
        if x = 1 ∧ y = 1 ∧ z = 1 ∧ w = 1 then -8 else if x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0 then 1
        else 0 := fun w hw z hz y hy x hx => by
    simp only [half, mem_range] at hw hz hy hx
    exact weight_c1 hx hy hz hw
  rw [sum_congr rfl fun w hw => sum_congr rfl fun z hz => sum_congr rfl fun y hy =>
    sum_congr rfl fun x hx => key w hw z hz y hy x hx]
  simp only [half, sum_range_succ, sum_range_zero]
  norm_num

/-! ## The tree `T2`: amplitude `-15` -/

/-- The sum over spins on five edges, as five nested sums (all other edges have spin `0`). -/
lemma sum_pi_five {V : Type*} [DecidableEq V] {a b c d e : Finset V}
    (ha : a ∉ (insert b (insert c (insert d (insert e ∅))) : Finset (Finset V)))
    (hb : b ∉ (insert c (insert d (insert e ∅)) : Finset (Finset V)))
    (hc : c ∉ (insert d (insert e ∅) : Finset (Finset V)))
    (hd : d ∉ (insert e ∅ : Finset (Finset V))) (t : Finset V → Finset ℕ)
    (F : Colouring V → ℝ) :
    ∑ σ ∈ (insert a (insert b (insert c (insert d (insert e ∅)))) : Finset (Finset V)).pi t,
        F (extS (insert a (insert b (insert c (insert d (insert e ∅))))) σ) =
      ∑ v ∈ t e, ∑ w ∈ t d, ∑ z ∈ t c, ∑ y ∈ t b, ∑ x ∈ t a,
        F (Function.update (Function.update (Function.update (Function.update
          (Function.update (fun _ => 0) e v) d w) c z) b y) a x) := by
  rw [sum_pi_insert ha]
  have h4 := sum_pi_four hb hc hd t (fun col => ∑ x ∈ t a, F (Function.update col a x))
  beta_reduce at h4
  exact h4

/-- Spins `x, y, z, w, v` on `05, 15, 24, 34, 45`, and `0` on every other edge. -/
def c2 (x y z w v : ℕ) : Colouring (Fin 6) :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (fun _ => 0) {4, 5} v) {3, 4} w) {2, 4} z) {5, 1} y) {5, 0} x

/-- `T2` forces `12, 13, 23, 14` and then `35` (through the triangle `235`), which leaves
`05, 15, 24, 34, 45` free. -/
theorem T2_force : amplitudeGF R T2 half =
    amplitudeGF R (insert {3, 5} (insert {1, 4} (insert {2, 3} (insert {1, 3} (insert {1, 2}
      T2))))) half := by
  rw [← amplitudeGF_force R (T := T2) (p := 1) (q := 2) (r := 0) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide),
    ← amplitudeGF_force R (T := insert {1, 2} T2) (p := 1) (q := 3) (r := 0) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    ← amplitudeGF_force R (T := insert {1, 3} (insert {1, 2} T2)) (p := 2) (q := 3) (r := 0)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    ← amplitudeGF_force R (T := insert {2, 3} (insert {1, 3} (insert {1, 2} T2))) (p := 1) (q := 4)
      (r := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    ← amplitudeGF_force R (T := insert {1, 4} (insert {2, 3} (insert {1, 3} (insert {1, 2} T2))))
      (p := 3) (q := 5) (r := 2) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]

/-- The all-`½` colouring of the five free edges has weight `-16`: the edge factors give
`(-2)^5 = -32`, the triangle signs cancel, and the tetrahedra `2345`, `4501` each give
`{0 0 0; ½ ½ ½} = -1/√2`. -/
theorem weight_c2_one : weight R (c2 1 1 1 1 1) = -16 := by
  have hE : (∏ e ∈ R.edges, edgeW (c2 1 1 1 1 1 e)) =
      ((∏ e ∈ R.edges, (((c2 1 1 1 1 1 e : ℤ) + 1) * (-1) ^ (c2 1 1 1 1 1 e)) : ℤ) : ℝ) := by
    push_cast [edgeW]
    rfl
  have hE' : (∏ e ∈ R.edges, (((c2 1 1 1 1 1 e : ℤ) + 1) * (-1) ^ (c2 1 1 1 1 1 e))) = -32 := by
    decide
  have hF : (∏ f ∈ R.tris, triW (c2 1 1 1 1 1) f) =
      ((∏ f ∈ R.tris, (-1 : ℤ) ^ ((∑ e ∈ f.powersetCard 2, c2 1 1 1 1 1 e) / 2) : ℤ) : ℝ) := by
    push_cast [triW]
    rfl
  have hF' : (∏ f ∈ R.tris, (-1 : ℤ) ^ ((∑ e ∈ f.powersetCard 2, c2 1 1 1 1 1 e) / 2)) = 1 := by
    decide
  have hT : (∏ t ∈ R.tets, tetW (c2 1 1 1 1 1) t) = 1 / 2 := by
    rw [show R.tets = {{0, 1, 2, 3}, {2, 3, 4, 5}, {4, 5, 0, 1}} from rfl,
      prod_insert (by decide), prod_insert (by decide), prod_singleton,
      tetW_eq_tetAmp _ (by decide) (p := ![0, 1, 2, 3]) (by decide) (by decide),
      tetW_eq_tetAmp _ (by decide) (p := ![4, 5, 2, 3]) (by decide) (by decide),
      tetW_eq_tetAmp _ (by decide) (p := ![5, 4, 0, 1]) (by decide) (by decide),
      tetAmp_eq, tetAmp_eq, tetAmp_eq]
    simp (config := { decide := true }) only [c2, Function.update_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons, ite_true, ite_false]
    simp only [sixJSym_zero_left]
    norm_num [Tri, Real.mul_self_sqrt, div_mul_div_comm]
  rw [weight, hE, hE', hF, hF', hT]
  norm_num

set_option linter.unusedTactic false in
set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 8000000 in
/-- The weight of a colouring of the five free edges of `T2`: `1` for all spins `0`, `-16` for all
spins `½`, and `0` otherwise (some triangle then has an odd perimeter). -/
theorem weight_c2 {x y z w v : ℕ} (hx : x < 2) (hy : y < 2) (hz : z < 2) (hw : w < 2)
    (hv : v < 2) :
    weight R (c2 x y z w v) =
      if x = 1 ∧ y = 1 ∧ z = 1 ∧ w = 1 ∧ v = 1 then -16
      else if x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0 ∧ v = 0 then 1 else 0 := by
  by_cases h1 : x = 1 ∧ y = 1 ∧ z = 1 ∧ w = 1 ∧ v = 1
  · obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h1
    simpa using weight_c2_one
  by_cases h0 : x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0 ∧ v = 0
  · obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h0
    simp only [and_self, ite_true, one_ne_zero, ite_false, false_and, and_false]
    rw [show c2 0 0 0 0 0 = fun _ => 0 by simp [c2]]
    exact weight_zero R
  simp only [h1, h0, ite_false]
  interval_cases x <;> interval_cases y <;> interval_cases z <;> interval_cases w <;>
    interval_cases v <;>
    first
    | exact absurd ⟨rfl, rfl, rfl, rfl, rfl⟩ h1
    | exact absurd ⟨rfl, rfl, rfl, rfl, rfl⟩ h0
    | (refine weight_eq_zero_of_not_Tri (K := R) (p := 2) (q := 3) (r := 4) (by decide) (by decide)
        (by decide) (by decide) ?_
       simp (config := { decide := true }) [c2, Function.update_apply, Tri]; done)
    | (refine weight_eq_zero_of_not_Tri (K := R) (p := 2) (q := 4) (r := 5) (by decide) (by decide)
        (by decide) (by decide) ?_
       simp (config := { decide := true }) [c2, Function.update_apply, Tri]; done)
    | (refine weight_eq_zero_of_not_Tri (K := R) (p := 4) (q := 5) (r := 0) (by decide) (by decide)
        (by decide) (by decide) ?_
       simp (config := { decide := true }) [c2, Function.update_apply, Tri]; done)
    | (refine weight_eq_zero_of_not_Tri (K := R) (p := 4) (q := 5) (r := 1) (by decide) (by decide)
        (by decide) (by decide) ?_
       simp (config := { decide := true }) [c2, Function.update_apply, Tri]; done)

/-- **With the tree `T2` and cutoff `½`, the gauge-fixed amplitude of the ring is `-15`.** -/
theorem amplitudeGF_R_T2 : amplitudeGF R T2 half = -15 := by
  rw [T2_force]
  simp only [amplitudeGF]
  rw [show R.edges \ insert {3, 5} (insert {1, 4} (insert {2, 3} (insert {1, 3} (insert {1, 2}
      T2)))) = insert {5, 0} (insert {5, 1} (insert {2, 4} (insert {3, 4} (insert {4, 5} ∅))))
      from by decide,
    sum_pi_five (by decide) (by decide) (by decide) (by decide)]
  change ∑ v ∈ _, ∑ w ∈ _, ∑ z ∈ _, ∑ y ∈ _, ∑ x ∈ _, weight R (c2 x y z w v) = -15
  have key : ∀ v ∈ range (half {4, 5} + 1), ∀ w ∈ range (half {3, 4} + 1),
      ∀ z ∈ range (half {2, 4} + 1), ∀ y ∈ range (half {5, 1} + 1),
      ∀ x ∈ range (half {5, 0} + 1),
      weight R (c2 x y z w v) =
        if x = 1 ∧ y = 1 ∧ z = 1 ∧ w = 1 ∧ v = 1 then -16
        else if x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0 ∧ v = 0 then 1 else 0 :=
    fun v hv w hw z hz y hy x hx => by
      simp only [half, mem_range] at hv hw hz hy hx
      exact weight_c2 hx hy hz hw hv
  rw [sum_congr rfl fun v hv => sum_congr rfl fun w hw => sum_congr rfl fun z hz =>
    sum_congr rfl fun y hy => sum_congr rfl fun x hx => key v hv w hw z hz y hy x hx]
  simp only [half, sum_range_succ, sum_range_zero]
  norm_num

/-! ## Conclusion -/

/-- **Independence of the maximal tree fails**: `T1` and `T2` are maximal trees of `R`, and with
cutoff `½` their gauge-fixed amplitudes differ (`-7` and `-15`). -/
theorem amplitudeGF_tree_dependent :
    IsMaxTree R T1 ∧ IsMaxTree R T2 ∧ amplitudeGF R T1 half ≠ amplitudeGF R T2 half :=
  ⟨isMaxTree_T1, isMaxTree_T2, by rw [amplitudeGF_R_T1, amplitudeGF_R_T2]; norm_num⟩

/-- The link of the vertex `0` in `R`: the triangles `123` and `145`, which share only the vertex
`1`. Its Euler characteristic is `1`. -/
theorem euler2_link_R : euler2 (R.link 0) = 1 := by decide

/-- **`R` is not a combinatorial 3-manifold**: the link of `0` is not a 2-sphere (its Euler
characteristic is `1`). The tetrahedra of `R` meet only along edges, so every triangle is a
boundary triangle. The counterexamples on `R` therefore lie outside the assumptions of
Freidel–Louapre's tree independence, which is stated for triangulated 3-manifolds. -/
theorem not_isCombManifold_R : ¬ IsCombManifold R := fun h => by
  have := (h 0 (by decide)).euler
  rw [euler2_link_R] at this
  exact absurd this (by decide)

/-- Consequently `T1` and `T2` are **not** connected by triangle exchanges
(otherwise `amplitudeGF_eqvGen_exchange` would make the amplitudes equal). -/
theorem not_eqvGen_exchange_T1_T2 : ¬ Relation.EqvGen (TreeExchange R) T1 T2 := fun h =>
  amplitudeGF_tree_dependent.2.2 (amplitudeGF_eqvGen_exchange R h half)

end Lightlike.PR.Test.Ring
