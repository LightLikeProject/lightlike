import Lightlike.FourD.Pachner
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Orientation of 4-complexes

Orientations are handled as in ordered simplicial homology: the vertex type carries a linear
order, and a simplex `s` (a vertex set) stands for the oriented simplex with its vertices in
increasing order. An orientation of a 4-complex is then a sign `±1` for each 4-simplex.

## Chains and the boundary operator (every dimension)

* `pos s v`: the number of vertices of `s` below `v`; `inc s v = (-1)^(pos s v)`, the sign of
  the face `s \ {v}` in the boundary of `s`.
* `Chain V = Finset V →₀ ℤ`: integer chains, `bd : Chain V →ₗ[ℤ] Chain V` the boundary operator,
  `bd [s] = Σ_{v ∈ s} inc s v • [s \ {v}]`.
* `cone a`: the cone with apex `a`; `osimp l`: the oriented simplex `[v₀, …, vₖ]` for a list of
  vertices `l = [v₀, …, vₖ]` in any order, defined as an iterated cone.

## Orientations of 4-complexes

* `relSign s t`: the incidence number `[s : t]` of a simplex and a face with one vertex less.
* `fundChain F o = Σ_{s ∈ F} o s • [s]`.
* `IsOrientation K o`: `o s = ±1` on the 4-simplices, and two 4-simplices sharing a tetrahedron
  induce opposite orientations on it. `IsOrientable K`: some orientation exists.

## Main results

* `bd_bd`: **`∂ ∘ ∂ = 0`**.
* `bd_osimp`: the textbook formula `∂[v₀, …, vₖ] = Σᵢ (-1)^i [v₀, …, v̂ᵢ, …, vₖ]` for every
  ordering; `osimp_sort`: `[s]` is the oriented simplex with increasing vertices;
  `osimp_swap`, `osimp_swap_append`: exchanging two neighbouring vertices reverses the
  orientation, so `[v₀, …, vₖ]` is the sign of the sorting permutation times the basis simplex.
  The conventions here are the standard ones (e.g. Munkres, *Elements of Algebraic Topology*,
  §5).
* `IsOrientation.isPseudo4`: an orientable complex is a pseudo-manifold.
* `isOrientation_iff`, `isOrientation_iff_of_closed`: an orientation is a choice of signs whose
  fundamental chain has no boundary on the interior tetrahedra; for a closed complex, a
  fundamental cycle.
* `bd_fundChain`: the boundary of the fundamental chain is the fundamental chain of the boundary
  tetrahedra with the induced orientation (and it is a cycle, by `bd_bd`).
* `isOrientation_sphere`: the boundary of a 5-simplex is orientable.
* `isOrientable_move_iff`: **Pachner moves preserve orientability**, in both directions.
-/

open Finset

namespace Lightlike.FourD

variable {V : Type*} [LinearOrder V]

/-! ## Incidence signs -/

/-- The position of `v` among the vertices of `s`: the number of vertices of `s` below `v`. -/
def pos (s : Finset V) (v : V) : ℕ := #(s.filter (· < v))

/-- The sign `(-1)^(pos s v)` of the face `s \ {v}` in the boundary of the simplex `s`. -/
def inc (s : Finset V) (v : V) : ℤ := (-1) ^ pos s v

lemma inc_eq_one_or (s : Finset V) (v : V) : inc s v = 1 ∨ inc s v = -1 :=
  neg_one_pow_eq_or ℤ _

lemma inc_mul_self (s : Finset V) (v : V) : inc s v * inc s v = 1 := by
  rcases inc_eq_one_or s v with h | h <;> rw [h] <;> norm_num

lemma pos_erase_of_lt {s : Finset V} {v w : V} (h : w < v) : pos (s.erase v) w = pos s w := by
  unfold pos
  rw [filter_erase, erase_eq_of_notMem]
  simp [h.le]

lemma pos_erase_of_gt {s : Finset V} {v w : V} (hv : v ∈ s) (h : v < w) :
    pos (s.erase v) w + 1 = pos s w := by
  unfold pos
  rw [filter_erase, card_erase_add_one (mem_filter.mpr ⟨hv, h⟩)]

lemma pos_insert_of_lt {s : Finset V} {a v : V} (ha : a ∉ s) (h : a < v) :
    pos (insert a s) v = pos s v + 1 := by
  unfold pos
  rw [filter_insert, ite_eq_left h, card_insert_of_notMem (fun h' => ha (mem_filter.mp h').1)]

lemma pos_insert_of_gt {s : Finset V} {a v : V} (h : v < a) : pos (insert a s) v = pos s v := by
  unfold pos
  rw [filter_insert, ite_eq_right (not_lt.mpr h.le)]

lemma inc_erase_of_lt {s : Finset V} {v w : V} (h : w < v) : inc (s.erase v) w = inc s w := by
  rw [inc, inc, pos_erase_of_lt h]

lemma inc_erase_of_gt {s : Finset V} {v w : V} (hv : v ∈ s) (h : v < w) :
    inc (s.erase v) w = -inc s w := by
  rw [inc, inc, ← pos_erase_of_gt hv h, pow_succ]
  ring

lemma inc_insert_of_lt {s : Finset V} {a v : V} (ha : a ∉ s) (h : a < v) :
    inc (insert a s) v = -inc s v := by
  rw [inc, inc, pos_insert_of_lt ha h, pow_succ]
  ring

lemma inc_insert_of_gt {s : Finset V} {a v : V} (h : v < a) : inc (insert a s) v = inc s v := by
  rw [inc, inc, pos_insert_of_gt h]

lemma inc_insert_self {s : Finset V} {a : V} : inc (insert a s) a = inc s a := by
  rw [inc, inc, pos, pos, filter_insert, ite_eq_right (lt_irrefl a)]

/-- **The sign identity behind `∂ ∘ ∂ = 0`**: removing `v` and then `w` from `s` gives the
opposite sign to removing `w` and then `v`. -/
theorem inc_mul_inc_erase {s : Finset V} {v w : V} (hv : v ∈ s) (hw : w ∈ s) (hvw : v ≠ w) :
    inc s v * inc (s.erase v) w = -(inc s w * inc (s.erase w) v) := by
  rcases lt_or_gt_of_ne hvw with h | h
  · rw [inc_erase_of_gt hv h, inc_erase_of_lt h]
    ring
  · rw [inc_erase_of_lt h, inc_erase_of_gt hw h]
    ring

/-! ## Chains and the boundary operator -/

/-- Integer chains: finite formal combinations of vertex sets, each standing for the simplex
with its vertices in increasing order. -/
abbrev Chain (V : Type*) := Finset V →₀ ℤ

open Finsupp (single)

/-- The boundary of the simplex `s`: `Σ_{v ∈ s} inc s v • [s \ {v}]`. -/
noncomputable def bdSimplex (s : Finset V) : Chain V :=
  ∑ v ∈ s, inc s v • single (s.erase v) 1

/-- The boundary operator on chains. -/
noncomputable def bd : Chain V →ₗ[ℤ] Chain V := Finsupp.linearCombination ℤ bdSimplex

lemma bd_single (s : Finset V) (c : ℤ) : bd (single s c) = c • bdSimplex s :=
  Finsupp.linearCombination_single ℤ c s

/-- A double sum `Σ_{v ∈ s} Σ_{w ∈ s, w ≠ v} F v w` of chains vanishes when `F` is antisymmetric. -/
lemma sum_sum_erase_antisymm {s : Finset V} (F : V → V → Chain V)
    (hF : ∀ v ∈ s, ∀ w ∈ s, v ≠ w → F w v = -F v w) :
    ∑ v ∈ s, ∑ w ∈ s.erase v, F v w = 0 := by
  set G : V → V → Chain V := fun v w => if v = w then 0 else F v w with hG
  have h1 : ∀ v ∈ s, ∑ w ∈ s.erase v, F v w = ∑ w ∈ s, G v w := by
    intro v _
    rw [← sum_erase s (by simp [hG] : G v v = 0)]
    exact sum_congr rfl fun w hw => by simp [hG, (ne_of_mem_erase hw).symm]
  have hanti : ∀ v ∈ s, ∀ w ∈ s, G w v = -G v w := by
    intro v hv w hw
    by_cases hvw : v = w
    · simp [hG, hvw]
    · simp only [hG, ite_eq_right hvw, ite_eq_right (Ne.symm hvw), hF v hv w hw hvw]
  rw [sum_congr rfl h1]
  set T := ∑ v ∈ s, ∑ w ∈ s, G v w with hT
  have hneg : T = -T := by
    calc T = ∑ w ∈ s, ∑ v ∈ s, G v w := sum_comm
      _ = ∑ w ∈ s, ∑ v ∈ s, -G w v := sum_congr rfl fun w hw =>
          sum_congr rfl fun v hv => hanti w hw v hv
      _ = -T := by simp only [hT, sum_neg_distrib]
  ext x
  have := DFunLike.congr_fun hneg x
  simp only [Finsupp.coe_neg, Pi.neg_apply] at this
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  omega

/-- `∂∂[s] = 0` for a single simplex. -/
theorem bd_bdSimplex (s : Finset V) : bd (bdSimplex s) = 0 := by
  have h : bd (bdSimplex s) = ∑ v ∈ s, ∑ w ∈ s.erase v,
      (inc s v * inc (s.erase v) w) • single ((s.erase v).erase w) 1 := by
    simp only [bdSimplex, map_sum, map_zsmul, bd_single, smul_sum, smul_smul, one_mul]
  rw [h]
  refine sum_sum_erase_antisymm _ fun v hv w hw hvw => ?_
  rw [inc_mul_inc_erase hw hv (Ne.symm hvw), erase_right_comm, neg_smul]

/-- **`∂ ∘ ∂ = 0`.** -/
theorem bd_bd (c : Chain V) : bd (bd c) = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single s c => rw [bd_single, map_zsmul, bd_bdSimplex, smul_zero]

/-! ## Cones and oriented simplices for arbitrary vertex orderings -/

/-- The cone with apex `a` on the simplex `s`: the simplex `s ∪ {a}`, with the sign that puts `a`
first, and `0` if `a ∈ s`. -/
noncomputable def coneSimplex (a : V) (s : Finset V) : Chain V :=
  if a ∈ s then 0 else inc s a • single (insert a s) 1

/-- The cone with apex `a`, as a linear map on chains. -/
noncomputable def cone (a : V) : Chain V →ₗ[ℤ] Chain V :=
  Finsupp.linearCombination ℤ (coneSimplex a)

lemma cone_single (a : V) (s : Finset V) (c : ℤ) :
    cone a (single s c) = c • coneSimplex a s :=
  Finsupp.linearCombination_single ℤ c s

/-- **The cone identity** `∂(a * x) = x - a * ∂x` for a simplex `x` not containing `a`. -/
theorem bd_cone_single {a : V} {s : Finset V} (ha : a ∉ s) :
    bd (cone a (single s 1)) = single s 1 - cone a (bd (single s 1)) := by
  have hL : bd (cone a (single s 1)) = single s 1 +
      ∑ v ∈ s, (inc s a * inc (insert a s) v) • single (insert a (s.erase v)) 1 := by
    rw [cone_single, one_smul, coneSimplex, ite_eq_right ha, map_zsmul, bd_single, one_smul,
      bdSimplex, sum_insert ha, erase_insert ha, smul_add, smul_smul, inc_insert_self,
      inc_mul_self, one_smul, smul_sum]
    congr 1
    refine sum_congr rfl fun v hv => ?_
    rw [smul_smul, erase_insert_of_ne (fun h : a = v => ha (h ▸ hv))]
  have hR : cone a (bd (single s 1)) =
      ∑ v ∈ s, (inc s v * inc (s.erase v) a) • single (insert a (s.erase v)) 1 := by
    rw [bd_single, one_smul, bdSimplex, map_sum]
    refine sum_congr rfl fun v _ => ?_
    rw [map_zsmul, cone_single, one_smul, coneSimplex,
      ite_eq_right (fun h => ha (mem_of_mem_erase h)), smul_smul]
  rw [hL, hR, sub_eq_add_neg, ← sum_neg_distrib]
  congr 1
  refine sum_congr rfl fun v hv => ?_
  rw [← neg_smul]
  congr 1
  have hav : a ≠ v := fun h => ha (h ▸ hv)
  rcases lt_or_gt_of_ne hav with h | h
  · rw [inc_insert_of_lt ha h, inc_erase_of_lt h]
    ring
  · rw [inc_insert_of_gt h, inc_erase_of_gt hv h]
    ring

/-- The cone identity for multiples of a simplex not containing `a`. -/
lemma bd_cone_smul {a : V} {s : Finset V} (ha : a ∉ s) (c : ℤ) :
    bd (cone a (c • single s 1)) = c • single s 1 - cone a (bd (c • single s 1)) := by
  rw [map_zsmul, map_zsmul, bd_cone_single ha, map_zsmul, map_zsmul, smul_sub]

/-- The oriented simplex `[v₀, …, vₖ]` for a list of vertices: the iterated cone
`v₀ * (v₁ * ⋯ (vₖ * [∅]))`. -/
noncomputable def osimp : List V → Chain V
  | [] => single ∅ 1
  | a :: l => cone a (osimp l)

/-- For distinct vertices, `[v₀, …, vₖ]` is `±1` times the simplex `{v₀, …, vₖ}`. -/
theorem osimp_eq {l : List V} (hl : l.Nodup) :
    ∃ c : ℤ, (c = 1 ∨ c = -1) ∧ osimp l = c • single l.toFinset 1 := by
  induction l with
  | nil => exact ⟨1, Or.inl rfl, by simp [osimp]⟩
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := List.nodup_cons.mp hl
    obtain ⟨c, hc, he⟩ := ih hl
    have ha' : a ∉ l.toFinset := fun h => ha (List.mem_toFinset.mp h)
    refine ⟨c * inc l.toFinset a, ?_, ?_⟩
    · rcases hc with rfl | rfl <;> rcases inc_eq_one_or l.toFinset a with h | h <;> simp [h]
    · rw [osimp, he, map_zsmul, cone_single, one_smul, coneSimplex, ite_eq_right ha', smul_smul,
        List.toFinset_cons]

/-- **The textbook boundary formula** `∂[v₀, …, vₖ] = Σᵢ (-1)^i [v₀, …, v̂ᵢ, …, vₖ]`, for every
list of distinct vertices. -/
theorem bd_osimp {l : List V} (hl : l.Nodup) :
    bd (osimp l) = ∑ i : Fin l.length, ((-1 : ℤ) ^ (i : ℕ)) • osimp (l.eraseIdx i) := by
  induction l with
  | nil => simp [osimp, bd_single, bdSimplex]
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := List.nodup_cons.mp hl
    obtain ⟨c, -, he⟩ := osimp_eq hl
    have ha' : a ∉ l.toFinset := fun h => ha (List.mem_toFinset.mp h)
    have hcone : bd (osimp (a :: l)) = osimp l - cone a (bd (osimp l)) := by
      rw [osimp, he, bd_cone_smul ha']
    rw [hcone, ih hl, map_sum]
    show _ = ∑ i : Fin (l.length + 1), ((-1 : ℤ) ^ (i : ℕ)) • osimp ((a :: l).eraseIdx i)
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_smul, List.eraseIdx_cons_zero, Fin.val_succ,
      List.eraseIdx_cons_succ, map_zsmul, pow_succ, mul_neg_one, neg_smul, osimp]
    rw [sum_neg_distrib, sub_eq_add_neg]

/-- The basis chain `[s]` is the oriented simplex with the vertices of `s` in increasing order. -/
theorem osimp_sort (s : Finset V) : osimp (s.sort (· ≤ ·)) = single s 1 := by
  have hsorted : (s.sort (· ≤ ·)).Pairwise (· < ·) :=
    ((pairwise_sort s (· ≤ ·)).and (sort_nodup s (· ≤ ·))).imp fun h => lt_of_le_of_ne h.1 h.2
  have key : ∀ l : List V, l.Pairwise (· < ·) → osimp l = single l.toFinset 1 := by
    intro l hl
    induction l with
    | nil => rfl
    | cons a l ih =>
      obtain ⟨hal, hl⟩ := List.pairwise_cons.mp hl
      have ha : a ∉ l.toFinset := fun h => lt_irrefl a (hal a (List.mem_toFinset.mp h))
      have hpos : pos l.toFinset a = 0 := by
        rw [pos, card_eq_zero, filter_eq_empty_iff]
        exact fun b hb hba => lt_asymm hba (hal b (List.mem_toFinset.mp hb))
      rw [osimp, ih hl, cone_single, one_smul, coneSimplex, ite_eq_right ha, inc, hpos, pow_zero,
        one_smul, List.toFinset_cons]
  rw [key _ hsorted, sort_toFinset]

/-- **Exchanging the first two vertices reverses the orientation.** -/
theorem osimp_swap {a b : V} {l : List V} (hl : (a :: b :: l).Nodup) :
    osimp (a :: b :: l) = -osimp (b :: a :: l) := by
  obtain ⟨ha, hl'⟩ := List.nodup_cons.mp hl
  obtain ⟨hb, hl⟩ := List.nodup_cons.mp hl'
  have hab : a ≠ b := fun h => ha (h ▸ List.mem_cons_self)
  have ha' : a ∉ l.toFinset := fun h => ha (List.mem_cons_of_mem b (List.mem_toFinset.mp h))
  have hb' : b ∉ l.toFinset := fun h => hb (List.mem_toFinset.mp h)
  obtain ⟨c, -, he⟩ := osimp_eq hl
  have h1 : a ∉ insert b l.toFinset := by rw [mem_insert, not_or]; exact ⟨hab, ha'⟩
  have h2 : b ∉ insert a l.toFinset := by rw [mem_insert, not_or]; exact ⟨hab.symm, hb'⟩
  simp only [osimp, he, map_zsmul, cone_single, coneSimplex, ite_eq_right ha',
    ite_eq_right hb', ite_eq_right h1, ite_eq_right h2, smul_smul]
  rw [insert_comm a b, ← neg_smul]
  congr 1
  rcases lt_or_gt_of_ne hab with h | h
  · rw [inc_insert_of_gt h, inc_insert_of_lt ha' h]
    ring
  · rw [inc_insert_of_lt hb' h, inc_insert_of_gt h]
    ring

/-- **Exchanging two neighbouring vertices anywhere reverses the orientation.** Since such
transpositions generate all permutations and `osimp_sort` fixes the increasing order,
`[v₀, …, vₖ]` is the sign of the sorting permutation times `[{v₀, …, vₖ}]`: the definition of
oriented simplices as classes of vertex orderings. -/
theorem osimp_swap_append {a b : V} (p : List V) {q : List V} (hl : (p ++ a :: b :: q).Nodup) :
    osimp (p ++ a :: b :: q) = -osimp (p ++ b :: a :: q) := by
  induction p with
  | nil => exact osimp_swap hl
  | cons c p ih =>
    simp only [List.cons_append, osimp]
    rw [ih (List.nodup_cons.mp hl).2, map_neg]

/-! ## Incidence numbers and fundamental chains -/

/-- A face `t ⊆ s` with one vertex less is `s \ {v}` for a vertex `v` of `s`. -/
lemma exists_eq_erase {s t : Finset V} (hts : t ⊆ s) (hc : #s = #t + 1) :
    ∃ v ∈ s, t = s.erase v := by
  obtain ⟨v, hv⟩ := card_eq_one.mp (by rw [card_sdiff_of_subset hts, hc]; omega : #(s \ t) = 1)
  have hvs : v ∈ s \ t := hv ▸ mem_singleton_self v
  refine ⟨v, (mem_sdiff.mp hvs).1, ?_⟩
  rw [erase_eq, ← hv, Finset.sdiff_sdiff_eq_self hts]

/-- The faces of `S` with one vertex less are the sets `S \ {v}`. -/
lemma powersetCard_eq_image_erase {S : Finset V} {n : ℕ} (hS : #S = n + 1) :
    S.powersetCard n = S.image S.erase := by
  ext t
  simp only [mem_powersetCard, mem_image]
  constructor
  · rintro ⟨hts, ht⟩
    obtain ⟨v, hv, rfl⟩ := exists_eq_erase hts (by rw [hS, ht])
    exact ⟨v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨erase_subset v S, by rw [card_erase_of_mem hv, hS, Nat.add_sub_cancel]⟩

/-- The incidence number `[s : t]` of a simplex `s` and a face `t` with one vertex less: the
sign `inc s v` of the vertex `v` of `s` that is not in `t`. -/
def relSign (s t : Finset V) : ℤ := ∑ v ∈ s \ t, inc s v

lemma relSign_erase {s : Finset V} {v : V} (hv : v ∈ s) : relSign s (s.erase v) = inc s v := by
  rw [relSign, sdiff_erase_self hv, sum_singleton]

lemma relSign_eq_one_or {s t : Finset V} (hts : t ⊆ s) (hc : #s = #t + 1) :
    relSign s t = 1 ∨ relSign s t = -1 := by
  obtain ⟨v, hv, rfl⟩ := exists_eq_erase hts hc
  rw [relSign_erase hv]
  exact inc_eq_one_or s v

/-- The coefficient of `t` in `∂[s]` is `[s : t]` if `t` is a face of `s` with one vertex less,
and `0` otherwise. -/
lemma bdSimplex_apply (s t : Finset V) :
    bdSimplex s t = if t ⊆ s ∧ #s = #t + 1 then relSign s t else 0 := by
  rw [bdSimplex, Finsupp.finsetSum_apply]
  simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [← sum_filter]
  split_ifs with h
  · obtain ⟨v, hv, rfl⟩ := exists_eq_erase h.1 h.2
    rw [relSign_erase hv]
    have : s.filter (fun x => s.erase x = s.erase v) = {v} := by
      ext x
      simp only [mem_filter, mem_singleton]
      constructor
      · rintro ⟨hx, he⟩
        exact erase_injOn s hx hv he
      · rintro rfl
        exact ⟨hv, rfl⟩
    rw [this, sum_singleton]
  · refine sum_eq_zero fun v hv => absurd ?_ h
    obtain ⟨hvs, he⟩ := mem_filter.mp hv
    rw [← he]
    have := card_pos.mpr ⟨v, hvs⟩
    exact ⟨erase_subset v s, by rw [card_erase_of_mem hvs]; omega⟩

/-- The fundamental chain `Σ_{s ∈ F} o s • [s]` of a family of simplices with signs `o`. -/
noncomputable def fundChain (F : Finset (Finset V)) (o : Finset V → ℤ) : Chain V :=
  ∑ s ∈ F, o s • single s 1

lemma bd_fundChain_apply (F : Finset (Finset V)) (o : Finset V → ℤ) (t : Finset V) :
    bd (fundChain F o) t = ∑ s ∈ F, o s * bdSimplex s t := by
  simp only [fundChain, map_sum, map_zsmul, bd_single, one_smul, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, smul_eq_mul]

namespace Complex4

/-- The coefficient of a tetrahedron `t` in the boundary of the fundamental chain of `K`:
`Σ_{s ∋ t} o s • [s : t]`. -/
lemma bd_fundChain_apply_tet (K : Complex4 V) (o : Finset V → ℤ) {t : Finset V} (ht : #t = 4) :
    bd (fundChain K.simps o) t = ∑ s ∈ K.star t, o s * relSign s t := by
  rw [bd_fundChain_apply, Complex4.star, sum_filter]
  refine sum_congr rfl fun s hs => ?_
  simp only [bdSimplex_apply, K.card_eq s hs, ht]
  by_cases h : t ⊆ s <;> simp [h]

/-- Only tetrahedra of `K` occur in the boundary of its fundamental chain. -/
lemma bd_fundChain_apply_of_notMem (K : Complex4 V) (o : Finset V → ℤ) {t : Finset V}
    (ht : t ∉ K.tets) : bd (fundChain K.simps o) t = 0 := by
  rw [bd_fundChain_apply]
  refine sum_eq_zero fun s hs => ?_
  rw [bdSimplex_apply, ite_eq_right, mul_zero]
  rintro ⟨hts, hc⟩
  exact ht (mem_faces.mpr ⟨s, hs, hts, by rw [K.card_eq s hs] at hc; omega⟩)

/-! ## Orientations -/

/-- **An orientation of a 4-complex**: a sign `o s = ±1` for every 4-simplex (the orientation
of `s` relative to the increasing order of its vertices) such that two distinct 4-simplices
sharing a tetrahedron `t` induce opposite orientations on `t`. -/
structure IsOrientation (K : Complex4 V) (o : Finset V → ℤ) : Prop where
  sign : ∀ s ∈ K.simps, o s = 1 ∨ o s = -1
  coherent : ∀ s ∈ K.simps, ∀ s' ∈ K.simps, s ≠ s' → ∀ t ∈ K.tets, t ⊆ s → t ⊆ s' →
    o s * relSign s t = -(o s' * relSign s' t)

/-- `K` has an orientation. -/
def IsOrientable (K : Complex4 V) : Prop := ∃ o, K.IsOrientation o

variable {K : Complex4 V} {o : Finset V → ℤ}

lemma IsOrientation.sign_mul (ho : K.IsOrientation o) {s t : Finset V} (hs : s ∈ K.simps)
    (hts : t ⊆ s) (ht : #t = 4) : o s * relSign s t = 1 ∨ o s * relSign s t = -1 := by
  have h2 := relSign_eq_one_or hts (by rw [K.card_eq s hs, ht])
  rcases ho.sign s hs with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp [h1, h2]

/-- **An orientable complex is a pseudo-manifold**: three 4-simplices around one tetrahedron
cannot induce pairwise opposite orientations on it. -/
theorem IsOrientation.isPseudo4 (ho : K.IsOrientation o) : K.IsPseudo4 := by
  intro t ht
  have ht4 : #t = 4 := card_of_mem_faces ht
  by_contra hlt
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := two_lt_card.mp (not_le.mp hlt)
  rw [mem_star] at ha hb hc
  have h1 := ho.coherent a ha.1 b hb.1 hab t ht ha.2 hb.2
  have h2 := ho.coherent b hb.1 c hc.1 hbc t ht hb.2 hc.2
  have h3 := ho.coherent a ha.1 c hc.1 hac t ht ha.2 hc.2
  rcases ho.sign_mul ha.1 ha.2 ht4 with h | h <;> linarith

/-- **Orientations through the boundary operator**: `o` is an orientation exactly when it takes
the values `±1`, `K` is a pseudo-manifold, and the boundary of the fundamental chain vanishes on
every interior tetrahedron. -/
theorem isOrientation_iff : K.IsOrientation o ↔ (∀ s ∈ K.simps, o s = 1 ∨ o s = -1) ∧
    K.IsPseudo4 ∧ ∀ t ∈ K.tets, #(K.star t) = 2 → bd (fundChain K.simps o) t = 0 := by
  constructor
  · intro ho
    refine ⟨ho.sign, ho.isPseudo4, fun t ht h2 => ?_⟩
    obtain ⟨a, b, hab, hst⟩ := card_eq_two.mp h2
    have ha : a ∈ K.star t := hst ▸ mem_insert_self a {b}
    have hb : b ∈ K.star t := hst ▸ mem_insert_of_mem (mem_singleton_self b)
    rw [mem_star] at ha hb
    rw [bd_fundChain_apply_tet K o (card_of_mem_faces ht), hst, sum_pair hab,
      ho.coherent a ha.1 b hb.1 hab t ht ha.2 hb.2]
    ring
  · rintro ⟨hsign, hP, hbd⟩
    refine ⟨hsign, fun s hs s' hs' hne t ht hts hts' => ?_⟩
    have hsub : ({s, s'} : Finset (Finset V)) ⊆ K.star t := by
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact mem_star.mpr ⟨hs, hts⟩
      · rw [mem_singleton.mp hx]
        exact mem_star.mpr ⟨hs', hts'⟩
    have h2 : #(K.star t) = 2 :=
      le_antisymm (hP t ht) (by rw [← card_pair hne]; exact card_le_card hsub)
    have heq : K.star t = {s, s'} :=
      (eq_of_subset_of_card_le hsub (by rw [h2, card_pair hne])).symm
    have := hbd t ht h2
    rw [bd_fundChain_apply_tet K o (card_of_mem_faces ht), heq, sum_pair hne] at this
    linarith

/-- **For a closed complex, an orientation is a fundamental cycle**: signs `±1` whose chain has
zero boundary. -/
theorem isOrientation_iff_of_closed (hK : K.IsClosed4) :
    K.IsOrientation o ↔ (∀ s ∈ K.simps, o s = 1 ∨ o s = -1) ∧ bd (fundChain K.simps o) = 0 := by
  rw [isOrientation_iff]
  constructor
  · rintro ⟨hsign, -, hbd⟩
    refine ⟨hsign, Finsupp.ext fun t => ?_⟩
    by_cases ht : t ∈ K.tets
    · exact hbd t ht (hK t ht)
    · exact bd_fundChain_apply_of_notMem K o ht
  · rintro ⟨hsign, hbd⟩
    exact ⟨hsign, fun t ht => (hK t ht).le, fun t _ _ => by rw [hbd]; rfl⟩

/-- The orientation induced on the boundary tetrahedra: `t` gets `Σ_{s ∋ t} o s • [s : t]`. -/
def bdryOrient (K : Complex4 V) (o : Finset V → ℤ) (t : Finset V) : ℤ :=
  ∑ s ∈ K.star t, o s * relSign s t

/-- **The boundary of an oriented complex**: the boundary of its fundamental chain is the
fundamental chain of the boundary tetrahedra with the induced orientation. -/
theorem IsOrientation.bd_fundChain (ho : K.IsOrientation o) :
    bd (fundChain K.simps o) = fundChain K.bdryTets (K.bdryOrient o) := by
  ext t
  have hR : fundChain K.bdryTets (K.bdryOrient o) t =
      if t ∈ K.bdryTets then K.bdryOrient o t else 0 := by
    simp only [fundChain, Finsupp.finsetSum_apply, Finsupp.smul_apply, Finsupp.single_apply,
      smul_eq_mul, mul_ite, mul_one, mul_zero, sum_ite_eq']
  rw [hR]
  by_cases ht : t ∈ K.tets
  · rw [bd_fundChain_apply_tet K o (card_of_mem_faces ht)]
    by_cases h1 : #(K.star t) = 1
    · rw [ite_eq_left (mem_bdryTets.mpr ⟨ht, h1⟩), bdryOrient]
    · have h2 : #(K.star t) = 2 := by
        have := ho.isPseudo4 t ht
        have := (star_nonempty ht).card_pos
        omega
      rw [ite_eq_right fun hb => h1 (mem_bdryTets.mp hb).2,
        ← bd_fundChain_apply_tet K o (card_of_mem_faces ht)]
      exact (isOrientation_iff.mp ho).2.2 t ht h2
  · rw [bd_fundChain_apply_of_notMem K o ht, ite_eq_right fun hb => ht (mem_bdryTets.mp hb).1]

/-- The induced orientation of the boundary is a cycle. -/
theorem IsOrientation.bd_fundChain_bdry (ho : K.IsOrientation o) :
    bd (fundChain K.bdryTets (K.bdryOrient o)) = 0 := by
  rw [← ho.bd_fundChain, bd_bd]

/-- **The boundary of a 5-simplex is orientable**: `s ↦ [S : s]` is an orientation, whose
fundamental cycle is `∂[S]`. -/
theorem isOrientation_sphere {S : Finset V} (hS : #S = 6) : (sphere S).IsOrientation (relSign S) := by
  have hchain : fundChain (sphere S).simps (relSign S) = bdSimplex S := by
    rw [sphere, fundChain]
    dsimp only
    rw [powersetCard_eq_image_erase (by rw [hS] : #S = 5 + 1), sum_image fun x hx y hy hxy =>
      erase_injOn S hx hy hxy, bdSimplex]
    exact sum_congr rfl fun v hv => by rw [relSign_erase hv]
  rw [isOrientation_iff_of_closed (isClosed4_sphere hS), hchain, bd_bdSimplex]
  refine ⟨fun s hs => ?_, rfl⟩
  obtain ⟨hsS, hs5⟩ := mem_powersetCard.mp hs
  exact relSign_eq_one_or hsS (by rw [hS, hs5])

/-- **Pachner moves preserve orientations.** The new 4-simplices `(σ ∪ τ) \ {u}` get the
orientation that makes the fundamental chain change by a multiple of `∂[σ ∪ τ]`, which has no
boundary. -/
theorem IsOrientation.move (ho : K.IsOrientation o) {σ τ : Finset V} (h : K.IsMove σ τ) :
    (K.move h).IsOrientable := by
  obtain ⟨v₀, hv₀⟩ := h.nonempty_right
  have hv₀S : v₀ ∈ σ ∪ τ := mem_union_right σ hv₀
  -- the removed 4-simplices are oriented as in `ε • ∂[σ ∪ τ]`
  have hA : ∀ v ∈ τ, o ((σ ∪ τ).erase v) =
      o ((σ ∪ τ).erase v₀) * inc (σ ∪ τ) v₀ * inc (σ ∪ τ) v := by
    intro v hv
    by_cases hvv : v = v₀
    · subst hvv
      rw [mul_assoc, inc_mul_self, mul_one]
    · have hvS : v ∈ σ ∪ τ := mem_union_right σ hv
      have hne : (σ ∪ τ).erase v ≠ (σ ∪ τ).erase v₀ := fun he => hvv (erase_injOn _ hvS hv₀S he)
      have h1 : v₀ ∈ (σ ∪ τ).erase v := mem_erase.mpr ⟨Ne.symm hvv, hv₀S⟩
      have h2 : v ∈ (σ ∪ τ).erase v₀ := mem_erase.mpr ⟨hvv, hvS⟩
      have htK : ((σ ∪ τ).erase v).erase v₀ ∈ K.tets := mem_faces.mpr ⟨_, h.mem v hv,
        erase_subset _ _, by rw [card_erase_of_mem h1, card_erase_of_mem hvS, h.card_union]⟩
      have hc := ho.coherent _ (h.mem v hv) _ (h.mem v₀ hv₀) hne _ htK (erase_subset _ _)
        (by rw [erase_right_comm]; exact erase_subset _ _)
      rw [relSign_erase h1, erase_right_comm, relSign_erase h2] at hc
      have hpair := inc_mul_inc_erase hvS hv₀S hvv
      have hx := inc_mul_self ((σ ∪ τ).erase v) v₀
      have hq := inc_mul_self (σ ∪ τ) v₀
      linear_combination (o ((σ ∪ τ).erase v₀) * inc (σ ∪ τ) v * inc (σ ∪ τ) v₀ -
          o ((σ ∪ τ).erase v)) * hx + inc ((σ ∪ τ).erase v) v₀ * hc +
        o ((σ ∪ τ).erase v₀) * inc ((σ ∪ τ).erase v) v₀ * inc ((σ ∪ τ).erase v₀) v * hq -
        o ((σ ∪ τ).erase v₀) * inc (σ ∪ τ) v₀ * inc ((σ ∪ τ).erase v) v₀ * hpair
  set ε := o ((σ ∪ τ).erase v₀) * inc (σ ∪ τ) v₀ with hε_def
  have hε : ε = 1 ∨ ε = -1 := by
    rcases ho.sign _ (h.mem v₀ hv₀) with h1 | h1 <;>
      rcases inc_eq_one_or (σ ∪ τ) v₀ with h2 | h2 <;> simp [hε_def, h1, h2]
  refine ⟨fun s => if τ ⊆ s then -ε * relSign (σ ∪ τ) s else o s, ?_⟩
  -- the fundamental chain changes by `-ε • ∂[σ ∪ τ]`
  have hchain : fundChain (K.move h).simps
      (fun s => if τ ⊆ s then -ε * relSign (σ ∪ τ) s else o s) =
      fundChain K.simps o - ε • bdSimplex (σ ∪ τ) := by
    have hdisj : Disjoint (K.simps.filter fun s => ¬ σ ⊆ s)
        (σ.image fun u => (σ ∪ τ).erase u) := by
      refine disjoint_left.mpr fun s hs hs' => ?_
      obtain ⟨u, hu, rfl⟩ := mem_image.mp hs'
      exact h.fresh _ (mem_filter.mp hs).1
        (subset_erase_of_notMem subset_union_right (disjoint_left.mp h.disj hu))
    have hold : ∀ s ∈ K.simps.filter (fun s => ¬ σ ⊆ s),
        (if τ ⊆ s then -ε * relSign (σ ∪ τ) s else o s) = o s := fun s hs =>
      ite_eq_right (h.fresh s (mem_filter.mp hs).1)
    have hinj : ∀ X ⊆ σ ∪ τ, Set.InjOn (fun u => (σ ∪ τ).erase u) X := fun X hX x hx y hy hxy =>
      erase_injOn _ (hX hx) (hX hy) hxy
    have hnew : ∀ u ∈ σ, (if τ ⊆ (σ ∪ τ).erase u then -ε * relSign (σ ∪ τ) ((σ ∪ τ).erase u)
        else o ((σ ∪ τ).erase u)) = -ε * inc (σ ∪ τ) u := fun u hu => by
      rw [ite_eq_left (subset_erase_of_notMem subset_union_right (disjoint_left.mp h.disj hu)),
        relSign_erase (mem_union_left τ hu)]
    have hL : fundChain (K.move h).simps
        (fun s => if τ ⊆ s then -ε * relSign (σ ∪ τ) s else o s) =
        ∑ s ∈ K.simps.filter (fun s => ¬ σ ⊆ s), o s • single s 1 +
          ∑ u ∈ σ, (-ε * inc (σ ∪ τ) u) • single ((σ ∪ τ).erase u) 1 := by
      rw [fundChain, Complex4.move]
      dsimp only
      rw [sum_union hdisj, sum_image (hinj σ subset_union_left)]
      congr 1
      · exact sum_congr rfl fun s hs => by rw [hold s hs]
      · exact sum_congr rfl fun u hu => by rw [hnew u hu]
    have hK : fundChain K.simps o =
        ∑ v ∈ τ, (ε * inc (σ ∪ τ) v) • single ((σ ∪ τ).erase v) 1 +
          ∑ s ∈ K.simps.filter (fun s => ¬ σ ⊆ s), o s • single s 1 := by
      rw [fundChain, ← sum_filter_add_sum_filter_not K.simps (σ ⊆ ·), h.filter_simps,
        sum_image (hinj τ subset_union_right)]
      congr 1
      exact sum_congr rfl fun v hv => by rw [hA v hv]
    have hB : bdSimplex (σ ∪ τ) =
        ∑ u ∈ σ, inc (σ ∪ τ) u • single ((σ ∪ τ).erase u) 1 +
          ∑ v ∈ τ, inc (σ ∪ τ) v • single ((σ ∪ τ).erase v) 1 := by
      rw [bdSimplex, sum_union h.disj]
    rw [hL, hK, hB]
    simp only [smul_add, smul_sum, smul_smul, neg_mul, neg_smul, sum_neg_distrib]
    abel
  rw [isOrientation_iff]
  refine ⟨fun s hs => ?_, (isPseudo4_move_iff h).mpr ho.isPseudo4, fun t ht h2 => ?_⟩
  · by_cases hτ : τ ⊆ s
    · rw [ite_eq_left hτ]
      rcases mem_move.mp hs with ⟨hs, -⟩ | ⟨u, hu, rfl⟩
      · exact absurd hτ (h.fresh s hs)
      · rw [relSign_erase (mem_union_left τ hu)]
        rcases hε with h1 | h1 <;> rcases inc_eq_one_or (σ ∪ τ) u with h2 | h2 <;> simp [h1, h2]
    · rw [ite_eq_right hτ]
      rcases mem_move.mp hs with ⟨hs, -⟩ | ⟨u, hu, rfl⟩
      · exact ho.sign s hs
      · exact absurd (subset_erase_of_notMem subset_union_right (disjoint_left.mp h.disj hu)) hτ
  · rw [hchain, map_sub, map_zsmul, bd_bdSimplex, smul_zero, sub_zero]
    by_cases hτ : τ ⊆ t
    · refine bd_fundChain_apply_of_notMem K o fun htK => ?_
      obtain ⟨s, hs, hts, -⟩ := mem_faces.mp htK
      exact h.fresh s hs (hτ.trans hts)
    · have hσ : ¬ σ ⊆ t := fun hσ => h.notMem_tets_move hσ ht
      have htK := (h.mem_tets_move_iff hσ hτ).mp ht
      have h2' : #(K.star t) = 2 := by
        rw [← h.card_star_move_eq (card_of_mem_faces ht) hσ hτ]
        exact h2
      exact (isOrientation_iff.mp ho).2.2 t htK h2'

/-- **Pachner moves preserve orientability**, in both directions. -/
theorem isOrientable_move_iff {σ τ : Finset V} (h : K.IsMove σ τ) :
    (K.move h).IsOrientable ↔ K.IsOrientable := by
  constructor
  · rintro ⟨o', ho'⟩
    have := ho'.move h.symm
    rwa [move_move] at this
  · rintro ⟨o, ho⟩
    exact ho.move h

end Complex4

end Lightlike.FourD
