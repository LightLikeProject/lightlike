import Lightlike.SpinFoam.Vertex

/-!
# Sums over projections indexed by faces

The gluing of 4-simplices along their faces is easiest to state when the projection variables are
indexed by the faces themselves (vertex sets), so that a face shared by two 4-simplices is
automatically the same variable. `tbox T col` is the finite set of functions `x : Finset V → ℤ`
that vanish off a finite set `T` of faces and satisfy `|x f| ≤ col f` on `T`. A sum over it is a
sum over one projection for each face of `T`.

## Main results

* `sum_tbox_insert`: a sum over `tbox (insert f T)` is a sum over `tbox T` and over the
  projection of `f`.
* `sum_tbox_empty`: a sum over `tbox ∅` is the value at the zero function.
* `vertexContr_eq_vertexF`: the vertex contraction is the sum over one projection for each
  triangle of the 4-simplex (`vertexF`).

## References

- H. Ooguri, *Topological lattice models in four dimensions*, Mod. Phys. Lett. A 7, 2799 (1992):
  the vertex amplitude as the contraction of five intertwiners along the triangles of a
  4-simplex.
-/

open Finset Lightlike.Recoupling

namespace Lightlike.SpinFoam

variable {V : Type*} [DecidableEq V]

open Classical in
/-- The functions `x : Finset V → ℤ` that vanish off `T` and satisfy `|x f| ≤ col f` on `T`. -/
noncomputable def tbox (T : Finset (Finset V)) (col : Finset V → ℕ) : Finset (Finset V → ℤ) :=
  (T.pi fun f => Icc (-(col f : ℤ)) (col f)).image fun c f => if h : f ∈ T then c f h else 0

lemma mem_tbox {T : Finset (Finset V)} {col : Finset V → ℕ} {x : Finset V → ℤ} :
    x ∈ tbox T col ↔ (∀ f ∈ T, x f ∈ Icc (-(col f : ℤ)) (col f)) ∧ ∀ f ∉ T, x f = 0 := by
  unfold tbox
  simp only [mem_image, mem_pi]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨fun f hf => by simpa [hf] using hc f hf, fun f hf => by simp [hf]⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun f _ => x f, fun f hf => h1 f hf, ?_⟩
    funext f
    by_cases hf : f ∈ T
    · simp [hf]
    · simp [hf, h2 f hf]

/-- A sum over no faces is the value at the zero function. -/
lemma sum_tbox_empty (col : Finset V → ℕ) (F : (Finset V → ℤ) → ℝ) :
    ∑ x ∈ tbox ∅ col, F x = F 0 := by
  have : tbox (∅ : Finset (Finset V)) col = {0} := by
    ext x
    simp only [mem_tbox, notMem_empty, IsEmpty.forall_iff, implies_true, not_false_eq_true,
      forall_const, true_and, mem_singleton]
    exact ⟨fun h => funext h, fun h f => by rw [h]; rfl⟩
  rw [this, sum_singleton]

/-- **Peeling one face**: a sum over `tbox (insert f T)` is a sum over `tbox T` and over the
projection `a` of `f`, with `x` updated at `f`. -/
lemma sum_tbox_insert {T : Finset (Finset V)} {f : Finset V} (hf : f ∉ T) (col : Finset V → ℕ)
    (F : (Finset V → ℤ) → ℝ) :
    ∑ x ∈ tbox (insert f T) col, F x =
      ∑ x ∈ tbox T col, ∑ a ∈ Icc (-(col f : ℤ)) (col f), F (Function.update x f a) := by
  rw [← sum_product']
  apply sum_nbij' (fun x => (Function.update x f 0, x f)) (fun p => Function.update p.1 f p.2)
  · intro x hx
    rw [mem_tbox] at hx
    simp only [mem_product, mem_tbox]
    refine ⟨⟨fun g hg => ?_, fun g hg => ?_⟩, hx.1 f (mem_insert_self f T)⟩
    · have hgf : g ≠ f := fun h => hf (h ▸ hg)
      rw [Function.update_of_ne hgf]
      exact hx.1 g (mem_insert_of_mem hg)
    · by_cases hgf : g = f
      · subst hgf; simp
      · rw [Function.update_of_ne hgf]
        exact hx.2 g (fun h => (mem_insert.mp h).elim hgf hg)
  · rintro ⟨x, a⟩ h
    rw [mem_product, mem_tbox] at h
    rw [mem_tbox]
    refine ⟨fun g hg => ?_, fun g hg => ?_⟩
    · by_cases hgf : g = f
      · subst hgf; simpa using h.2
      · rw [Function.update_of_ne hgf]
        exact h.1.1 g ((mem_insert.mp hg).resolve_left hgf)
    · have hgf : g ≠ f := fun h' => hg (h' ▸ mem_insert_self f T)
      rw [Function.update_of_ne hgf]
      exact h.1.2 g (fun h' => hg (mem_insert_of_mem h'))
  · intro x _
    simp
  · rintro ⟨x, a⟩ h
    rw [mem_product, mem_tbox] at h
    simp only [Function.update_idem, Function.update_self, Prod.mk.injEq, and_true]
    funext g
    by_cases hgf : g = f
    · subst hgf
      have := h.1.2 g hf
      simp only at this
      simp [this]
    · simp [Function.update_of_ne hgf]
  · intro x _
    simp


/-! ## The vertex network with face-indexed projections -/

section Vertex

variable {V : Type*} [LinearOrder V]

/-- The canonical intertwiner of the face `s∖{a}` of a 4-simplex `s` in the vertex network: its leg
`(s∖{a})∖{b}` carries the projection `legSign o s a b * x ((s∖{a})∖{b})`. -/
noncomputable def tetF (o : ℤ) (s : Finset V) (col : Finset V → ℕ) (x : Finset V → ℤ) (a : V) :
    ℝ :=
  if h : #(s.erase a) = 4 then
    canonTet col (s.erase a) h (fun j => legSign o s a ((s.erase a).orderEmbOfFin h j) *
      x ((s.erase a).erase ((s.erase a).orderEmbOfFin h j)))
  else 0

/-- **The vertex network with face-indexed projections**: the same contraction as `vertexContr`,
with one projection variable for each triangle of `s`. -/
noncomputable def vertexF (o : ℤ) (s : Finset V) (col : Finset V → ℕ) : ℝ :=
  ∑ x ∈ tbox (s.powersetCard 3) col,
    (∏ f ∈ s.powersetCard 3, edgeSign (col f) (x f)) * ∏ a ∈ s, tetF o s col x a

/-- The triangle of `s` opposite the positions `p, q`. -/
def tri (s : Finset V) (hs : #s = 5) (p q : Fin 5) : Finset V :=
  (s.erase (s.orderEmbOfFin hs p)).erase (s.orderEmbOfFin hs q)

lemma tri_comm (s : Finset V) (hs : #s = 5) (p q : Fin 5) : tri s hs p q = tri s hs q p :=
  erase_right_comm

lemma notMem_tri {s : Finset V} {hs : #s = 5} {p q r : Fin 5} (h : r = p ∨ r = q) :
    s.orderEmbOfFin hs r ∉ tri s hs p q := by
  unfold tri
  rcases h with rfl | rfl
  · exact fun hm => (mem_erase.mp (mem_of_mem_erase hm)).1 rfl
  · exact fun hm => (mem_erase.mp hm).1 rfl

lemma mem_tri {s : Finset V} {hs : #s = 5} {p q r : Fin 5} (hp : r ≠ p) (hq : r ≠ q) :
    s.orderEmbOfFin hs r ∈ tri s hs p q := by
  have hinj := (s.orderEmbOfFin hs).injective
  unfold tri
  exact mem_erase.mpr ⟨fun h => hq (hinj h), mem_erase.mpr ⟨fun h => hp (hinj h),
    s.orderEmbOfFin_mem hs r⟩⟩

/-- Two triangles of `s` agree exactly when they are opposite the same pair of positions. -/
lemma tri_eq_iff {s : Finset V} {hs : #s = 5} {p q p' q' : Fin 5} (hpq : p ≠ q) :
    tri s hs p q = tri s hs p' q' ↔ (p = p' ∧ q = q') ∨ (p = q' ∧ q = p') := by
  constructor
  · intro h
    have h1 : p = p' ∨ p = q' := by
      by_contra hc
      rw [not_or] at hc
      have := mem_tri (hs := hs) hc.1 hc.2
      rw [← h] at this
      exact notMem_tri (Or.inl rfl) this
    have h2 : q = p' ∨ q = q' := by
      by_contra hc
      rw [not_or] at hc
      have := mem_tri (hs := hs) hc.1 hc.2
      rw [← h] at this
      exact notMem_tri (Or.inr rfl) this
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
    · exact absurd rfl hpq
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact absurd rfl hpq
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact tri_comm s hs _ _

lemma tri_ne {s : Finset V} {hs : #s = 5} {p q p' q' : Fin 5} (hpq : p ≠ q)
    (h : ¬((p = p' ∧ q = q') ∨ (p = q' ∧ q = p'))) : tri s hs p q ≠ tri s hs p' q' :=
  fun he => h ((tri_eq_iff hpq).mp he)

lemma tri_mem_powersetCard {s : Finset V} {hs : #s = 5} {p q : Fin 5} (hpq : p ≠ q) :
    tri s hs p q ∈ s.powersetCard 3 := by
  rw [mem_powersetCard]
  refine ⟨(erase_subset _ _).trans (erase_subset _ _), ?_⟩
  unfold tri
  rw [card_erase_of_mem (mem_erase.mpr ⟨fun h => hpq ((s.orderEmbOfFin hs).injective h).symm,
    s.orderEmbOfFin_mem hs q⟩), card_erase_of_mem (s.orderEmbOfFin_mem hs p), hs]

/-- The ten triangles of `s`, listed so that peeling them off gives the order of the sums in
`vertexContr`. -/
def triList (s : Finset V) (hs : #s = 5) : Finset (Finset V) :=
  insert (tri s hs 1 3) (insert (tri s hs 3 4) (insert (tri s hs 1 4) (insert (tri s hs 2 3)
    (insert (tri s hs 1 2) (insert (tri s hs 2 4) (insert (tri s hs 0 3) (insert (tri s hs 0 1)
      (insert (tri s hs 0 4) {tri s hs 0 2}))))))))

lemma powersetCard_eq_triList (s : Finset V) (hs : #s = 5) :
    s.powersetCard 3 = triList s hs := by
  symm
  apply eq_of_subset_of_card_le
  · intro f hf
    simp only [triList, mem_insert, mem_singleton] at hf
    rcases hf with h | h | h | h | h | h | h | h | h | h <;> rw [h] <;>
      exact tri_mem_powersetCard (by decide)
  · rw [card_powersetCard, hs]
    unfold triList
    rw [card_insert_of_notMem, card_insert_of_notMem, card_insert_of_notMem, card_insert_of_notMem,
      card_insert_of_notMem, card_insert_of_notMem, card_insert_of_notMem, card_insert_of_notMem,
      card_insert_of_notMem, card_singleton]
    · decide
    all_goals
      simp only [mem_insert, mem_singleton, not_or]
      repeat' constructor
    all_goals exact tri_ne (by decide) (by decide)

/-- A sum over one face. -/
lemma sum_tbox_singleton (f : Finset V) (col : Finset V → ℕ) (F : (Finset V → ℤ) → ℝ) :
    ∑ x ∈ tbox {f} col, F x = ∑ a ∈ Icc (-(col f : ℤ)) (col f), F (Function.update 0 f a) := by
  rw [← Finset.insert_empty, sum_tbox_insert (notMem_empty f), sum_tbox_empty]

/-- A product over the vertices of `s` as a product over their positions. -/
lemma prod_simplex (s : Finset V) (hs : #s = 5) (g : V → ℝ) :
    ∏ a ∈ s, g a = ∏ i : Fin 5, g (s.orderEmbOfFin hs i) := by
  conv_lhs => rw [← image_orderEmbOfFin_univ s hs]
  rw [prod_image fun i _ j _ h => (s.orderEmbOfFin hs).injective h]

/-- Closes `tri s hs p q ∉ insert (tri s hs p' q') ⋯` for distinct position pairs. -/
local macro "tri_nm" : tactic =>
  `(tactic| (simp only [mem_insert, mem_singleton, not_or]; (repeat' constructor) <;>
    exact tri_ne (by decide) (by decide)))

/-- The face-indexed projections with value `a_pq` on the triangle `tri s hs p q`, built in the
order in which `vertexF` is peeled. -/
noncomputable def triX (s : Finset V) (hs : #s = 5) (a01 a02 a03 a04 a12 a13 a14 a23 a24 a34 : ℤ) :
    Finset V → ℤ :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update 0
    (tri s hs 0 2) a02) (tri s hs 0 4) a04) (tri s hs 0 1) a01) (tri s hs 0 3) a03)
    (tri s hs 2 4) a24) (tri s hs 1 2) a12) (tri s hs 2 3) a23) (tri s hs 1 4) a14)
    (tri s hs 3 4) a34) (tri s hs 1 3) a13

lemma triX_apply (s : Finset V) (hs : #s = 5) (a01 a02 a03 a04 a12 a13 a14 a23 a24 a34 : ℤ)
    (i k : Fin 5) (hik : i ≠ k) :
    triX s hs a01 a02 a03 a04 a12 a13 a14 a23 a24 a34 (tri s hs i k) =
      cornerMat a01 a02 a03 a04 a12 a13 a14 a23 a24 a34 i k := by
  unfold triX
  fin_cases i <;> fin_cases k <;> first
    | exact absurd rfl hik
    | simp [Function.update_apply, tri_eq_iff, cornerMat]

/-- The edge signs of `vertexF` at the projections `triX`. -/
lemma prod_triList_edgeSign (s : Finset V) (hs : #s = 5) (col : Finset V → ℕ)
    (a01 a02 a03 a04 a12 a13 a14 a23 a24 a34 : ℤ) :
    ∏ f ∈ triList s hs, edgeSign (col f) (triX s hs a01 a02 a03 a04 a12 a13 a14 a23 a24 a34 f) =
      edgeSign (col (tri s hs 0 1)) a01 * edgeSign (col (tri s hs 0 2)) a02 *
        edgeSign (col (tri s hs 0 3)) a03 * edgeSign (col (tri s hs 0 4)) a04 *
        edgeSign (col (tri s hs 1 2)) a12 * edgeSign (col (tri s hs 1 3)) a13 *
        edgeSign (col (tri s hs 1 4)) a14 * edgeSign (col (tri s hs 2 3)) a23 *
        edgeSign (col (tri s hs 2 4)) a24 * edgeSign (col (tri s hs 3 4)) a34 := by
  unfold triList
  rw [prod_insert (by tri_nm), prod_insert (by tri_nm), prod_insert (by tri_nm),
    prod_insert (by tri_nm), prod_insert (by tri_nm), prod_insert (by tri_nm),
    prod_insert (by tri_nm), prod_insert (by tri_nm), prod_insert (by tri_nm), prod_singleton]
  simp only [triX_apply s hs _ _ _ _ _ _ _ _ _ _ _ _ (by decide : (1 : Fin 5) ≠ 3),
    triX_apply s hs _ _ _ _ _ _ _ _ _ _ _ _ (by decide : (3 : Fin 5) ≠ 4),
    triX_apply s hs _ _ _ _ _ _ _ _ _ _ _ _ (by decide : (1 : Fin 5) ≠ 4),
    triX_apply s hs _ _ _ _ _ _ _ _ _ _ _ _ (by decide : (2 : Fin 5) ≠ 3),
    triX_apply s hs _ _ _ _ _ _ _ _ _ _ _ _ (by decide : (1 : Fin 5) ≠ 2),
    triX_apply s hs _ _ _ _ _ _ _ _ _ _ _ _ (by decide : (2 : Fin 5) ≠ 4),
    triX_apply s hs _ _ _ _ _ _ _ _ _ _ _ _ (by decide : (0 : Fin 5) ≠ 3),
    triX_apply s hs _ _ _ _ _ _ _ _ _ _ _ _ (by decide : (0 : Fin 5) ≠ 1),
    triX_apply s hs _ _ _ _ _ _ _ _ _ _ _ _ (by decide : (0 : Fin 5) ≠ 4),
    triX_apply s hs _ _ _ _ _ _ _ _ _ _ _ _ (by decide : (0 : Fin 5) ≠ 2),
    cornerMat_01, cornerMat_02, cornerMat_03, cornerMat_04, cornerMat_12, cornerMat_13,
    cornerMat_14, cornerMat_23, cornerMat_24, cornerMat_34]
  ring

/-- The tetrahedron `s∖sᵢ` of `vertexF` in terms of positions. -/
lemma tetF_orderEmbOfFin (o : ℤ) (s : Finset V) (hs : #s = 5) (col : Finset V → ℕ)
    (x : Finset V → ℤ) (i : Fin 5) :
    tetF o s col x (s.orderEmbOfFin hs i) =
      canonTet col (s.erase (s.orderEmbOfFin hs i)) (card_erase_orderEmbOfFin hs i) (fun j =>
        legSign o s (s.orderEmbOfFin hs i) (s.orderEmbOfFin hs (i.succAbove j)) *
          x (tri s hs i (i.succAbove j))) := by
  unfold tetF
  rw [dite_eq_left_of_eq_true (eq_true (card_erase_orderEmbOfFin hs i))]
  congr 1
  funext j
  rw [orderEmbOfFin_erase hs i]
  rfl

/-- **The vertex network with face-indexed projections** is the vertex contraction: the ten sums
of `vertexContr` are the sum over the projections of the ten triangles of `s`. -/
theorem vertexContr_eq_vertexF (o : ℤ) (s : Finset V) (hs : #s = 5) (col : Finset V → ℕ) :
    vertexContr o s hs col = vertexF o s col := by
  unfold vertexF
  rw [powersetCard_eq_triList s hs]
  conv_rhs => enter [1]; unfold triList
  rw [sum_tbox_insert (by tri_nm), sum_tbox_insert (by tri_nm), sum_tbox_insert (by tri_nm),
    sum_tbox_insert (by tri_nm), sum_tbox_insert (by tri_nm), sum_tbox_insert (by tri_nm),
    sum_tbox_insert (by tri_nm), sum_tbox_insert (by tri_nm), sum_tbox_insert (by tri_nm),
    sum_tbox_singleton]
  unfold vertexContr
  dsimp only
  refine sum_congr rfl fun a02 _ => sum_congr rfl fun a04 _ => sum_congr rfl fun a01 _ =>
    sum_congr rfl fun a03 _ => sum_congr rfl fun a24 _ => sum_congr rfl fun a12 _ =>
    sum_congr rfl fun a23 _ => sum_congr rfl fun a14 _ => sum_congr rfl fun a34 _ =>
    sum_congr rfl fun a13 _ => ?_
  have hx := prod_triList_edgeSign s hs col a01 a02 a03 a04 a12 a13 a14 a23 a24 a34
  unfold triX at hx
  rw [hx, prod_simplex s hs, Fin.prod_univ_five, Fin.prod_univ_five]
  simp only [tetF_orderEmbOfFin]
  have hc : ∀ i : Fin 5, ∀ j : Fin 4,
      triX s hs a01 a02 a03 a04 a12 a13 a14 a23 a24 a34 (tri s hs i (i.succAbove j)) =
        cornerMat a01 a02 a03 a04 a12 a13 a14 a23 a24 a34 i (i.succAbove j) :=
    fun i j => triX_apply s hs _ _ _ _ _ _ _ _ _ _ i _ (Fin.succAbove_ne i j).symm
  unfold triX at hc
  simp only [hc]
  rfl

end Vertex

end Lightlike.SpinFoam
