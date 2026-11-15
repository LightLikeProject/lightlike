import Lightlike.PL.CommonSub

/-!
# Geometric realisation of the order complex of a cell structure

A **cell structure** is a finite poset of pairwise disjoint convex "open cells" in a real vector
space, each with a convex "closure" that is the union of the cells below it. The strata of
`CommonSub` are one example (the open cells `σ° ∩ τ°`), and the cells of a slicing by hyperplanes
are another. The order complex of such a poset, realised by choosing a point in each cell, is
a geometric complex: the chosen points of a chain are affinely independent, and a point of the
open simplex of a chain lies in the top cell of the chain.

Only the axioms that these two facts use are collected in `CellStructure`.

## Main results

* `CellStructure.pt_injOn`: distinct cells have distinct chosen points.
* `CellStructure.affineIndepOn_image_pt`: the chosen points of a chain of cells are affinely
  independent.
* `CellStructure.mem_cell_top`: a point of the open simplex of a chain lies in its top cell.
-/

open Finset
open scoped Classical

namespace Lightlike.PL

/-- A finite poset of cells in a real vector space `E`: each cell `a` has an open part
`cell a` and a closed part `hull a`, with the properties used to realise chains of cells as
simplices. -/
structure CellStructure (E α : Type*) [AddCommGroup E] [Module ℝ E] [PartialOrder α] where
  /-- The index set of the cells. -/
  cells : Finset α
  /-- The open part of a cell. -/
  cell : α → Set E
  /-- The closed part of a cell. -/
  hull : α → Set E
  /-- The **chosen point** of each cell, a point of its open part. -/
  pt : α → E
  /-- Every cell has a point. -/
  nonempty : ∀ a ∈ cells, (cell a).Nonempty
  /-- The chosen point of a cell lies in its open part. -/
  pt_mem : ∀ a ∈ cells, pt a ∈ cell a
  /-- The closed part is convex. -/
  convex_hull : ∀ a ∈ cells, Convex ℝ (hull a)
  /-- The open part lies in the closed part. -/
  cell_subset_hull : ∀ a ∈ cells, cell a ⊆ hull a
  /-- Closed parts increase with the order. -/
  hull_mono : ∀ a ∈ cells, ∀ b ∈ cells, b ≤ a → hull b ⊆ hull a
  /-- Open parts of distinct cells are disjoint. -/
  cell_inj : ∀ a ∈ cells, ∀ b ∈ cells, ∀ x, x ∈ cell a → x ∈ cell b → a = b
  /-- A point strictly between a point of the open part and a point of the closed part is in
  the open part. -/
  combo_mem : ∀ a ∈ cells, ∀ {p z : E}, p ∈ cell a → z ∈ hull a → ∀ {l : ℝ}, 0 < l → l ≤ 1 →
    l • p + (1 - l) • z ∈ cell a
  /-- The open part of a cell is off the affine span of the closed part of a smaller cell. -/
  notMem_span : ∀ a ∈ cells, ∀ b ∈ cells, b < a → ∀ x ∈ cell a, x ∉ affineSpan ℝ (hull b)

namespace CellStructure

variable {E α : Type*} [AddCommGroup E] [Module ℝ E] [PartialOrder α] (S : CellStructure E α)

/-- Distinct cells have distinct chosen points. -/
lemma pt_injOn : Set.InjOn S.pt (↑S.cells : Set α) := by
  intro a ha b hb hab
  exact S.cell_inj a ha b hb (S.pt a) (S.pt_mem _ ha) (hab ▸ S.pt_mem _ hb)

/-- A **chain of cells**: cells totally ordered by the order of the structure. -/
def IsCellChain (C : Finset α) : Prop :=
  C ⊆ S.cells ∧ IsChain (· ≤ ·) (C : Set α)

lemma IsCellChain.mono {S : CellStructure E α} {C D : Finset α} (hD : S.IsCellChain D)
    (h : C ⊆ D) : S.IsCellChain C :=
  ⟨h.trans hD.1, hD.2.mono (coe_subset.2 h)⟩

/-- The chosen points of cells below `m` span a convex set inside the closed part of `m`. -/
lemma convexHull_image_pt_subset {C : Finset α} (hC : C ⊆ S.cells) {m : α} (hm : m ∈ S.cells)
    (hle : ∀ p ∈ C, p ≤ m) : convexHull ℝ (↑(C.image S.pt) : Set E) ⊆ S.hull m := by
  refine convexHull_min ?_ (S.convex_hull m hm)
  intro y hy
  rw [coe_image] at hy
  obtain ⟨p, hp, rfl⟩ := hy
  exact S.hull_mono m hm p (hC hp) (hle p hp)
    (S.cell_subset_hull p (hC hp) (S.pt_mem _ (hC hp)))

/-- **The chosen points of a chain of cells are affinely independent.** -/
theorem affineIndepOn_image_pt :
    ∀ C : Finset α, S.IsCellChain C → AffineIndepOn ℝ id (↑(C.image S.pt) : Set E) := by
  intro C
  induction C using Finset.strongInduction with
  | H C ih =>
    intro hC
    rcases C.eq_empty_or_nonempty with rfl | hne
    · simp
    obtain ⟨m, hmC, hm⟩ := exists_greatest_of_isChain hC.2 hne
    have hC'C : C.erase m ⊂ C := erase_ssubset hmC
    have ih' := ih _ hC'C (hC.mono hC'C.subset)
    rw [← insert_erase hmC, image_insert, coe_insert]
    refine ih'.id_insert fun hmem => ?_
    rcases (C.erase m).eq_empty_or_nonempty with he | hne'
    · rw [he] at hmem
      simp only [Finset.image_empty, coe_empty, AffineSubspace.span_empty] at hmem
      exact AffineSubspace.notMem_bot ℝ E _ hmem
    obtain ⟨m', hm'C, hm'⟩ := exists_greatest_of_isChain (hC.mono hC'C.subset).2 hne'
    have hlt : m' < m := lt_of_le_of_ne (hm m' (mem_of_mem_erase hm'C)) (ne_of_mem_erase hm'C)
    have hmcells : m ∈ S.cells := hC.1 hmC
    have hm'cells : m' ∈ S.cells := hC.1 (mem_of_mem_erase hm'C)
    have hsub := S.convexHull_image_pt_subset (hC.mono hC'C.subset).1 hm'cells hm'
    have hA : affineSpan ℝ (↑((C.erase m).image S.pt) : Set E) ≤ affineSpan ℝ (S.hull m') :=
      affineSpan_mono ℝ fun y hy => hsub (subset_convexHull ℝ _ hy)
    exact S.notMem_span m hmcells m' hm'cells hlt _ (S.pt_mem _ hmcells) (hA hmem)

/-- **A point of the open simplex of a chain lies in the top cell of the chain.** -/
theorem mem_cell_top {C : Finset α} (hC : S.IsCellChain C) {m : α} (hmC : m ∈ C)
    (hm : ∀ p ∈ C, p ≤ m) {x : E} (hx : x ∈ openHull (C.image S.pt)) : x ∈ S.cell m := by
  have hmc : m ∈ S.cells := hC.1 hmC
  have hnot : S.pt m ∉ (C.erase m).image S.pt := by
    intro h
    obtain ⟨p, hp, hpm⟩ := mem_image.1 h
    exact ne_of_mem_erase hp
      (S.pt_injOn (hC.1 (mem_of_mem_erase hp)) hmc hpm)
  rw [← insert_erase hmC, image_insert] at hx
  rcases openHull_insert_cases hnot hx with ⟨-, rfl⟩ | ⟨l, hl0, hl1, y, hy, rfl⟩
  · exact S.pt_mem _ hmc
  · have hsub := S.convexHull_image_pt_subset (hC.mono (erase_subset m C)).1 hmc
      (fun p hp => hm p (mem_of_mem_erase hp))
    exact S.combo_mem m hmc (S.pt_mem _ hmc) (hsub (openHull_subset_convexHull _ hy)) hl0 hl1.le

/-- A point spanned by cells strictly below `m` is not in the open part of `m`. -/
lemma notMem_cell_of_lt {C : Finset α} (hC : S.IsCellChain C) {m : α} (hm : m ∈ S.cells)
    (hlt : ∀ p ∈ C, p < m) {y : E} (hy : y ∈ convexHull ℝ (↑(C.image S.pt) : Set E)) :
    y ∉ S.cell m := by
  intro hym
  rcases C.eq_empty_or_nonempty with rfl | hne
  · simp at hy
  obtain ⟨m', hm'C, hm'⟩ := exists_greatest_of_isChain hC.2 hne
  have hy' := S.convexHull_image_pt_subset hC.1 (hC.1 hm'C) hm' hy
  exact S.notMem_span m hm m' (hC.1 hm'C) (hlt m' hm'C) y hym (subset_affineSpan ℝ _ hy')

/-- The key step of chain uniqueness: a point strictly between the top chosen point `b` and a
point spanned by a chain strictly below `m` cannot also be written with a smaller weight on `b`
and a point of the closed part of `m`. -/
lemma not_combo_eq {C : Finset α} (hC : S.IsCellChain C) {m : α} (hm : m ∈ S.cells)
    (hlt : ∀ p ∈ C, p < m) {y z : E} (hy : y ∈ convexHull ℝ (↑(C.image S.pt) : Set E))
    (hz : z ∈ S.hull m) {l l' : ℝ} (hll' : l < l') (hl' : l' ≤ 1)
    (heq : l • S.pt m + (1 - l) • y = l' • S.pt m + (1 - l') • z) : False := by
  have hpos : 0 < 1 - l := by linarith
  set μ := (l' - l) / (1 - l) with hμ
  have hμ0 : 0 < μ := div_pos (by linarith) hpos
  have hμ1 : μ ≤ 1 := (div_le_one hpos).2 (by linarith)
  have h1 : (1 - l) * μ = l' - l := by rw [hμ]; field_simp
  have h2 : (1 - l) * (1 - μ) = 1 - l' := by rw [mul_sub, h1]; ring
  have key : (1 - l) • y = (1 - l) • (μ • S.pt m + (1 - μ) • z) := by
    rw [smul_add, smul_smul, smul_smul, h1, h2]
    linear_combination (norm := module) heq
  have hyz : y = μ • S.pt m + (1 - μ) • z := smul_right_injective E hpos.ne' key
  exact S.notMem_cell_of_lt hC hm hlt hy (hyz ▸ S.combo_mem m hm (S.pt_mem _ hm) hz hμ0 hμ1)

/-- **A point determines its chain of cells**: if a point lies in the open simplices spanned by
the chosen points of two chains, the chains are equal. -/
theorem eq_of_mem_openHull_image_pt :
    ∀ C D : Finset α, ∀ x : E, S.IsCellChain C → S.IsCellChain D →
      x ∈ openHull (C.image S.pt) → x ∈ openHull (D.image S.pt) → C = D := by
  intro C
  induction C using Finset.strongInduction with
  | H C ih =>
    intro D x hC hD hxC hxD
    have hCne : C.Nonempty := by
      rcases C.eq_empty_or_nonempty with rfl | h
      · simp at hxC
      · exact h
    have hDne : D.Nonempty := by
      rcases D.eq_empty_or_nonempty with rfl | h
      · simp at hxD
      · exact h
    obtain ⟨m, hmC, hm⟩ := exists_greatest_of_isChain hC.2 hCne
    obtain ⟨n, hnD, hn⟩ := exists_greatest_of_isChain hD.2 hDne
    have hxm := S.mem_cell_top hC hmC hm hxC
    have hxn := S.mem_cell_top hD hnD hn hxD
    have hmn : m = n := S.cell_inj m (hC.1 hmC) n (hD.1 hnD) x hxm hxn
    subst hmn
    have hmc : m ∈ S.cells := hC.1 hmC
    have hC' : S.IsCellChain (C.erase m) := hC.mono (erase_subset _ _)
    have hD' : S.IsCellChain (D.erase m) := hD.mono (erase_subset _ _)
    have hltC : ∀ p ∈ C.erase m, p < m := fun p hp =>
      lt_of_le_of_ne (hm p (mem_of_mem_erase hp)) (ne_of_mem_erase hp)
    have hltD : ∀ p ∈ D.erase m, p < m := fun p hp =>
      lt_of_le_of_ne (hn p (mem_of_mem_erase hp)) (ne_of_mem_erase hp)
    have hbC : S.pt m ∉ (C.erase m).image S.pt := by
      intro h
      obtain ⟨p, hp, hpm⟩ := Finset.mem_image.1 h
      exact (hltC p hp).ne (S.pt_injOn (hC.1 (mem_of_mem_erase hp)) hmc hpm)
    have hbD : S.pt m ∉ (D.erase m).image S.pt := by
      intro h
      obtain ⟨p, hp, hpm⟩ := Finset.mem_image.1 h
      exact (hltD p hp).ne (S.pt_injOn (hD.1 (mem_of_mem_erase hp)) hmc hpm)
    rw [← insert_erase hmC, image_insert] at hxC
    rw [← insert_erase hnD, image_insert] at hxD
    have hb := S.cell_subset_hull m hmc (S.pt_mem _ hmc)
    suffices h : C.erase m = D.erase m by rw [← insert_erase hmC, ← insert_erase hnD, h]
    rcases openHull_insert_cases hbC hxC with ⟨hCe, rfl⟩ | ⟨l, hl0, hl1, y, hy, rfl⟩ <;>
      rcases openHull_insert_cases hbD hxD with ⟨hDe, hxe⟩ | ⟨l', hl0', hl1', y', hy', hxe⟩
    · rw [image_eq_empty.1 hCe, image_eq_empty.1 hDe]
    · exact (S.not_combo_eq hD' hmc hltD (openHull_subset_convexHull _ hy') hb
        hl1' le_rfl (by rw [← hxe]; module)).elim
    · exact (S.not_combo_eq hC' hmc hltC (openHull_subset_convexHull _ hy) hb
        hl1 le_rfl (by rw [hxe]; module)).elim
    · have hsub := S.convexHull_image_pt_subset hC'.1 hmc fun p hp => (hltC p hp).le
      have hsub' := S.convexHull_image_pt_subset hD'.1 hmc fun p hp => (hltD p hp).le
      have hyc := hsub (openHull_subset_convexHull _ hy)
      have hyc' := hsub' (openHull_subset_convexHull _ hy')
      rcases lt_trichotomy l l' with h | rfl | h
      · exact (S.not_combo_eq hC' hmc hltC (openHull_subset_convexHull _ hy) hyc'
          h hl1'.le hxe).elim
      · have hpos : (1 - l) ≠ 0 := by linarith
        have hyy : y = y' := smul_right_injective E hpos (add_left_cancel hxe)
        subst hyy
        exact ih _ (erase_ssubset hmC) _ y hC' hD' hy hy'
      · exact (S.not_combo_eq hD' hmc hltD (openHull_subset_convexHull _ hy') hyc
          h hl1.le hxe.symm).elim

/-- The **chain complex** of a cell structure: its faces are the sets of chosen points of the
chains of cells. -/
noncomputable def chainComplex : SComplex E where
  faces := (S.cells.powerset.filter fun C : Finset α =>
    IsChain (· ≤ ·) (↑C : Set α)).image (Finset.image S.pt)
  down s hs t ht := by
    simp only [Finset.mem_image, mem_filter, mem_powerset] at hs ⊢
    obtain ⟨C, ⟨hCs, hC⟩, rfl⟩ := hs
    obtain ⟨C', hC'C, rfl⟩ := subset_image_iff.1 ht
    exact ⟨C', ⟨hC'C.trans hCs, hC.mono (coe_subset.2 hC'C)⟩, rfl⟩

lemma mem_chainComplex {s : Finset E} :
    s ∈ S.chainComplex ↔ ∃ C, S.IsCellChain C ∧ C.image S.pt = s := by
  rw [← SComplex.mem_faces]
  simp only [chainComplex, Finset.mem_image, mem_filter, mem_powerset, IsCellChain]

/-- The chain complex has the empty face. -/
lemma empty_mem_chainComplex : (∅ : Finset E) ∈ S.chainComplex :=
  S.mem_chainComplex.2 ⟨∅, ⟨by simp, by simp⟩, by simp⟩

/-- **The chain complex is geometric.** -/
theorem isGeom_chainComplex : SComplex.IsGeom S.chainComplex where
  indep s hs := by
    obtain ⟨C, hC, rfl⟩ := S.mem_chainComplex.1 hs
    exact S.affineIndepOn_image_pt C hC
  inter s hs t ht := by
    obtain ⟨C, hC, rfl⟩ := S.mem_chainComplex.1 hs
    obtain ⟨D, hD, rfl⟩ := S.mem_chainComplex.1 ht
    rintro x ⟨hxC, hxD⟩
    obtain ⟨s', hs'C, hxs'⟩ := exists_openHull_of_mem_convexHull hxC
    obtain ⟨t', ht'D, hxt'⟩ := exists_openHull_of_mem_convexHull hxD
    obtain ⟨C', hC'C, rfl⟩ := subset_image_iff.1 hs'C
    obtain ⟨D', hD'D, rfl⟩ := subset_image_iff.1 ht'D
    have hCD := S.eq_of_mem_openHull_image_pt C' D' x (hC.mono hC'C) (hD.mono hD'D) hxs' hxt'
    subst hCD
    refine convexHull_mono ?_ (openHull_subset_convexHull _ hxs')
    rw [← coe_inter]
    exact coe_subset.2 (subset_inter hs'C ht'D)

/-- **Every point of a cell lies in a simplex of the chain complex**, provided that the ray from
the chosen point of a cell through any other point of the cell leaves it through a smaller
cell. -/
theorem exists_chain_of_mem_cell
    (hexit : ∀ a ∈ S.cells, ∀ x ∈ S.cell a, x ≠ S.pt a →
      ∃ t : ℝ, 1 ≤ t ∧ ∃ b ∈ S.cells, b < a ∧ S.pt a + t • (x - S.pt a) ∈ S.cell b) :
    ∀ n : ℕ, ∀ a ∈ S.cells, (S.cells.filter (· < a)).card = n → ∀ x ∈ S.cell a,
      ∃ C, S.IsCellChain C ∧ (∀ p ∈ C, p ≤ a) ∧ x ∈ convexHull ℝ (↑(C.image S.pt) : Set E) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a ha hn x hx
    by_cases hxb : x = S.pt a
    · refine ⟨{a}, ⟨singleton_subset_iff.2 ha, ?_⟩, by simp, ?_⟩
      · rw [coe_singleton]; exact IsChain.singleton
      · rw [image_singleton, coe_singleton, convexHull_singleton, hxb]; rfl
    obtain ⟨t, ht1, b, hb, hba, hy⟩ := hexit a ha x hx hxb
    have htpos : 0 < t := by linarith
    have hlt : (S.cells.filter (· < b)).card < n := by
      rw [← hn]
      refine card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨?_, ?_⟩)
      · intro p hp
        rw [mem_filter] at hp ⊢
        exact ⟨hp.1, lt_trans hp.2 hba⟩
      · intro he
        have : b ∈ S.cells.filter (· < a) := mem_filter.2 ⟨hb, hba⟩
        rw [← he] at this
        exact lt_irrefl _ (mem_filter.1 this).2
    obtain ⟨C', hC', hC'le, hyC'⟩ := ih _ hlt b hb rfl _ hy
    refine ⟨insert a C', ⟨insert_subset ha hC'.1, ?_⟩, ?_, ?_⟩
    · rw [coe_insert]
      exact hC'.2.insert fun p hp _ => Or.inr ((hC'le p hp).trans hba.le)
    · intro p hp
      rcases mem_insert.1 hp with rfl | hp
      · exact le_rfl
      · exact (hC'le p hp).trans hba.le
    · rw [image_insert]
      have hbh : S.pt a ∈ convexHull ℝ (↑(insert (S.pt a) (C'.image S.pt)) : Set E) :=
        subset_convexHull ℝ _ (by simp)
      have hyh : S.pt a + t • (x - S.pt a) ∈
          convexHull ℝ (↑(insert (S.pt a) (C'.image S.pt)) : Set E) :=
        convexHull_mono (by rw [coe_insert]; exact Set.subset_insert _ _) hyC'
      have hmem := (convex_convexHull ℝ _).add_smul_sub_mem hbh hyh
        ⟨inv_nonneg.2 htpos.le, inv_le_one_of_one_le₀ ht1⟩
      convert hmem using 1
      rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ htpos.ne', one_smul, add_sub_cancel]

end CellStructure

namespace SComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {K L : SComplex E}

/-- The strata of two geometric complexes form a cell structure: the open cell of `(σ, τ)` is
`σ° ∩ τ°` and its closed part is `σ ∩ τ`. -/
noncomputable def strataStructure (hK : IsGeom K) (hL : IsGeom L) :
    CellStructure E (Finset E × Finset E) where
  cells := strata K L
  cell p := openHull p.1 ∩ openHull p.2
  hull p := convexHull ℝ (p.1 : Set E) ∩ convexHull ℝ (p.2 : Set E)
  pt := pt
  pt_mem _ hp := pt_mem (mem_strata.1 hp).2.2
  nonempty _ hp := (mem_strata.1 hp).2.2
  convex_hull _ _ := (convex_convexHull ℝ _).inter (convex_convexHull ℝ _)
  cell_subset_hull _ _ x hx :=
    ⟨openHull_subset_convexHull _ hx.1, openHull_subset_convexHull _ hx.2⟩
  hull_mono _ _ _ _ hle _ hx :=
    ⟨convexHull_mono (coe_subset.2 hle.1) hx.1, convexHull_mono (coe_subset.2 hle.2) hx.2⟩
  cell_inj a ha b hb x hxa hxb :=
    Prod.ext (hK.eq_of_mem_openHull (mem_strata.1 ha).1 (mem_strata.1 hb).1 hxa.1 hxb.1)
      (hL.eq_of_mem_openHull (mem_strata.1 ha).2.1 (mem_strata.1 hb).2.1 hxa.2 hxb.2)
  combo_mem a ha p z hp hz l hl0 hl1 :=
    ⟨combo_mem_openHull hp.1 hz.1 hl0 hl1, combo_mem_openHull hp.2 hz.2 hl0 hl1⟩
  notMem_span a ha b hb hlt x hx hxs := by
    have h1 : affineSpan ℝ (convexHull ℝ (b.1 : Set E) ∩ convexHull ℝ (b.2 : Set E)) ≤
        affineSpan ℝ (b.1 : Set E) := by
      rw [← affineSpan_convexHull (b.1 : Set E)]
      exact affineSpan_mono ℝ Set.inter_subset_left
    have h2 : affineSpan ℝ (convexHull ℝ (b.1 : Set E) ∩ convexHull ℝ (b.2 : Set E)) ≤
        affineSpan ℝ (b.2 : Set E) := by
      rw [← affineSpan_convexHull (b.2 : Set E)]
      exact affineSpan_mono ℝ Set.inter_subset_right
    obtain ⟨ha₁, ha₂, -⟩ := mem_strata.1 ha
    by_cases he : b.1 = a.1
    · have hne₂ : b.2 ≠ a.2 := fun h => hlt.ne (Prod.ext he h)
      exact notMem_affineSpan_of_mem_openHull (hL.indep _ ha₂) hlt.le.2 hne₂ hx.2 (h2 hxs)
    · exact notMem_affineSpan_of_mem_openHull (hK.indep _ ha₁) hlt.le.1 he hx.1 (h1 hxs)

/-- The chosen points of the strata are the points of the cell structure of the strata. -/
lemma strataStructure_pt (hK : IsGeom K) (hL : IsGeom L) (p : Finset E × Finset E) :
    (strataStructure hK hL).pt p = pt p := rfl

/-- The chosen points of a chain of strata are affinely independent: the corresponding case of
`CellStructure.affineIndepOn_image_pt`. -/
theorem affineIndepOn_image_pt_of_structure (hK : IsGeom K) (hL : IsGeom L)
    (C : Finset (Finset E × Finset E)) (hC : IsStrataChain K L C) :
    AffineIndepOn ℝ id (↑(C.image pt) : Set E) :=
  (strataStructure hK hL).affineIndepOn_image_pt C hC

end SComplex

end Lightlike.PL
