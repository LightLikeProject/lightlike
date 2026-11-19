import Lightlike.FieldTheory.ZeroDim.GraphComp
import Mathlib.Data.Finset.Sort

/-!
# Restricting a labelled graph to a closed vertex set

For `Γ : LGraph n k` and a closed vertex set `B` (no edge leaves `B`), the half-edges at `B` (`hedges Γ B`) and `B`
are relabelled by `Fin` in increasing order (`Finset.orderIsoOfFin`), and `restrictL` is the graph induced on them; the
complement of a closed set is closed (`closed_compl`), so `Γ` splits into its parts at `B` and at `Bᶜ`. This is the
"split off one component" step of the class-refined exponential formula (Borinsky, Theorem 2.4.1, p. 18).
-/

open Finset

namespace Lightlike.FieldTheory.GraphAlg

section OrderIsoFin

variable {α : Type*} [LinearOrder α] (s : Finset α) {m : ℕ} (h : s.card = m)

/-- The increasing enumeration of `s` inverts its inverse, in the `orderEmbOfFin` form simp produces. -/
lemma orderIsoOfFin_symm_emb (a : Fin m) (hx : s.orderEmbOfFin h a ∈ s) :
    (s.orderIsoOfFin h).symm ⟨s.orderEmbOfFin h a, hx⟩ = a := by
  have : (⟨s.orderEmbOfFin h a, hx⟩ : s) = s.orderIsoOfFin h a := Subtype.ext (coe_orderIsoOfFin_apply s h a).symm
  rw [this, OrderIso.symm_apply_apply]

/-- The increasing enumeration of `s` after its inverse is the identity on `s`. -/
lemma emb_orderIsoOfFin_symm (x : α) (hx : x ∈ s) : s.orderEmbOfFin h ((s.orderIsoOfFin h).symm ⟨x, hx⟩) = x := by
  rw [← coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]

end OrderIsoFin

/-- The enumeration of a complement misses the set. -/
lemma orderEmbOfFin_compl_notMem {r m : ℕ} (t : Finset (Fin r)) (h : tᶜ.card = m) (a : Fin m) :
    tᶜ.orderEmbOfFin h a ∉ t :=
  mem_compl.1 (orderEmbOfFin_mem _ _ _)

attribute [local simp] orderIsoOfFin_symm_emb emb_orderIsoOfFin_symm orderEmbOfFin_compl_notMem

variable {n k : ℕ}

/-- The half-edges attached to the vertex set `B`. -/
def hedges (Γ : LGraph n k) (B : Finset (Fin k)) : Finset (Fin n) := univ.filter fun h => Γ.att h ∈ B

lemma mem_hedges {Γ : LGraph n k} {B : Finset (Fin k)} {h : Fin n} : h ∈ hedges Γ B ↔ Γ.att h ∈ B := by
  simp [hedges]

/-- The complement of a closed vertex set is closed. -/
lemma closed_compl {Γ : LGraph n k} {B : Finset (Fin k)} (hB : HalfEdge.Closed Γ.att Γ.inv B) :
    HalfEdge.Closed Γ.att Γ.inv Bᶜ := by
  intro h hh
  rw [mem_compl] at hh ⊢
  intro hc
  have := hB (Γ.inv h) hc
  rw [Γ.invol h] at this
  exact hh this

/-- **The graph induced on a closed vertex set `B`** with half-edge set `A` (the half-edges at `B`), relabelled by
`Fin` in increasing order. -/
noncomputable def restrictL (Γ : LGraph n k) (A : Finset (Fin n)) (B : Finset (Fin k))
    (hAB : ∀ h, h ∈ A ↔ Γ.att h ∈ B) (hB : HalfEdge.Closed Γ.att Γ.inv B) {n₁ k₁ : ℕ} (hA : A.card = n₁)
    (hk : B.card = k₁) : LGraph n₁ k₁ where
  att a := (B.orderIsoOfFin hk).symm ⟨Γ.att (A.orderIsoOfFin hA a), (hAB _).1 (A.orderIsoOfFin hA a).2⟩
  inv a := (A.orderIsoOfFin hA).symm
    ⟨Γ.inv (A.orderIsoOfFin hA a), (hAB _).2 (hB _ ((hAB _).1 (A.orderIsoOfFin hA a).2))⟩
  invol a := by
    apply (A.orderIsoOfFin hA).injective
    simp only [OrderIso.apply_symm_apply]
    exact Subtype.ext (Γ.invol _)

/-- **Gluing** a graph on `(A, B)` and a graph on `(Aᶜ, Bᶜ)` into a graph on `Fin n`, `Fin k`. -/
noncomputable def glue (A : Finset (Fin n)) (B : Finset (Fin k)) {n₁ k₁ n₂ k₂ : ℕ} (hA : A.card = n₁)
    (hk : B.card = k₁) (hA' : Aᶜ.card = n₂) (hk' : Bᶜ.card = k₂) (Γ₁ : LGraph n₁ k₁) (Γ₂ : LGraph n₂ k₂) :
    LGraph n k where
  att h := if hh : h ∈ A then (B.orderIsoOfFin hk (Γ₁.att ((A.orderIsoOfFin hA).symm ⟨h, hh⟩)) : Fin k)
    else (Bᶜ.orderIsoOfFin hk' (Γ₂.att ((Aᶜ.orderIsoOfFin hA').symm ⟨h, mem_compl.2 hh⟩)) : Fin k)
  inv h := if hh : h ∈ A then (A.orderIsoOfFin hA (Γ₁.inv ((A.orderIsoOfFin hA).symm ⟨h, hh⟩)) : Fin n)
    else (Aᶜ.orderIsoOfFin hA' (Γ₂.inv ((Aᶜ.orderIsoOfFin hA').symm ⟨h, mem_compl.2 hh⟩)) : Fin n)
  invol h := by
    by_cases hh : h ∈ A
    · have hm : (A.orderIsoOfFin hA (Γ₁.inv ((A.orderIsoOfFin hA).symm ⟨h, hh⟩)) : Fin n) ∈ A :=
        (A.orderIsoOfFin hA _).2
      have hi := Γ₁.invol ((A.orderIsoOfFin hA).symm ⟨h, hh⟩)
      simp only [hh, dite_true, hm, Subtype.coe_eta, OrderIso.symm_apply_apply, hi, OrderIso.apply_symm_apply]
    · have hm : (Aᶜ.orderIsoOfFin hA' (Γ₂.inv ((Aᶜ.orderIsoOfFin hA').symm ⟨h, mem_compl.2 hh⟩)) : Fin n) ∉ A :=
        mem_compl.1 (Aᶜ.orderIsoOfFin hA' _).2
      have hi := Γ₂.invol ((Aᶜ.orderIsoOfFin hA').symm ⟨h, mem_compl.2 hh⟩)
      simp only [hh, dite_false, hm, Subtype.coe_eta, OrderIso.symm_apply_apply, hi, OrderIso.apply_symm_apply]

/-- The half-edges at `B` and at `Bᶜ` partition the half-edges. -/
lemma card_hedges_add (Γ : LGraph n k) (B : Finset (Fin k)) :
    (hedges Γ B).card + (hedges Γ Bᶜ).card = n := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun h => Γ.att h ∈ B)
  simpa [hedges] using h


section Glue

variable {A : Finset (Fin n)} {B : Finset (Fin k)} {n₁ k₁ n₂ k₂ : ℕ} {hA : A.card = n₁} {hk : B.card = k₁}
  {hA' : Aᶜ.card = n₂} {hk' : Bᶜ.card = k₂} {Γ₁ : LGraph n₁ k₁} {Γ₂ : LGraph n₂ k₂}

lemma glue_att_mem (h : Fin n) : (glue A B hA hk hA' hk' Γ₁ Γ₂).att h ∈ B ↔ h ∈ A := by
  by_cases hh : h ∈ A
  · simp only [glue, hh, dite_true, iff_true]; exact (B.orderIsoOfFin hk _).2
  · simp only [glue, hh, dite_false, iff_false]; exact mem_compl.1 (Bᶜ.orderIsoOfFin hk' _).2

lemma closed_glue : HalfEdge.Closed (glue A B hA hk hA' hk' Γ₁ Γ₂).att (glue A B hA hk hA' hk' Γ₁ Γ₂).inv B := by
  intro h hh
  rw [glue_att_mem] at hh ⊢
  simp only [glue, hh, dif_pos]
  exact (A.orderIsoOfFin hA _).2

lemma restrictL_glue :
    restrictL (glue A B hA hk hA' hk' Γ₁ Γ₂) A B (fun h => (glue_att_mem h).symm) closed_glue hA hk = Γ₁ := by
  refine LGraph.ext (funext fun a => ?_) (funext fun a => ?_)
  · simp [restrictL, glue]
  · simp [restrictL, glue]

lemma restrictL_glue_compl :
    restrictL (glue A B hA hk hA' hk' Γ₁ Γ₂) Aᶜ Bᶜ
      (fun h => by rw [mem_compl, mem_compl, glue_att_mem]) (closed_compl closed_glue) hA' hk' = Γ₂ := by
  refine LGraph.ext (funext fun a => ?_) (funext fun a => ?_)
  · have ha : ((Aᶜ.orderIsoOfFin hA' a : Fin n)) ∉ A := mem_compl.1 (Aᶜ.orderIsoOfFin hA' a).2
    simp [restrictL, glue, ha]
  · have ha : ((Aᶜ.orderIsoOfFin hA' a : Fin n)) ∉ A := mem_compl.1 (Aᶜ.orderIsoOfFin hA' a).2
    simp [restrictL, glue, ha]

end Glue

/-- **A graph is glued from its parts** at a closed vertex set. -/
lemma glue_restrictL (Γ : LGraph n k) {A : Finset (Fin n)} {B : Finset (Fin k)} (hAB : ∀ h, h ∈ A ↔ Γ.att h ∈ B)
    (hB : HalfEdge.Closed Γ.att Γ.inv B) {n₁ k₁ n₂ k₂ : ℕ} (hA : A.card = n₁) (hk : B.card = k₁)
    (hA' : Aᶜ.card = n₂) (hk' : Bᶜ.card = k₂) :
    glue A B hA hk hA' hk' (restrictL Γ A B hAB hB hA hk)
      (restrictL Γ Aᶜ Bᶜ (fun h => by rw [mem_compl, mem_compl, hAB]) (closed_compl hB) hA' hk') = Γ := by
  refine LGraph.ext (funext fun h => ?_) (funext fun h => ?_)
  · by_cases hh : h ∈ A
    · simp [glue, restrictL, hh]
    · simp [glue, restrictL, hh]
  · by_cases hh : h ∈ A
    · simp [glue, restrictL, hh]
    · simp [glue, restrictL, hh]


section Conn

variable {A : Finset (Fin n)} {B : Finset (Fin k)} {n₁ k₁ n₂ k₂ : ℕ} {hA : A.card = n₁} {hk : B.card = k₁}
  {hA' : Aᶜ.card = n₂} {hk' : Bᶜ.card = k₂} {Γ₁ : LGraph n₁ k₁} {Γ₂ : LGraph n₂ k₂}

/-- The vertex embedding of the first part. -/
noncomputable def embB (B : Finset (Fin k)) {k₁ : ℕ} (hk : B.card = k₁) : Fin k₁ ↪ Fin k :=
  (B.orderIsoOfFin hk).toEquiv.toEmbedding.trans (Function.Embedding.subtype _)

lemma glue_att_emb (a : Fin n₁) :
    (glue A B hA hk hA' hk' Γ₁ Γ₂).att (A.orderIsoOfFin hA a) = embB B hk (Γ₁.att a) := by
  simp [glue, embB]

lemma glue_inv_emb (a : Fin n₁) :
    (glue A B hA hk hA' hk' Γ₁ Γ₂).inv (A.orderIsoOfFin hA a) = (A.orderIsoOfFin hA (Γ₁.inv a) : Fin n) := by
  simp [glue]

/-- Closed subsets of `B` in the glued graph are the images of closed sets of the first part. -/
lemma closed_glue_map (T : Finset (Fin k₁)) :
    HalfEdge.Closed (glue A B hA hk hA' hk' Γ₁ Γ₂).att (glue A B hA hk hA' hk' Γ₁ Γ₂).inv (T.map (embB B hk)) ↔
      HalfEdge.Closed Γ₁.att Γ₁.inv T := by
  constructor
  · intro hT a ha
    have := hT (A.orderIsoOfFin hA a) (by rw [glue_att_emb]; exact mem_map_of_mem _ ha)
    rwa [glue_inv_emb, show ((A.orderIsoOfFin hA (Γ₁.inv a) : Fin n)) = (A.orderIsoOfFin hA (Γ₁.inv a) : Fin n)
      from rfl, glue_att_emb, mem_map' ] at this
  · intro hT h hh
    have hB : (glue A B hA hk hA' hk' Γ₁ Γ₂).att h ∈ B := by
      obtain ⟨t, -, ht⟩ := mem_map.1 hh
      rw [← ht]; exact (B.orderIsoOfFin hk _).2
    have hhA : h ∈ A := (glue_att_mem h).1 hB
    obtain ⟨a, rfl⟩ : ∃ a, (A.orderIsoOfFin hA a : Fin n) = h :=
      ⟨(A.orderIsoOfFin hA).symm ⟨h, hhA⟩, by simp⟩
    rw [glue_att_emb, mem_map'] at hh
    rw [glue_inv_emb, glue_att_emb]
    exact mem_map_of_mem _ (hT a hh)

/-- **The glued graph is connected on `B` iff the first part is connected.** -/
lemma connOn_glue_iff :
    HalfEdge.ConnOn (glue A B hA hk hA' hk' Γ₁ Γ₂).att (glue A B hA hk hA' hk' Γ₁ Γ₂).inv B ↔ IsConnected Γ₁ := by
  have hBmap : B = (univ : Finset (Fin k₁)).map (embB B hk) := by
    ext v
    simp only [mem_map, mem_univ, true_and]
    constructor
    · intro hv; exact ⟨(B.orderIsoOfFin hk).symm ⟨v, hv⟩, by simp [embB]⟩
    · rintro ⟨a, rfl⟩; exact (B.orderIsoOfFin hk a).2
  unfold IsConnected
  constructor
  · rintro ⟨hn, hc⟩
    refine ⟨univ_nonempty_iff.2 ?_, fun T _ hT => ?_⟩
    · obtain ⟨v, hv⟩ := hn
      exact ⟨(B.orderIsoOfFin hk).symm ⟨v, hv⟩⟩
    · have hsub : T.map (embB B hk) ⊆ B := by
        intro v hv
        obtain ⟨a, -, rfl⟩ := mem_map.1 hv
        exact (B.orderIsoOfFin hk a).2
      rcases hc _ hsub ((closed_glue_map T).2 hT) with h | h
      · exact Or.inl (map_eq_empty.1 h)
      · exact Or.inr (map_injective _ (h.trans hBmap))
  · rintro ⟨hn, hc⟩
    refine ⟨by rw [hBmap]; exact map_nonempty.2 hn, fun U hUB hU => ?_⟩
    have hU' : U = (univ.filter fun a => embB B hk a ∈ U).map (embB B hk) := by
      ext v
      simp only [mem_map, mem_filter, mem_univ, true_and]
      constructor
      · intro hv
        have hvB := hUB hv
        rw [hBmap] at hvB
        obtain ⟨a, -, rfl⟩ := mem_map.1 hvB
        exact ⟨a, hv, rfl⟩
      · rintro ⟨a, ha, rfl⟩; exact ha
    rw [hU'] at hU ⊢
    rcases hc _ (subset_univ _) ((closed_glue_map _).1 hU) with h | h
    · left; rw [h, map_empty]
    · right; rw [h, ← hBmap]

end Conn


section ClassEq

open MulAction

/-- Transport of a labelled graph along equalities of the sizes. -/
def castL {m n j k : ℕ} (h : m = n) (h' : j = k) (Γ : LGraph m j) : LGraph n k := h ▸ h' ▸ Γ

lemma anyClass_castL {m n j k : ℕ} (h : m = n) (h' : j = k) (Γ : LGraph m j) :
    (⟨(m, j), ⟦Γ⟧⟩ : AnyClass) = ⟨(n, k), ⟦castL h h' Γ⟧⟩ := by
  subst h; subst h'; rfl

lemma castL_att {m n j k : ℕ} (h : m = n) (h' : j = k) (Γ : LGraph m j) (x : Fin n) :
    ((castL h h' Γ).att x : ℕ) = Γ.att (Fin.cast h.symm x) := by
  subst h; subst h'; rfl

lemma castL_inv {m n j k : ℕ} (h : m = n) (h' : j = k) (Γ : LGraph m j) (x : Fin n) :
    ((castL h h' Γ).inv x : ℕ) = Γ.inv (Fin.cast h.symm x) := by
  subst h; subst h'; rfl

end ClassEq


section GlueUnion

open MulAction

/-- The labels of `Fin m` as the labels of a set `A` followed by those of `Aᶜ` (`Fin (m₁ + m₂) ≃ Fin m`). -/
noncomputable def splitEquiv {m : ℕ} (A : Finset (Fin m)) {m₁ m₂ : ℕ} (hA : A.card = m₁) (hA' : Aᶜ.card = m₂) :
    Fin (m₁ + m₂) ≃ Fin m :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr (A.orderIsoOfFin hA).toEquiv
    ((Aᶜ.orderIsoOfFin hA').toEquiv.trans (Equiv.subtypeEquivRight fun x => mem_compl))).trans
      (Equiv.sumCompl fun x => x ∈ A))

lemma splitEquiv_castAdd {m : ℕ} (A : Finset (Fin m)) {m₁ m₂ : ℕ} (hA : A.card = m₁) (hA' : Aᶜ.card = m₂)
    (a : Fin m₁) : splitEquiv A hA hA' (Fin.castAdd m₂ a) = (A.orderIsoOfFin hA a : Fin m) := by
  simp [splitEquiv]

lemma splitEquiv_natAdd {m : ℕ} (A : Finset (Fin m)) {m₁ m₂ : ℕ} (hA : A.card = m₁) (hA' : Aᶜ.card = m₂)
    (b : Fin m₂) : splitEquiv A hA hA' (Fin.natAdd m₁ b) = (Aᶜ.orderIsoOfFin hA' b : Fin m) := by
  simp [splitEquiv]

lemma splitEquiv_castAdd_emb {m : ℕ} (A : Finset (Fin m)) {m₁ m₂ : ℕ} (hA : A.card = m₁) (hA' : Aᶜ.card = m₂)
    (a : Fin m₁) : splitEquiv A hA hA' (Fin.castAdd m₂ a) = A.orderEmbOfFin hA a :=
  splitEquiv_castAdd A hA hA' a

lemma splitEquiv_natAdd_emb {m : ℕ} (A : Finset (Fin m)) {m₁ m₂ : ℕ} (hA : A.card = m₁) (hA' : Aᶜ.card = m₂)
    (b : Fin m₂) : splitEquiv A hA hA' (Fin.natAdd m₁ b) = Aᶜ.orderEmbOfFin hA' b :=
  splitEquiv_natAdd A hA hA' b

lemma splitEquiv_symm_emb {m : ℕ} (A : Finset (Fin m)) {m₁ m₂ : ℕ} (hA : A.card = m₁) (hA' : Aᶜ.card = m₂)
    (a : Fin m₁) : (splitEquiv A hA hA').symm (A.orderEmbOfFin hA a) = Fin.castAdd m₂ a := by
  rw [Equiv.symm_apply_eq]; exact (splitEquiv_castAdd A hA hA' a).symm

lemma splitEquiv_symm_emb_compl {m : ℕ} (A : Finset (Fin m)) {m₁ m₂ : ℕ} (hA : A.card = m₁)
    (hA' : Aᶜ.card = m₂) (b : Fin m₂) : (splitEquiv A hA hA').symm (Aᶜ.orderEmbOfFin hA' b) = Fin.natAdd m₁ b := by
  rw [Equiv.symm_apply_eq]; exact (splitEquiv_natAdd A hA hA' b).symm

/-- Relabelling a graph along bijections of the half-edges and of the vertices. -/
def mapL {m n j k : ℕ} (e : Fin m ≃ Fin n) (f : Fin j ≃ Fin k) (Γ : LGraph m j) : LGraph n k where
  att := f ∘ Γ.att ∘ e.symm
  inv := e ∘ Γ.inv ∘ e.symm
  invol x := by simp [Γ.invol _]

/-- **A relabelled graph has the same isomorphism class.** -/
theorem anyClass_mapL {m n j k : ℕ} (e : Fin m ≃ Fin n) (f : Fin j ≃ Fin k) (Γ : LGraph m j) :
    (⟨(m, j), ⟦Γ⟧⟩ : AnyClass) = ⟨(n, k), ⟦mapL e f Γ⟧⟩ := by
  obtain rfl : m = n := Fin.equiv_iff_eq.1 ⟨e⟩
  obtain rfl : j = k := Fin.equiv_iff_eq.1 ⟨f⟩
  have h : (⟦mapL e f Γ⟧ : GClass m j) = ⟦Γ⟧ := Quotient.sound (mem_orbit_iff.2 ⟨(e, f), LGraph.ext rfl rfl⟩)
  rw [h]

variable {A : Finset (Fin n)} {B : Finset (Fin k)} {n₁ k₁ n₂ k₂ : ℕ} (hA : A.card = n₁) (hk : B.card = k₁)
  (hA' : Aᶜ.card = n₂) (hk' : Bᶜ.card = k₂) (Γ₁ : LGraph n₁ k₁) (Γ₂ : LGraph n₂ k₂)

/-- **The glued graph is a relabelling of the disjoint union** of its parts. -/
theorem glue_eq_mapL_union :
    glue A B hA hk hA' hk' Γ₁ Γ₂ = mapL (splitEquiv A hA hA') (splitEquiv B hk hk') (union Γ₁ Γ₂) := by
  refine LGraph.ext (funext fun x => ?_) (funext fun x => ?_) <;> by_cases hx : x ∈ A
  · obtain ⟨a, rfl⟩ : ∃ a, A.orderEmbOfFin hA a = x := ⟨(A.orderIsoOfFin hA).symm ⟨x, hx⟩, by simp⟩
    simp [glue, mapL, union, splitEquiv_symm_emb, splitEquiv_castAdd_emb]
  · obtain ⟨b, rfl⟩ : ∃ b, Aᶜ.orderEmbOfFin hA' b = x := ⟨(Aᶜ.orderIsoOfFin hA').symm ⟨x, mem_compl.2 hx⟩, by simp⟩
    simp [glue, mapL, union, splitEquiv_symm_emb_compl, splitEquiv_natAdd_emb]
  · obtain ⟨a, rfl⟩ : ∃ a, A.orderEmbOfFin hA a = x := ⟨(A.orderIsoOfFin hA).symm ⟨x, hx⟩, by simp⟩
    simp [glue, mapL, union, splitEquiv_symm_emb, splitEquiv_castAdd_emb]
  · obtain ⟨b, rfl⟩ : ∃ b, Aᶜ.orderEmbOfFin hA' b = x := ⟨(Aᶜ.orderIsoOfFin hA').symm ⟨x, mem_compl.2 hx⟩, by simp⟩
    simp [glue, mapL, union, splitEquiv_symm_emb_compl, splitEquiv_natAdd_emb]

/-- **The class of a glued graph is the disjoint union of the classes of its parts.** -/
theorem anyClass_glue :
    (⟨(n, k), ⟦glue A B hA hk hA' hk' Γ₁ Γ₂⟧⟩ : AnyClass) =
      ⟨(n₁ + n₂, k₁ + k₂), unionC ⟦Γ₁⟧ ⟦Γ₂⟧⟩ := by
  rw [glue_eq_mapL_union, ← anyClass_mapL]
  rfl

end GlueUnion


section Comps

variable {A : Finset (Fin n)} {B : Finset (Fin k)} {n₁ k₁ n₂ k₂ : ℕ} {hA : A.card = n₁} {hk : B.card = k₁}
  {hA' : Aᶜ.card = n₂} {hk' : Bᶜ.card = k₂} {Γ₁ : LGraph n₁ k₁} {Γ₂ : LGraph n₂ k₂}

lemma glue_att_emb₂ (b : Fin n₂) :
    (glue A B hA hk hA' hk' Γ₁ Γ₂).att (Aᶜ.orderIsoOfFin hA' b) = embB Bᶜ hk' (Γ₂.att b) := by
  have hb : ((Aᶜ.orderIsoOfFin hA' b : Fin n)) ∉ A := mem_compl.1 (Aᶜ.orderIsoOfFin hA' b).2
  simp [glue, embB, hb]

lemma glue_inv_emb₂ (b : Fin n₂) :
    (glue A B hA hk hA' hk' Γ₁ Γ₂).inv (Aᶜ.orderIsoOfFin hA' b) = (Aᶜ.orderIsoOfFin hA' (Γ₂.inv b) : Fin n) := by
  have hb : ((Aᶜ.orderIsoOfFin hA' b : Fin n)) ∉ A := mem_compl.1 (Aᶜ.orderIsoOfFin hA' b).2
  simp [glue, hb]

/-- Closed sets of the second part give closed sets of the glued graph. -/
lemma closed_glue_map₂ (T : Finset (Fin k₂)) :
    HalfEdge.Closed (glue A B hA hk hA' hk' Γ₁ Γ₂).att (glue A B hA hk hA' hk' Γ₁ Γ₂).inv (T.map (embB Bᶜ hk')) ↔
      HalfEdge.Closed Γ₂.att Γ₂.inv T := by
  constructor
  · intro hT b hb
    have := hT (Aᶜ.orderIsoOfFin hA' b) (by rw [glue_att_emb₂]; exact mem_map_of_mem _ hb)
    rwa [glue_inv_emb₂, glue_att_emb₂, mem_map'] at this
  · intro hT h hh
    have hB : (glue A B hA hk hA' hk' Γ₁ Γ₂).att h ∉ B := by
      obtain ⟨t, -, ht⟩ := mem_map.1 hh
      rw [← ht]; exact mem_compl.1 (Bᶜ.orderIsoOfFin hk' _).2
    have hhA : h ∈ Aᶜ := mem_compl.2 fun h' => hB ((glue_att_mem h).2 h')
    obtain ⟨b, rfl⟩ : ∃ b, (Aᶜ.orderIsoOfFin hA' b : Fin n) = h :=
      ⟨(Aᶜ.orderIsoOfFin hA').symm ⟨h, hhA⟩, by simp⟩
    rw [glue_att_emb₂, mem_map'] at hh
    rw [glue_inv_emb₂, glue_att_emb₂]
    exact mem_map_of_mem _ (hT b hh)

/-- Connectedness of the images of vertex sets of the second part. -/
lemma connOn_glue_map₂ (T : Finset (Fin k₂)) :
    HalfEdge.ConnOn (glue A B hA hk hA' hk' Γ₁ Γ₂).att (glue A B hA hk hA' hk' Γ₁ Γ₂).inv (T.map (embB Bᶜ hk')) ↔
      HalfEdge.ConnOn Γ₂.att Γ₂.inv T := by
  constructor
  · rintro ⟨hn, hc⟩
    refine ⟨map_nonempty.1 hn, fun T' hT'T hT' => ?_⟩
    rcases hc (T'.map (embB Bᶜ hk')) (map_subset_map.2 hT'T) ((closed_glue_map₂ T').2 hT') with h | h
    · exact Or.inl (map_eq_empty.1 h)
    · exact Or.inr (map_injective _ h)
  · rintro ⟨hn, hc⟩
    refine ⟨map_nonempty.2 hn, fun U hUT hU => ?_⟩
    have hU' : U = (T.filter fun a => embB Bᶜ hk' a ∈ U).map (embB Bᶜ hk') := by
      ext v
      simp only [mem_map, mem_filter]
      constructor
      · intro hv
        obtain ⟨a, ha, rfl⟩ := mem_map.1 (hUT hv)
        exact ⟨a, ⟨ha, hv⟩, rfl⟩
      · rintro ⟨a, ⟨-, ha⟩, rfl⟩; exact ha
    rw [hU'] at hU ⊢
    rcases hc _ (filter_subset _ _) ((closed_glue_map₂ _).1 hU) with h | h
    · left; rw [h, map_empty]
    · right; rw [h]

/-- The vertex sets of the second part, as vertex sets of the glued graph. -/
noncomputable def mapB₂ (B : Finset (Fin k)) {k₂ : ℕ} (hk' : Bᶜ.card = k₂) : Finset (Fin k₂) ↪ Finset (Fin k) :=
  ⟨fun T => T.map (embB Bᶜ hk'), map_injective _⟩

/-- **The components of a glued graph**: `B` (if the first part is connected) and the images of the components of
the second part. -/
theorem comps_glue (hconn : IsConnected Γ₁) :
    comps (glue A B hA hk hA' hk' Γ₁ Γ₂) = insert B ((comps Γ₂).map (mapB₂ B hk')) := by
  classical
  set Γ := glue A B hA hk hA' hk' Γ₁ Γ₂
  have hBc : B ∈ comps Γ := by
    rw [comps, mem_filter]
    exact ⟨mem_univ _, closed_glue, connOn_glue_iff.2 hconn⟩
  have himg : ∀ T ∈ comps Γ₂, T.map (embB Bᶜ hk') ∈ comps Γ := by
    intro T hT
    rw [comps, mem_filter] at hT ⊢
    exact ⟨mem_univ _, (closed_glue_map₂ T).2 hT.2.1, (connOn_glue_map₂ T).2 hT.2.2⟩
  ext U
  rw [mem_insert, mem_map]
  constructor
  · intro hU
    have hUne : U.Nonempty := by rw [comps, mem_filter] at hU; exact hU.2.2.1
    obtain ⟨v, hv⟩ := hUne
    by_cases hvB : v ∈ B
    · left; exact ((existsUnique_comp Γ v).unique ⟨hU, hv⟩ ⟨hBc, hvB⟩)
    · right
      obtain ⟨w, rfl⟩ : ∃ w, embB Bᶜ hk' w = v :=
        ⟨(Bᶜ.orderIsoOfFin hk').symm ⟨v, mem_compl.2 hvB⟩, by simp [embB]⟩
      obtain ⟨T, ⟨hT, hwT⟩, -⟩ := existsUnique_comp Γ₂ w
      refine ⟨T, hT, ?_⟩
      exact ((existsUnique_comp Γ _).unique ⟨himg T hT, mem_map_of_mem _ hwT⟩ ⟨hU, hv⟩)
  · rintro (rfl | ⟨T, hT, rfl⟩)
    · exact hBc
    · exact himg T hT

end Comps

end Lightlike.FieldTheory.GraphAlg
