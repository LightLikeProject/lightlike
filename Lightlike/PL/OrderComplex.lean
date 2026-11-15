import Lightlike.PL.SphereBall

/-!
# The order complex and the first derived subdivision

The order complex of a finite poset has the chains as faces. The *first derived subdivision* of a
complex `K` is the order complex of its nonempty faces ordered by inclusion. This file shows that
it is a stellar subdivision: starring the faces of `K` one by one, in an order in which every face
comes after all faces strictly containing it, produces the order complex.

The intermediate complexes are described explicitly. After starring a set `P` of faces closed
upwards in `K`, a face is a pair `(U, C)` of a set `U` of old vertices and a chain `C` of starred
faces (`mixPred`).
-/

open Finset

namespace Lightlike.PL
namespace SComplex
variable {V : Type*} [DecidableEq V]

/-! ## The order complex -/

open Classical in
/-- The **order complex** of the elements `S` of a poset: its faces are the chains in `S`. -/
noncomputable def orderComplex {P : Type*} [PartialOrder P] [DecidableEq P] (S : Finset P) :
    SComplex P where
  faces := S.powerset.filter fun C => ∀ a ∈ C, ∀ b ∈ C, a ≤ b ∨ b ≤ a
  down s hs t ht := by
    simp only [mem_filter, mem_powerset] at hs ⊢
    exact ⟨ht.trans hs.1, fun a ha b hb => hs.2 a (ht ha) b (ht hb)⟩

open Classical in
lemma mem_orderComplex {P : Type*} [PartialOrder P] [DecidableEq P] {S : Finset P} {C : Finset P} :
    C ∈ orderComplex S ↔ C ⊆ S ∧ ∀ a ∈ C, ∀ b ∈ C, a ≤ b ∨ b ≤ a := by
  change C ∈ (S.powerset.filter _) ↔ _
  simp only [mem_filter, mem_powerset]

/-- The **first derived subdivision** of `K`: the order complex of its nonempty faces ordered by
inclusion. Its vertices are the nonempty faces of `K`. -/
noncomputable def sd (K : SComplex V) : SComplex (Finset V) :=
  orderComplex (K.faces.erase ∅)

/-! ## The complexes between `K` and its derived subdivision -/

/-- The faces of the complex obtained from `K` by starring the faces in `P`: a face is a set `U` of
old vertices together with a chain `C` of starred faces, such that `U` together with the largest
face of `C` is a face of `K`, and no face of `P` is covered by `U` and a member of `C` without
already lying in that member. -/
def mixPred (K : SComplex V) (P : Finset (Finset V)) (U : Finset V) (C : Finset (Finset V)) :
    Prop :=
  (∀ a ∈ C, ∀ b ∈ C, a ⊆ b ∨ b ⊆ a) ∧ C ⊆ P ∧ U ∪ C.sup id ∈ K ∧
    ∀ c₀ ∈ insert ∅ C, ∀ c ∈ P, c ⊆ U ∪ c₀ → c ⊆ c₀

/-- The hypotheses for starring the face `A` after the faces of `P`: `P` consists of nonempty faces
and is closed upwards in `K`, and `A` is a face outside `P` all of whose proper supersets are in
`P`. -/
structure StepOK (K : SComplex V) (P : Finset (Finset V)) (A : Finset V) : Prop where
  /-- Members of `P` are nonempty. -/
  pne : ∀ c ∈ P, c.Nonempty
  /-- `P` is closed upwards in `K`. -/
  up : ∀ c ∈ P, ∀ b ∈ K, c ⊂ b → b ∈ P
  /-- `A` is a face. -/
  mem : A ∈ K
  /-- `A` is nonempty. -/
  ne : A.Nonempty
  /-- `A` has not been starred. -/
  notP : A ∉ P
  /-- All proper supersets of `A` have been starred. -/
  sup : ∀ b ∈ K, A ⊂ b → b ∈ P

namespace StepOK
variable {K : SComplex V} {P : Finset (Finset V)} {A : Finset V}

/-- No starred face lies inside `A`. -/
lemma not_sub (h : StepOK K P A) {c : Finset V} (hc : c ∈ P) : ¬ c ⊆ A := by
  intro hca
  rcases hca.eq_or_ssubset with rfl | hlt
  · exact h.notP hc
  · exact h.notP (h.up c hc A h.mem hlt)

end StepOK

lemma mixPred_not_sub {K : SComplex V} {P : Finset (Finset V)} {A : Finset V} {U : Finset V}
    {C : Finset (Finset V)} (hne : A.Nonempty) (h : mixPred K (insert A P) U C) : ¬ A ⊆ U := by
  intro hA
  have := h.2.2.2 ∅ (mem_insert_self _ _) A (mem_insert_self _ _) (by simpa using hA)
  exact hne.ne_empty (subset_empty.1 this)

lemma mixPred_insert_of_not {K : SComplex V} {P : Finset (Finset V)} {A : Finset V}
    (h : StepOK K P A) {U : Finset V} {C : Finset (Finset V)} (hP : mixPred K P U C)
    (hAU : ¬ A ⊆ U) : mixPred K (insert A P) U C := by
  refine ⟨hP.1, hP.2.1.trans (subset_insert _ _), hP.2.2.1, fun c₀ hc₀ c hc hsub => ?_⟩
  rcases mem_insert.1 hc with hcA | hcP
  · rw [hcA] at hsub ⊢
    rcases mem_insert.1 hc₀ with h0 | hc₀C
    · rw [h0] at hsub
      exact absurd (by simpa using hsub) hAU
    · have hc₀P := hP.2.1 hc₀C
      have hBK : U ∪ c₀ ∈ K :=
        K.down_mem hP.2.2.1 (union_subset_union_right (le_sup (f := id) hc₀C))
      rcases hsub.eq_or_ssubset with heq | hlt
      · exact absurd (by rw [heq]; exact subset_union_right) (h.not_sub hc₀P)
      · exact hsub.trans (hP.2.2.2 c₀ hc₀ _ (h.sup _ hBK hlt) subset_rfl)
  · exact hP.2.2.2 c₀ hc₀ c hcP hsub

lemma mixPred_of_mem {K : SComplex V} {P : Finset (Finset V)} {A : Finset V}
    (h : StepOK K P A) {U : Finset V} {C : Finset (Finset V)}
    (hP : mixPred K (insert A P) U C) (hAC : A ∈ C) :
    mixPred K P U (C.erase A) ∧ mixPred K P (U ∪ A) (C.erase A) := by
  have hsupA : A ⊆ C.sup id := le_sup (f := id) hAC
  have hsupE : (C.erase A).sup id ⊆ C.sup id := sup_mono (erase_subset _ _)
  have hchain : ∀ a ∈ C.erase A, ∀ b ∈ C.erase A, a ⊆ b ∨ b ⊆ a :=
    fun a ha b hb => hP.1 a (mem_of_mem_erase ha) b (mem_of_mem_erase hb)
  have hCP : C.erase A ⊆ P := by
    intro c hc
    rcases mem_insert.1 (hP.2.1 (mem_of_mem_erase hc)) with rfl | hcP
    · exact absurd rfl (ne_of_mem_erase hc)
    · exact hcP
  refine ⟨⟨hchain, hCP, K.down_mem hP.2.2.1 (union_subset_union_right hsupE), ?_⟩,
    ⟨hchain, hCP, K.down_mem hP.2.2.1 ?_, ?_⟩⟩
  · intro c₀ hc₀ c hc hsub
    exact hP.2.2.2 c₀ (by
      rcases mem_insert.1 hc₀ with h0 | h0
      · exact mem_insert.2 (.inl h0)
      · exact mem_insert_of_mem (mem_of_mem_erase h0)) c (mem_insert_of_mem hc) hsub
  · exact union_subset (union_subset subset_union_left (hsupA.trans subset_union_right))
      (hsupE.trans subset_union_right)
  · intro c₀ hc₀ c hc hsub
    have hc₀' : c₀ = ∅ ∨ c₀ ∈ C.erase A := mem_insert.1 hc₀
    have hcmp : c₀ ⊆ A ∨ A ⊆ c₀ := by
      rcases hc₀' with rfl | hc₀E
      · exact .inl (empty_subset _)
      · exact hP.1 c₀ (mem_of_mem_erase hc₀E) A hAC
    rcases hcmp with hle | hle
    · exfalso
      refine h.not_sub hc (?_ : c ⊆ A)
      have : c ⊆ U ∪ A := hsub.trans (by
        intro x hx
        rcases mem_union.1 hx with hx | hx
        · rcases mem_union.1 hx with hx | hx
          · exact mem_union_left _ hx
          · exact mem_union_right _ hx
        · exact mem_union_right _ (hle hx))
      exact hP.2.2.2 A (mem_insert_of_mem hAC) c (mem_insert_of_mem hc) this
    · have hc₀C : c₀ ∈ insert ∅ C := by
        rcases hc₀' with h0 | h0
        · exact mem_insert.2 (.inl h0)
        · exact mem_insert_of_mem (mem_of_mem_erase h0)
      exact hP.2.2.2 c₀ hc₀C c (mem_insert_of_mem hc) (hsub.trans (by
        intro x hx
        rcases mem_union.1 hx with hx | hx
        · rcases mem_union.1 hx with hx | hx
          · exact mem_union_left _ hx
          · exact mem_union_right _ (hle hx)
        · exact mem_union_right _ hx))

lemma mixPred_of_not_mem {K : SComplex V} {P : Finset (Finset V)} {A : Finset V}
    {U : Finset V} {C : Finset (Finset V)} (hP : mixPred K (insert A P) U C) (hAC : A ∉ C) :
    mixPred K P U C := by
  refine ⟨hP.1, fun c hc => ?_, hP.2.2.1, fun c₀ hc₀ c hc hsub =>
    hP.2.2.2 c₀ hc₀ c (mem_insert_of_mem hc) hsub⟩
  rcases mem_insert.1 (hP.2.1 hc) with rfl | h
  · exact absurd hc hAC
  · exact h

lemma mixPred_insert {K : SComplex V} {P : Finset (Finset V)} {A : Finset V}
    (h : StepOK K P A) {U : Finset V} {C : Finset (Finset V)} (hP : mixPred K P U C)
    (hP2 : mixPred K P (U ∪ A) C) (hAU : ¬ A ⊆ U) :
    mixPred K (insert A P) U (insert A C) := by
  have key : ∀ c ∈ C, A ⊆ c := by
    intro c hc
    have hcP := hP.2.1 hc
    have hBK : A ∪ c ∈ K := by
      refine K.down_mem hP2.2.2.1 ?_
      intro y hy
      rcases mem_union.1 hy with hy | hy
      · exact mem_union_left _ (mem_union_right _ hy)
      · exact mem_union_right _ (le_sup (f := id) hc hy)
    by_cases hlt : A ⊂ A ∪ c
    · have hBP := h.sup _ hBK hlt
      have := hP2.2.2.2 c (mem_insert_of_mem hc) _ hBP (by
        intro y hy
        rcases mem_union.1 hy with hy | hy
        · exact mem_union_left _ (mem_union_right _ hy)
        · exact mem_union_right _ hy)
      exact subset_union_left.trans this
    · exfalso
      have : A ∪ c ⊆ A := by
        by_contra hn
        exact hlt ⟨subset_union_left, fun hh => hn hh⟩
      exact h.not_sub hcP (subset_union_right.trans this)
  have hAnC : A ∉ C := fun hA => h.notP (hP.2.1 hA)
  refine ⟨?_, insert_subset_insert _ hP.2.1, ?_, ?_⟩
  · intro a ha b hb
    rcases mem_insert.1 ha with rfl | haC <;> rcases mem_insert.1 hb with rfl | hbC
    · exact .inl subset_rfl
    · exact .inl (key b hbC)
    · exact .inr (key a haC)
    · exact hP.1 a haC b hbC
  · have : U ∪ (insert A C).sup id = (U ∪ A) ∪ C.sup id := by
      rw [sup_insert, id, Finset.sup_eq_union, union_assoc]
    rw [this]; exact hP2.2.2.1
  · intro c₀ hc₀ c hc hsub
    rcases mem_insert.1 hc₀ with h0 | hc₀'
    · rw [h0] at hsub ⊢
      rcases mem_insert.1 hc with hcA | hcP
      · rw [hcA] at hsub; exact absurd (by simpa using hsub) hAU
      · exact hP.2.2.2 ∅ (mem_insert_self _ _) c hcP hsub
    · rcases mem_insert.1 hc₀' with h0 | hc₀C
      · rw [h0] at hsub ⊢
        rcases mem_insert.1 hc with hcA | hcP
        · rw [hcA]
        · exact (hP2.2.2.2 ∅ (mem_insert_self _ _) c hcP (by simpa using hsub)).trans
            (empty_subset _)
      · rcases mem_insert.1 hc with hcA | hcP
        · rw [hcA]; exact key c₀ hc₀C
        · exact hP.2.2.2 c₀ (mem_insert_of_mem hc₀C) c hcP hsub

/-! ## Starring the faces in order -/

/-- The complex obtained from `K` by starring the faces in the list, the last one first, at the new
vertices `inr A`. -/
def iterStar (K : SComplex V) : List (Finset V) → SComplex (V ⊕ Finset V)
  | [] => K.map Function.Embedding.inl
  | A :: L => (iterStar K L).starAt (A.map Function.Embedding.inl) (Sum.inr A)

/-- A list of faces is admissible if each face comes after all faces strictly containing it
(reading from the right), and the faces are nonempty and distinct. -/
def Adm (K : SComplex V) : List (Finset V) → Prop
  | [] => True
  | A :: L => Adm K L ∧ A ∈ K ∧ A.Nonempty ∧ A ∉ L ∧ ∀ b ∈ K, A ⊂ b → b ∈ L

lemma Adm.stepOK {K : SComplex V} : ∀ {L : List (Finset V)}, Adm K L → 
    (∀ c ∈ L, c.Nonempty) ∧ (∀ c ∈ L, ∀ b ∈ K, c ⊂ b → b ∈ L)
  | [], _ => ⟨by simp, by simp⟩
  | A :: L, ⟨hL, hAK, hne, _, hsup⟩ => by
    obtain ⟨h1, h2⟩ := Adm.stepOK hL
    refine ⟨fun c hc => ?_, fun c hc b hb hcb => ?_⟩
    · rcases List.mem_cons.1 hc with rfl | hc
      · exact hne
      · exact h1 c hc
    · rcases List.mem_cons.1 hc with rfl | hc
      · exact List.mem_cons_of_mem _ (hsup b hb hcb)
      · exact List.mem_cons_of_mem _ (h2 c hc b hb hcb)

lemma toLeft_map_inl (A : Finset V) :
    (A.map (Function.Embedding.inl : V ↪ V ⊕ Finset V)).toLeft = A := by
  ext x; simp

lemma toRight_map_inl (A : Finset V) :
    (A.map (Function.Embedding.inl : V ↪ V ⊕ Finset V)).toRight = ∅ := by
  ext x; simp

lemma toLeft_erase_inr (s : Finset (V ⊕ Finset V)) (A : Finset V) :
    (s.erase (Sum.inr A)).toLeft = s.toLeft := by
  ext x; simp

lemma toRight_erase_inr (s : Finset (V ⊕ Finset V)) (A : Finset V) :
    (s.erase (Sum.inr A)).toRight = s.toRight.erase A := by
  ext x; simp

lemma mem_map_inl_iff (K : SComplex V) (s : Finset (V ⊕ Finset V)) :
    s ∈ K.map (Function.Embedding.inl : V ↪ V ⊕ Finset V) ↔ s.toLeft ∈ K ∧ s.toRight = ∅ := by
  rw [mem_map]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨by rwa [toLeft_map_inl], toRight_map_inl t⟩
  · rintro ⟨h1, h2⟩
    refine ⟨s.toLeft, h1, ?_⟩
    ext x
    rcases x with x | x
    · simp
    · have : x ∉ s.toRight := by rw [h2]; simp
      simpa using this

/-- **The faces of the partially subdivided complex.** For an admissible list, the complex
`iterStar K L` has exactly the faces described by `mixPred`. -/
theorem mem_iterStar (K : SComplex V) : ∀ L : List (Finset V), Adm K L →
    ∀ s : Finset (V ⊕ Finset V),
      s ∈ iterStar K L ↔ mixPred K L.toFinset s.toLeft s.toRight
  | [], _, s => by
    rw [iterStar, mem_map_inl_iff]
    constructor
    · rintro ⟨h1, h2⟩
      rw [h2]
      refine ⟨by simp, by simp, by simpa using h1, by simp⟩
    · rintro ⟨-, h2, h3, -⟩
      have : s.toRight = ∅ := by simpa using h2
      refine ⟨?_, this⟩
      simpa [this] using h3
  | A :: L, hadm, s => by
    obtain ⟨hL, hAK, hne, hAL, hsup⟩ := hadm
    have ih := mem_iterStar K L hL
    obtain ⟨hpne, hup⟩ := Adm.stepOK hL
    have hstep : StepOK K L.toFinset A :=
      ⟨fun c hc => hpne c (List.mem_toFinset.1 hc),
        fun c hc b hb hcb => List.mem_toFinset.2 (hup c (List.mem_toFinset.1 hc) b hb hcb),
        hAK, hne, fun h => hAL (List.mem_toFinset.1 h),
        fun b hb hlt => List.mem_toFinset.2 (hsup b hb hlt)⟩
    rw [iterStar, List.toFinset_cons, mem_starAt]
    constructor
    · rintro (⟨hs, hn⟩ | ⟨t, ht, hn, hAt, rfl⟩)
      · exact mixPred_insert_of_not hstep ((ih s).1 hs)
          (by rwa [Finset.map_inl_subset_iff_subset_toLeft] at hn)
      · have h1 := (ih t).1 ht
        have h2 := (ih _).1 hAt
        rw [toLeft_union, toRight_union, toLeft_map_inl, toRight_map_inl, empty_union] at h2
        rw [Finset.toLeft_insert_inr, Finset.toRight_insert_inr]
        exact mixPred_insert hstep h1 (by rwa [Finset.union_comm] at h2)
          (by rwa [Finset.map_inl_subset_iff_subset_toLeft] at hn)
    · intro h
      by_cases hAC : A ∈ s.toRight
      · obtain ⟨h1, h2⟩ := mixPred_of_mem hstep h hAC
        right
        refine ⟨s.erase (Sum.inr A), (ih _).2 ?_, ?_, ?_, ?_⟩
        · rw [toLeft_erase_inr, toRight_erase_inr]; exact h1
        · rw [Finset.map_inl_subset_iff_subset_toLeft, toLeft_erase_inr]
          exact mixPred_not_sub hne h
        · refine (ih _).2 ?_
          rw [toLeft_union, toRight_union, toLeft_map_inl, toRight_map_inl, toLeft_erase_inr,
            toRight_erase_inr, empty_union, Finset.union_comm]
          exact h2
        · exact Finset.insert_erase (Finset.mem_toRight.1 hAC)
      · left
        exact ⟨(ih s).2 (mixPred_of_not_mem h hAC), by
          rw [Finset.map_inl_subset_iff_subset_toLeft]; exact mixPred_not_sub hne h⟩

/-- Every set of nonempty faces closed upwards in `K` is the set of an admissible list. -/
theorem exists_adm (K : SComplex V) : ∀ (n : ℕ) (P : Finset (Finset V)), #P = n →
    (∀ c ∈ P, c ∈ K ∧ c.Nonempty) → (∀ c ∈ P, ∀ b ∈ K, c ⊂ b → b ∈ P) →
    ∃ L : List (Finset V), Adm K L ∧ L.toFinset = P
  | 0, P, hP, _, _ => ⟨[], trivial, by rw [card_eq_zero] at hP; simp [hP]⟩
  | n + 1, P, hP, hmem, hup => by
    have hPne : P.Nonempty := by rw [← card_pos]; omega
    obtain ⟨A, hAP, hmin⟩ := exists_min_image P (fun c => #c) hPne
    have hlt : ∀ c ∈ P, ¬ c ⊂ A := fun c hc hcA => by
      have := card_lt_card hcA
      have := hmin c hc
      omega
    obtain ⟨L, hL, hLP⟩ := exists_adm K n (P.erase A) (by rw [card_erase_of_mem hAP]; omega)
      (fun c hc => hmem c (mem_of_mem_erase hc))
      (fun c hc b hb hcb => mem_erase.2 ⟨fun hba => hlt c (mem_of_mem_erase hc) (hba ▸ hcb),
        hup c (mem_of_mem_erase hc) b hb hcb⟩)
    refine ⟨A :: L, ⟨hL, (hmem A hAP).1, (hmem A hAP).2, ?_, ?_⟩, ?_⟩
    · intro h
      have := List.mem_toFinset.2 h
      rw [hLP] at this; simp at this
    · intro b hb hAb
      have : b ∈ L.toFinset := by
        rw [hLP]; exact mem_erase.2 ⟨hAb.ne', hup A hAP b hb hAb⟩
      exact List.mem_toFinset.1 this
    · rw [List.toFinset_cons, hLP, insert_erase hAP]

/-- A chain of faces of a complex (with `∅` a face) has its union as a face: the union is the
largest member, or empty. -/
lemma chain_sup_mem {K : SComplex V} (h0 : ∅ ∈ K) {C : Finset (Finset V)} (hC : C ⊆ K.faces)
    (hch : ∀ a ∈ C, ∀ b ∈ C, a ⊆ b ∨ b ⊆ a) : C.sup id ∈ K := by
  rcases C.eq_empty_or_nonempty with rfl | hne
  · simpa using h0
  · obtain ⟨m, hm, hmax⟩ := exists_max_image C (fun c => #c) hne
    have : C.sup id = m := by
      refine le_antisymm (Finset.sup_le fun c hc => ?_) (le_sup (f := id) hm)
      rcases hch c hc m hm with h | h
      · exact h
      · exact (eq_of_subset_of_card_le h (hmax c hc)).symm.subset
    rw [this]; exact hC hm

/-- Starring the faces of an admissible list is a stellar equivalence. -/
theorem stellarEquivIn_iterStar (K : SComplex V) :
    ∀ L : List (Finset V), Adm K L →
      StellarEquivIn (K.map (Function.Embedding.inl : V ↪ V ⊕ Finset V)) (iterStar K L)
  | [], _ => .refl _
  | A :: L, hadm => by
    have hL := hadm.1
    obtain ⟨hAK, hne, hAL, hsup⟩ := hadm.2
    have ih := stellarEquivIn_iterStar K L hL
    obtain ⟨hpne, hup⟩ := Adm.stepOK hL
    have hstep : StepOK K L.toFinset A :=
      ⟨fun c hc => hpne c (List.mem_toFinset.1 hc),
        fun c hc b hb hcb => List.mem_toFinset.2 (hup c (List.mem_toFinset.1 hc) b hb hcb),
        hAK, hne, fun h => hAL (List.mem_toFinset.1 h),
        fun b hb hlt => List.mem_toFinset.2 (hsup b hb hlt)⟩
    refine ih.trans (StellarEquivIn.starAt ?_ hne.map ?_)
    · rw [mem_iterStar K L hL, toLeft_map_inl, toRight_map_inl]
      refine ⟨by simp, by simp, by simpa using hAK, fun c₀ hc₀ c hc hsub => ?_⟩
      have : c₀ = ∅ := by simpa using hc₀
      rw [this] at hsub ⊢
      exact absurd (by simpa using hsub) (hstep.not_sub hc)
    · intro hv
      rw [mem_verts, mem_iterStar K L hL] at hv
      have := hv.2.1 (mem_toRight.2 (by simp : Sum.inr A ∈ ({Sum.inr A} : Finset (V ⊕ Finset V))))
      exact hAL (List.mem_toFinset.1 this)

/-- **The derived subdivision is a stellar subdivision.** Starring the faces of `K` in an
admissible order turns it into the order complex of its nonempty faces, with the face `A` of `K`
becoming the new vertex `inr A`. -/
theorem stellarEquivIn_sd (K : SComplex V) (h0 : ∅ ∈ K) :
    StellarEquivIn (K.map (Function.Embedding.inl : V ↪ V ⊕ Finset V))
      ((sd K).map (Function.Embedding.inr : Finset V ↪ V ⊕ Finset V)) := by
  obtain ⟨L, hL, hLP⟩ := exists_adm K _ (K.faces.erase ∅) rfl
    (fun c hc => ⟨mem_faces.1 (mem_of_mem_erase hc),
      nonempty_iff_ne_empty.2 (ne_of_mem_erase hc)⟩)
    (fun c hc b hb hcb => mem_erase.2 ⟨(nonempty_iff_ne_empty.1
      ((nonempty_iff_ne_empty.2 (ne_of_mem_erase hc)).mono hcb.subset)), hb⟩)
  have hEq : iterStar K L = (sd K).map (Function.Embedding.inr : Finset V ↪ V ⊕ Finset V) := by
    refine ext_mem fun s => ?_
    rw [mem_iterStar K L hL, hLP, mem_map]
    constructor
    · rintro ⟨hch, hCP, hUK, hcond⟩
      have hU : s.toLeft = ∅ := by
        by_contra hne
        have hUK' : s.toLeft ∈ K := K.down_mem hUK subset_union_left
        have := hcond ∅ (mem_insert_self _ _) s.toLeft
          (mem_erase.2 ⟨hne, mem_faces.2 hUK'⟩) (by simp)
        exact hne (subset_empty.1 this)
      refine ⟨s.toRight, ?_, ?_⟩
      · exact mem_orderComplex.2 ⟨hCP, hch⟩
      · ext x
        rcases x with x | x
        · have : x ∉ s.toLeft := by rw [hU]; simp
          simpa using this
        · simp
    · rintro ⟨C, hC, rfl⟩
      obtain ⟨hCP, hch⟩ := mem_orderComplex.1 hC
      have hCK : C ⊆ K.faces := fun c hc => mem_of_mem_erase (hCP hc)
      have hl : (C.map (Function.Embedding.inr : Finset V ↪ V ⊕ Finset V)).toLeft = ∅ := by
        ext x; simp
      have hr : (C.map (Function.Embedding.inr : Finset V ↪ V ⊕ Finset V)).toRight = C := by
        ext x; simp
      rw [hl, hr]
      exact ⟨hch, hCP, by simpa using chain_sup_mem h0 hCK hch, fun c₀ hc₀ c hc hsub => by
        simpa using hsub⟩
  rw [← hEq]
  exact stellarEquivIn_iterStar K L hL

/-- The order complex of the image of a set under an order embedding is the image of its order
complex. -/
lemma orderComplex_map {P Q : Type*} [PartialOrder P] [DecidableEq P] [PartialOrder Q]
    [DecidableEq Q] (f : P ↪ Q) (hf : ∀ a b, f a ≤ f b ↔ a ≤ b) (S : Finset P) :
    orderComplex (S.map f) = (orderComplex S).map f := by
  refine ext_mem fun C => ?_
  rw [mem_orderComplex, mem_map]
  constructor
  · rintro ⟨hC, hch⟩
    obtain ⟨u, hu, rfl⟩ := Finset.subset_map_iff.1 hC
    refine ⟨u, mem_orderComplex.2 ⟨hu, fun a ha b hb => ?_⟩, rfl⟩
    have := hch (f a) (mem_map_of_mem f ha) (f b) (mem_map_of_mem f hb)
    simpa only [hf] using this
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨hu1, hu2⟩ := mem_orderComplex.1 hu
    refine ⟨map_subset_map.2 hu1, fun a ha b hb => ?_⟩
    obtain ⟨a', ha', rfl⟩ := Finset.mem_map.1 ha
    obtain ⟨b', hb', rfl⟩ := Finset.mem_map.1 hb
    simpa only [hf] using hu2 a' ha' b' hb'

/-! ## Trust checks -/

/-- Non-vacuity: in the derived subdivision of an edge, a vertex and the edge containing it form a
face (a chain). -/
example : ({{0}, {0, 1}} : Finset (Finset ℕ)) ∈ sd (simplex ({0, 1} : Finset ℕ)) := by
  rw [sd, mem_orderComplex]
  refine ⟨?_, ?_⟩
  · intro c hc
    simp only [mem_insert, mem_singleton] at hc
    rcases hc with rfl | rfl <;> simp [mem_erase, simplex]
  · intro a ha b hb
    simp only [mem_insert, mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

/-- Wrong-model check: the two endpoints of an edge are not comparable, so they do not form a face
of the derived subdivision (the original edge is replaced). -/
example : ({{0}, {1}} : Finset (Finset ℕ)) ∉ sd (simplex ({0, 1} : Finset ℕ)) := by
  rw [sd, mem_orderComplex]
  rintro ⟨-, h⟩
  have := h {0} (by simp) {1} (by simp)
  revert this; decide

end SComplex
end Lightlike.PL
