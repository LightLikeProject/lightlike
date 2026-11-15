import Lightlike.SpinFoam.Move24

/-!
# The 2-4 move of the Ooguri model: the state sum

The local identities of `Move24` give the invariance of the gauge-fixed Ooguri state sum under
the 2-4 Pachner move. The move has `#σ = 4` (the tetrahedron `A`, shared by the two
four-simplices before the move) and `#τ = 2` (the edge `B`, shared by the four four-simplices
after it).

Before the move the only coloured face that contains `σ` is `σ` itself. After the move the
coloured faces that contain `τ` are the four triangles `τ ∪ {a}` and the six tetrahedra
`τ ∪ {a, a'}`, `a, a' ∈ σ`. The triangle `τ ∪ {a₀}` for the smallest `a₀ ∈ σ` carries the gauge
colour `0`.
-/

open Finset Lightlike.Recoupling Lightlike.FourD Complex4

namespace Lightlike.SpinFoam

variable {V : Type*} [LinearOrder V] {K : Complex4 V} {σ τ : Finset V}

/-! ## Coloured faces around the shared simplex -/

/-- The coloured faces are the faces of `K` with three or four vertices. -/
lemma mem_colFaces_iff {f : Finset V} :
    f ∈ colFaces K ↔ f ∈ K.allFaces ∧ (#f = 3 ∨ #f = 4) := by
  simp only [colFaces, mem_union, mem_faces_iff]
  constructor
  · rintro (⟨h, h3⟩ | ⟨h, h4⟩)
    · exact ⟨h, Or.inl h3⟩
    · exact ⟨h, Or.inr h4⟩
  · rintro ⟨h, h3 | h4⟩
    · exact Or.inl ⟨h, h3⟩
    · exact Or.inr ⟨h, h4⟩

/-- **The coloured faces containing `σ`** are the sets `σ ∪ τ'` with `τ'` a proper subset of `τ`
that have three or four vertices. -/
lemma mem_colFaces_of_subset_gen (h : IsMove K σ τ) {f : Finset V} :
    (f ∈ colFaces K ∧ σ ⊆ f) ↔
      ∃ τ' ⊆ τ, τ' ≠ τ ∧ (#(σ ∪ τ') = 3 ∨ #(σ ∪ τ') = 4) ∧ f = σ ∪ τ' := by
  have key : f ∈ K.allFaces ∧ σ ⊆ f ↔ ∃ τ' ⊆ τ, τ' ≠ τ ∧ σ ∪ τ' = f := by
    have := congrArg (f ∈ ·) h.filter_allFaces_eq_image
    simp only [mem_filter, mem_image, mem_erase, mem_powerset, eq_iff_iff] at this
    rw [this]
    constructor
    · rintro ⟨τ', ⟨hne, hsub⟩, rfl⟩
      exact ⟨τ', hsub, hne, rfl⟩
    · rintro ⟨τ', hsub, hne, rfl⟩
      exact ⟨τ', ⟨hne, hsub⟩, rfl⟩
  rw [mem_colFaces_iff]
  constructor
  · rintro ⟨⟨hf, hc⟩, hσf⟩
    obtain ⟨τ', hsub, hne, rfl⟩ := key.mp ⟨hf, hσf⟩
    exact ⟨τ', hsub, hne, hc, rfl⟩
  · rintro ⟨τ', hsub, hne, hc, rfl⟩
    exact ⟨⟨(key.mpr ⟨τ', hsub, hne, rfl⟩).1, hc⟩, subset_union_left⟩

/-- **The weight around a shared simplex `σ`**: the weight of `K` is the weight away from `σ`, the
dimension factors of the triangles containing `σ`, and the vertex amplitudes around it. -/
lemma weight_eq_outerW_gen (h : IsMove K σ τ) (g : Finset V → ℕ) :
    weight K g = outerW K σ g * ((∏ f ∈ K.tris.filter (σ ⊆ ·), ((g f : ℝ) + 1)) *
      ∏ v ∈ τ, simpW g ((σ ∪ τ).erase v)) := by
  rw [weight, outerW, ← prod_filter_mul_prod_filter_not K.tris (σ ⊆ ·),
    ← prod_filter_mul_prod_filter_not K.simps (σ ⊆ ·), h.filter_simps,
    prod_image fun x hx y hy hxy =>
      erase_injOn_union (mem_union_right σ hx) (mem_union_right σ hy) hxy]
  ring


/-- The triangles of `σ ∪ τ` that lie neither in `σ` nor around `τ`: the outer triangles of the
2-4 move. -/
def outerTri (σ τ : Finset V) : Finset (Finset V) :=
  ((σ ∪ τ).powersetCard 3).filter fun f => ¬ f ⊆ σ ∧ ¬ τ ⊆ f

namespace Move24

open Move33 MoveBlocks

/-- The pairs of positions of `A` whose tetrahedra `B ∪ {a_i, a_j}` are `teT c 0..5`. -/
def prT : Fin 6 → Fin 4 × Fin 4 := ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

/-! ### Bitmask facts, checked by the kernel -/

set_option maxRecDepth 100000 in
lemma card_bits_bmT : ∀ c, #(bits (bmT c)) = 2 := by decide +kernel

set_option maxRecDepth 100000 in
lemma card_bits_sgT : ∀ c, #(bits (sgT c)) = 4 := by decide +kernel

set_option maxRecDepth 100000 in
lemma bits_sgT : ∀ c, bits (sgT c) = univ \ bits (bmT c) := by decide +kernel

set_option maxRecDepth 100000 in
lemma bits_sgT_image : ∀ c, bits (sgT c) = univ.image (aposT c) := by decide +kernel

set_option maxRecDepth 100000 in
lemma aposT_strictMono : ∀ c, StrictMono (aposT c) := by decide +kernel

set_option maxRecDepth 100000 in
lemma bits_bmT_image : ∀ c, bits (bmT c) = univ.image (bposT c) := by decide +kernel

set_option maxRecDepth 100000 in
lemma bits_trT : ∀ c k, bits (trT c k) = insert (aposT c k) (bits (bmT c)) := by decide +kernel

set_option maxRecDepth 100000 in
lemma bits_teT : ∀ c j, bits (teT c j) =
    insert (aposT c (prT j).1) (insert (aposT c (prT j).2) (bits (bmT c))) := by decide +kernel

set_option maxRecDepth 100000 in
lemma exists_case : ∀ P : Finset (Fin 6), #P = 2 → ∃ c, bits (bmT c) = P := by decide +kernel

set_option maxRecDepth 100000 in
lemma exists_pair : ∀ i j : Fin 4, i ≠ j → ∃ q, prT q = (i, j) ∨ prT q = (j, i) := by decide +kernel

lemma aposT_injective (c : Fin 15) : Function.Injective (aposT c) := (aposT_strictMono c).injective

/-! ### Transfer to colourings of `V` -/

variable (φ : Fin 6 ↪o V)

lemma card_bF_bmT (c : Fin 15) : #(bF φ (bmT c)) = 2 := by
  rw [bF, card_map, card_bits_bmT]

lemma card_bF_sgT (c : Fin 15) : #(bF φ (sgT c)) = 4 := by
  rw [bF, card_map, card_bits_sgT]

lemma bF_sgT_union (c : Fin 15) :
    bF φ (sgT c) ∪ bF φ (bmT c) = univ.map φ.toEmbedding := by
  rw [bF, bF, ← map_union, bits_sgT, sdiff_union_of_subset (subset_univ _)]

lemma bF_disjoint (c : Fin 15) : Disjoint (bF φ (sgT c)) (bF φ (bmT c)) := by
  rw [bF, bF, disjoint_map, bits_sgT]
  exact sdiff_disjoint

lemma bF_trT (c : Fin 15) (k : Fin 4) :
    bF φ (trT c k) = insert (φ (aposT c k)) (bF φ (bmT c)) := by
  rw [bF, bits_trT, map_insert]
  rfl

lemma bF_teT (c : Fin 15) (j : Fin 6) : bF φ (teT c j) =
    insert (φ (aposT c (prT j).1)) (insert (φ (aposT c (prT j).2)) (bF φ (bmT c))) := by
  rw [bF, bits_teT, map_insert, map_insert]
  rfl

lemma bF_sgT_eq_image (c : Fin 15) : bF φ (sgT c) = univ.image fun k => φ (aposT c k) := by
  rw [bF, bits_sgT_image, map_eq_image, image_image]
  rfl

lemma bF_bmT_eq_image (c : Fin 15) : bF φ (bmT c) = univ.image fun k => φ (bposT c k) := by
  rw [bF, bits_bmT_image, map_eq_image, image_image]
  rfl

/-- The two vertex amplitudes of the two-simplex side of case `c` are the evaluation of `UB c`. -/
lemma prod_simpW_eq_B (c : Fin 15) (g : Finset V → ℕ) :
    ∏ k : Fin 2, simpW g ((univ.map φ.toEmbedding).erase (φ (bposT c k))) =
      (UB c).ev (bcol φ g) := by
  rw [UB, SNet.ev_union _ _ (fun _ => ⟨rfl, rfl⟩)]
  refine prod_congr rfl fun k _ => ?_
  rw [simpW, dite_eq_left (card_erase_univ_map φ _), vertexAmp_erase_eq]

set_option maxRecDepth 100000 in
lemma image_faT : ∀ c : Fin 15, (bits (sgT c)).powersetCard 3 =
    univ.image fun i => bits (faT c i) := by decide +kernel

set_option maxRecDepth 100000 in
lemma faT_injective : ∀ c : Fin 15, Function.Injective (faT c) := by decide +kernel

/-- The four triangles of the tetrahedron `A`. -/
lemma sum_faT (c : Fin 15) (h : Finset V → ℕ) :
    ∑ i, h (bF φ (faT c i)) = ∑ f ∈ (bF φ (sgT c)).powersetCard 3, h f := by
  have e : (bF φ (sgT c)).powersetCard 3 =
      (univ.image fun i => bits (faT c i)).map (mapEmbedding φ.toEmbedding).toEmbedding := by
    rw [← image_faT, bF, ← powersetCard_map]
  rw [e, sum_map, sum_image fun i _ j _ hij => faT_injective c (bits_injective hij)]
  rfl

set_option maxRecDepth 100000 in
lemma bposT_injective : ∀ c : Fin 15, Function.Injective (bposT c) := by decide +kernel

/-- **The old side of the 2-4 move**: for the tetrahedron `σ` and the edge `τ` given by case `c`
and the positions `φ`, the state sum is the sum over the outer colourings of the outer weight
times `(QB c).ev`. -/
theorem amplitudeGF_eq_sum (K : Complex4 V) (h : IsMove K σ τ) (c : Fin 15)
    (hσ : σ = bF φ (sgT c)) (hτ : τ = bF φ (bmT c)) (T : Finset (Finset V))
    (hT : ∀ f ∈ T, ¬ σ ⊆ f) (cut : Finset V → ℕ)
    (hA : ∑ f ∈ σ.powersetCard 3, cut f ≤ cut σ) :
    amplitudeGF K T cut =
      ∑ σ' ∈ ((colFaces K).filter (¬ σ ⊆ ·) \ T).pi (fun f => range (cut f + 1)),
        outerW K σ (Lightlike.PR.extS _ σ') * (QB c).ev (bcol φ (Lightlike.PR.extS _ σ')) := by
  have hσ4 : #σ = 4 := by rw [hσ, card_bF_sgT]
  have hW : σ ∪ τ = univ.map φ.toEmbedding := by rw [hσ, hτ, bF_sgT_union]
  have hτ' : τ = univ.image fun k => φ (bposT c k) := by rw [hτ, bF_bmT_eq_image]
  set O := (colFaces K).filter (¬ σ ⊆ ·) \ T with hO
  have hσK : σ ∈ colFaces K := by
    have := (mem_colFaces_of_subset_gen h (f := σ)).mpr ⟨∅, empty_subset _,
      fun he => by have := h.nonempty_right; rw [← he] at this; simp at this,
      Or.inr (by simpa using hσ4), by simp⟩
    exact this.1
  have hnO : σ ∉ O := fun hm => (mem_filter.mp (mem_sdiff.mp hm).1).2 (subset_refl σ)
  have hS : colFaces K \ T = insert σ O := by
    ext f
    simp only [mem_insert, mem_sdiff, hO, mem_filter]
    constructor
    · rintro ⟨hfK, hfT⟩
      by_cases hf : σ ⊆ f
      · left
        have h34 := (mem_colFaces_iff.mp hfK).2
        exact (eq_of_subset_of_card_le hf (by omega)).symm
      · exact Or.inr ⟨⟨hfK, hf⟩, hfT⟩
    · rintro (rfl | ⟨⟨hfK, -⟩, hfT⟩)
      · exact ⟨hσK, fun hT' => hT _ hT' (subset_refl _)⟩
      · exact ⟨hfK, hfT⟩
  rw [amplitudeGF, hS, Lightlike.PR.sum_pi_insert hnO]
  refine sum_congr rfl fun σ' hσ' => ?_
  set g := Lightlike.PR.extS O σ'
  have hg : ∀ f, g f ≤ cut f := Lightlike.PR.extS_le hσ'
  have hnt : K.tris.filter (σ ⊆ ·) = ∅ := by
    refine filter_eq_empty_iff.mpr fun f hf hsub => ?_
    have := card_le_card hsub
    have h3 := card_of_mem_faces hf
    omega
  have hw : ∀ x, weight K (Function.update g σ x) =
      outerW K σ g * (UB c).ev (Function.update (bcol φ g) (sgT c) x) := by
    intro x
    have hu : Function.update g σ x = Function.update g (bF φ (sgT c)) x := by rw [← hσ]
    rw [weight_eq_outerW_gen h, hnt, prod_empty, one_mul, hW, hτ', prod_image fun i _ j _ hij =>
      bposT_injective c (φ.injective hij)]
    congr 1
    · apply outerW_congr
      intro f hf
      exact Function.update_of_ne (fun he => hf (by rw [he])) _ _
    · rw [← bcol_update, ← hu, ← prod_simpW_eq_B φ c]
  simp only [hw, ← mul_sum]
  congr 1
  have hs := sum_faT φ c g
  rw [← hσ] at hs
  have hcond : bcol φ g (faT c 0) + bcol φ g (faT c 1) + bcol φ g (faT c 2) +
      bcol φ g (faT c 3) ≤ cut σ := by
    have h1 : ∑ i, g (bF φ (faT c i)) ≤ cut σ :=
      hs ▸ (sum_le_sum fun f _ => hg f).trans hA
    rw [Fin.sum_univ_four] at h1
    exact h1
  exact sumB_eq_ev_QB c (bcol φ g) (cut σ) hcond

set_option maxRecDepth 100000 in
lemma prT_ne : ∀ m : Fin 6, (prT m).1 ≠ (prT m).2 := by decide +kernel

set_option maxRecDepth 100000 in
lemma exists_prT : ∀ i j : Fin 4, i ≠ j → ∃ m, prT m = (i, j) ∨ prT m = (j, i) := by decide +kernel

lemma mem_bF_sgT (c : Fin 15) {x : V} : x ∈ bF φ (sgT c) ↔ ∃ k, x = φ (aposT c k) := by
  rw [bF_sgT_eq_image, mem_image]
  simp [eq_comm]

/-- **The coloured faces of the new complex containing the edge `τ`**: the four inner triangles
`τ ∪ {a_k}` and the six inner tetrahedra `τ ∪ {a_i, a_j}`. -/
lemma mem_colFaces_new (h : IsMove K σ τ) (c : Fin 15) (hσ : σ = bF φ (sgT c))
    (hτ : τ = bF φ (bmT c)) {f : Finset V} :
    (f ∈ colFaces (move K h) ∧ τ ⊆ f) ↔
      (∃ k, f = bF φ (trT c k)) ∨ (∃ j, f = bF φ (teT c j)) := by
  have hdisj := bF_disjoint φ c
  have hτ2 := card_bF_bmT φ c
  rw [← hσ, ← hτ] at hdisj
  rw [← hτ] at hτ2
  rw [mem_colFaces_of_subset_gen h.symm]
  constructor
  · rintro ⟨τ', hsub, hne, hc, rfl⟩
    have hdj : Disjoint τ τ' := hdisj.symm.mono_right hsub
    rw [card_union_of_disjoint hdj] at hc
    have h12 : #τ' = 1 ∨ #τ' = 2 := by omega
    rcases h12 with h1 | h2
    · obtain ⟨x, rfl⟩ := card_eq_one.mp h1
      obtain ⟨k, hk⟩ := (mem_bF_sgT φ c).mp (hσ ▸ hsub (mem_singleton_self x))
      left
      refine ⟨k, ?_⟩
      rw [bF_trT, ← hτ, hk, insert_eq, union_comm]
    · obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp h2
      obtain ⟨i, hi⟩ := (mem_bF_sgT φ c).mp (hσ ▸ hsub (mem_insert_self x {y}))
      obtain ⟨j, hj⟩ := (mem_bF_sgT φ c).mp (hσ ▸ hsub (mem_insert_of_mem (mem_singleton_self y)))
      have hij : i ≠ j := fun e => hxy (by rw [hi, hj, e])
      obtain ⟨m, hm | hm⟩ := exists_prT i j hij
      · right
        refine ⟨m, ?_⟩
        rw [bF_teT, hm, ← hτ]
        ext v
        simp only [← hi, ← hj, mem_union, mem_insert, mem_singleton]
        tauto
      · right
        refine ⟨m, ?_⟩
        rw [bF_teT, hm, ← hτ]
        ext v
        simp only [← hi, ← hj, mem_union, mem_insert, mem_singleton]
        tauto
  · have hmem : ∀ k, φ (aposT c k) ∈ σ := fun k => by
      rw [hσ]; exact (mem_bF_sgT φ c).mpr ⟨k, rfl⟩
    have hcardσ : #σ = 4 := by rw [hσ, card_bF_sgT]
    rintro (⟨k, rfl⟩ | ⟨m, rfl⟩)
    · have hsub : {φ (aposT c k)} ⊆ σ := singleton_subset_iff.mpr (hmem k)
      refine ⟨{φ (aposT c k)}, hsub, fun e => ?_, Or.inl ?_, ?_⟩
      · have := congrArg card e
        rw [card_singleton] at this
        omega
      · rw [card_union_of_disjoint (hdisj.symm.mono_right hsub), card_singleton, hτ2]
      · rw [bF_trT, ← hτ, insert_eq, union_comm]
    · have hne := prT_ne m
      have hsub : {φ (aposT c (prT m).1), φ (aposT c (prT m).2)} ⊆ σ := by
        intro v hv
        rcases mem_insert.mp hv with rfl | hv
        · exact hmem _
        · rw [mem_singleton.mp hv]; exact hmem _
      have hc2 : #({φ (aposT c (prT m).1), φ (aposT c (prT m).2)} : Finset V) = 2 :=
        card_pair fun e => hne (aposT_injective c (φ.injective e))
      refine ⟨{φ (aposT c (prT m).1), φ (aposT c (prT m).2)}, hsub, fun e => ?_, Or.inr ?_, ?_⟩
      · have := congrArg card e
        omega
      · rw [card_union_of_disjoint (hdisj.symm.mono_right hsub), hc2, hτ2]
      · rw [bF_teT, ← hτ]
        ext v
        simp only [mem_union, mem_insert, mem_singleton]
        tauto

set_option maxRecDepth 100000 in
lemma teT_eq_iff : ∀ c i j, teT c i = teT c j ↔ i = j := by decide +kernel

/-- The nine faces that carry a sum, outermost sum first: the triangles `x3`, `x2`, `x1` and the
tetrahedra in the order of the nested sum. -/
def lstT (c : Fin 15) : List (Fin 64) :=
  [trT c 3, teT c 2, trT c 2, teT c 5, trT c 1, teT c 4, teT c 3, teT c 1, teT c 0]

set_option maxRecDepth 100000 in
lemma lstT_nodup : ∀ c, (lstT c).Nodup := by decide +kernel

/-- Nested sums over the colours of the faces of a list, the head outermost. -/
def nest (t : Finset V → Finset ℕ) : List (Finset V) → (Finset V → ℕ) → ((Finset V → ℕ) → ℝ) → ℝ
  | [], g, F => F g
  | a :: l, g, F => ∑ x ∈ t a, nest t l (Function.update g a x) F

lemma nest_nil (t : Finset V → Finset ℕ) (g F) : nest t [] g F = F g := rfl

lemma nest_cons (t : Finset V → Finset ℕ) (a l g F) :
    nest t (a :: l) g F = ∑ x ∈ t a, nest t l (Function.update g a x) F := rfl

/-- Summing over colourings of faces inserted one after the other: the first face of the list is
the outermost sum. -/
lemma sum_pi_foldl (t : Finset V → Finset ℕ) (F : (Finset V → ℕ) → ℝ) :
    ∀ (l : List (Finset V)) (S : Finset (Finset V)), l.Nodup → (∀ a ∈ l, a ∉ S) →
      ∑ σ ∈ (l.foldl (fun s a => insert a s) S).pi t, F (Lightlike.PR.extS _ σ) =
        ∑ σ ∈ S.pi t, nest t l (Lightlike.PR.extS S σ) F
  | [], S, _, _ => rfl
  | a :: l, S, hl, hS => by
    rw [List.foldl_cons]
    have hnd := List.nodup_cons.mp hl
    rw [sum_pi_foldl t F l (insert a S) hnd.2 fun b hb => by
      rw [mem_insert, not_or]
      exact ⟨fun e => hnd.1 (e ▸ hb), hS b (List.mem_cons_of_mem _ hb)⟩,
      Lightlike.PR.sum_pi_insert (hS a (List.mem_cons_self))
        (F := fun g => nest t l g F)]
    rfl

lemma mem_foldl_insert (l : List (Finset V)) (S : Finset (Finset V)) (f : Finset V) :
    f ∈ l.foldl (fun s a => insert a s) S ↔ f ∈ S ∨ f ∈ l := by
  induction l generalizing S with
  | nil => simp
  | cons a l ih => simp only [List.foldl_cons, ih, mem_insert, List.mem_cons]; tauto

set_option maxRecDepth 100000 in
lemma card_bits_trT : ∀ c k, #(bits (trT c k)) = 3 := by decide +kernel

set_option maxRecDepth 100000 in
lemma card_bits_teT : ∀ c j, #(bits (teT c j)) = 4 := by decide +kernel

set_option maxRecDepth 100000 in
lemma lstT_mem : ∀ (c : Fin 15) (n : Fin 64), n ∈ lstT c ↔
    ((∃ k, k ≠ 0 ∧ n = trT c k) ∨ ∃ j, n = teT c j) := by decide +kernel

set_option maxRecDepth 100000 in
lemma lstT_ne_tri0 : ∀ (c : Fin 15) (n : Fin 64), n ∈ lstT c → n ≠ trT c 0 := by decide +kernel

lemma card_bF_trT (c : Fin 15) (k : Fin 4) : #(bF φ (trT c k)) = 3 := by
  rw [bF, card_map, card_bits_trT]

lemma card_bF_teT (c : Fin 15) (j : Fin 6) : #(bF φ (teT c j)) = 4 := by
  rw [bF, card_map, card_bits_teT]

/-- The triangles of the new complex containing the edge `τ` are the four inner triangles. -/
lemma tris_filter_new (h : IsMove K σ τ) (c : Fin 15) (hσ : σ = bF φ (sgT c))
    (hτ : τ = bF φ (bmT c)) :
    (move K h).tris.filter (τ ⊆ ·) = univ.image fun k => bF φ (trT c k) := by
  ext f
  rw [mem_filter, mem_image]
  constructor
  · rintro ⟨hf, hτf⟩
    have hc : f ∈ colFaces (move K h) := mem_union_left _ hf
    rcases (mem_colFaces_new φ h c hσ hτ).mp ⟨hc, hτf⟩ with ⟨k, hk⟩ | ⟨j, hj⟩
    · exact ⟨k, mem_univ _, hk.symm⟩
    · have := card_of_mem_faces hf
      rw [hj, card_bF_teT] at this
      omega
  · rintro ⟨k, -, rfl⟩
    obtain ⟨hc, hτf⟩ := (mem_colFaces_new φ h c hσ hτ).mpr (Or.inl ⟨k, rfl⟩)
    refine ⟨?_, hτf⟩
    rcases mem_union.mp hc with ht | ht
    · exact ht
    · have := card_of_mem_faces ht
      rw [card_bF_trT] at this
      omega

/-- The four vertex amplitudes of the four-simplex side of case `c` are the evaluation of `U4 c`. -/
lemma prod_simpW_eq_A (c : Fin 15) (g : Finset V → ℕ) :
    ∏ k : Fin 4, simpW g ((univ.map φ.toEmbedding).erase (φ (aposT c k))) =
      (U4 c).ev (bcol φ g) := by
  rw [U4, SNet.ev_union _ _ (fun _ => ⟨rfl, rfl⟩)]
  refine prod_congr rfl fun k _ => ?_
  rw [simpW, dite_eq_left (card_erase_univ_map φ _), vertexAmp_erase_eq]

/-- Nested sums depend only on the function on colourings that agree with `g` off the faces of the
list. -/
lemma nest_congr (t : Finset V → Finset ℕ) (F F' : (Finset V → ℕ) → ℝ) :
    ∀ (l : List (Finset V)) (g : Finset V → ℕ),
      (∀ u, (∀ f, f ∉ l → u f = g f) → F u = F' u) → nest t l g F = nest t l g F'
  | [], g, h => h g fun _ _ => rfl
  | a :: l, g, h => by
    refine sum_congr rfl fun x _ => nest_congr t F F' l _ fun u hu => h u fun f hf => ?_
    have hfa : f ≠ a := fun e => hf (e ▸ List.mem_cons_self)
    rw [hu f fun hl => hf (List.mem_cons_of_mem _ hl), Function.update_of_ne hfa]

/-- **The new side of the 2-4 move**: for the tetrahedron `σ` and the edge `τ` given by case `c`
and the positions `φ`, the gauge-fixed state sum of the new complex, with the inner triangle
`τ ∪ {a_0}` fixed to colour `0`, is the same sum over outer colourings as for the old side. -/
theorem amplitudeGF_eq_sum_new (K : Complex4 V) (h : IsMove K σ τ) (c : Fin 15)
    (hσ : σ = bF φ (sgT c)) (hτ : τ = bF φ (bmT c)) (T : Finset (Finset V))
    (hT : ∀ f ∈ T, ¬ τ ⊆ f) (cut : Finset V → ℕ) (Ω : ℕ)
    (hΩ : ∀ j, cut (bF φ (ouT c j 0)) + cut (bF φ (ouT c j 1)) ≤ Ω)
    (hc3 : Ω ≤ cut (bF φ (trT c 3)))
    (hc2 : cut (bF φ (trT c 3)) + Ω ≤ cut (bF φ (trT c 2)))
    (hc1 : cut (bF φ (trT c 3)) + Ω ≤ cut (bF φ (trT c 1)))
    (hte : ∀ j, cut (bF φ (trT c 1)) + cut (bF φ (trT c 2)) + cut (bF φ (trT c 3)) + Ω ≤
      cut (bF φ (teT c j))) :
    amplitudeGF (move K h) (insert (bF φ (trT c 0)) T) cut =
      ∑ σ' ∈ ((colFaces K).filter (¬ σ ⊆ ·) \ T).pi (fun f => range (cut f + 1)),
        outerW K σ (Lightlike.PR.extS _ σ') * (QB c).ev (bcol φ (Lightlike.PR.extS _ σ')) := by
  have hsub : ∀ f ∈ (lstT c).map (bF φ), τ ⊆ f := fun f hf => by
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hf
    rcases (lstT_mem c n).mp hn with ⟨k, -, rfl⟩ | ⟨j, rfl⟩
    · exact ((mem_colFaces_new φ h c hσ hτ).mpr (Or.inl ⟨k, rfl⟩)).2
    · exact ((mem_colFaces_new φ h c hσ hτ).mpr (Or.inr ⟨j, rfl⟩)).2
  have hsub0 : τ ⊆ bF φ (trT c 0) :=
    ((mem_colFaces_new φ h c hσ hτ).mpr (Or.inl ⟨0, rfl⟩)).2
  set O := (colFaces K).filter (¬ σ ⊆ ·) \ T with hO
  have hOmem : ∀ f, f ∈ O ↔ (f ∈ colFaces (move K h) ∧ ¬ τ ⊆ f) ∧ f ∉ T := fun f => by
    have := congrArg (f ∈ ·) (colFaces_filter_move h)
    simp only [mem_filter, eq_iff_iff] at this
    rw [hO, mem_sdiff, mem_filter, ← this]
  have hS : colFaces (move K h) \ insert (bF φ (trT c 0)) T =
      ((lstT c).map (bF φ)).foldl (fun s a => insert a s) O := by
    ext f
    rw [mem_foldl_insert, mem_sdiff, mem_insert, hOmem, List.mem_map]
    constructor
    · rintro ⟨hfK, hf⟩
      rw [not_or] at hf
      by_cases hτf : τ ⊆ f
      · right
        rcases (mem_colFaces_new φ h c hσ hτ).mp ⟨hfK, hτf⟩ with ⟨k, rfl⟩ | ⟨j, rfl⟩
        · refine ⟨trT c k, (lstT_mem c _).mpr (Or.inl ⟨k, fun e => hf.1 (by rw [e]), rfl⟩), rfl⟩
        · exact ⟨teT c j, (lstT_mem c _).mpr (Or.inr ⟨j, rfl⟩), rfl⟩
      · exact Or.inl ⟨⟨hfK, hτf⟩, hf.2⟩
    · rintro (⟨⟨hfK, hτf⟩, hfT⟩ | ⟨n, hn, rfl⟩)
      · refine ⟨hfK, ?_⟩
        rw [not_or]
        exact ⟨fun e => hτf (e ▸ hsub0), hfT⟩
      · rcases (lstT_mem c n).mp hn with ⟨k, -, rfl⟩ | ⟨j, rfl⟩
        · refine ⟨((mem_colFaces_new φ h c hσ hτ).mpr (Or.inl ⟨k, rfl⟩)).1, ?_⟩
          rw [not_or]
          exact ⟨fun e => lstT_ne_tri0 c _ hn (bF_injective φ e), fun hT' => hT _ hT' (hsub _
            (List.mem_map.mpr ⟨_, hn, rfl⟩))⟩
        · refine ⟨((mem_colFaces_new φ h c hσ hτ).mpr (Or.inr ⟨j, rfl⟩)).1, ?_⟩
          rw [not_or]
          exact ⟨fun e => lstT_ne_tri0 c _ hn (bF_injective φ e), fun hT' => hT _ hT' (hsub _
            (List.mem_map.mpr ⟨_, hn, rfl⟩))⟩
  have hnO : ∀ f ∈ (lstT c).map (bF φ), f ∉ O := fun f hf hfO =>
    ((hOmem f).mp hfO).1.2 (hsub f hf)
  rw [amplitudeGF, hS, sum_pi_foldl _ _ _ O ((lstT_nodup c).map (bF_injective φ)) hnO]
  refine sum_congr rfl fun σ' hσ' => ?_
  set g := Lightlike.PR.extS O σ' with hgdef
  have hg : ∀ f, g f ≤ cut f := Lightlike.PR.extS_le hσ'
  have h0 : g (bF φ (trT c 0)) = 0 :=
    Lightlike.PR.extS_of_not_mem fun hm => ((hOmem _).mp hm).1.2 hsub0
  have hn0 : bF φ (trT c 0) ∉ (lstT c).map (bF φ) := fun hm => by
    obtain ⟨n, hn, e⟩ := List.mem_map.mp hm
    exact lstT_ne_tri0 c n hn (bF_injective φ e)
  have hσ' : σ = univ.image fun k => φ (aposT c k) := by rw [hσ, bF_sgT_eq_image]
  have hW' : τ ∪ σ = univ.map φ.toEmbedding := by rw [union_comm, hσ, hτ, bF_sgT_union]
  have key : ∀ u : Finset V → ℕ, (∀ f ∉ (lstT c).map (bF φ), u f = g f) →
      weight (move K h) u = outerW K σ g * (((u (bF φ (trT c 1)) : ℝ) + 1) *
        ((u (bF φ (trT c 2)) : ℝ) + 1) * ((u (bF φ (trT c 3)) : ℝ) + 1) *
        (U4 c).ev (bcol φ u)) := by
    intro u hu
    have hprod : ∏ v ∈ σ, simpW u ((τ ∪ σ).erase v) = (U4 c).ev (bcol φ u) := by
      rw [hW', hσ', prod_image fun i _ j _ hij => aposT_injective c (φ.injective hij),
        prod_simpW_eq_A]
    have hout : outerW (move K h) τ u = outerW K σ g := by
      rw [← outerW_move h g]
      exact outerW_congr _ _ fun f hf => hu f fun hm => hf (hsub f hm)
    have hu0 : u (bF φ (trT c 0)) = 0 := (hu _ hn0).trans h0
    rw [weight_eq_outerW_gen h.symm, hprod, hout, tris_filter_new φ h c hσ hτ,
      prod_image fun i _ j _ hij => (trT_eq_iff c i j).mp (bF_injective φ hij), Fin.prod_univ_four,
      hu0]
    simp only [Nat.cast_zero, zero_add, one_mul]
  have hF : nest (fun f => range (cut f + 1)) ((lstT c).map (bF φ)) g (weight (move K h)) =
      nest (fun f => range (cut f + 1)) ((lstT c).map (bF φ)) g fun u =>
        outerW K σ g * (((u (bF φ (trT c 1)) : ℝ) + 1) * ((u (bF φ (trT c 2)) : ℝ) + 1) *
          ((u (bF φ (trT c 3)) : ℝ) + 1) * (U4 c).ev (bcol φ u)) :=
    nest_congr _ _ _ _ _ fun u hu => key u hu
  rw [hF]
  have ho : ∀ j, bcol φ g (ouT c j 0) + bcol φ g (ouT c j 1) ≤ Ω := fun j =>
    (add_le_add (hg _) (hg _)).trans (hΩ j)
  have h0' : bcol φ g (trT c 0) = 0 := h0
  have hloc := lhs_eq_ev_NL24 c (bcol φ g) (cut (bF φ (trT c 3))) (cut (bF φ (teT c 2)))
    (cut (bF φ (trT c 2))) (cut (bF φ (teT c 5))) (cut (bF φ (trT c 1))) (cut (bF φ (teT c 4)))
    (cut (bF φ (teT c 3))) (cut (bF φ (teT c 1))) (cut (bF φ (teT c 0)))
    (by have := h0'; have := ho 2; omega)
    (by have := h0'; have := ho 2; have := hte 2; omega)
    (by have := h0'; have := ho 5; omega)
    (by have := h0'; have := ho 5; have := hte 5; omega)
    (by have := h0'; have := ho 4; omega)
    (by have := h0'; have := ho 4; have := hte 4; omega)
    (by have := h0'; have := ho 3; have := hte 3; omega)
    (by have := h0'; have := ho 1; have := hte 1; omega)
    (by have := h0'; have := ho 0; have := hte 0; omega)
  rw [ev_NL_eq_QB, h0'] at hloc
  simp only [lstT, List.map_cons, List.map_nil]
  simp (config := {maxSteps := 3000000}) only [nest_cons, nest_nil]
  simp (config := {maxSteps := 3000000, decide := true}) only [bcol_update, Function.update_apply,
    (bF_injective φ).eq_iff, trT_eq_iff, trT_ne_teT, ite_true, ite_false]
  simp only [Nat.cast_zero, zero_add, one_mul] at hloc
  rw [← hloc]
  simp only [mul_sum]
  repeat' refine sum_congr rfl fun _ _ => ?_
  ring

set_option maxRecDepth 100000 in
lemma card_bits_ouT : ∀ c j e, #(bits (ouT c j e)) = 3 := by decide +kernel

set_option maxRecDepth 100000 in
lemma ouT_nsub_sg : ∀ c j e, ¬ bits (ouT c j e) ⊆ bits (sgT c) := by decide +kernel

set_option maxRecDepth 100000 in
lemma ouT_nsub_bm : ∀ c j e, ¬ bits (bmT c) ⊆ bits (ouT c j e) := by decide +kernel

set_option maxRecDepth 100000 in
lemma ouT_ne_pair : ∀ c j, ouT c j 0 ≠ ouT c j 1 := by decide +kernel

/-- The two outer triangles of each inner tetrahedron are outer triangles of the move. -/
lemma pair_le_outer (c : Fin 15) (hσ : σ = bF φ (sgT c)) (hτ : τ = bF φ (bmT c))
    (cut : Finset V → ℕ) (j : Fin 6) :
    cut (bF φ (ouT c j 0)) + cut (bF φ (ouT c j 1)) ≤ ∑ f ∈ outerTri σ τ, cut f := by
  have hW : σ ∪ τ = univ.map φ.toEmbedding := by rw [hσ, hτ, bF_sgT_union]
  have hmem : ∀ e, bF φ (ouT c j e) ∈ outerTri σ τ := fun e => by
    rw [outerTri, mem_filter, mem_powersetCard, hW, hσ, hτ]
    refine ⟨⟨?_, by rw [bF, card_map, card_bits_ouT]⟩, ?_, ?_⟩
    · exact map_subset_map.mpr (subset_univ _)
    · rw [bF, bF, map_subset_map]; exact ouT_nsub_sg c j e
    · rw [bF, bF, map_subset_map]; exact ouT_nsub_bm c j e
  have hne : bF φ (ouT c j 0) ≠ bF φ (ouT c j 1) := fun e =>
    ouT_ne_pair c j (bF_injective φ e)
  calc cut (bF φ (ouT c j 0)) + cut (bF φ (ouT c j 1))
      = ∑ f ∈ {bF φ (ouT c j 0), bF φ (ouT c j 1)}, cut f := (sum_pair hne).symm
    _ ≤ _ := sum_le_sum_of_subset fun f hf => by
        rcases mem_insert.mp hf with rfl | hf
        · exact hmem 0
        · rw [mem_singleton.mp hf]; exact hmem 1

end Move24

open Move24 in
/-- **The Ooguri state sum is invariant under the 2-4 move** (the move replacing the tetrahedron
`σ` in the two 4-simplices `(σ ∪ τ) ∖ {b}`, `b ∈ τ`, by the edge `τ` in the four 4-simplices
`(σ ∪ τ) ∖ {a}`, `a ∈ σ`). Write `a_0 < a_1 < a_2 < a_3` for the vertices of `σ` and `Ω` for the
sum of the cutoffs over the twelve outer triangles. The gauge set of the new complex contains in
addition the inner triangle `τ ∪ {a_0}`. The cutoffs satisfy: on the old tetrahedron `σ` at least
the sum over its four triangles; on `τ ∪ {a_3}` at least `Ω`; on `τ ∪ {a_2}` and `τ ∪ {a_1}` at
least the cutoff on `τ ∪ {a_3}` plus `Ω`; on each inner tetrahedron at least the sum of the cutoffs
on `τ ∪ {a_1}`, `τ ∪ {a_2}`, `τ ∪ {a_3}` plus `Ω`. -/
theorem amplitudeGF_move24 (K : Complex4 V) {σ τ : Finset V} (h : IsMove K σ τ) (hσ : #σ = 4)
    (T : Finset (Finset V)) (hT : ∀ f ∈ T, ¬ σ ⊆ f ∧ ¬ τ ⊆ f) (cut : Finset V → ℕ)
    (hA : ∑ f ∈ σ.powersetCard 3, cut f ≤ cut σ)
    (hc3 : ∑ f ∈ outerTri σ τ, cut f ≤ cut (insert (σ.orderEmbOfFin hσ 3) τ))
    (hc2 : cut (insert (σ.orderEmbOfFin hσ 3) τ) + ∑ f ∈ outerTri σ τ, cut f ≤
      cut (insert (σ.orderEmbOfFin hσ 2) τ))
    (hc1 : cut (insert (σ.orderEmbOfFin hσ 3) τ) + ∑ f ∈ outerTri σ τ, cut f ≤
      cut (insert (σ.orderEmbOfFin hσ 1) τ))
    (hte : ∀ x ∈ σ, ∀ y ∈ σ, x ≠ y →
      cut (insert (σ.orderEmbOfFin hσ 1) τ) + cut (insert (σ.orderEmbOfFin hσ 2) τ) +
        cut (insert (σ.orderEmbOfFin hσ 3) τ) + ∑ f ∈ outerTri σ τ, cut f ≤
        cut (insert x (insert y τ))) :
    amplitudeGF (move K h) (insert (insert (σ.orderEmbOfFin hσ 0) τ) T) cut =
      amplitudeGF K T cut := by
  have h6 : #(σ ∪ τ) = 6 := h.card_union
  set φ := (σ ∪ τ).orderEmbOfFin h6
  have hW : univ.map φ.toEmbedding = σ ∪ τ := by
    ext v
    rw [mem_map]
    constructor
    · rintro ⟨i, -, rfl⟩
      exact (σ ∪ τ).orderEmbOfFin_mem h6 i
    · intro hv
      have : v ∈ Set.range φ := by rw [range_orderEmbOfFin]; exact hv
      obtain ⟨i, rfl⟩ := this
      exact ⟨i, mem_univ _, rfl⟩
  have hτW : τ ⊆ univ.map φ.toEmbedding := hW ▸ subset_union_right
  set P := univ.filter fun i => φ i ∈ τ with hPdef
  have hP : P.map φ.toEmbedding = τ := by
    ext v
    simp only [mem_map, hPdef, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hv
      obtain ⟨i, -, rfl⟩ := mem_map.mp (hτW hv)
      exact ⟨i, hv, rfl⟩
  have hP2 : #P = 2 := by
    rw [← card_map φ.toEmbedding, hP]
    have := h.card
    omega
  obtain ⟨c, hc⟩ := Move24.exists_case P hP2
  have hτ : τ = Move33.bF φ (Move24.bmT c) := by rw [Move33.bF, hc, hP]
  have hσ' : σ = Move33.bF φ (Move24.sgT c) := by
    have : Move33.bF φ (Move24.sgT c) = univ.map φ.toEmbedding \ Move33.bF φ (Move24.bmT c) := by
      rw [Move33.bF, Move24.bits_sgT, Finset.map_sdiff]
      rfl
    rw [this, ← hτ, hW, union_sdiff_cancel_right h.disj]
  -- the sorted vertices of `σ` are `φ (aposT c k)`
  have ha : ∀ k, σ.orderEmbOfFin hσ k = φ (Move24.aposT c k) := fun k => by
    have := orderEmbOfFin_unique (s := σ) hσ (f := fun k => φ (Move24.aposT c k))
      (fun k => by rw [hσ']; exact (Move24.mem_bF_sgT φ c).mpr ⟨k, rfl⟩)
      (φ.strictMono.comp (Move24.aposT_strictMono c))
    exact (congrFun this k).symm
  have htri : ∀ k, insert (σ.orderEmbOfFin hσ k) τ = Move33.bF φ (Move24.trT c k) := fun k => by
    rw [Move24.bF_trT, ha, ← hτ]
  have hteT : ∀ j, Move33.bF φ (Move24.teT c j) = insert (σ.orderEmbOfFin hσ (Move24.prT j).1)
      (insert (σ.orderEmbOfFin hσ (Move24.prT j).2) τ) := fun j => by
    rw [Move24.bF_teT, ha, ha, ← hτ]
  have hmemσ : ∀ k, σ.orderEmbOfFin hσ k ∈ σ := fun k => σ.orderEmbOfFin_mem hσ k
  rw [htri 0, Move24.amplitudeGF_eq_sum_new φ K h c hσ' hτ T (fun f hf => (hT f hf).2) cut
      (∑ f ∈ outerTri σ τ, cut f) (fun j => Move24.pair_le_outer φ c hσ' hτ cut j)
      (by rw [← htri]; exact hc3) (by rw [← htri, ← htri]; exact hc2)
      (by rw [← htri, ← htri]; exact hc1)
      (fun j => by
        rw [← htri, ← htri, ← htri, hteT]
        exact hte _ (hmemσ _) _ (hmemσ _) fun e =>
          Move24.prT_ne j ((σ.orderEmbOfFin hσ).injective e))]
  exact (Move24.amplitudeGF_eq_sum φ K h c hσ' hτ T (fun f hf => (hT f hf).1) cut hA).symm



/-! ### The gauge rule under the 2-4 move -/

/-- **The gauge rule survives the 2-4 move.** The new complex has one more edge `τ` and one more
triangle `τ ∪ {a}` (for any `a ∈ σ`), and `τ` is a free face of `τ ∪ {a}` in the gauge complex, so
one elementary collapse returns the gauge complex of `K`. -/
theorem IsGauge.move24 {K : Complex4 V} {σ τ : Finset V} (h : K.IsMove σ τ) (hσ : #σ = 4)
    {a : V} (ha : a ∈ σ) {T : Finset (Finset V)} (hg : IsGauge K T) :
    IsGauge (K.move h) (insert (insert a τ) T) := by
  have hτ : #τ = 2 := by have := h.card; omega
  have haτ : a ∉ τ := fun hh => disjoint_left.mp h.disj ha hh
  have hfresh : ∀ f, (∃ s ∈ K.simps, f ⊆ s) → ¬ τ ⊆ f := fun f ⟨s, hs, hfs⟩ hτf =>
    h.fresh s hs (hτf.trans hfs)
  have hfreshF : ∀ k f, f ∈ K.faces k → ¬ τ ⊆ f := fun k f hf =>
    hfresh f (by obtain ⟨s, hs, hfs, -⟩ := Complex4.mem_faces.mp hf; exact ⟨s, hs, hfs⟩)
  -- a vertex `u ∈ σ` other than `a`
  obtain ⟨u, hu, hua⟩ : ∃ u ∈ σ, u ≠ a := by
    by_contra hcon
    push Not at hcon
    have : σ ⊆ {a} := fun x hx => mem_singleton.mpr (hcon x hx)
    have := card_le_card this
    simp at this; omega
  have hsim : (σ ∪ τ).erase u ∈ (K.move h).simps :=
    Complex4.mem_move.mpr (Or.inr ⟨u, hu, rfl⟩)
  have hsub : insert a τ ⊆ (σ ∪ τ).erase u := fun x hx => by
    rw [mem_erase]
    rcases mem_insert.mp hx with rfl | hx
    · exact ⟨hua.symm, mem_union_left _ ha⟩
    · exact ⟨fun e => disjoint_left.mp h.disj (e ▸ hu) hx, mem_union_right _ hx⟩
  have htri : insert a τ ∈ (K.move h).faces 2 :=
    Complex4.mem_faces.mpr ⟨_, hsim, hsub, by rw [card_insert_of_notMem haτ, hτ]⟩
  have hedge : τ ∈ (K.move h).faces 1 :=
    Complex4.mem_faces.mpr ⟨_, hsim, (subset_insert _ _).trans hsub, hτ⟩
  have h0 : (K.move h).faces 0 = K.faces 0 := faces_move_of_lt h (by omega) (by omega)
  have h1 : (K.move h).faces 1 = insert τ (K.faces 1) := by
    ext f
    constructor
    · intro hf
      by_cases hτf : τ ⊆ f
      · exact mem_insert.mpr (Or.inl (eq_of_subset_of_card_le hτf
          (by rw [Complex4.card_of_mem_faces hf, hτ])).symm)
      · exact mem_insert_of_mem (mem_faces_of_mem_move h hf hτf)
    · intro hf
      rcases mem_insert.mp hf with rfl | hf
      · exact hedge
      · exact mem_faces_move h hf fun hs => by
          have := card_le_card hs; rw [Complex4.card_of_mem_faces hf] at this; omega
  have hTsub : ∀ f ∈ T, f ∈ K.faces 2 := hg.1
  refine ⟨?_, ?_⟩
  · intro f hf
    rcases mem_insert.mp hf with rfl | hf
    · exact htri
    · exact mem_faces_move h (hTsub f hf) fun hs => by
        have := card_le_card hs; rw [Complex4.card_of_mem_faces (hTsub f hf)] at this; omega
  · have hX : gaugeCx (K.move h) (insert (insert a τ) T) =
        insert (insert a τ) (insert τ (gaugeCx K T)) := by
      unfold gaugeCx
      rw [h0, h1]
      ext f; simp only [mem_union, mem_insert]; tauto
    have hn1 : τ ∉ gaugeCx K T := fun hh => by
      unfold gaugeCx at hh
      simp only [mem_union] at hh
      rcases hh with (hh | hh) | hh
      · exact hfreshF 0 τ hh subset_rfl
      · exact hfreshF 1 τ hh subset_rfl
      · exact hfreshF 2 τ (hTsub τ hh) subset_rfl
    have hn2 : insert a τ ∉ gaugeCx K T := fun hh => by
      unfold gaugeCx at hh
      simp only [mem_union] at hh
      rcases hh with (hh | hh) | hh
      · exact hfreshF 0 _ hh (subset_insert _ _)
      · exact hfreshF 1 _ hh (subset_insert _ _)
      · exact hfreshF 2 _ (hTsub _ hh) (subset_insert _ _)
    rw [hX]
    have hne : insert a τ ≠ τ := fun e => haτ (e ▸ mem_insert_self a τ)
    refine Collapsible.collapse τ (insert a τ) (mem_insert_of_mem (mem_insert_self _ _))
      (mem_insert_self _ _) (subset_insert _ _) (by rw [card_insert_of_notMem haτ]) ?_ ?_
    · intro ρ hρ hτρ
      simp only [mem_insert] at hρ
      rcases hρ with rfl | rfl | hρ
      · exact Or.inr rfl
      · exact Or.inl rfl
      · exfalso
        unfold gaugeCx at hρ
        simp only [mem_union] at hρ
        rcases hρ with (hρ | hρ) | hρ
        · exact hfreshF 0 ρ hρ hτρ
        · exact hfreshF 1 ρ hρ hτρ
        · exact hfreshF 2 ρ (hTsub ρ hρ) hτρ
    · have : ((insert (insert a τ) (insert τ (gaugeCx K T))).erase (insert a τ)).erase τ =
          gaugeCx K T := by
        rw [erase_insert (by simp only [mem_insert, not_or]; exact ⟨hne, hn2⟩), erase_insert hn1]
      rw [this]; exact hg.2

open Move24 in
/-- **The gauge-fixed Ooguri amplitude is invariant under the 2-4 move.** For a gauge set `T` of
`K`, the set `T ∪ {τ ∪ {a_0}}` is a gauge set of the moved complex (`IsGauge.move24`), and the two
gauge-fixed amplitudes agree under the cutoff conditions of `amplitudeGF_move24`. -/
theorem amplitudeGF_move24_gauge (K : Complex4 V) {σ τ : Finset V} (h : IsMove K σ τ)
    (hσ : #σ = 4) (T : Finset (Finset V)) (hg : IsGauge K T) (cut : Finset V → ℕ)
    (hA : ∑ f ∈ σ.powersetCard 3, cut f ≤ cut σ)
    (hc3 : ∑ f ∈ outerTri σ τ, cut f ≤ cut (insert (σ.orderEmbOfFin hσ 3) τ))
    (hc2 : cut (insert (σ.orderEmbOfFin hσ 3) τ) + ∑ f ∈ outerTri σ τ, cut f ≤
      cut (insert (σ.orderEmbOfFin hσ 2) τ))
    (hc1 : cut (insert (σ.orderEmbOfFin hσ 3) τ) + ∑ f ∈ outerTri σ τ, cut f ≤
      cut (insert (σ.orderEmbOfFin hσ 1) τ))
    (hte : ∀ x ∈ σ, ∀ y ∈ σ, x ≠ y →
      cut (insert (σ.orderEmbOfFin hσ 1) τ) + cut (insert (σ.orderEmbOfFin hσ 2) τ) +
        cut (insert (σ.orderEmbOfFin hσ 3) τ) + ∑ f ∈ outerTri σ τ, cut f ≤
        cut (insert x (insert y τ))) :
    IsGauge (move K h) (insert (insert (σ.orderEmbOfFin hσ 0) τ) T) ∧
    amplitudeGF (move K h) (insert (insert (σ.orderEmbOfFin hσ 0) τ) T) cut =
      amplitudeGF K T cut := by
  have hT : ∀ f ∈ T, ¬ σ ⊆ f ∧ ¬ τ ⊆ f := fun f hf => by
    have hc := Complex4.card_of_mem_faces (hg.1 hf)
    obtain ⟨s, hs, hfs, -⟩ := Complex4.mem_faces.mp (hg.1 hf)
    exact ⟨fun hh => by have := card_le_card hh; omega, fun hh => h.fresh s hs (hh.trans hfs)⟩
  exact ⟨IsGauge.move24 h hσ (σ.orderEmbOfFin_mem hσ 0) hg,
    amplitudeGF_move24 K h hσ T hT cut hA hc3 hc2 hc1 hte⟩

open Move24 in
/-- **The gauge-fixed Ooguri amplitude is invariant under the 4-2 move** (the move replacing the
four 4-simplices `(σ ∪ τ) ∖ {a}`, `a ∈ τ`, around the edge `σ` by the two 4-simplices
`(σ ∪ τ) ∖ {b}`, `b ∈ σ`). The gauge set `T` is a gauge set of the complex after the move; the
complex before the move has the additional triangle `σ ∪ {τ_0}`, where `τ_0` is the least vertex
of the tetrahedron `τ`. The cutoff conditions are those of the 2-4 move with the roles of `σ` and
`τ` exchanged. -/
theorem amplitudeGF_move42_gauge (K : Complex4 V) {σ τ : Finset V} (h : IsMove K σ τ)
    (hτ : #τ = 4) (T : Finset (Finset V)) (hg : IsGauge (move K h) T) (cut : Finset V → ℕ)
    (hA : ∑ f ∈ τ.powersetCard 3, cut f ≤ cut τ)
    (hc3 : ∑ f ∈ outerTri τ σ, cut f ≤ cut (insert (τ.orderEmbOfFin hτ 3) σ))
    (hc2 : cut (insert (τ.orderEmbOfFin hτ 3) σ) + ∑ f ∈ outerTri τ σ, cut f ≤
      cut (insert (τ.orderEmbOfFin hτ 2) σ))
    (hc1 : cut (insert (τ.orderEmbOfFin hτ 3) σ) + ∑ f ∈ outerTri τ σ, cut f ≤
      cut (insert (τ.orderEmbOfFin hτ 1) σ))
    (hte : ∀ x ∈ τ, ∀ y ∈ τ, x ≠ y →
      cut (insert (τ.orderEmbOfFin hτ 1) σ) + cut (insert (τ.orderEmbOfFin hτ 2) σ) +
        cut (insert (τ.orderEmbOfFin hτ 3) σ) + ∑ f ∈ outerTri τ σ, cut f ≤
        cut (insert x (insert y σ))) :
    IsGauge K (insert (insert (τ.orderEmbOfFin hτ 0) σ) T) ∧
    amplitudeGF K (insert (insert (τ.orderEmbOfFin hτ 0) σ) T) cut =
      amplitudeGF (move K h) T cut := by
  have := amplitudeGF_move24_gauge (move K h) h.symm hτ T hg cut hA hc3 hc2 hc1 hte
  rwa [move_move] at this

end Lightlike.SpinFoam
