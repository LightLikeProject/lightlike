import Lightlike.SpinFoam.Move15
import Lightlike.SpinFoam.Move24Global

/-!
# The 1-5 move of the Ooguri model: the state sum

The local identities of `Move15` give the invariance of the gauge-fixed Ooguri state sum under
the 1-5 Pachner move. The move has `#σ = 5` (the four-simplex before the move) and `τ = {v}` (the
new vertex). After the move the coloured faces that contain `v` are the ten triangles
`{v, a_i, a_j}` and the ten tetrahedra `{v, a_i, a_j, a_k}`, `a_i ∈ σ`. The four triangles
`{v, a_0, a_j}` carry the gauge colour `0`.
-/

open Finset Lightlike.Recoupling Lightlike.FourD Complex4

namespace Lightlike.SpinFoam

variable {V : Type*} [LinearOrder V] {K : Complex4 V} {σ τ : Finset V}

namespace Move15

open Move33 MoveBlocks

/-- The pairs of positions of `σ` of the ten triangles `{v, a_i, a_j}`, in lexicographic order. -/
def pr5 : Fin 10 → Fin 5 × Fin 5 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]

/-- The triples of positions of `σ` of the ten tetrahedra and outer triangles, in lexicographic
order. -/
def tp5 : Fin 10 → Fin 5 × Fin 5 × Fin 5 :=
  ![(0, 1, 2), (0, 1, 3), (0, 1, 4), (0, 2, 3), (0, 2, 4), (0, 3, 4), (1, 2, 3), (1, 2, 4),
    (1, 3, 4), (2, 3, 4)]

/-! ### Bitmask facts, checked by the kernel -/

set_option maxRecDepth 100000 in
lemma bits_bmT : ∀ c, bits (bmT c) = {c} := by decide +kernel

set_option maxRecDepth 100000 in
lemma aposT_strictMono : ∀ c, StrictMono (aposT c) := by decide +kernel

set_option maxRecDepth 100000 in
lemma aposT_ne : ∀ c k, aposT c k ≠ c := by decide +kernel

set_option maxRecDepth 100000 in
lemma image_aposT : ∀ c, univ.image (aposT c) = univ.erase c := by decide +kernel

set_option maxRecDepth 100000 in
lemma bits_trT : ∀ c p, bits (trT c p) =
    insert c (insert (aposT c (pr5 p).1) {aposT c (pr5 p).2}) := by decide +kernel

set_option maxRecDepth 100000 in
lemma bits_teT : ∀ c q, bits (teT c q) = insert c (insert (aposT c (tp5 q).1)
    (insert (aposT c (tp5 q).2.1) {aposT c (tp5 q).2.2})) := by decide +kernel

set_option maxRecDepth 100000 in
lemma bits_otT : ∀ c q, bits (otT c q) = insert (aposT c (tp5 q).1)
    (insert (aposT c (tp5 q).2.1) {aposT c (tp5 q).2.2}) := by decide +kernel

set_option maxRecDepth 100000 in
lemma card_bits_trT : ∀ c p, #(bits (trT c p)) = 3 := by decide +kernel

set_option maxRecDepth 100000 in
lemma card_bits_teT : ∀ c q, #(bits (teT c q)) = 4 := by decide +kernel

set_option maxRecDepth 100000 in
lemma exists_trT : ∀ (c : Fin 6) (P : Finset (Fin 6)), c ∈ P → #P = 3 →
    ∃ p, bits (trT c p) = P := by decide +kernel

set_option maxRecDepth 100000 in
lemma exists_teT : ∀ (c : Fin 6) (P : Finset (Fin 6)), c ∈ P → #P = 4 →
    ∃ q, bits (teT c q) = P := by decide +kernel

set_option maxRecDepth 100000 in
lemma mem_bits_trT : ∀ c p, c ∈ bits (trT c p) := by decide +kernel

set_option maxRecDepth 100000 in
lemma mem_bits_teT : ∀ c q, c ∈ bits (teT c q) := by decide +kernel

set_option maxRecDepth 100000 in
lemma teT_eq_iff : ∀ c i j, teT c i = teT c j ↔ i = j := by decide +kernel

lemma aposT_injective (c : Fin 6) : Function.Injective (aposT c) := (aposT_strictMono c).injective

/-! ### Transfer to colourings of `V` -/

variable (φ : Fin 6 ↪o V)

lemma bF_bmT (c : Fin 6) : bF φ (bmT c) = {φ c} := by
  rw [bF, bits_bmT, map_singleton]; rfl

lemma bF_trT (c : Fin 6) (p : Fin 10) : bF φ (trT c p) =
    insert (φ c) (insert (φ (aposT c (pr5 p).1)) {φ (aposT c (pr5 p).2)}) := by
  rw [bF, bits_trT, map_insert, map_insert, map_singleton]; rfl

lemma bF_teT (c : Fin 6) (q : Fin 10) : bF φ (teT c q) =
    insert (φ c) (insert (φ (aposT c (tp5 q).1)) (insert (φ (aposT c (tp5 q).2.1))
      {φ (aposT c (tp5 q).2.2)})) := by
  rw [bF, bits_teT, map_insert, map_insert, map_insert, map_singleton]; rfl

lemma card_bF_trT (c : Fin 6) (p : Fin 10) : #(bF φ (trT c p)) = 3 := by
  rw [bF, card_map, card_bits_trT]

lemma card_bF_teT (c : Fin 6) (q : Fin 10) : #(bF φ (teT c q)) = 4 := by
  rw [bF, card_map, card_bits_teT]

/-- A subset of `φ(Fin 6)` is the image of a set of positions. -/
lemma exists_map_of_subset {f : Finset V} (hf : f ⊆ univ.map φ.toEmbedding) :
    f = (univ.filter fun i => φ i ∈ f).map φ.toEmbedding := by
  ext x
  simp only [mem_map, mem_filter, mem_univ, true_and]
  constructor
  · intro hx
    obtain ⟨i, -, rfl⟩ := mem_map.mp (hf hx)
    exact ⟨i, hx, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact hi

/-- **The coloured faces of the new complex containing the new vertex**, in terms of the vertex
`v` alone. -/
lemma mem_colFaces_new15 (h : IsMove K σ τ) {v : V} (hτ : τ = {v}) {f : Finset V} :
    (f ∈ colFaces (move K h) ∧ τ ⊆ f) ↔ v ∈ f ∧ f ⊆ σ ∪ τ ∧ (#f = 3 ∨ #f = 4) := by
  have hcard := h.card
  have hdisj := h.disj
  rw [mem_colFaces_of_subset_gen h.symm]
  subst hτ
  have h5 : #σ = 5 := by rw [card_singleton] at hcard; omega
  have hvσ : v ∉ σ := fun hv => disjoint_left.mp hdisj hv (mem_singleton_self v)
  constructor
  · rintro ⟨τ', hsub, hne, hc, rfl⟩
    refine ⟨by simp, ?_, hc⟩
    intro x hx
    simp only [mem_union, mem_singleton] at hx ⊢
    rcases hx with hx | hx
    · exact Or.inr hx
    · exact Or.inl (hsub hx)
  · rintro ⟨hv, hfs, hc⟩
    have he : {v} ∪ f.erase v = f := (insert_eq v _).symm.trans (insert_erase hv)
    have hce : #(f.erase v) + 1 = #f := card_erase_add_one hv
    refine ⟨f.erase v, ?_, fun e => by rw [e] at hce; omega, by rw [he]; exact hc, he.symm⟩
    intro x hx
    obtain ⟨hxv, hxf⟩ := mem_erase.mp hx
    have := hfs hxf
    simp only [mem_union, mem_singleton] at this
    exact this.resolve_right hxv

/-- **The coloured faces of the new complex containing the new vertex** are the ten inner
triangles and the ten inner tetrahedra. -/
lemma mem_colFaces_new (h : IsMove K σ τ) (c : Fin 6) (hW : σ ∪ τ = univ.map φ.toEmbedding)
    (hτ : τ = bF φ (bmT c)) {f : Finset V} :
    (f ∈ colFaces (move K h) ∧ τ ⊆ f) ↔
      (∃ p, f = bF φ (trT c p)) ∨ (∃ q, f = bF φ (teT c q)) := by
  have hτ1 : τ = {φ c} := by rw [hτ, bF_bmT]
  rw [mem_colFaces_new15 h hτ1, hW]
  constructor
  · rintro ⟨hv, hfs, hc⟩
    have hf := exists_map_of_subset φ hfs
    set P := univ.filter fun i => φ i ∈ f with hP
    have hcP : c ∈ P := by simp [hP, hv]
    have hcardP : #P = #f := by
      conv_rhs => rw [hf]
      rw [card_map]
    rcases hc with hc | hc
    · obtain ⟨p, hp⟩ := exists_trT c P hcP (by omega)
      exact Or.inl ⟨p, by rw [bF, hp, ← hf]⟩
    · obtain ⟨q, hq⟩ := exists_teT c P hcP (by omega)
      exact Or.inr ⟨q, by rw [bF, hq, ← hf]⟩
  · rintro (⟨p, rfl⟩ | ⟨q, rfl⟩)
    · refine ⟨?_, map_subset_map.mpr (subset_univ _), Or.inl (card_bF_trT φ c p)⟩
      rw [bF, mem_map]
      exact ⟨c, mem_bits_trT c p, rfl⟩
    · refine ⟨?_, map_subset_map.mpr (subset_univ _), Or.inr (card_bF_teT φ c q)⟩
      rw [bF, mem_map]
      exact ⟨c, mem_bits_teT c q, rfl⟩


/-- The vertex amplitude of the old four-simplex is the evaluation of `QB c`. -/
lemma simpW_eq_QB (c : Fin 6) (g : Finset V → ℕ) :
    simpW g ((univ.map φ.toEmbedding).erase (φ c)) = (QB c).ev (bcol φ g) := by
  rw [QB, SNet.ev_union _ _ (fun _ => ⟨rfl, rfl⟩), Fin.prod_univ_one, simpW,
    dite_eq_left (card_erase_univ_map φ _), vertexAmp_erase_eq]

/-- **The old side of the 1-5 move**: for the four-simplex `σ` and the vertex `τ` given by
case `c` and the positions `φ`, the state sum is the sum over the outer colourings of the outer
weight times `(QB c).ev`. -/
theorem amplitudeGF_eq_sum (K : Complex4 V) (h : IsMove K σ τ) (c : Fin 6)
    (hW : σ ∪ τ = univ.map φ.toEmbedding) (hτ : τ = bF φ (bmT c))
    (T : Finset (Finset V)) (cut : Finset V → ℕ) :
    amplitudeGF K T cut =
      ∑ σ' ∈ ((colFaces K).filter (¬ σ ⊆ ·) \ T).pi (fun f => range (cut f + 1)),
        outerW K σ (Lightlike.PR.extS _ σ') * (QB c).ev (bcol φ (Lightlike.PR.extS _ σ')) := by
  have hτ1 : τ = {φ c} := by rw [hτ, bF_bmT]
  have hcard := h.card
  have h5 : #σ = 5 := by rw [hτ1, card_singleton] at hcard; omega
  have hfilt : (colFaces K).filter (¬ σ ⊆ ·) = colFaces K :=
    filter_true_of_mem fun f hf hsub => by
      have := card_le_card hsub
      have h34 := (mem_colFaces_iff.mp hf).2
      omega
  rw [amplitudeGF, hfilt]
  refine sum_congr rfl fun σ' hσ' => ?_
  set g := Lightlike.PR.extS _ σ'
  have hnt : K.tris.filter (σ ⊆ ·) = ∅ := by
    refine filter_eq_empty_iff.mpr fun f hf hsub => ?_
    have := card_le_card hsub
    have h3 := card_of_mem_faces hf
    omega
  rw [weight_eq_outerW_gen h, hnt, prod_empty, one_mul, hW, hτ1, prod_singleton,
    simpW_eq_QB]

/-- The faces that carry a sum, outermost sum first: the triangles `x6 .. x1` and the
tetrahedra in the order of the nested sum. -/
def lstT (c : Fin 6) : List (Fin 64) :=
  [trT c 9, teT c 5, trT c 8, teT c 4, trT c 7, teT c 9, trT c 6, teT c 2, trT c 5, teT c 8,
    trT c 4, teT c 7, teT c 6, teT c 3, teT c 1, teT c 0]

set_option maxRecDepth 100000 in
lemma lstT_nodup : ∀ c, (lstT c).Nodup := by decide +kernel

set_option maxRecDepth 100000 in
lemma lstT_mem : ∀ (c : Fin 6) (n : Fin 64), n ∈ lstT c ↔
    ((∃ p : Fin 10, 4 ≤ p.val ∧ n = trT c p) ∨ ∃ q, n = teT c q) := by decide +kernel

set_option maxRecDepth 100000 in
lemma lstT_ne_tri : ∀ (c : Fin 6) (n : Fin 64), n ∈ lstT c → ∀ p : Fin 10, p.val < 4 →
    n ≠ trT c p := by decide +kernel

lemma prod_ten (F : Fin 10 → ℝ) :
    ∏ p, F p = F 0 * F 1 * F 2 * F 3 * F 4 * F 5 * F 6 * F 7 * F 8 * F 9 := by
  simp [Fin.prod_univ_succ]
  ring


/-- The triangles of the new complex containing the new vertex are the ten inner triangles. -/
lemma tris_filter_new (h : IsMove K σ τ) (c : Fin 6) (hW : σ ∪ τ = univ.map φ.toEmbedding)
    (hτ : τ = bF φ (bmT c)) :
    (move K h).tris.filter (τ ⊆ ·) = univ.image fun p => bF φ (trT c p) := by
  ext f
  rw [mem_filter, mem_image]
  constructor
  · rintro ⟨hf, hτf⟩
    have hc : f ∈ colFaces (move K h) := mem_union_left _ hf
    rcases (mem_colFaces_new φ h c hW hτ).mp ⟨hc, hτf⟩ with ⟨p, hp⟩ | ⟨q, hq⟩
    · exact ⟨p, mem_univ _, hp.symm⟩
    · have := card_of_mem_faces hf
      rw [hq, card_bF_teT] at this
      omega
  · rintro ⟨p, -, rfl⟩
    obtain ⟨hc, hτf⟩ := (mem_colFaces_new φ h c hW hτ).mpr (Or.inl ⟨p, rfl⟩)
    refine ⟨?_, hτf⟩
    rcases mem_union.mp hc with ht | ht
    · exact ht
    · have := card_of_mem_faces ht
      rw [card_bF_trT] at this
      omega

/-- The vertex amplitudes of the five four-simplices of the new side are the evaluation of
`U5 c`. -/
lemma prod_simpW_eq_A (c : Fin 6) (g : Finset V → ℕ) :
    ∏ k : Fin 5, simpW g ((univ.map φ.toEmbedding).erase (φ (aposT c k))) =
      (U5 c).ev (bcol φ g) := by
  rw [U5, SNet.ev_union _ _ (fun _ => ⟨rfl, rfl⟩)]
  refine prod_congr rfl fun k _ => ?_
  rw [simpW, dite_eq_left (card_erase_univ_map φ _), vertexAmp_erase_eq]

/-- The cutoff conditions of the 1-5 move, for functions `tr`, `te`, `ot` giving the ten inner
triangles `{v, a_i, a_j}`, the ten inner tetrahedra `{v, a_i, a_j, a_k}` and the ten outer
triangles `{a_i, a_j, a_k}`, each in lexicographic order of the positions. They say that the
cutoff of each face is at least the sum of the largest colours that the triangle inequalities of
the faces around it allow. -/
def Cut15 (cut : Finset V → ℕ) (tr te ot : Fin 10 → Finset V) : Prop :=
  cut (ot 5) ≤ cut (tr 9) ∧ cut (tr 9) + cut (ot 5) ≤ cut (te 5) ∧
  cut (ot 4) ≤ cut (tr 8) ∧ cut (tr 8) + cut (ot 4) ≤ cut (te 4) ∧
  cut (ot 9) + cut (tr 8) + cut (tr 9) ≤ cut (tr 7) ∧
  cut (tr 7) + (cut (ot 9) + cut (tr 8) + cut (tr 9)) ≤ cut (te 9) ∧
  cut (ot 2) ≤ cut (tr 6) ∧ cut (tr 6) + cut (ot 2) ≤ cut (te 2) ∧
  cut (ot 8) + cut (tr 6) + cut (tr 9) ≤ cut (tr 5) ∧
  cut (tr 5) + (cut (ot 8) + cut (tr 6) + cut (tr 9)) ≤ cut (te 8) ∧
  cut (ot 7) + cut (tr 6) + cut (tr 8) ≤ cut (tr 4) ∧
  cut (tr 4) + (cut (ot 7) + cut (tr 6) + cut (tr 8)) ≤ cut (te 7) ∧
  cut (ot 6) + cut (tr 4) + cut (tr 5) + cut (tr 7) ≤ cut (te 6) ∧
  cut (ot 3) + cut (tr 7) ≤ cut (te 3) ∧
  cut (ot 1) + cut (tr 5) ≤ cut (te 1) ∧
  cut (ot 0) + cut (tr 4) ≤ cut (te 0)

/-- The four inner triangles `{v, a_0, a_j}` that are fixed to colour `0`. -/
def gaugeSet (c : Fin 6) : Finset (Finset V) :=
  (univ.filter fun p : Fin 10 => p.val < 4).image fun p => bF φ (trT c p)


/-- Nested sums over the colours of faces given by bitmasks, the head outermost. -/
def nestB (t : Fin 64 → Finset ℕ) : List (Fin 64) → (Fin 64 → ℕ) → ((Fin 64 → ℕ) → ℝ) → ℝ
  | [], g, F => F g
  | a :: l, g, F => ∑ x ∈ t a, nestB t l (Function.update g a x) F

lemma nestB_cons (t : Fin 64 → Finset ℕ) (a l g F) :
    nestB t (a :: l) g F = ∑ x ∈ t a, nestB t l (Function.update g a x) F := rfl

lemma nestB_nil (t : Fin 64 → Finset ℕ) (g F) : nestB t [] g F = F g := rfl

/-- Nested sums over faces given by bitmasks are nested sums over the colourings of `V` when
the summand depends on the colouring only through `bcol`. -/
lemma nest_map (t : Finset V → Finset ℕ) (Fb : (Fin 64 → ℕ) → ℝ) :
    ∀ (l : List (Fin 64)) (g : Finset V → ℕ),
      Move24.nest t (l.map (bF φ)) g (fun u => Fb (bcol φ u)) =
        nestB (fun n => t (bF φ n)) l (bcol φ g) Fb
  | [], g => rfl
  | a :: l, g => by
    rw [List.map_cons, Move24.nest_cons, nestB_cons]
    refine sum_congr rfl fun x _ => ?_
    rw [nest_map t Fb l (Function.update g (bF φ a) x), bcol_update]


/-- The nested sum over the sixteen faces of the 1-5 move, written out. -/
lemma nestB_lstT (c : Fin 6) (t : Fin 64 → Finset ℕ) (col : Fin 64 → ℕ) (F : (Fin 64 → ℕ) → ℝ) :
    nestB t (lstT c) col F =
      ∑ x6 ∈ t (trT c 9),
      ∑ k6 ∈ t (teT c 5),
      ∑ x5 ∈ t (trT c 8),
      ∑ k5 ∈ t (teT c 4),
      ∑ x4 ∈ t (trT c 7),
      ∑ k4 ∈ t (teT c 9),
      ∑ x3 ∈ t (trT c 6),
      ∑ k3 ∈ t (teT c 2),
      ∑ x2 ∈ t (trT c 5),
      ∑ k2 ∈ t (teT c 8),
      ∑ x1 ∈ t (trT c 4),
      ∑ k1 ∈ t (teT c 7),
      ∑ g4 ∈ t (teT c 6),
      ∑ g3 ∈ t (teT c 3),
      ∑ g2 ∈ t (teT c 1),
      ∑ g1 ∈ t (teT c 0),
      F (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update col (trT c 9) x6) (teT c 5) k6) (trT c 8) x5) (teT c 4) k5) (trT c 7) x4) (teT c 9) k4) (trT c 6) x3) (teT c 2) k3) (trT c 5) x2) (teT c 8) k2) (trT c 4) x1) (teT c 7) k1) (teT c 6) g4) (teT c 3) g3) (teT c 1) g2) (teT c 0) g1) := rfl


/-- The colours of the six inner triangles after the sixteen updates of the nested sum. -/
lemma chain_eval (c : Fin 6) (col : Fin 64 → ℕ) (x6 k6 x5 k5 x4 k4 x3 k3 x2 k2 x1 k1 g4 g3 g2 g1 : ℕ) :
    (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update col (trT c 9) x6) (teT c 5) k6) (trT c 8) x5) (teT c 4) k5) (trT c 7) x4) (teT c 9) k4) (trT c 6) x3) (teT c 2) k3) (trT c 5) x2) (teT c 8) k2) (trT c 4) x1) (teT c 7) k1) (teT c 6) g4) (teT c 3) g3) (teT c 1) g2) (teT c 0) g1) (trT c 4) = x1 ∧
    (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update col (trT c 9) x6) (teT c 5) k6) (trT c 8) x5) (teT c 4) k5) (trT c 7) x4) (teT c 9) k4) (trT c 6) x3) (teT c 2) k3) (trT c 5) x2) (teT c 8) k2) (trT c 4) x1) (teT c 7) k1) (teT c 6) g4) (teT c 3) g3) (teT c 1) g2) (teT c 0) g1) (trT c 5) = x2 ∧
    (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update col (trT c 9) x6) (teT c 5) k6) (trT c 8) x5) (teT c 4) k5) (trT c 7) x4) (teT c 9) k4) (trT c 6) x3) (teT c 2) k3) (trT c 5) x2) (teT c 8) k2) (trT c 4) x1) (teT c 7) k1) (teT c 6) g4) (teT c 3) g3) (teT c 1) g2) (teT c 0) g1) (trT c 6) = x3 ∧
    (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update col (trT c 9) x6) (teT c 5) k6) (trT c 8) x5) (teT c 4) k5) (trT c 7) x4) (teT c 9) k4) (trT c 6) x3) (teT c 2) k3) (trT c 5) x2) (teT c 8) k2) (trT c 4) x1) (teT c 7) k1) (teT c 6) g4) (teT c 3) g3) (teT c 1) g2) (teT c 0) g1) (trT c 7) = x4 ∧
    (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update col (trT c 9) x6) (teT c 5) k6) (trT c 8) x5) (teT c 4) k5) (trT c 7) x4) (teT c 9) k4) (trT c 6) x3) (teT c 2) k3) (trT c 5) x2) (teT c 8) k2) (trT c 4) x1) (teT c 7) k1) (teT c 6) g4) (teT c 3) g3) (teT c 1) g2) (teT c 0) g1) (trT c 8) = x5 ∧
    (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update col (trT c 9) x6) (teT c 5) k6) (trT c 8) x5) (teT c 4) k5) (trT c 7) x4) (teT c 9) k4) (trT c 6) x3) (teT c 2) k3) (trT c 5) x2) (teT c 8) k2) (trT c 4) x1) (teT c 7) k1) (teT c 6) g4) (teT c 3) g3) (teT c 1) g2) (teT c 0) g1) (trT c 9) = x6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp (config := {decide := true}) only [Function.update_apply, trT_eq_iff, trT_ne_teT,
    ite_true, ite_false]

set_option maxHeartbeats 400000 in
/-- **The new side of the 1-5 move**: for the four-simplex `σ` and the vertex `τ` given by case
`c` and the positions `φ`, the gauge-fixed state sum of the new complex, with the four inner
triangles through `a_0` fixed to colour `0`, is the same sum over outer colourings as for the old
side. -/
theorem amplitudeGF_eq_sum_new (K : Complex4 V) (h : IsMove K σ τ) (c : Fin 6)
    (hW : σ ∪ τ = univ.map φ.toEmbedding) (hτ : τ = bF φ (bmT c)) (T : Finset (Finset V))
    (hT : ∀ f ∈ T, ¬ τ ⊆ f) (cut : Finset V → ℕ)
    (hcut : Cut15 cut (fun p => bF φ (trT c p)) (fun p => bF φ (teT c p))
      (fun p => bF φ (otT c p))) :
    amplitudeGF (move K h) (gaugeSet φ c ∪ T) cut =
      ∑ σ' ∈ ((colFaces K).filter (¬ σ ⊆ ·) \ T).pi (fun f => range (cut f + 1)),
        outerW K σ (Lightlike.PR.extS _ σ') * (QB c).ev (bcol φ (Lightlike.PR.extS _ σ')) := by
  have hsubtri : ∀ p, τ ⊆ bF φ (trT c p) := fun p =>
    ((mem_colFaces_new φ h c hW hτ).mpr (Or.inl ⟨p, rfl⟩)).2
  have hsub : ∀ f ∈ (lstT c).map (bF φ), τ ⊆ f := fun f hf => by
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hf
    rcases (lstT_mem c n).mp hn with ⟨p, -, rfl⟩ | ⟨q, rfl⟩
    · exact hsubtri p
    · exact ((mem_colFaces_new φ h c hW hτ).mpr (Or.inr ⟨q, rfl⟩)).2
  have hGsub : ∀ f ∈ gaugeSet φ c, τ ⊆ f := fun f hf => by
    obtain ⟨p, -, rfl⟩ := mem_image.mp hf
    exact hsubtri p
  set O := (colFaces K).filter (¬ σ ⊆ ·) \ T with hO
  have hOmem : ∀ f, f ∈ O ↔ (f ∈ colFaces (move K h) ∧ ¬ τ ⊆ f) ∧ f ∉ T := fun f => by
    have := congrArg (f ∈ ·) (colFaces_filter_move h)
    simp only [mem_filter, eq_iff_iff] at this
    rw [hO, mem_sdiff, mem_filter, ← this]
  have hS : colFaces (move K h) \ (gaugeSet φ c ∪ T) =
      ((lstT c).map (bF φ)).foldl (fun s a => insert a s) O := by
    ext f
    rw [Move24.mem_foldl_insert, mem_sdiff, mem_union, hOmem, List.mem_map]
    constructor
    · rintro ⟨hfK, hf⟩
      rw [not_or] at hf
      by_cases hτf : τ ⊆ f
      · right
        rcases (mem_colFaces_new φ h c hW hτ).mp ⟨hfK, hτf⟩ with ⟨p, rfl⟩ | ⟨q, rfl⟩
        · have hp : 4 ≤ p.val := by
            by_contra hlt
            exact hf.1 (mem_image.mpr ⟨p, mem_filter.mpr ⟨mem_univ _, by omega⟩, rfl⟩)
          exact ⟨trT c p, (lstT_mem c _).mpr (Or.inl ⟨p, hp, rfl⟩), rfl⟩
        · exact ⟨teT c q, (lstT_mem c _).mpr (Or.inr ⟨q, rfl⟩), rfl⟩
      · exact Or.inl ⟨⟨hfK, hτf⟩, hf.2⟩
    · rintro (⟨⟨hfK, hτf⟩, hfT⟩ | ⟨n, hn, rfl⟩)
      · exact ⟨hfK, not_or.mpr ⟨fun hG => hτf (hGsub f hG), hfT⟩⟩
      · have hmem : bF φ n ∈ colFaces (move K h) := by
          rcases (lstT_mem c n).mp hn with ⟨p, -, rfl⟩ | ⟨q, rfl⟩
          · exact ((mem_colFaces_new φ h c hW hτ).mpr (Or.inl ⟨p, rfl⟩)).1
          · exact ((mem_colFaces_new φ h c hW hτ).mpr (Or.inr ⟨q, rfl⟩)).1
        refine ⟨hmem, not_or.mpr ⟨fun hG => ?_, fun hT' => hT _ hT' (hsub _
          (List.mem_map.mpr ⟨_, hn, rfl⟩))⟩⟩
        obtain ⟨p, hp, e⟩ := mem_image.mp hG
        exact lstT_ne_tri c n hn p (mem_filter.mp hp).2 (bF_injective φ e).symm
  have hnO : ∀ f ∈ (lstT c).map (bF φ), f ∉ O := fun f hf hfO =>
    ((hOmem f).mp hfO).1.2 (hsub f hf)
  rw [amplitudeGF, hS, Move24.sum_pi_foldl _ _ _ O ((lstT_nodup c).map (bF_injective φ)) hnO]
  refine sum_congr rfl fun σ' hσ' => ?_
  set g := Lightlike.PR.extS O σ' with hgdef
  have hg : ∀ f, g f ≤ cut f := Lightlike.PR.extS_le hσ'
  have h0 : ∀ p : Fin 10, g (bF φ (trT c p)) = 0 := fun p =>
    Lightlike.PR.extS_of_not_mem fun hm => ((hOmem _).mp hm).1.2 (hsubtri p)
  have hn0 : ∀ p : Fin 10, p.val < 4 → bF φ (trT c p) ∉ (lstT c).map (bF φ) :=
    fun p hp hm => by
      obtain ⟨n, hn, e⟩ := List.mem_map.mp hm
      exact lstT_ne_tri c n hn p hp (bF_injective φ e)
  have hσ' : σ = univ.image fun k => φ (aposT c k) := by
    have hτ1 : τ = {φ c} := by rw [hτ, bF_bmT]
    have hdisj := h.disj
    ext x
    rw [mem_image]
    constructor
    · intro hx
      have hx' : x ∈ univ.map φ.toEmbedding := hW ▸ mem_union_left _ hx
      obtain ⟨i, -, rfl⟩ := mem_map.mp hx'
      have hne : i ≠ c := fun e => disjoint_left.mp hdisj hx (by rw [hτ1, e]; exact mem_singleton_self _)
      have : i ∈ univ.image (aposT c) := by rw [image_aposT]; simp [hne]
      obtain ⟨k, -, rfl⟩ := mem_image.mp this
      exact ⟨k, mem_univ _, rfl⟩
    · rintro ⟨k, -, rfl⟩
      have hx' : φ (aposT c k) ∈ σ ∪ τ := hW ▸ mem_map.mpr ⟨_, mem_univ _, rfl⟩
      rcases mem_union.mp hx' with hx | hx
      · exact hx
      · exfalso
        rw [hτ1, mem_singleton] at hx
        exact aposT_ne c k (φ.injective hx)
  have hW' : τ ∪ σ = univ.map φ.toEmbedding := by rw [union_comm]; exact hW
  have key : ∀ u : Finset V → ℕ, (∀ f ∉ (lstT c).map (bF φ), u f = g f) →
      weight (move K h) u = outerW K σ g *
        ((((u (bF φ (trT c 4)) : ℝ) + 1) * ((u (bF φ (trT c 5)) : ℝ) + 1) *
          ((u (bF φ (trT c 6)) : ℝ) + 1) * ((u (bF φ (trT c 7)) : ℝ) + 1) *
          ((u (bF φ (trT c 8)) : ℝ) + 1) * ((u (bF φ (trT c 9)) : ℝ) + 1)) *
        (U5 c).ev (bcol φ u)) := by
    intro u hu
    have hprod : ∏ v ∈ σ, simpW u ((τ ∪ σ).erase v) = (U5 c).ev (bcol φ u) := by
      rw [hW', hσ', prod_image fun i _ j _ hij => aposT_injective c (φ.injective hij),
        prod_simpW_eq_A]
    have hout : outerW (move K h) τ u = outerW K σ g := by
      rw [← outerW_move h g]
      exact outerW_congr _ _ fun f hf => hu f fun hm => hf (hsub f hm)
    have hz : ∀ p : Fin 10, p.val < 4 → u (bF φ (trT c p)) = 0 := fun p hp =>
      (hu _ (hn0 p hp)).trans (h0 p)
    rw [weight_eq_outerW_gen h.symm, hprod, hout, tris_filter_new φ h c hW hτ,
      prod_image fun i _ j _ hij => (trT_eq_iff c i j).mp (bF_injective φ hij), prod_ten,
      hz 0 (by decide), hz 1 (by decide), hz 2 (by decide), hz 3 (by decide)]
    simp only [Nat.cast_zero, zero_add, one_mul]
  set Fb : (Fin 64 → ℕ) → ℝ := fun w => outerW K σ g *
    ((((w (trT c 4) : ℝ) + 1) * ((w (trT c 5) : ℝ) + 1) * ((w (trT c 6) : ℝ) + 1) *
      ((w (trT c 7) : ℝ) + 1) * ((w (trT c 8) : ℝ) + 1) * ((w (trT c 9) : ℝ) + 1)) *
    (U5 c).ev w) with hFb
  have hF : Move24.nest (fun f => range (cut f + 1)) ((lstT c).map (bF φ)) g (weight (move K h)) =
      Move24.nest (fun f => range (cut f + 1)) ((lstT c).map (bF φ)) g
        (fun u => Fb (bcol φ u)) :=
    Move24.nest_congr _ _ _ _ _ fun u hu => key u hu
  rw [hF, nest_map]
  have ho : ∀ j, bcol φ g (otT c j) ≤ cut (bF φ (otT c j)) := fun j => hg _
  have z0 : bcol φ g (trT c 0) = 0 := h0 0
  have z1 : bcol φ g (trT c 1) = 0 := h0 1
  have z2 : bcol φ g (trT c 2) = 0 := h0 2
  have z3 : bcol φ g (trT c 3) = 0 := h0 3
  unfold Cut15 at hcut
  beta_reduce at hcut
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16⟩ := hcut
  have o0 := ho 0
  have o1 := ho 1
  have o2 := ho 2
  have o3 := ho 3
  have o4 := ho 4
  have o5 := ho 5
  have o6 := ho 6
  have o7 := ho 7
  have o8 := ho 8
  have o9 := ho 9
  have hloc := lhs_eq_ev_NL15 c (bcol φ g)
    (cut (bF φ (trT c 9))) (cut (bF φ (teT c 5))) (cut (bF φ (trT c 8))) (cut (bF φ (teT c 4)))
    (cut (bF φ (trT c 7))) (cut (bF φ (teT c 9))) (cut (bF φ (trT c 6))) (cut (bF φ (teT c 2)))
    (cut (bF φ (trT c 5))) (cut (bF φ (teT c 8))) (cut (bF φ (trT c 4))) (cut (bF φ (teT c 7)))
    (cut (bF φ (teT c 6))) (cut (bF φ (teT c 3))) (cut (bF φ (teT c 1))) (cut (bF φ (teT c 0)))
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [ev_NL_eq_QB] at hloc
  replace hloc := hloc.trans (show _ = (QB c).ev (bcol φ g) by rw [z0, z1, z2, z3]; simp)
  rw [nestB_lstT]
  clear_value Fb
  rw [← hloc]
  conv_rhs => rw [mul_sum]
  refine sum_congr rfl fun x6 _ => ?_
  conv_rhs => rw [← mul_assoc]
  conv_rhs => rw [mul_sum]
  refine sum_congr rfl fun k6 _ => ?_
  conv_rhs => rw [mul_sum]
  refine sum_congr rfl fun x5 _ => ?_
  conv_rhs => rw [← mul_assoc]
  conv_rhs => rw [mul_sum]
  refine sum_congr rfl fun k5 _ => ?_
  conv_rhs => rw [mul_sum]
  refine sum_congr rfl fun x4 _ => ?_
  conv_rhs => rw [← mul_assoc]
  conv_rhs => rw [mul_sum]
  refine sum_congr rfl fun k4 _ => ?_
  conv_rhs => rw [mul_sum]
  refine sum_congr rfl fun x3 _ => ?_
  conv_rhs => rw [← mul_assoc]
  conv_rhs => rw [mul_sum]
  refine sum_congr rfl fun k3 _ => ?_
  conv_rhs => rw [mul_sum]
  refine sum_congr rfl fun x2 _ => ?_
  conv_rhs => rw [← mul_assoc]
  conv_rhs => rw [mul_sum]
  refine sum_congr rfl fun k2 _ => ?_
  conv_rhs => rw [mul_sum]
  refine sum_congr rfl fun x1 _ => ?_
  conv_rhs => rw [← mul_assoc]
  conv_rhs => rw [mul_sum]
  refine sum_congr rfl fun k1 _ => ?_
  conv_rhs => rw [mul_sum]
  refine sum_congr rfl fun g4 _ => ?_
  conv_rhs => rw [mul_sum]
  refine sum_congr rfl fun g3 _ => ?_
  conv_rhs => rw [mul_sum]
  refine sum_congr rfl fun g2 _ => ?_
  conv_rhs => rw [mul_sum]
  refine sum_congr rfl fun g1 _ => ?_
  obtain ⟨e4, e5, e6, e7, e8, e9⟩ := chain_eval c (bcol φ g) x6 k6 x5 k5 x4 k4 x3 k3 x2 k2 x1 k1 g4 g3 g2 g1
  rw [hFb]
  dsimp only
  rw [e4, e5, e6, e7, e8, e9]
  ring

/-! ### The statement in terms of the sorted vertices of `σ` -/

/-- The triangle `{v, a_i, a_j}` for the `p`-th pair of positions. -/
def triV (a : Fin 5 → V) (v : V) (p : Fin 10) : Finset V :=
  insert v (insert (a (pr5 p).1) {a (pr5 p).2})

/-- The tetrahedron `{v, a_i, a_j, a_k}` for the `q`-th triple of positions. -/
def teV (a : Fin 5 → V) (v : V) (q : Fin 10) : Finset V :=
  insert v (insert (a (tp5 q).1) (insert (a (tp5 q).2.1) {a (tp5 q).2.2}))

/-- The triangle `{a_i, a_j, a_k}` for the `q`-th triple of positions. -/
def otV (a : Fin 5 → V) (q : Fin 10) : Finset V :=
  insert (a (tp5 q).1) (insert (a (tp5 q).2.1) {a (tp5 q).2.2})

/-- The four gauge triangles `{v, a_0, a_j}`, `j ≠ 0`, of the 1-5 move. -/
def gaugeTri (a : Fin 5 → V) (v : V) : Finset (Finset V) :=
  (univ.erase (0 : Fin 5)).image fun j => insert v (insert (a 0) {a j})

lemma pr5_lt : ∀ p : Fin 10, p.val < 4 → (pr5 p).1 = 0 ∧ (pr5 p).2 ≠ 0 := by decide

lemma pr5_surj : ∀ j : Fin 5, j ≠ 0 → ∃ p : Fin 10, p.val < 4 ∧ pr5 p = (0, j) := by decide

lemma gaugeSet_eq (c : Fin 6) : gaugeSet φ c = gaugeTri (fun k => φ (aposT c k)) (φ c) := by
  unfold gaugeSet gaugeTri
  ext f
  simp only [mem_image, mem_filter, mem_univ, true_and, mem_erase]
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨h1, h2⟩ := pr5_lt p hp
    refine ⟨(pr5 p).2, ⟨h2, trivial⟩, ?_⟩
    rw [bF_trT, h1]
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨p, hp, hpj⟩ := pr5_surj j hj.1
    refine ⟨p, hp, ?_⟩
    rw [bF_trT, hpj]

/-- **The Ooguri amplitude is invariant under the 1-5 move.** Here `σ` is the 4-simplex that the
move subdivides, `τ = {v}` the new vertex and `a` the sorted vertices of `σ`. After the move the
four triangles `{v, a_0, a_j}` are fixed to colour `0`; the cutoff conditions `Cut15` say that the
cutoff of every face is at least what the triangle inequalities around it allow. -/
theorem amplitudeGF_move15 (K : Complex4 V) (h : IsMove K σ τ) (hσ : #σ = 5) {v : V}
    (hτ : τ = {v}) (T : Finset (Finset V)) (hT : ∀ f ∈ T, ¬ σ ⊆ f ∧ ¬ τ ⊆ f)
    (cut : Finset V → ℕ)
    (hcut : Cut15 cut (triV (σ.orderEmbOfFin hσ) v) (teV (σ.orderEmbOfFin hσ) v)
      (otV (σ.orderEmbOfFin hσ))) :
    amplitudeGF (move K h) (gaugeTri (σ.orderEmbOfFin hσ) v ∪ T) cut =
      amplitudeGF K T cut := by
  have h6 : #(σ ∪ τ) = 6 := h.card_union
  set φ := (σ ∪ τ).orderEmbOfFin h6
  have hW : σ ∪ τ = univ.map φ.toEmbedding := by
    ext x
    rw [mem_map]
    constructor
    · intro hx
      have : x ∈ Set.range φ := by rw [range_orderEmbOfFin]; exact hx
      obtain ⟨i, rfl⟩ := this
      exact ⟨i, mem_univ _, rfl⟩
    · rintro ⟨i, -, rfl⟩
      exact (σ ∪ τ).orderEmbOfFin_mem h6 i
  have hvW : v ∈ σ ∪ τ := mem_union_right _ (by rw [hτ]; exact mem_singleton_self v)
  obtain ⟨c, hc⟩ : ∃ c, φ c = v := by
    have : v ∈ Set.range φ := by rw [range_orderEmbOfFin]; exact hvW
    exact this
  have hτc : τ = bF φ (bmT c) := by rw [bF_bmT, hc, hτ]
  have ha : ∀ k, σ.orderEmbOfFin hσ k = φ (aposT c k) := fun k => by
    have hmem : ∀ k, φ (aposT c k) ∈ σ := fun k => by
      have h1 : φ (aposT c k) ∈ σ ∪ τ := hW ▸ mem_map_of_mem _ (mem_univ _)
      rcases mem_union.mp h1 with h2 | h2
      · exact h2
      · exfalso
        rw [hτ, mem_singleton, ← hc] at h2
        exact aposT_ne c k (φ.injective h2)
    have := orderEmbOfFin_unique (s := σ) hσ (f := fun k => φ (aposT c k)) hmem
      (φ.strictMono.comp (aposT_strictMono c))
    exact (congrFun this k).symm
  have hcut' : Cut15 cut (fun p => bF φ (trT c p)) (fun p => bF φ (teT c p))
      (fun p => bF φ (otT c p)) := by
    have e1 : (fun p => bF φ (trT c p)) = triV (σ.orderEmbOfFin hσ) v := by
      funext p; rw [bF_trT]; simp only [triV, ha, hc]
    have e2 : (fun p => bF φ (teT c p)) = teV (σ.orderEmbOfFin hσ) v := by
      funext p; rw [bF_teT]; simp only [teV, ha, hc]
    have e3 : (fun p => bF φ (otT c p)) = otV (σ.orderEmbOfFin hσ) := by
      funext p
      rw [bF, bits_otT, map_insert, map_insert, map_singleton]
      simp only [otV, ha]; rfl
    rw [e1, e2, e3]; exact hcut
  have hg : gaugeTri (σ.orderEmbOfFin hσ) v = gaugeSet φ c := by
    rw [gaugeSet_eq]
    unfold gaugeTri
    simp only [ha, hc]
  rw [hg, amplitudeGF_eq_sum_new φ K h c hW hτc T (fun f hf => (hT f hf).2) cut hcut',
    amplitudeGF_eq_sum φ K h c hW hτc T cut]

/-! ### The gauge rule under the 1-5 move -/

/-- One elementary collapse, in the form used to build collapsible sets: adding a free face `s`
together with a face `t` one dimension higher keeps a set collapsible. -/
lemma collapsible_insert {Y : Finset (Finset V)} (hY : Collapsible Y) {s t : Finset V}
    (hst : s ⊆ t) (hcard : #t = #s + 1) (hfree : ∀ ρ ∈ Y, ¬ s ⊆ ρ) :
    Collapsible (insert t (insert s Y)) := by
  have hs : s ∉ Y := fun hh => hfree s hh subset_rfl
  have ht : t ∉ Y := fun hh => hfree t hh hst
  have hne : t ≠ s := fun e => by rw [e] at hcard; omega
  refine Collapsible.collapse s t (mem_insert_of_mem (mem_insert_self _ _)) (mem_insert_self _ _)
    hst hcard ?_ ?_
  · intro ρ hρ hsρ
    simp only [mem_insert] at hρ
    rcases hρ with rfl | rfl | hρ
    · exact Or.inr rfl
    · exact Or.inl rfl
    · exact absurd hsρ (hfree ρ hρ)
  · rw [erase_insert (by simp only [mem_insert, not_or]; exact ⟨hne, ht⟩), erase_insert hs]
    exact hY

section Gauge15

variable (a : Fin 5 → V) (v : V)

/-- The edge `{v, a_j}`. -/
def edgeV (j : Fin 5) : Finset V := insert v {a j}

/-- The triangle `{v, a_0, a_j}`. -/
def triG (j : Fin 5) : Finset V := insert v (insert (a 0) {a j})

variable {a v}

lemma edgeV_subset_triG (j : Fin 5) : edgeV a v j ⊆ triG a v j := by
  intro x hx; simp only [edgeV, triG, mem_insert, mem_singleton] at hx ⊢; tauto

lemma card_edgeV (hav : ∀ k, a k ≠ v) (j : Fin 5) : #(edgeV a v j) = 2 := by
  unfold edgeV
  rw [card_insert_of_notMem (by simpa using (hav j).symm)]; simp

lemma card_triG (hav : ∀ k, a k ≠ v) (hinj : Function.Injective a) {j : Fin 5} (hj : j ≠ 0) :
    #(triG a v j) = #(edgeV a v j) + 1 := by
  have : triG a v j = insert (a 0) (edgeV a v j) := by
    unfold triG edgeV; exact insert_comm _ _ _
  rw [this, card_insert_of_notMem]
  simp only [edgeV, mem_insert, mem_singleton, not_or]
  exact ⟨hav 0, fun e => hj (hinj e).symm⟩

/-- Collapsing the edges `{v, a_j}` against the triangles `{v, a_0, a_j}`, one `j` at a time. -/
lemma collapsible_stars (hav : ∀ k, a k ≠ v) (hinj : Function.Injective a)
    {B : Finset (Finset V)} (hB : Collapsible B)
    (hfree : ∀ j : Fin 5, j ≠ 0 → ∀ ρ ∈ B, ¬ edgeV a v j ⊆ ρ) :
    ∀ S : Finset (Fin 5), S ⊆ univ.erase 0 →
      Collapsible (B ∪ S.image (edgeV a v) ∪ S.image (triG a v)) := by
  intro S
  induction S using Finset.induction_on with
  | empty => intro _; simpa using hB
  | insert j S hjS ih =>
    intro hS
    have hj0 : j ≠ 0 := fun e => by
      have := hS (mem_insert_self _ _); simp [e] at this
    have hSsub : S ⊆ univ.erase 0 := (subset_insert _ _).trans hS
    have key := collapsible_insert (ih hSsub) (edgeV_subset_triG j)
      (card_triG hav hinj hj0) (fun ρ hρ hsub => by
        simp only [mem_union, mem_image] at hρ
        rcases hρ with (hρ | ⟨k, hk, rfl⟩) | ⟨k, hk, rfl⟩
        · exact hfree j hj0 ρ hρ hsub
        · have hkj : k ≠ j := fun e => hjS (e ▸ hk)
          have := hsub (mem_insert_of_mem (mem_singleton_self (a j)) : a j ∈ edgeV a v j)
          simp only [edgeV, mem_insert, mem_singleton] at this
          rcases this with e | e
          · exact hav j e
          · exact hkj (hinj e).symm
        · have hkj : k ≠ j := fun e => hjS (e ▸ hk)
          have := hsub (mem_insert_of_mem (mem_singleton_self (a j)) : a j ∈ edgeV a v j)
          simp only [triG, mem_insert, mem_singleton] at this
          rcases this with e | e | e
          · exact hav j e
          · exact hj0 (hinj e)
          · exact hkj (hinj e).symm)
    have heq : B ∪ (insert j S).image (edgeV a v) ∪ (insert j S).image (triG a v) =
        insert (triG a v j) (insert (edgeV a v j)
          (B ∪ S.image (edgeV a v) ∪ S.image (triG a v))) := by
      rw [image_insert, image_insert]
      ext f
      simp only [mem_union, mem_insert]
      tauto
    rw [heq]; exact key

end Gauge15

section Faces15

variable (h : IsMove K σ τ) {v : V} (hτ : τ = {v})
include h hτ

lemma not_mem_of_fresh_faces {k : ℕ} {f : Finset V} (hf : f ∈ K.faces k) : v ∉ f := fun hv => by
  obtain ⟨s, hs, hfs, -⟩ := Complex4.mem_faces.mp hf
  exact h.fresh s hs (by rw [hτ]; exact singleton_subset_iff.mpr (hfs hv))

lemma hvσ : v ∉ σ := fun hv =>
  disjoint_left.mp h.disj hv (by rw [hτ]; exact mem_singleton_self v)

lemma faces0_move15 (hσ : #σ = 5) : (move K h).faces 0 = insert {v} (K.faces 0) := by
  have hv := hvσ h hτ
  have hcard : #σ = 5 := hσ
  obtain ⟨u, hu⟩ : σ.Nonempty := h.nonempty_left
  ext f
  constructor
  · intro hf
    by_cases hτf : τ ⊆ f
    · have := eq_of_subset_of_card_le hτf (by rw [Complex4.card_of_mem_faces hf, hτ]; simp)
      rw [← this, hτ]; exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_faces_of_mem_move h hf hτf)
  · intro hf
    rcases mem_insert.mp hf with rfl | hf
    · have hsim : (σ ∪ τ).erase u ∈ (move K h).simps := Complex4.mem_move.mpr (Or.inr ⟨u, hu, rfl⟩)
      refine Complex4.mem_faces.mpr ⟨_, hsim, ?_, by simp⟩
      intro x hx
      rw [mem_singleton] at hx
      subst hx
      exact mem_erase.mpr ⟨fun e => hv (e ▸ hu), mem_union_right _ (by rw [hτ]; exact mem_singleton_self _)⟩
    · exact mem_faces_move h hf fun hs => by
        have := card_le_card hs; rw [Complex4.card_of_mem_faces hf] at this; omega

lemma faces1_move15 (hσ : #σ = 5) {a : Fin 5 → V} (hinj : Function.Injective a)
    (hsurj : ∀ x, x ∈ σ ↔ ∃ j, a j = x) :
    (move K h).faces 1 = K.faces 1 ∪ univ.image (edgeV a v) := by
  have hv := hvσ h hτ
  have hmemσ : ∀ j, a j ∈ σ := fun j => (hsurj _).mpr ⟨j, rfl⟩
  have hav : ∀ k, a k ≠ v := fun k e => hv (e ▸ hmemσ k)
  ext f
  constructor
  · intro hf
    by_cases hτf : τ ⊆ f
    · refine mem_union_right _ ?_
      obtain ⟨s, hs, hfs, hf2⟩ := Complex4.mem_faces.mp hf
      rcases Complex4.mem_move.mp hs with ⟨hsK, -⟩ | ⟨u, hu, rfl⟩
      · exact absurd (hτf.trans hfs) (h.fresh s hsK)
      · have hvf : v ∈ f := hτf (by rw [hτ]; exact mem_singleton_self v)
        obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hf2
        have hsub : ∀ w ∈ ({x, y} : Finset V), w ∈ σ ∪ τ := fun w hw =>
          (mem_erase.mp (hfs hw)).2
        have key : ∀ w, w ≠ v → w ∈ ({x, y} : Finset V) → w ∈ σ := fun w hwv hw => by
          rcases mem_union.mp (hsub w hw) with h1 | h1
          · exact h1
          · rw [hτ, mem_singleton] at h1; exact absurd h1 hwv
        simp only [mem_insert, mem_singleton] at hvf
        rcases hvf with rfl | rfl
        · obtain ⟨j, hj⟩ := (hsurj y).mp (key y (Ne.symm hxy) (by simp))
          exact mem_image.mpr ⟨j, mem_univ _, by rw [edgeV, hj]⟩
        · obtain ⟨j, hj⟩ := (hsurj x).mp (key x hxy (by simp))
          exact mem_image.mpr ⟨j, mem_univ _, by rw [edgeV, hj, pair_comm]⟩
    · exact mem_union_left _ (mem_faces_of_mem_move h hf hτf)
  · intro hf
    rcases mem_union.mp hf with hf | hf
    · exact mem_faces_move h hf fun hs => by
        have := card_le_card hs; rw [Complex4.card_of_mem_faces hf] at this; omega
    · obtain ⟨j, -, rfl⟩ := mem_image.mp hf
      obtain ⟨k, hk⟩ : ∃ k : Fin 5, k ≠ j := by
        by_cases hj : j = 0
        · exact ⟨1, by rw [hj]; decide⟩
        · exact ⟨0, fun e => hj e.symm⟩
      have hsim : (σ ∪ τ).erase (a k) ∈ (move K h).simps :=
        Complex4.mem_move.mpr (Or.inr ⟨a k, hmemσ k, rfl⟩)
      refine Complex4.mem_faces.mpr ⟨_, hsim, ?_, card_edgeV hav j⟩
      intro x hx
      simp only [edgeV, mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact mem_erase.mpr ⟨fun e => hav k e.symm, mem_union_right _ (by rw [hτ]; exact mem_singleton_self _)⟩
      · exact mem_erase.mpr ⟨fun e => hk (hinj e).symm, mem_union_left _ (hmemσ j)⟩

/-- **The gauge rule survives the 1-5 move.** The new complex has one more vertex `v`, five more
edges `{v, a_j}` and ten more triangles. With the four triangles `{v, a_0, a_j}` added to a gauge
set of `K`, the gauge complex collapses first to the gauge complex of `K` together with the vertex
`v` and the edge `{v, a_0}`, and then to that of `K`. -/
theorem isGauge_move15 (hσ : #σ = 5) {a : Fin 5 → V} (hinj : Function.Injective a)
    (hsurj : ∀ x, x ∈ σ ↔ ∃ j, a j = x) {T : Finset (Finset V)} (hg : IsGauge K T) :
    IsGauge (move K h) (gaugeTri a v ∪ T) := by
  have hv := hvσ h hτ
  have hmemσ : ∀ j, a j ∈ σ := fun j => (hsurj _).mpr ⟨j, rfl⟩
  have hav : ∀ k, a k ≠ v := fun k e => hv (e ▸ hmemσ k)
  have hTsub : ∀ f ∈ T, f ∈ K.faces 2 := hg.1
  have hfresh : ∀ f ∈ gaugeCx K T, v ∉ f := fun f hf => by
    unfold gaugeCx at hf
    simp only [mem_union] at hf
    rcases hf with (hf | hf) | hf
    · exact not_mem_of_fresh_faces h hτ hf
    · exact not_mem_of_fresh_faces h hτ hf
    · exact not_mem_of_fresh_faces h hτ (hTsub f hf)
  refine ⟨?_, ?_⟩
  · intro f hf
    rcases mem_union.mp hf with hf | hf
    · obtain ⟨j, hj, rfl⟩ := mem_image.mp hf
      have hj0 : j ≠ 0 := (mem_erase.mp hj).1
      obtain ⟨k, hk0, hkj⟩ : ∃ k : Fin 5, k ≠ 0 ∧ k ≠ j := by
        have : ∀ j : Fin 5, ∃ k : Fin 5, k ≠ 0 ∧ k ≠ j := by decide
        exact this j
      have hsim : (σ ∪ τ).erase (a k) ∈ (move K h).simps :=
        Complex4.mem_move.mpr (Or.inr ⟨a k, hmemσ k, rfl⟩)
      refine Complex4.mem_faces.mpr ⟨_, hsim, ?_, ?_⟩
      · intro x hx
        simp only [mem_insert, mem_singleton] at hx
        have hvU : v ∈ σ ∪ τ := mem_union_right _ (by rw [hτ]; exact mem_singleton_self _)
        rcases hx with rfl | rfl | rfl
        · exact mem_erase.mpr ⟨fun e => hav k e.symm, hvU⟩
        · exact mem_erase.mpr ⟨fun e => hk0 (hinj e.symm), mem_union_left _ (hmemσ 0)⟩
        · exact mem_erase.mpr ⟨fun e => hkj (hinj e.symm), mem_union_left _ (hmemσ j)⟩
      · have := card_triG hav hinj hj0
        have h2 := card_edgeV hav j
        unfold triG edgeV at this h2
        omega
    · exact mem_faces_move h (hTsub f hf) fun hs => by
        have := card_le_card hs; rw [Complex4.card_of_mem_faces (hTsub f hf)] at this; omega
  · have hE : (univ : Finset (Fin 5)).image (edgeV a v) =
        insert (edgeV a v 0) ((univ.erase 0).image (edgeV a v)) := by
      conv_lhs => rw [← insert_erase (mem_univ (0 : Fin 5))]
      rw [image_insert]
    have hX : gaugeCx (move K h) (gaugeTri a v ∪ T) =
        insert (edgeV a v 0) (insert {v} (gaugeCx K T)) ∪
          (univ.erase (0 : Fin 5)).image (edgeV a v) ∪
          (univ.erase (0 : Fin 5)).image (triG a v) := by
      unfold gaugeCx
      rw [faces0_move15 h hτ hσ, faces1_move15 h hτ hσ hinj hsurj, hE]
      ext f
      simp only [mem_union, mem_insert, mem_singleton]
      have : gaugeTri a v = (univ.erase (0 : Fin 5)).image (triG a v) := rfl
      rw [this]
      tauto
    have hB := collapsible_insert (Y := gaugeCx K T) hg.2 (s := {v}) (t := edgeV a v 0)
      (by intro x hx; rw [mem_singleton] at hx; simp [edgeV, hx])
      (by rw [card_edgeV hav]; simp)
      (fun ρ hρ hsub => hfresh ρ hρ (hsub (mem_singleton_self v)))
    have key := collapsible_stars (a := a) (v := v) hav hinj hB (fun j hj ρ hρ hsub => by
      simp only [mem_insert] at hρ
      have hav' : a j ∈ edgeV a v j := mem_insert_of_mem (mem_singleton_self _)
      rcases hρ with rfl | rfl | hρ
      · have := hsub hav'
        simp only [edgeV, mem_insert, mem_singleton] at this
        rcases this with e | e
        · exact hav j e
        · exact hj (hinj e)
      · have := hsub hav'
        rw [mem_singleton] at this
        exact hav j this
      · exact hfresh ρ hρ (hsub (mem_insert_self _ _))) (univ.erase 0) subset_rfl
    rw [hX]
    exact key

end Faces15

/-- **The gauge-fixed Ooguri amplitude is invariant under the 1-5 move.** For a gauge set `T` of
`K`, adding the four triangles `{v, a_0, a_j}` gives a gauge set of the moved complex
(`isGauge_move15`), and the two gauge-fixed amplitudes agree under the cutoff conditions `Cut15`
(`amplitudeGF_move15`). -/
theorem amplitudeGF_move15_gauge (K : Complex4 V) (h : IsMove K σ τ) (hσ : #σ = 5) {v : V}
    (hτ : τ = {v}) (T : Finset (Finset V)) (hg : IsGauge K T) (cut : Finset V → ℕ)
    (hcut : Cut15 cut (triV (σ.orderEmbOfFin hσ) v) (teV (σ.orderEmbOfFin hσ) v)
      (otV (σ.orderEmbOfFin hσ))) :
    IsGauge (move K h) (gaugeTri (σ.orderEmbOfFin hσ) v ∪ T) ∧
    amplitudeGF (move K h) (gaugeTri (σ.orderEmbOfFin hσ) v ∪ T) cut =
      amplitudeGF K T cut := by
  have hT : ∀ f ∈ T, ¬ σ ⊆ f ∧ ¬ τ ⊆ f := fun f hf => by
    have hc := Complex4.card_of_mem_faces (hg.1 hf)
    obtain ⟨s, hs, hfs, -⟩ := Complex4.mem_faces.mp (hg.1 hf)
    exact ⟨fun hh => by have := card_le_card hh; omega, fun hh => h.fresh s hs (hh.trans hfs)⟩
  refine ⟨isGauge_move15 h hτ hσ (σ.orderEmbOfFin hσ).injective (fun x => ?_) hg,
    amplitudeGF_move15 K h hσ hτ T hT cut hcut⟩
  constructor
  · intro hx
    have : x ∈ Set.range (σ.orderEmbOfFin hσ) := by rw [range_orderEmbOfFin]; exact hx
    exact this
  · rintro ⟨j, rfl⟩
    exact σ.orderEmbOfFin_mem hσ j

/-- **The gauge-fixed Ooguri amplitude is invariant under the 5-1 move** (the move replacing the
five 4-simplices `(σ ∪ τ) ∖ {a}`, `a ∈ τ`, around the vertex `σ = {v}` by the single 4-simplex
`τ`). The gauge set `T` is a gauge set of the complex after the move; the complex before the move
has the four additional triangles `{v, b_0, b_j}` of the sorted vertices `b` of `τ`. -/
theorem amplitudeGF_move51_gauge (K : Complex4 V) (h : IsMove K σ τ) (hτ : #τ = 5) {v : V}
    (hσ : σ = {v}) (T : Finset (Finset V)) (hg : IsGauge (move K h) T) (cut : Finset V → ℕ)
    (hcut : Cut15 cut (triV (τ.orderEmbOfFin hτ) v) (teV (τ.orderEmbOfFin hτ) v)
      (otV (τ.orderEmbOfFin hτ))) :
    IsGauge K (gaugeTri (τ.orderEmbOfFin hτ) v ∪ T) ∧
    amplitudeGF K (gaugeTri (τ.orderEmbOfFin hτ) v ∪ T) cut =
      amplitudeGF (move K h) T cut := by
  have := amplitudeGF_move15_gauge (move K h) h.symm hτ hσ T hg cut hcut
  rwa [move_move] at this

end Move15

end Lightlike.SpinFoam
