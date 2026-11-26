import Lightlike.PonzanoRegge.TriangulationIndependence.Rename
import Lightlike.PonzanoRegge.TriangulationIndependence.StellarForward

/-!
# The star of an edge as a common forward descendant

No stellar subdivision at an edge is a forward descendant (`not_forwardMoves_starAt_edge`: forward
moves keep every edge). It is reached as a common forward descendant instead
(`commonForward_starAt_edge`). Let the edge `AB` have the link cycle `c 0, …, c (n - 1)` and let
`a` be fresh.

* From `K`: the fresh vertex `a` grows, in the link of `A`, over the fan of triangles
  `{B, c i, c (i + 1)}`, `i ≤ n - 2` (`fanR`, a tree shelling with boundary `fanB`), by
  `forwardMoves_grown`: one 1-4 move and `n - 2` 2-3 moves.
* From the star: one 2-3 move on `{a, c (n - 1), c 0}` with apexes `A` and `B` brings the edge `AB`
  back and gives the same complex.
-/

open Finset Lightlike.PL Lightlike.PL.SComplex

namespace Lightlike.PR

variable {V : Type*} [DecidableEq V]

/-- Closes an equality of two explicit four-element sets listing the same elements. -/
macro "set_perm" : tactic => `(tactic| (ext y; simp only [Finset.mem_insert, Finset.mem_singleton]; constructor <;> intro hy <;> rcases hy with hy | hy | hy | hy <;> simp [hy]))

section Fan

variable (B : V) (c : ℕ → V)

/-- The fan of triangles `{B, c i, c (i + 1)}` for `i ≤ k`. -/
def fanR : ℕ → Finset (Finset V)
  | 0 => {{B, c 0, c 1}}
  | k + 1 => insert {B, c (k + 1), c (k + 2)} (fanR k)

/-- The boundary edges of the fan `fanR B c k`, built by the shelling recursion. -/
def fanB : ℕ → Finset (Finset V)
  | 0 => {{B, c 0}, {B, c 1}, {c 0, c 1}}
  | k + 1 => insert {B, c (k + 2)} (insert {c (k + 1), c (k + 2)} ((fanB k).erase {B, c (k + 1)}))

variable {B c}

lemma mem_fanR {k : ℕ} {σ : Finset V} : σ ∈ fanR B c k ↔ ∃ i ≤ k, σ = {B, c i, c (i + 1)} := by
  induction k with
  | zero => simp [fanR]
  | succ k ih =>
    simp only [fanR, mem_insert, ih]
    constructor
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨k + 1, le_rfl, rfl⟩
      · exact ⟨i, by omega, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      rcases Nat.lt_or_ge i (k + 1) with h | h
      · exact .inr ⟨i, by omega, rfl⟩
      · obtain rfl : i = k + 1 := by omega
        exact .inl rfl

lemma verts2_fanR {k : ℕ} {x : V} (hx : x ∈ verts2 (fanR B c k)) :
    x = B ∨ ∃ i ≤ k + 1, x = c i := by
  obtain ⟨σ, hσ, hxσ⟩ := mem_verts2.1 hx
  obtain ⟨i, hi, rfl⟩ := mem_fanR.1 hσ
  simp only [mem_insert, mem_singleton] at hxσ
  rcases hxσ with rfl | rfl | rfl
  · exact .inl rfl
  · exact .inr ⟨i, by omega, rfl⟩
  · exact .inr ⟨i + 1, by omega, rfl⟩

lemma mem_fanB_last (k : ℕ) : ({B, c (k + 1)} : Finset V) ∈ fanB B c k := by
  cases k with
  | zero => simp [fanB]
  | succ k => simp [fanB]

/-- **The fan is a tree shelling** when `B, c 0, …, c (k + 1)` are distinct. -/
theorem isTreeShelling_fan {k : ℕ} (hcB : ∀ i ≤ k + 1, c i ≠ B)
    (hc : ∀ i ≤ k + 1, ∀ j ≤ k + 1, c i = c j → i = j) :
    IsTreeShelling (fanR B c k) (fanB B c k) := by
  induction k with
  | zero =>
    exact .single (Ne.symm (hcB 0 (by omega))) (Ne.symm (hcB 1 (by omega)))
      (fun h => absurd (hc 0 (by omega) 1 (by omega) h) (by omega))
  | succ k ih =>
    refine .step (ih (fun i hi => hcB i (by omega)) (fun i hi j hj => hc i (by omega) j (by omega)))
      (mem_fanB_last k) fun hz => ?_
    rcases verts2_fanR hz with h | ⟨i, hi, h⟩
    · exact hcB (k + 2) le_rfl h
    · have := hc (k + 2) le_rfl i (by omega) h
      omega

end Fan

section Fan2

variable {B : V} {c : ℕ → V}

lemma pair_left_inj {x y : V} (hx : x ≠ B) (h : ({B, x} : Finset V) = {B, y}) : x = y := by
  have : x ∈ ({B, y} : Finset V) := h ▸ by simp
  simp only [mem_insert, mem_singleton] at this
  exact this.resolve_left hx

/-- The boundary of the fan: `{B, c 0}`, `{B, c (k + 1)}` and the edges `{c i, c (i + 1)}`,
`i ≤ k`. -/
lemma mem_fanB {k : ℕ} (hcB : ∀ i ≤ k + 1, c i ≠ B)
    (hc : ∀ i ≤ k + 1, ∀ j ≤ k + 1, c i = c j → i = j) {e : Finset V} :
    e ∈ fanB B c k ↔ e = {B, c 0} ∨ e = {B, c (k + 1)} ∨ ∃ i ≤ k, e = {c i, c (i + 1)} := by
  induction k with
  | zero => simp [fanB]
  | succ k ih =>
    have ih' := ih (fun i hi => hcB i (by omega)) (fun i hi j hj => hc i (by omega) j (by omega))
    simp only [fanB, mem_insert, mem_erase, ih']
    have hne0 : ({B, c 0} : Finset V) ≠ {B, c (k + 1)} := fun h =>
      absurd (hc 0 (by omega) (k + 1) (by omega) (pair_left_inj (hcB 0 (by omega)) h)) (by omega)
    have hneB : ∀ i ≤ k + 1, ({c i, c (i + 1)} : Finset V) ≠ {B, c (k + 1)} := fun i hi h => by
      have : B ∈ ({c i, c (i + 1)} : Finset V) := h ▸ by simp
      simp only [mem_insert, mem_singleton] at this
      rcases this with h' | h'
      · exact hcB i (by omega) h'.symm
      · exact hcB (i + 1) (by omega) h'.symm
    constructor
    · rintro (rfl | rfl | ⟨hne, rfl | rfl | ⟨i, hi, rfl⟩⟩)
      · exact .inr (.inl rfl)
      · exact .inr (.inr ⟨k + 1, le_rfl, rfl⟩)
      · exact .inl rfl
      · exact absurd rfl hne
      · exact .inr (.inr ⟨i, by omega, rfl⟩)
    · rintro (rfl | rfl | ⟨i, hi, rfl⟩)
      · exact .inr (.inr ⟨hne0, .inl rfl⟩)
      · exact .inl rfl
      · rcases Nat.lt_or_ge i (k + 1) with h | h
        · exact .inr (.inr ⟨hneB i (by omega), .inr (.inr ⟨i, by omega, rfl⟩)⟩)
        · obtain rfl : i = k + 1 := by omega
          exact .inr (.inl rfl)

end Fan2

section Edge

variable {K : Complex3 V} {A B a : V} {c : ℕ → V} {m : ℕ}

/-- The stellar subdivision of `K` at the edge `AB` with apex `a`, for the link cycle
`c 0, …, c (m + 2)` (`c (m + 3) = c 0`), as a complex: the tetrahedra of `K` not containing `AB`
and the cones `{a, A, c i, c (i + 1)}`, `{a, B, c i, c (i + 1)}`. -/
def edgeStar (K : Complex3 V) (A B a : V) (c : ℕ → V) (m : ℕ) : Complex3 V where
  tets := (K.tets.filter (¬ ({A, B} : Finset V) ⊆ ·) ∪
    (range (m + 3)).image (fun i => {a, A, c i, c (i + 1)}) ∪
    (range (m + 3)).image (fun i => {a, B, c i, c (i + 1)})).filter (#· = 4)
  card_eq _ h := (mem_filter.1 h).2

/-- The hypotheses on the edge `AB` and its link cycle. -/
structure EdgeData (K : Complex3 V) (A B : V) (c : ℕ → V) (m : ℕ) : Prop where
  hAB : A ≠ B
  hcA : ∀ i < m + 3, c i ≠ A
  hcB : ∀ i < m + 3, c i ≠ B
  hc : ∀ i < m + 3, ∀ j < m + 3, c i = c j → i = j
  hcyc : c (m + 3) = c 0
  mem : ∀ i < m + 3, ({A, B, c i, c (i + 1)} : Finset V) ∈ K.tets
  star : ∀ t ∈ K.tets, ({A, B} : Finset V) ⊆ t → ∃ i < m + 3, t = {A, B, c i, c (i + 1)}

namespace EdgeData

variable (h : EdgeData K A B c m)
include h

lemma c_succ_ne {i : ℕ} (hi : i < m + 3) : c i ≠ c (i + 1) := fun e => by
  rcases Nat.lt_or_ge (i + 1) (m + 3) with h1 | h1
  · exact absurd (h.hc i hi (i + 1) h1 e) (by omega)
  · obtain rfl : i = m + 2 := by omega
    rw [h.hcyc] at e
    exact absurd (h.hc (m + 2) hi 0 (by omega) e) (by omega)

lemma c_succ_lt {i : ℕ} (hi : i < m + 3) : ∃ j < m + 3, c (i + 1) = c j := by
  rcases Nat.lt_or_ge (i + 1) (m + 3) with h1 | h1
  · exact ⟨i + 1, h1, rfl⟩
  · obtain rfl : i = m + 2 := by omega
    exact ⟨0, by omega, h.hcyc⟩

omit h in
lemma a_ne (ha : a ∉ K.verts) {x : V} (hx : x ∈ K.verts) : a ≠ x := fun e => ha (e ▸ hx)

omit h in
lemma mem_verts_of_tet {t : Finset V} (ht : t ∈ K.tets) {x : V} (hx : x ∈ t) : x ∈ K.verts :=
  mem_biUnion.2 ⟨t, ht, hx⟩

lemma verts_A : A ∈ K.verts := mem_verts_of_tet (h.mem 0 (by omega)) (by simp)
lemma verts_B : B ∈ K.verts := mem_verts_of_tet (h.mem 0 (by omega)) (by simp)
lemma verts_c {i : ℕ} (hi : i < m + 3) : c i ∈ K.verts :=
  mem_verts_of_tet (h.mem i hi) (by simp)
lemma verts_c1 {i : ℕ} (hi : i < m + 3) : c (i + 1) ∈ K.verts :=
  mem_verts_of_tet (h.mem i hi) (by simp)

lemma mem_edgeStar (ha : a ∉ K.verts) {t : Finset V} :
    t ∈ (edgeStar K A B a c m).tets ↔ (t ∈ K.tets ∧ ¬ ({A, B} : Finset V) ⊆ t) ∨
      (∃ i < m + 3, t = {a, A, c i, c (i + 1)}) ∨ ∃ i < m + 3, t = {a, B, c i, c (i + 1)} := by
  simp only [edgeStar, mem_filter, mem_union, mem_image, mem_range]
  constructor
  · rintro ⟨((h1 | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩), -⟩
    · exact .inl h1
    · exact .inr (.inl ⟨i, hi, rfl⟩)
    · exact .inr (.inr ⟨i, hi, rfl⟩)
  · rintro (h1 | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact ⟨.inl (.inl h1), K.card_eq t h1.1⟩
    · refine ⟨.inl (.inr ⟨i, hi, rfl⟩), ?_⟩
      exact card_four (a_ne ha h.verts_A) (a_ne ha (h.verts_c hi)) (a_ne ha (h.verts_c1 hi))
        (Ne.symm (h.hcA i hi)) (fun e => by
          obtain ⟨j, hj, hj'⟩ := h.c_succ_lt hi
          exact h.hcA j hj (hj' ▸ e.symm)) (h.c_succ_ne hi)
    · refine ⟨.inr ⟨i, hi, rfl⟩, ?_⟩
      exact card_four (a_ne ha h.verts_B) (a_ne ha (h.verts_c hi)) (a_ne ha (h.verts_c1 hi))
        (Ne.symm (h.hcB i hi)) (fun e => by
          obtain ⟨j, hj, hj'⟩ := h.c_succ_lt hi
          exact h.hcB j hj (hj' ▸ e.symm)) (h.c_succ_ne hi)


/-- `c (i + 1)` is `c j` for some index `j < m + 3` (`j = i + 1`, or `0` at the end of the cycle). -/
lemma succ_idx {i : ℕ} (hi : i < m + 3) : c (i + 1) = c (if i + 1 < m + 3 then i + 1 else 0) := by
  split_ifs with h1
  · rfl
  · obtain rfl : i = m + 2 := by omega
    exact h.hcyc

omit h in
lemma idx_lt (i : ℕ) : (if i + 1 < m + 3 then i + 1 else 0) < m + 3 := by
  split_ifs <;> omega

/-- Two cycle vertices `c i`, `c j` with `i, j < m + 3` are equal only for `i = j`. -/
lemma idx_eq {i j : ℕ} (hi : i < m + 3) (hj : j < m + 3) (e : c i = c j) : i = j := h.hc i hi j hj e

omit h [DecidableEq V] in
lemma ne_of_mem_notMem {S T : Finset V} {y : V} (hT : y ∈ T) (hS : y ∉ S) : S ≠ T :=
  fun e => hS (e ▸ hT)

lemma eA {i : ℕ} (hi : i < m + 3) :
    insert a (({A, B, c i, c (i + 1)} : Finset V).erase A) = {a, B, c i, c (i + 1)} := by
  have h1 := h.hcA i hi
  have h2 : c (i + 1) ≠ A := by rw [h.succ_idx hi]; exact h.hcA _ (idx_lt i)
  have h3 := h.hAB
  ext y; simp only [mem_insert, mem_erase, mem_singleton]; grind

lemma eB {i : ℕ} (hi : i < m + 3) :
    insert a (({A, B, c i, c (i + 1)} : Finset V).erase B) = {a, A, c i, c (i + 1)} := by
  have h1 := h.hcB i hi
  have h2 : c (i + 1) ≠ B := by rw [h.succ_idx hi]; exact h.hcB _ (idx_lt i)
  have h3 := h.hAB
  ext y; simp only [mem_insert, mem_erase, mem_singleton]; grind

omit h in
lemma AB_sub {i : ℕ} : ({A, B} : Finset V) ⊆ {A, B, c i, c (i + 1)} :=
  insert_subset_insert A (singleton_subset_iff.2 (mem_insert_self B _))

/-- **`edgeStar` is the stellar subdivision of `ofComplex3 K` at the edge `AB`.** -/
theorem ofComplex3_edgeStar (ha : a ∉ K.verts) :
    ofComplex3 (edgeStar K A B a c m) = (ofComplex3 K).starAt {A, B} a := by
  rw [ofComplex3, ofComplex3, starAt_closure]
  congr 1
  ext t
  rw [h.mem_edgeStar ha]
  simp only [mem_union, mem_filter, mem_biUnion, mem_image, mem_insert, mem_singleton]
  constructor
  · rintro (h1 | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact .inl h1
    · exact .inr ⟨_, ⟨h.mem i hi, AB_sub⟩, B, .inr rfl, h.eB hi⟩
    · exact .inr ⟨_, ⟨h.mem i hi, AB_sub⟩, A, .inl rfl, h.eA hi⟩
  · rintro (h1 | ⟨u, ⟨hu, hAB⟩, y, hy, rfl⟩)
    · exact .inl h1
    · obtain ⟨i, hi, rfl⟩ := h.star u hu hAB
      rcases hy with rfl | rfl
      · exact .inr (.inr ⟨i, hi, h.eA hi⟩)
      · exact .inr (.inl ⟨i, hi, h.eB hi⟩)


lemma c0_ne_last : c 0 ≠ c (m + 2) := fun e => absurd (h.idx_eq (by omega) (by omega) e) (by omega)

lemma last_eq : ({a, A, c (m + 2), c (m + 2 + 1)} : Finset V) = {a, c (m + 2), c 0, A} := by
  rw [show m + 2 + 1 = m + 3 from rfl, h.hcyc]; ext; simp; tauto

lemma last_eqB : ({a, B, c (m + 2), c (m + 2 + 1)} : Finset V) = {a, c (m + 2), c 0, B} := by
  rw [show m + 2 + 1 = m + 3 from rfl, h.hcyc]; ext; simp; tauto

/-- The only cone of the star through `c (m + 2)` and `c 0` is the last one. -/
lemma last_idx {i : ℕ} (hi : i < m + 3) (h1 : c (m + 2) = c i ∨ c (m + 2) = c (i + 1))
    (h2 : c 0 = c i ∨ c 0 = c (i + 1)) : i = m + 2 := by
  rw [h.succ_idx hi] at h1 h2
  have hl := idx_lt (m := m) i
  rcases h1 with e1 | e1
  · exact (h.idx_eq (by omega) hi e1).symm
  · have k1 := h.idx_eq (by omega) hl e1
    rcases h2 with e2 | e2
    · have k2 := h.idx_eq (by omega) hi e2
      split_ifs at k1
      all_goals omega
    · have k2 := h.idx_eq (by omega) hl e2
      have := k1.trans k2.symm
      omega

/-- **The 2-3 move on the star** on `{a, c (m + 2), c 0}` with apexes `A` and `B`. -/
lemma isMove23_edgeStar (ha : a ∉ K.verts) :
    IsMove23 (edgeStar K A B a c m) a (c (m + 2)) (c 0) A B := by
  have hc2 := h.verts_c (i := m + 2) (by omega)
  have hc0 := h.verts_c (i := 0) (by omega)
  refine ⟨a_ne ha hc2, a_ne ha hc0, a_ne ha h.verts_A, a_ne ha h.verts_B,
    fun e => h.c0_ne_last e.symm, h.hcA _ (by omega), h.hcB _ (by omega), h.hcA _ (by omega),
    h.hcB _ (by omega), h.hAB, ?_, ?_, ?_, ?_⟩
  · rw [h.mem_edgeStar ha]; exact .inr (.inl ⟨m + 2, by omega, h.last_eq.symm⟩)
  · rw [h.mem_edgeStar ha]; exact .inr (.inr ⟨m + 2, by omega, h.last_eqB.symm⟩)
  · intro t ht hsub
    have hat : a ∈ t := hsub (by simp)
    have h2t : c (m + 2) ∈ t := hsub (by simp)
    have h0t : c 0 ∈ t := hsub (by simp)
    rw [h.mem_edgeStar ha] at ht
    rcases ht with ⟨ht, -⟩ | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · exact absurd (mem_verts_of_tet ht hat) ha
    · left
      simp only [mem_insert, mem_singleton] at h2t h0t
      have hA2 := h.hcA (m + 2) (by omega)
      have hA0 := h.hcA 0 (by omega)
      obtain rfl := h.last_idx hi
        (by rcases h2t with e | e | e | e; exacts [absurd e (a_ne ha hc2).symm, absurd e hA2, .inl e, .inr e])
        (by rcases h0t with e | e | e | e; exacts [absurd e (a_ne ha hc0).symm, absurd e hA0, .inl e, .inr e])
      exact h.last_eq
    · right
      simp only [mem_insert, mem_singleton] at h2t h0t
      have hB2 := h.hcB (m + 2) (by omega)
      have hB0 := h.hcB 0 (by omega)
      obtain rfl := h.last_idx hi
        (by rcases h2t with e | e | e | e; exacts [absurd e (a_ne ha hc2).symm, absurd e hB2, .inl e, .inr e])
        (by rcases h0t with e | e | e | e; exacts [absurd e (a_ne ha hc0).symm, absurd e hB0, .inl e, .inr e])
      exact h.last_eqB
  · intro t ht hsub
    have hAt : A ∈ t := hsub (by simp)
    have hBt : B ∈ t := hsub (by simp)
    rw [h.mem_edgeStar ha] at ht
    rcases ht with ⟨-, hn⟩ | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · exact hn hsub
    · simp only [mem_insert, mem_singleton] at hBt
      rcases hBt with e | e | e | e
      · exact a_ne ha h.verts_B e.symm
      · exact h.hAB e.symm
      · exact h.hcB i hi e.symm
      · rw [h.succ_idx hi] at e; exact h.hcB _ (idx_lt i) e.symm
    · simp only [mem_insert, mem_singleton] at hAt
      rcases hAt with e | e | e | e
      · exact a_ne ha h.verts_A e.symm
      · exact h.hAB e
      · exact h.hcA i hi e.symm
      · rw [h.succ_idx hi] at e; exact h.hcA _ (idx_lt i) e.symm


lemma fan_hcB : ∀ i ≤ m + 2, c i ≠ B := fun i hi => h.hcB i (by omega)

lemma fan_hc : ∀ i ≤ m + 2, ∀ j ≤ m + 2, c i = c j → i = j :=
  fun i hi j hj e => h.hc i (by omega) j (by omega) e

lemma fanR_sub_link : fanR B c (m + 1) ⊆ K.link A := by
  intro σ hσ
  obtain ⟨i, hi, rfl⟩ := mem_fanR.1 hσ
  refine Complex3.mem_link.2 ⟨?_, ?_⟩
  · simp only [mem_insert, mem_singleton, not_or]
    exact ⟨h.hAB, Ne.symm (h.hcA i (by omega)), Ne.symm (h.hcA (i + 1) (by omega))⟩
  · exact h.mem i (by omega)

/-- A cone on `{c i, c (i + 1)}` with `i ≤ m + 1` does not contain both `c (m + 2)` and `c 0`. -/
lemma not_last {i : ℕ} (hi : i ≤ m + 1) {X Y : V} (hX2 : X ≠ c (m + 2)) (hY2 : Y ≠ c (m + 2))
    (hX0 : X ≠ c 0) (hY0 : Y ≠ c 0) {T : Finset V} (h2 : c (m + 2) ∈ T) (h0 : c 0 ∈ T) :
    ({X, Y, c i, c (i + 1)} : Finset V) ≠ T := fun e => by
  rw [← e] at h2 h0
  simp only [mem_insert, mem_singleton] at h2 h0
  have := h.last_idx (i := i) (by omega)
    (by rcases h2 with e' | e' | e' | e'; exacts [absurd e'.symm hX2, absurd e'.symm hY2, .inl e', .inr e'])
    (by rcases h0 with e' | e' | e' | e'; exacts [absurd e'.symm hX0, absurd e'.symm hY0, .inl e', .inr e'])
  omega

/-- The common forward descendant: `a` grown over the fan in the link of `A`. -/
lemma move23_edgeStar (ha : a ∉ K.verts) :
    move23 (edgeStar K A B a c m) (h.isMove23_edgeStar ha) =
      grown K A a (fanR B c (m + 1)) (fanB B c (m + 1)) := by
  have hsh := isTreeShelling_fan (k := m + 1) h.fan_hcB h.fan_hc
  refine complex3_eq fun t => ?_
  rw [mem_grown h.fanR_sub_link hsh.bdry ha]
  simp only [move23, mem_union, mem_insert, mem_singleton, mem_erase, h.mem_edgeStar ha,
    mem_fanB h.fan_hcB h.fan_hc, mem_fanR]
  have hc2 := h.verts_c (i := m + 2) (by omega)
  have hc0 := h.verts_c (i := 0) (by omega)
  have haA := a_ne ha h.verts_A
  have haB := a_ne ha h.verts_B
  have ha2 := a_ne ha hc2
  have ha0 := a_ne ha hc0
  have hA2 := h.hcA (m + 2) (by omega)
  have hA0 := h.hcA 0 (by omega)
  have hB2 := h.hcB (m + 2) (by omega)
  have hB0 := h.hcB 0 (by omega)
  have hAB := h.hAB
  have h02 := h.c0_ne_last
  -- the link triangle left out of the fan
  have hlastK : ({A, B, c (m + 2), c 0} : Finset V) ∈ K.tets := by
    have := h.mem (m + 2) (by omega)
    rwa [show m + 2 + 1 = m + 3 from rfl, h.hcyc] at this
  have hnotfan : ¬ ∃ i ≤ m + 1, ({B, c (m + 2), c 0} : Finset V) = {B, c i, c (i + 1)} := by
    rintro ⟨i, hi, e⟩
    have h2 : c (m + 2) ∈ ({B, c i, c (i + 1)} : Finset V) := e ▸ by simp
    have h0 : c 0 ∈ ({B, c i, c (i + 1)} : Finset V) := e ▸ by simp
    simp only [mem_insert, mem_singleton] at h2 h0
    have := h.last_idx (i := i) (by omega)
      (by rcases h2 with e' | e' | e'; exacts [absurd e' hB2, .inl e', .inr e'])
      (by rcases h0 with e' | e' | e'; exacts [absurd e' hB0, .inl e', .inr e'])
    omega
  simp only [show m + 1 + 1 = m + 2 from rfl]
  constructor
  · rintro ((rfl | rfl | rfl) | ⟨h1, h2, (⟨ht, hnAB⟩ | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)⟩)
    · exact .inr (.inl ⟨{B, c (m + 2)}, .inr (.inl rfl), by set_perm⟩)
    · refine .inr (.inr (.inr ⟨{B, c (m + 2), c 0}, Complex3.mem_link.2 ⟨?_, hlastK⟩, hnotfan,
        by set_perm⟩))
      simp only [mem_insert, mem_singleton, not_or]
      exact ⟨hAB, Ne.symm hA2, Ne.symm hA0⟩
    · exact .inr (.inl ⟨{B, c 0}, .inl rfl, by set_perm⟩)
    · by_cases hAt : A ∈ t
      · have hBt : B ∉ t := fun hB => hnAB (insert_subset hAt (singleton_subset_iff.2 hB))
        refine .inr (.inr (.inr ⟨t.erase A, Complex3.mem_link.2 ⟨notMem_erase A t, by
          rwa [insert_erase hAt]⟩, ?_, insert_erase hAt⟩))
        rintro ⟨i, hi, e⟩
        exact hBt (mem_of_mem_erase (e ▸ (by simp : B ∈ ({B, c i, c (i + 1)} : Finset V))))
      · exact .inl ⟨ht, hAt⟩
    · have hi' : i ≤ m + 1 := by
        by_contra hc
        obtain rfl : i = m + 2 := by omega
        exact h2 h.last_eq
      exact .inr (.inl ⟨{c i, c (i + 1)}, .inr (.inr ⟨i, hi', rfl⟩), by set_perm⟩)
    · have hi' : i ≤ m + 1 := by
        by_contra hc
        obtain rfl : i = m + 2 := by omega
        exact h1 h.last_eqB
      exact .inr (.inr (.inl ⟨{B, c i, c (i + 1)}, ⟨i, hi', rfl⟩, rfl⟩))
  · rintro (⟨ht, hAt⟩ | ⟨e, he, rfl⟩ | ⟨τ, ⟨i, hi, rfl⟩, rfl⟩ | ⟨τ, hτ, hτR, rfl⟩)
    · have hat : a ∉ t := fun h' => ha (mem_verts_of_tet ht h')
      exact .inr ⟨ne_of_mem_notMem (by simp) hat, ne_of_mem_notMem (by simp) hat,
        .inl ⟨ht, fun hs => hAt (hs (by simp))⟩⟩
    · rcases he with rfl | rfl | ⟨i, hi, rfl⟩
      · exact .inl (.inr (.inr (by set_perm)))
      · exact .inl (.inl (by set_perm))
      · have e1 : insert A (insert a ({c i, c (i + 1)} : Finset V)) = {a, A, c i, c (i + 1)} := by
          set_perm
        rw [e1]
        refine .inr ⟨fun e => ?_, h.not_last hi ha2 (Ne.symm hA2) ha0 (Ne.symm hA0) (by simp)
          (by simp), .inr (.inl ⟨i, by omega, rfl⟩)⟩
        have : B ∈ ({a, A, c i, c (i + 1)} : Finset V) := e ▸ by simp
        simp only [mem_insert, mem_singleton] at this
        rcases this with e' | e' | e' | e'
        exacts [haB e'.symm, hAB e'.symm, h.hcB i (by omega) e'.symm,
          h.hcB (i + 1) (by omega) e'.symm]
    · refine .inr ⟨h.not_last hi ha2 (Ne.symm hB2) ha0 (Ne.symm hB0) (by simp) (by simp),
        fun e => ?_, .inr (.inr ⟨i, by omega, rfl⟩)⟩
      have : A ∈ ({a, B, c i, c (i + 1)} : Finset V) := e ▸ by simp
      simp only [mem_insert, mem_singleton] at this
      rcases this with e' | e' | e' | e'
      exacts [haA e'.symm, hAB e', h.hcA i (by omega) e'.symm, h.hcA (i + 1) (by omega) e'.symm]
    · obtain ⟨hAτ, ht⟩ := Complex3.mem_link.1 hτ
      by_cases hBτ : B ∈ τ
      · obtain ⟨i, hi, e⟩ := h.star _ ht (insert_subset_insert A (singleton_subset_iff.2 hBτ))
        have hAi : A ∉ ({B, c i, c (i + 1)} : Finset V) := by
          simp only [mem_insert, mem_singleton, not_or]
          refine ⟨hAB, Ne.symm (h.hcA i hi), fun e' => ?_⟩
          rw [h.succ_idx hi] at e'
          exact h.hcA _ (idx_lt i) e'.symm
        have hτe : τ = {B, c i, c (i + 1)} := insert_left_inj hAτ hAi e
        rcases Nat.lt_or_ge i (m + 2) with hi2 | hi2
        · exact absurd ⟨i, by omega, hτe⟩ hτR
        · obtain rfl : i = m + 2 := by omega
          refine .inl (.inr (.inl ?_))
          rw [e, show m + 2 + 1 = m + 3 from rfl, h.hcyc]
          set_perm
      · have hBt : B ∉ insert A τ := by
          rw [mem_insert, not_or]; exact ⟨Ne.symm hAB, hBτ⟩
        have hat : a ∉ insert A τ := fun h' => ha (mem_verts_of_tet ht h')
        exact .inr ⟨ne_of_mem_notMem (by simp) hat, ne_of_mem_notMem (by simp) hat,
          .inl ⟨ht, fun hs => hBt (hs (by simp))⟩⟩

end EdgeData


/-- **The star of an edge is a common forward descendant.** For an edge `AB` of `K` with link cycle
`c 0, …, c (m + 2)` (`EdgeData`), a vertex `A` whose link is a 2-sphere, and a fresh apex `a`, the
complex `edgeStar K A B a c m` is the stellar subdivision of `ofComplex3 K` at `AB`, and it and `K`
have a common forward descendant: `a` grown over the fan around `B` in the link of `A`
(`forwardMoves_grown`) from `K`, and one 2-3 move from the star. -/
theorem commonForward_starAt_edge {K : Complex3 V} {A B a : V} {c : ℕ → V} {m : ℕ}
    (h : EdgeData K A B c m) (hL : IsSphere2 (K.link A)) (ha : a ∉ K.verts) :
    ofComplex3 (edgeStar K A B a c m) = (ofComplex3 K).starAt {A, B} a ∧
      CommonForward K (edgeStar K A B a c m) := by
  refine ⟨h.ofComplex3_edgeStar ha, grown K A a (fanR B c (m + 1)) (fanB B c (m + 1)),
    forwardMoves_grown (isTreeShelling_fan h.fan_hcB h.fan_hc) h.fanR_sub_link hL.closed ha, ?_⟩
  rw [← h.move23_edgeStar ha]
  exact .single (.m23 (h.isMove23_edgeStar ha))

/-- **Non-vacuity of `commonForward_starAt_edge`**: the edge `01` of the boundary of the
4-simplex, with link cycle `2, 3, 4`, subdivided with the new vertex `5`. -/
theorem commonForward_starAt_edge_bdry4 :
    CommonForward bdry4 (edgeStar bdry4 0 1 5 (fun i => 2 + i % 3) 0) := by
  have h : EdgeData bdry4 0 1 (fun i => 2 + i % 3) 0 :=
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
  have hlink : bdry4.link 0 = bdry 1 2 3 4 := by decide
  have hsph : IsSphere2 (bdry4.link 0) := by
    rw [hlink]
    exact isSphere2_bdry (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact (commonForward_starAt_edge h hsph (by decide)).2

end Edge

end Lightlike.PR
