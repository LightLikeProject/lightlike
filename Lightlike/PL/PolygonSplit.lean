import Lightlike.PL.PolygonDiagonal3

/-!
# Splitting a polygon along a diagonal

The crossing test of the horizontal ray does not depend on the direction in which an edge is
traversed. This is what makes the parities of the two polygons obtained by cutting along a
diagonal add up to the parity of the original polygon: the diagonal is an edge of both, traversed
in opposite directions, and contributes twice.

## Main results

* `Lightlike.PL.crossesRay_symm`: the ray crosses `[u, v]` exactly when it crosses `[v, u]`
-/

namespace Lightlike.PL

/-- The abscissa of the line through two points at a given height does not depend on the order of
the points, when they are at different heights. -/
lemma xAt_symm {u v : ℝ × ℝ} (h : u.2 ≠ v.2) (t : ℝ) : xAt u v t = xAt v u t := by
  unfold xAt
  have h1 : v.2 - u.2 ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  have h2 : u.2 - v.2 ≠ 0 := sub_ne_zero.2 h
  field_simp
  ring

/-- **The ray crosses an edge independently of the direction of the edge.** -/
theorem crossesRay_symm (u v x : ℝ × ℝ) : CrossesRay u v x ↔ CrossesRay v u x := by
  unfold CrossesRay
  by_cases h : u.2 = v.2
  · constructor <;> rintro ⟨h1 | h1, -⟩ <;> exfalso <;> linarith [h1.1, h1.2]
  · rw [xAt_symm h]
    exact and_congr_left' (or_comm)

/-- The successor of an index in `Fin m` as a natural number. -/
lemma finRotate_val {m : ℕ} (hm : 2 ≤ m) (i : Fin m) :
    ((finRotate m i : Fin m) : ℕ) = (i + 1) % m := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [finRotate_apply, Fin.val_add]
  have h1 : ((1 : Fin (m' + 1)) : ℕ) = 1 := by
    simp [Nat.mod_eq_of_lt (show 1 < m' + 1 by omega)]
  rw [h1]

namespace Polygon

variable {n : ℕ} [NeZero n] (p : Polygon n)

/-- The vertices of a polygon read cyclically, as a function on all natural numbers. -/
def cyc (i : ℕ) : ℝ × ℝ := p ⟨i % n, Nat.mod_lt _ (NeZero.pos n)⟩

lemma cyc_of_lt {i : ℕ} (hi : i < n) : p.cyc i = p ⟨i, hi⟩ := by
  simp [cyc, Nat.mod_eq_of_lt hi]

lemma cyc_mod (i : ℕ) : p.cyc (i % n) = p.cyc i := by simp [cyc]

lemma cyc_self_add (i : ℕ) : p.cyc (n + i) = p.cyc i := by
  simp [cyc]

/-- The part of the polygon from the vertex `0` to the vertex `b`, closed by the diagonal from
`b` back to `0`. -/
def left (b : ℕ) : Polygon (b + 1) := fun i => p.cyc i

/-- The part of the polygon from the vertex `b` to the vertex `0` (that is `n`), closed by the
diagonal from `0` back to `b`. -/
def right (b : ℕ) : Polygon (n - b + 1) := fun j => p.cyc (b + j)

/-- One summand of the parity: the ray crosses the edge from the vertex `i` to the vertex `i+1`,
read cyclically. -/
noncomputable def crossTerm (x : ℝ × ℝ) (i : ℕ) : ZMod 2 :=
  ind (CrossesRay (p.cyc i) (p.cyc (i + 1)) x)

/-- The parity as a sum over the natural numbers below `n`. -/
lemma parity_eq_sum_range (hn : 2 ≤ n) (x : ℝ × ℝ) :
    p.parity x = ∑ i ∈ Finset.range n, p.crossTerm x i := by
  unfold parity
  rw [← Fin.sum_univ_eq_sum_range (fun i => p.crossTerm x i) n]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : p i = p.cyc i := by rw [p.cyc_of_lt i.2]
  have h2 : p (finRotate n i) = p.cyc (i + 1) := by
    simp only [cyc]; congr 1; ext; exact finRotate_val hn i
  rw [crossTerm, ← h1, ← h2]

/-- The parity of the left part. -/
lemma parity_left {b : ℕ} (hb : 1 ≤ b) (x : ℝ × ℝ) :
    (p.left b).parity x =
      ∑ i ∈ Finset.range b, p.crossTerm x i + ind (CrossesRay (p.cyc b) (p.cyc 0) x) := by
  have hb2 : 2 ≤ b + 1 := by omega
  have h1 : (p.left b).parity x =
      ∑ i : Fin (b + 1), ind (CrossesRay (p.cyc i) (p.cyc ((i + 1) % (b + 1))) x) := by
    unfold parity
    refine Finset.sum_congr rfl fun i _ => ?_
    have : (p.left b) (finRotate (b + 1) i) = p.cyc ((i + 1) % (b + 1)) := by
      show p.cyc ((finRotate (b + 1) i : Fin (b + 1)) : ℕ) = _
      rw [finRotate_val hb2]
    rw [this]; rfl
  rw [h1, Fin.sum_univ_eq_sum_range
    (fun i => ind (CrossesRay (p.cyc i) (p.cyc ((i + 1) % (b + 1))) x)) (b + 1),
    Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    have : (i + 1) % (b + 1) = i + 1 := Nat.mod_eq_of_lt (by have := Finset.mem_range.1 hi; omega)
    simp only [crossTerm, this]
  · simp

/-- The parity of the right part. -/
lemma parity_right {b : ℕ} (hbn : b < n) (x : ℝ × ℝ) :
    (p.right b).parity x =
      ∑ i ∈ Finset.range (n - b), p.crossTerm x (b + i) +
        ind (CrossesRay (p.cyc 0) (p.cyc b) x) := by
  have hb2 : 2 ≤ n - b + 1 := by omega
  have h1 : (p.right b).parity x =
      ∑ i : Fin (n - b + 1), ind (CrossesRay (p.cyc (b + i))
        (p.cyc (b + (i + 1) % (n - b + 1))) x) := by
    unfold parity
    refine Finset.sum_congr rfl fun i _ => ?_
    have : (p.right b) (finRotate (n - b + 1) i) = p.cyc (b + (i + 1) % (n - b + 1)) := by
      show p.cyc (b + ((finRotate (n - b + 1) i : Fin (n - b + 1)) : ℕ)) = _
      rw [finRotate_val hb2]
    rw [this]; rfl
  rw [h1, Fin.sum_univ_eq_sum_range
    (fun i => ind (CrossesRay (p.cyc (b + i)) (p.cyc (b + (i + 1) % (n - b + 1))) x)) (n - b + 1),
    Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    have : (i + 1) % (n - b + 1) = i + 1 := Nat.mod_eq_of_lt (by have := Finset.mem_range.1 hi; omega)
    simp only [crossTerm, this, Nat.add_assoc]
  · have e1 : b + (n - b) = n + 0 := by omega
    have e2 : (n - b + 1) % (n - b + 1) = 0 := Nat.mod_self _
    rw [e1, e2, p.cyc_self_add 0, Nat.add_zero]

/-- **The parities of the two parts add up to the parity of the polygon.** The diagonal is an
edge of both parts, traversed in opposite directions, so it is counted twice. -/
theorem parity_left_add_right {b : ℕ} (hb : 1 ≤ b) (hbn : b < n) (x : ℝ × ℝ) :
    (p.left b).parity x + (p.right b).parity x = p.parity x := by
  have hn : 2 ≤ n := by omega
  rw [parity_left p hb, parity_right p hbn, p.parity_eq_sum_range hn]
  have hsplit := Finset.sum_range_add (fun i => p.crossTerm x i) b (n - b)
  rw [Nat.add_sub_cancel' hbn.le] at hsplit
  rw [hsplit]
  have hd : ind (CrossesRay (p.cyc b) (p.cyc 0) x) = ind (CrossesRay (p.cyc 0) (p.cyc b) x) :=
    ind_congr (crossesRay_symm _ _ _)
  rw [hd]
  have h2 := CharTwo.add_self_eq_zero (ind (CrossesRay (p.cyc 0) (p.cyc b) x))
  linear_combination h2

variable {p}

omit [NeZero n] in
/-- **A vertex lies on an edge only if it is an end of the edge.** -/
lemma eq_or_eq_of_vertex_mem_edge (hs : p.IsSimple) {i e : Fin n} (h : p i ∈ p.edge e) :
    i = e ∨ i = finRotate n e := by
  by_cases hie : i = e
  · exact Or.inl hie
  · right
    have hi : p i ∈ p.edge i := left_mem_segment ℝ _ _
    rcases edge_meet_cases hs hie hi h with ⟨h1, h2⟩ | ⟨h1, -⟩
    · exact absurd (by rw [h1]; exact h2 : p i = p (finRotate n i)) (hs.1 i)
    · exact h1.symm

omit [NeZero n] in
/-- **The vertices of a simple polygon are distinct.** -/
lemma vertex_injective (hs : p.IsSimple) : Function.Injective p := by
  intro i j hij
  by_contra hne
  have hj : p j ∈ p.edge j := left_mem_segment ℝ _ _
  have hi : p i ∈ p.edge i := left_mem_segment ℝ _ _
  rcases eq_or_eq_of_vertex_mem_edge hs (hij ▸ hj : p i ∈ p.edge j) with h | h
  · exact hne h
  · exact hs.1 j (by rw [← h, hij])

/-- The polygon with its vertices shifted cyclically by `β`. -/
def rot (p : Polygon n) (β : Fin n) : Polygon n := fun i => p (i + β)

omit [NeZero n] in
lemma finRotate_add (i β : Fin n) : finRotate n (i + β) = finRotate n i + β := by
  rw [finRotate_apply, finRotate_apply, add_right_comm]

omit [NeZero n] in
lemma edge_rot (p : Polygon n) (β i : Fin n) : (p.rot β).edge i = p.edge (i + β) := by
  simp only [edge, rot, finRotate_add]

omit [NeZero n] in
/-- A cyclic shift of the vertices of a simple polygon is simple. -/
lemma isSimple_rot (hs : p.IsSimple) (β : Fin n) : (p.rot β).IsSimple := by
  refine ⟨fun i => ?_, fun i j hij h1 h2 => ?_, fun i => ?_⟩
  · have := hs.1 (i + β)
    rw [finRotate_add] at this
    exact this
  · rw [edge_rot, edge_rot]
    refine hs.2.1 (i + β) (j + β) (fun h => hij (add_right_cancel h)) ?_ ?_
    · rw [finRotate_add]; exact fun h => h1 (add_right_cancel h)
    · rw [finRotate_add]; exact fun h => h2 (add_right_cancel h)
  · have := hs.2.2 (i + β)
    rw [finRotate_add] at this
    rw [edge_rot, edge_rot]
    exact this

/-- The edge `i`, in terms of the cyclic reading of the vertices. -/
lemma edge_eq_cyc (hn : 2 ≤ n) (i : Fin n) : p.edge i = segment ℝ (p.cyc i) (p.cyc (i + 1)) := by
  have h1 : p i = p.cyc i := by rw [p.cyc_of_lt i.2]
  have h2 : p (finRotate n i) = p.cyc (i + 1) := by
    simp only [cyc]; congr 1; ext; exact finRotate_val hn i
  simp only [edge, h1, h2]

/-- **Simplicity in terms of natural-number indices.** -/
lemma isSimple_iff_nat (hn : 2 ≤ n) : p.IsSimple ↔
    (∀ i < n, p.cyc i ≠ p.cyc (i + 1)) ∧
    (∀ i j, i < n → j < n → i ≠ j → (i + 1) % n ≠ j → (j + 1) % n ≠ i →
      Disjoint (segment ℝ (p.cyc i) (p.cyc (i + 1))) (segment ℝ (p.cyc j) (p.cyc (j + 1)))) ∧
    (∀ i < n, segment ℝ (p.cyc i) (p.cyc (i + 1)) ∩
      segment ℝ (p.cyc ((i + 1) % n)) (p.cyc ((i + 1) % n + 1)) = {p.cyc (i + 1)}) := by
  have hv' : ∀ i (hi : i < n), ((finRotate n ⟨i, hi⟩ : Fin n) : ℕ) = (i + 1) % n :=
    fun i hi => finRotate_val hn ⟨i, hi⟩
  have hfr : ∀ i (hi : i < n), finRotate n ⟨i, hi⟩ = ⟨(i + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩ :=
    fun i hi => Fin.ext (hv' i hi)
  have hc' : ∀ i (hi : i < n), p (finRotate n ⟨i, hi⟩) = p.cyc (i + 1) := fun i hi => by
    rw [hfr i hi]; rfl
  have e' : ∀ i (hi : i < n), p.edge ⟨i, hi⟩ = segment ℝ (p.cyc i) (p.cyc (i + 1)) := by
    intro i hi
    show segment ℝ (p ⟨i, hi⟩) (p (finRotate n ⟨i, hi⟩)) = _
    rw [hc' i hi, ← p.cyc_of_lt hi]
  have e'' : ∀ i (hi : i < n), p.edge (finRotate n ⟨i, hi⟩) =
      segment ℝ (p.cyc ((i + 1) % n)) (p.cyc ((i + 1) % n + 1)) := by
    intro i hi
    rw [hfr i hi]; exact e' _ (Nat.mod_lt _ (NeZero.pos n))
  constructor
  · intro hs
    refine ⟨fun i hi => ?_, fun i j hi hj hij h1 h2 => ?_, fun i hi => ?_⟩
    · have := hs.1 ⟨i, hi⟩
      rwa [hc' i hi, show p ⟨i, hi⟩ = p.cyc i from (p.cyc_of_lt hi).symm] at this
    · have := hs.2.1 ⟨i, hi⟩ ⟨j, hj⟩ (fun h => hij (Fin.mk.inj h))
        (fun h => h1 (by have := congrArg Fin.val h; rw [hv' i hi] at this; exact this))
        (fun h => h2 (by have := congrArg Fin.val h; rw [hv' j hj] at this; exact this))
      rwa [e' i hi, e' j hj] at this
    · have := hs.2.2 ⟨i, hi⟩
      rwa [e' i hi, e'' i hi, hc' i hi] at this
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i => ?_, fun i j hij hi hj => ?_, fun i => ?_⟩
    · obtain ⟨i, hi⟩ := i
      rw [hc' i hi, show p ⟨i, hi⟩ = p.cyc i from (p.cyc_of_lt hi).symm]
      exact h1 i hi
    · obtain ⟨i, hi'⟩ := i
      obtain ⟨j, hj'⟩ := j
      rw [e' i hi', e' j hj']
      refine h2 i j hi' hj' (fun h => hij (Fin.ext h)) ?_ ?_
      · intro h; apply hi; exact Fin.ext (by rw [hv' i hi']; exact h)
      · intro h; apply hj; exact Fin.ext (by rw [hv' j hj']; exact h)
    · obtain ⟨i, hi'⟩ := i
      rw [e' i hi', e'' i hi', hc' i hi']
      exact h3 i hi'

lemma segment_cyc_subset_carrier (hn : 2 ≤ n) {k : ℕ} (hk : k < n) :
    segment ℝ (p.cyc k) (p.cyc (k + 1)) ⊆ p.carrier := by
  intro x hx
  refine Set.mem_iUnion.2 ⟨⟨k, hk⟩, ?_⟩
  rw [edge_eq_cyc hn]; exact hx

/-- A vertex on the edge `[cyc k, cyc (k+1)]` is one of its ends. -/
lemma vertex_mem_seg (hs : p.IsSimple) (hn : 2 ≤ n) {j k : ℕ} (hj : j < n) (hk : k < n)
    (h : p.cyc j ∈ segment ℝ (p.cyc k) (p.cyc (k + 1))) : j = k ∨ j = (k + 1) % n := by
  have h' : p ⟨j, hj⟩ ∈ p.edge ⟨k, hk⟩ := by
    rw [edge_eq_cyc hn, ← p.cyc_of_lt hj]; exact h
  rcases eq_or_eq_of_vertex_mem_edge hs h' with h1 | h1
  · left; exact Fin.mk.inj h1
  · right
    have := congrArg Fin.val h1
    rw [finRotate_val hn] at this
    exact this

/-- **The closed diagonal meets an edge only at its ends.** If the open diagonal from the vertex
`0` to the vertex `b` misses the carrier, then an edge `k` meeting the closed diagonal does so at
`cyc 0` or `cyc b`, and `cyc 0` is on it only when `k = 0` or `k + 1 = n`, `cyc b` only when
`k = b` or `k + 1 = b`. -/
lemma diag_inter (hn : 2 ≤ n) {b : ℕ}
    (hopen : ∀ q ∈ openSegment ℝ (p.cyc 0) (p.cyc b), q ∉ p.carrier) {k : ℕ} (hk : k < n) :
    segment ℝ (p.cyc k) (p.cyc (k + 1)) ∩ segment ℝ (p.cyc b) (p.cyc 0) ⊆ {p.cyc 0, p.cyc b} := by
  rintro x ⟨hx1, hx2⟩
  rw [segment_symm, ← insert_endpoints_openSegment] at hx2
  rcases hx2 with rfl | rfl | hx2
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact absurd (segment_cyc_subset_carrier hn hk hx1) (hopen x hx2)

/-- **The left part of a split simple polygon is simple.** The diagonal from the vertex `0` to the
vertex `b` has its open segment off the carrier. -/
theorem isSimple_left (hs : p.IsSimple) {b : ℕ} (hb : 2 ≤ b) (hbn : b + 2 ≤ n)
    (hopen : ∀ q ∈ openSegment ℝ (p.cyc 0) (p.cyc b), q ∉ p.carrier) : (p.left b).IsSimple := by
  have hn : 2 ≤ n := by omega
  have hs' := (isSimple_iff_nat hn).1 hs
  obtain ⟨hs1, hs2, hs3⟩ := hs'
  have hl : ∀ k, (p.left b).cyc k = p.cyc (k % (b + 1)) := fun k => rfl
  have hd : ∀ k, k < n → segment ℝ (p.cyc k) (p.cyc (k + 1)) ∩ segment ℝ (p.cyc b) (p.cyc 0) ⊆
      {p.cyc 0, p.cyc b} := fun k hk => diag_inter (p := p) hn (b := b) hopen hk
  have hv0 : ∀ k (hk : k < n), p.cyc 0 ∈ segment ℝ (p.cyc k) (p.cyc (k + 1)) → k = 0 ∨ k + 1 = n := by
    intro k hk h
    rcases vertex_mem_seg hs hn (by omega : 0 < n) hk h with h1 | h1
    · left; omega
    · right
      have : (k + 1) % n = 0 := h1.symm
      rcases Nat.lt_or_ge (k + 1) n with h2 | h2
      · rw [Nat.mod_eq_of_lt h2] at this; omega
      · omega
  have hvb : ∀ k (hk : k < n), p.cyc b ∈ segment ℝ (p.cyc k) (p.cyc (k + 1)) → k = b ∨ k + 1 = b := by
    intro k hk h
    rcases vertex_mem_seg hs hn (by omega : b < n) hk h with h1 | h1
    · left; omega
    · right
      rcases Nat.lt_or_ge (k + 1) n with h2 | h2
      · rw [Nat.mod_eq_of_lt h2] at h1; omega
      · have : k + 1 = n := by omega
        rw [this, Nat.mod_self] at h1; omega
  rw [isSimple_iff_nat (by omega : 2 ≤ b + 1)]
  refine ⟨fun i hi => ?_, fun i j hi hj hij h1 h2 => ?_, fun i hi => ?_⟩
  · simp only [hl]
    rcases Nat.lt_or_ge i b with h | h
    · rw [Nat.mod_eq_of_lt (by omega : i < b + 1), Nat.mod_eq_of_lt (by omega : i + 1 < b + 1)]
      exact hs1 i (by omega)
    · have : i = b := by omega
      subst this
      rw [Nat.mod_eq_of_lt (by omega : i < i + 1), Nat.mod_self]
      rw [p.cyc_of_lt (by omega : i < n), p.cyc_of_lt (by omega : 0 < n)]
      intro h'
      have := vertex_injective hs h'
      have := Fin.mk.inj this
      omega
  · -- disjointness of non-neighbouring edges
    simp only [hl]
    have hdis : ∀ k, 1 ≤ k → k + 2 ≤ b → Disjoint (segment ℝ (p.cyc k) (p.cyc (k + 1)))
        (segment ℝ (p.cyc b) (p.cyc 0)) := by
      intro k hk1 hk2
      rw [Set.disjoint_left]
      intro x hx1 hx2
      rcases hd k (by omega) ⟨hx1, hx2⟩ with rfl | rfl
      · rcases hv0 k (by omega) hx1 with h | h <;> omega
      · rcases hvb k (by omega) hx1 with h | h <;> omega
    rcases Nat.lt_or_ge i b with hi' | hi'
    · rcases Nat.lt_or_ge j b with hj' | hj'
      · rw [Nat.mod_eq_of_lt (by omega : i < b + 1), Nat.mod_eq_of_lt (by omega : i + 1 < b + 1),
          Nat.mod_eq_of_lt (by omega : j < b + 1), Nat.mod_eq_of_lt (by omega : j + 1 < b + 1)]
        rw [Nat.mod_eq_of_lt (by omega : i + 1 < b + 1)] at h1
        rw [Nat.mod_eq_of_lt (by omega : j + 1 < b + 1)] at h2
        exact hs2 i j (by omega) (by omega) hij
          (by rw [Nat.mod_eq_of_lt (by omega : i + 1 < n)]; exact h1)
          (by rw [Nat.mod_eq_of_lt (by omega : j + 1 < n)]; exact h2)
      · have : j = b := by omega
        subst this
        rw [Nat.mod_eq_of_lt (by omega : i < j + 1), Nat.mod_eq_of_lt (by omega : i + 1 < j + 1),
          Nat.mod_eq_of_lt (by omega : j < j + 1), Nat.mod_self]
        rw [Nat.mod_eq_of_lt (by omega : i + 1 < j + 1)] at h1
        rw [Nat.mod_self] at h2
        exact hdis i (by omega) (by omega)
    · have hib : i = b := by omega
      subst hib
      rcases Nat.lt_or_ge j i with hj' | hj'
      · rw [Nat.mod_eq_of_lt (by omega : j < i + 1), Nat.mod_eq_of_lt (by omega : j + 1 < i + 1),
          Nat.mod_eq_of_lt (by omega : i < i + 1), Nat.mod_self]
        rw [Nat.mod_self] at h1
        rw [Nat.mod_eq_of_lt (by omega : j + 1 < i + 1)] at h2
        exact (hdis j (by omega) (by omega)).symm
      · omega
  · -- consecutive edges
    simp only [hl]
    rcases Nat.lt_or_ge (i + 1) b with hi' | hi'
    · have hA : (i + 1) % (b + 1) = i + 1 := Nat.mod_eq_of_lt (by omega)
      have hB : (i + 1 + 1) % (b + 1) = i + 1 + 1 := Nat.mod_eq_of_lt (by omega)
      have hC : i % (b + 1) = i := Nat.mod_eq_of_lt (by omega)
      simp only [hA, hB, hC]
      have := hs3 i (by omega)
      rwa [Nat.mod_eq_of_lt (by omega : i + 1 < n)] at this
    · rcases Nat.lt_or_ge (i + 1) (b + 1) with hi'' | hi''
      · -- the edge before the diagonal
        have hib : i + 1 = b := by omega
        have hA : (i + 1) % (b + 1) = b := by rw [hib]; exact Nat.mod_eq_of_lt (by omega)
        have hB : (b + 1) % (b + 1) = 0 := Nat.mod_self _
        have hC : i % (b + 1) = i := Nat.mod_eq_of_lt (by omega)
        have hD : b % (b + 1) = b := Nat.mod_eq_of_lt (by omega)
        have hB' : (b + 1) % (b + 1) = 0 := hB
        simp only [hA, hB, hC, hD]
        refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨?_, left_mem_segment ℝ _ _⟩, ?_⟩
        · have : p.cyc b ∈ segment ℝ (p.cyc i) (p.cyc (i + 1)) := by
            rw [hib]; exact right_mem_segment ℝ _ _
          rw [hib] at this; exact this
        · rintro x ⟨hx1, hx2⟩
          have hx1' : x ∈ segment ℝ (p.cyc i) (p.cyc (i + 1)) := by rw [hib]; exact hx1
          rcases hd i (by omega) ⟨hx1', hx2⟩ with rfl | rfl
          · rcases hv0 i (by omega) hx1' with h | h <;> omega
          · rfl
      · -- the diagonal
        have hib : i = b := by omega
        subst hib
        have hA : (i + 1) % (i + 1) = 0 := Nat.mod_self _
        have hB : 0 % (i + 1) = 0 := Nat.zero_mod _
        have hC : i % (i + 1) = i := Nat.mod_eq_of_lt (by omega)
        have hD : (0 + 1) % (i + 1) = 1 := by rw [Nat.zero_add]; exact Nat.mod_eq_of_lt (by omega)
        simp only [hA, hB, hC, hD, Nat.zero_add]
        refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨right_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩, ?_⟩
        · rintro x ⟨hx1, hx2⟩
          have := hd 0 (by omega) ⟨by simpa using hx2, hx1⟩
          rcases this with rfl | rfl
          · rfl
          · have h0 : p.cyc i ∈ segment ℝ (p.cyc 0) (p.cyc (0 + 1)) := by simpa using hx2
            rcases hvb 0 (by omega) h0 with h | h <;> omega

end Polygon

end Lightlike.PL

