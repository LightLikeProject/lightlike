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

lemma rot_cyc (β : Fin n) (k : ℕ) : (p.rot β).cyc k = p.cyc (k + β) := by
  simp only [cyc, rot]
  congr 1
  ext
  simp [Fin.val_add, Nat.add_mod]

lemma carrier_rot (β : Fin n) : (p.rot β).carrier = p.carrier := by
  ext x
  simp only [carrier, Set.mem_iUnion, edge_rot]
  constructor
  · rintro ⟨i, hi⟩; exact ⟨i + β, hi⟩
  · rintro ⟨i, hi⟩; exact ⟨i - β, by simpa using hi⟩

/-- The right part is the left part of the shifted polygon. -/
lemma right_eq_left_rot {b : ℕ} (hbn : b < n) :
    p.right b = (p.rot ⟨b, hbn⟩).left (n - b) := by
  funext j
  show p.cyc (b + j) = (p.rot ⟨b, hbn⟩).cyc j
  rw [rot_cyc, Nat.add_comm]

/-- **The right part of a split simple polygon is simple.** -/
theorem isSimple_right (hs : p.IsSimple) {b : ℕ} (hb : 2 ≤ b) (hbn : b + 2 ≤ n)
    (hopen : ∀ q ∈ openSegment ℝ (p.cyc 0) (p.cyc b), q ∉ p.carrier) : (p.right b).IsSimple := by
  have hb' : b < n := by omega
  rw [right_eq_left_rot hb']
  refine isSimple_left (isSimple_rot hs ⟨b, hb'⟩) (by omega) (by omega) ?_
  intro q hq
  rw [carrier_rot]
  have e1 : (p.rot ⟨b, hb'⟩).cyc 0 = p.cyc b := by rw [rot_cyc]; simp
  have e2 : (p.rot ⟨b, hb'⟩).cyc (n - b) = p.cyc 0 := by
    rw [rot_cyc]
    simp only [Nat.sub_add_cancel hb'.le]
    simpa using p.cyc_self_add 0
  rw [e1, e2, openSegment_symm] at hq
  exact hopen q hq

lemma mem_carrier_iff (hn : 2 ≤ n) {x : ℝ × ℝ} :
    x ∈ p.carrier ↔ ∃ k, k < n ∧ x ∈ segment ℝ (p.cyc k) (p.cyc (k + 1)) := by
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    exact ⟨i, i.2, by rwa [edge_eq_cyc hn] at hi⟩
  · rintro ⟨k, hk, hx⟩
    exact Set.mem_iUnion.2 ⟨⟨k, hk⟩, by rw [edge_eq_cyc hn]; exact hx⟩

/-- The carrier of the left part: the first `b` edges and the diagonal. -/
lemma mem_carrier_left_iff {b : ℕ} (hb : 1 ≤ b) {x : ℝ × ℝ} :
    x ∈ (p.left b).carrier ↔
      (∃ k, k < b ∧ x ∈ segment ℝ (p.cyc k) (p.cyc (k + 1))) ∨ x ∈ segment ℝ (p.cyc b) (p.cyc 0) := by
  have hl : ∀ k, (p.left b).cyc k = p.cyc (k % (b + 1)) := fun k => rfl
  rw [mem_carrier_iff (by omega : 2 ≤ b + 1)]
  constructor
  · rintro ⟨k, hk, hx⟩
    rw [hl, hl] at hx
    rcases Nat.lt_or_ge k b with h | h
    · left
      refine ⟨k, h, ?_⟩
      rwa [Nat.mod_eq_of_lt (by omega : k < b + 1),
        Nat.mod_eq_of_lt (by omega : k + 1 < b + 1)] at hx
    · right
      have : k = b := by omega
      subst this
      rwa [Nat.mod_eq_of_lt (by omega : k < k + 1), Nat.mod_self] at hx
  · rintro (⟨k, hk, hx⟩ | hx)
    · refine ⟨k, by omega, ?_⟩
      rw [hl, hl, Nat.mod_eq_of_lt (by omega : k < b + 1),
        Nat.mod_eq_of_lt (by omega : k + 1 < b + 1)]
      exact hx
    · refine ⟨b, by omega, ?_⟩
      rw [hl, hl, Nat.mod_eq_of_lt (by omega : b < b + 1), Nat.mod_self]
      exact hx

/-- The carrier of the right part: the edges from `b` on, and the diagonal. -/
lemma mem_carrier_right_iff {b : ℕ} (hbn : b < n) {x : ℝ × ℝ} :
    x ∈ (p.right b).carrier ↔
      (∃ k, b ≤ k ∧ k < n ∧ x ∈ segment ℝ (p.cyc k) (p.cyc (k + 1))) ∨
        x ∈ segment ℝ (p.cyc 0) (p.cyc b) := by
  have hr : ∀ k, (p.right b).cyc k = p.cyc (b + k % (n - b + 1)) := fun k => rfl
  rw [mem_carrier_iff (by omega : 2 ≤ n - b + 1)]
  constructor
  · rintro ⟨k, hk, hx⟩
    rw [hr, hr] at hx
    rcases Nat.lt_or_ge k (n - b) with h | h
    · left
      refine ⟨b + k, by omega, by omega, ?_⟩
      rwa [Nat.mod_eq_of_lt (by omega : k < n - b + 1),
        Nat.mod_eq_of_lt (by omega : k + 1 < n - b + 1), ← Nat.add_assoc] at hx
    · right
      have : k = n - b := by omega
      subst this
      rw [Nat.mod_eq_of_lt (by omega : n - b < n - b + 1), Nat.mod_self] at hx
      have e : b + (n - b) = n + 0 := by omega
      rwa [e, p.cyc_self_add 0, Nat.add_zero] at hx
  · rintro (⟨k, hk1, hk2, hx⟩ | hx)
    · refine ⟨k - b, by omega, ?_⟩
      rw [hr, hr, Nat.mod_eq_of_lt (by omega : k - b < n - b + 1),
        Nat.mod_eq_of_lt (by omega : k - b + 1 < n - b + 1), ← Nat.add_assoc,
        Nat.add_sub_cancel' hk1]
      exact hx
    · refine ⟨n - b, by omega, ?_⟩
      rw [hr, hr, Nat.mod_eq_of_lt (by omega : n - b < n - b + 1), Nat.mod_self]
      have e : b + (n - b) = n + 0 := by omega
      rw [e, p.cyc_self_add 0, Nat.add_zero]
      exact hx

/-- The two parts together cover the polygon and the diagonal, and nothing else. -/
lemma mem_carrier_left_or_right (hn : 2 ≤ n) {b : ℕ} (hb : 1 ≤ b) (hbn : b < n) {x : ℝ × ℝ} :
    x ∈ (p.left b).carrier ∨ x ∈ (p.right b).carrier ↔
      x ∈ p.carrier ∨ x ∈ segment ℝ (p.cyc 0) (p.cyc b) := by
  rw [mem_carrier_left_iff hb, mem_carrier_right_iff hbn, mem_carrier_iff hn, segment_symm ℝ (p.cyc b) (p.cyc 0)]
  constructor
  · rintro ((⟨k, hk, hx⟩ | hx) | (⟨k, hk1, hk2, hx⟩ | hx))
    · exact Or.inl ⟨k, by omega, hx⟩
    · exact Or.inr hx
    · exact Or.inl ⟨k, hk2, hx⟩
    · exact Or.inr hx
  · rintro (⟨k, hk, hx⟩ | hx)
    · rcases Nat.lt_or_ge k b with h | h
      · exact Or.inl (Or.inl ⟨k, h, hx⟩)
      · exact Or.inr (Or.inl ⟨k, h, hk, hx⟩)
    · exact Or.inl (Or.inr hx)

lemma cyc_mem_carrier (hn : 2 ≤ n) {k : ℕ} (hk : k < n) : p.cyc k ∈ p.carrier :=
  (mem_carrier_iff hn).2 ⟨k, hk, left_mem_segment ℝ _ _⟩

/-- **Splitting the inside along an interior diagonal.** If the open diagonal from the vertex `0`
to the vertex `b` of a simple polygon lies in the inside, the inside of the polygon is the union
of the insides of the two parts and the open diagonal, and the two insides are disjoint. -/
theorem inside_split (hs : p.IsSimple) {b : ℕ} (hb : 2 ≤ b) (hbn : b + 2 ≤ n)
    (hD : openSegment ℝ (p.cyc 0) (p.cyc b) ⊆ p.inside) :
    Disjoint (p.left b).inside (p.right b).inside ∧
      p.inside = (p.left b).inside ∪ (p.right b).inside ∪ openSegment ℝ (p.cyc 0) (p.cyc b) := by
  have hn : 2 ≤ n := by omega
  have hopen : ∀ q ∈ openSegment ℝ (p.cyc 0) (p.cyc b), q ∉ p.carrier := fun q hq hqc =>
    hqc |> fun h => (hD hq).1 h
  have hsL := isSimple_left hs hb hbn hopen
  have hsR := isSimple_right hs hb hbn hopen
  set L := p.left b with hL
  set R := p.right b with hR
  have hadd : ∀ x, L.parity x + R.parity x = p.parity x := fun x =>
    parity_left_add_right p (by omega) (by omega) x
  have hcar := fun x => mem_carrier_left_or_right (p := p) hn (b := b) (by omega) (by omega) (x := x)
  have h0 : p.cyc 0 ∈ p.carrier := cyc_mem_carrier hn (by omega)
  have hb' : p.cyc b ∈ p.carrier := cyc_mem_carrier hn (by omega)
  -- a point off the carrier and off the open diagonal is off both parts
  have hoff : ∀ x, x ∉ p.carrier → x ∉ openSegment ℝ (p.cyc 0) (p.cyc b) →
      x ∉ L.carrier ∧ x ∉ R.carrier := by
    intro x hx1 hx2
    have : x ∉ L.carrier ∧ x ∉ R.carrier := by
      by_contra hcon
      have h : x ∈ L.carrier ∨ x ∈ R.carrier := by
        by_cases h1 : x ∈ L.carrier
        · exact Or.inl h1
        · exact Or.inr (by by_contra h2; exact hcon ⟨h1, h2⟩)
      rcases (hcar x).1 h with h | h
      · exact hx1 h
      · rw [← insert_endpoints_openSegment] at h
        rcases h with rfl | rfl | h
        · exact hx1 h0
        · exact hx1 hb'
        · exact hx2 h
    exact this
  have hz : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  -- the points inside both parts are off the polygon and outside it
  have hbothin : ∀ x, x ∈ L.inside → x ∈ R.inside → x ∈ p.outside := by
    intro x h1 h2
    have hxc : x ∉ p.carrier := fun hc => by
      rcases (hcar x).2 (Or.inl hc) with h | h
      · exact h1.1 h
      · exact h2.1 h
    refine ⟨hxc, ?_⟩
    rw [← hadd, h1.2, h2.2]; decide
  have hbothout : ∀ x, x ∈ L.outside → x ∈ R.outside → x ∈ p.outside := by
    intro x h1 h2
    have hxc : x ∉ p.carrier := fun hc => by
      rcases (hcar x).2 (Or.inl hc) with h | h
      · exact h1.1 h
      · exact h2.1 h
    refine ⟨hxc, ?_⟩
    rw [← hadd, h1.2, h2.2]; decide
  have hout : ∀ x, x ∈ p.outside → (x ∈ L.outside ∧ x ∈ R.outside) ∨
      (x ∈ L.inside ∧ x ∈ R.inside) := by
    intro x hx
    have hxD : x ∉ openSegment ℝ (p.cyc 0) (p.cyc b) := fun h =>
      (Set.disjoint_left.1 (disjoint_outside_inside p)) hx (hD h)
    obtain ⟨hxL, hxR⟩ := hoff x hx.1 hxD
    have hadd' := hadd x
    rw [hx.2] at hadd'
    rcases hz (L.parity x) with h1 | h1 <;> rcases hz (R.parity x) with h2 | h2
    · exact Or.inl ⟨⟨hxL, h1⟩, ⟨hxR, h2⟩⟩
    · rw [h1, h2] at hadd'; exact absurd hadd' (by decide)
    · rw [h1, h2] at hadd'; exact absurd hadd' (by decide)
    · exact Or.inr ⟨⟨hxL, h1⟩, ⟨hxR, h2⟩⟩
  -- no point is inside both parts
  have hdisj : Disjoint L.inside R.inside := by
    rw [Set.disjoint_left]
    intro x hxL hxR
    have hpre : IsPreconnected p.outside := isPreconnected_outside hs
    have hO : IsOpen (L.outside ∩ R.outside) := (isOpen_outside L).inter (isOpen_outside R)
    have hW : IsOpen (L.inside ∩ R.inside) := (isOpen_inside L).inter (isOpen_inside R)
    have hdj : Disjoint (L.outside ∩ R.outside) (L.inside ∩ R.inside) := by
      rw [Set.disjoint_left]
      rintro y ⟨hy1, -⟩ ⟨hy2, -⟩
      exact (Set.disjoint_left.1 (disjoint_outside_inside L)) hy1 hy2
    have hcov : p.outside ⊆ (L.outside ∩ R.outside) ∪ (L.inside ∩ R.inside) := fun y hy => by
      rcases hout y hy with h | h
      · exact Or.inl h
      · exact Or.inr h
    rcases hpre.subset_or_subset hO hW hdj hcov with h | h
    · exact (Set.disjoint_left.1 (disjoint_outside_inside L)) (hbothin x hxL hxR |> fun hp => (h hp).1) hxL
    · exact not_isBounded_outside p ((isBounded_inside L).subset (fun y hy => (h hy).1))
  -- a point inside a part is off the other part
  have hcross1 : ∀ y, y ∈ L.inside → y ∉ R.carrier := by
    intro y hy hyc
    have hcl := carrier_subset_closure_class hsR 1 hyc
    obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 hcl _ (isOpen_inside L) hy
    exact Set.disjoint_left.1 hdisj hz1 hz2
  have hcross2 : ∀ y, y ∈ R.inside → y ∉ L.carrier := by
    intro y hy hyc
    have hcl := carrier_subset_closure_class hsL 1 hyc
    obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 hcl _ (isOpen_inside R) hy
    exact Set.disjoint_left.1 hdisj hz2 hz1
  refine ⟨hdisj, ?_⟩
  ext x
  constructor
  · intro hx
    by_cases hxD : x ∈ openSegment ℝ (p.cyc 0) (p.cyc b)
    · exact Or.inr hxD
    · obtain ⟨hxL, hxR⟩ := hoff x hx.1 hxD
      have hadd' := hadd x
      rw [hx.2] at hadd'
      rcases hz (L.parity x) with h1 | h1 <;> rcases hz (R.parity x) with h2 | h2
      · rw [h1, h2] at hadd'; exact absurd hadd' (by decide)
      · exact Or.inl (Or.inr ⟨hxR, h2⟩)
      · exact Or.inl (Or.inl ⟨hxL, h1⟩)
      · rw [h1, h2] at hadd'; exact absurd hadd' (by decide)
  · rintro ((hx | hx) | hx)
    · have hxR : x ∉ R.carrier := hcross1 x hx
      have hxp : x ∉ p.carrier := fun hc => by
        rcases (hcar x).2 (Or.inl hc) with h | h
        · exact hx.1 h
        · exact hxR h
      refine ⟨hxp, ?_⟩
      have hr0 : R.parity x = 0 := by
        rcases hz (R.parity x) with h | h
        · exact h
        · exact absurd ⟨hxR, h⟩ (fun hh => Set.disjoint_left.1 hdisj hx hh)
      rw [← hadd, hx.2, hr0]; decide
    · have hxL : x ∉ L.carrier := hcross2 x hx
      have hxp : x ∉ p.carrier := fun hc => by
        rcases (hcar x).2 (Or.inl hc) with h | h
        · exact hxL h
        · exact hx.1 h
      refine ⟨hxp, ?_⟩
      have hl0 : L.parity x = 0 := by
        rcases hz (L.parity x) with h | h
        · exact h
        · exact absurd ⟨hxL, h⟩ (fun hh => Set.disjoint_left.1 hdisj hh hx)
      rw [← hadd, hx.2, hl0]; decide
    · exact hD hx

lemma parity_rot (β : Fin n) (x : ℝ × ℝ) : (p.rot β).parity x = p.parity x := by
  unfold parity
  rw [← Equiv.sum_comp (Equiv.addRight β) (fun i => ind (CrossesRay (p i) (p (finRotate n i)) x))]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [rot, Equiv.coe_addRight, finRotate_add]

lemma inside_rot (β : Fin n) : (p.rot β).inside = p.inside := by
  ext x; simp only [inside, carrier_rot, parity_rot]

lemma outside_rot (β : Fin n) : (p.rot β).outside = p.outside := by
  ext x; simp only [outside, carrier_rot, parity_rot]

/-- **A simple polygon with at least four vertices splits along an interior diagonal.** After a
cyclic shift of the vertices, the diagonal runs from the vertex `0` to a vertex `b` with
`2 ≤ b ≤ n - 2`, the two parts are simple, and the inside is the union of their insides and the
open diagonal. -/
theorem exists_split (hs : p.IsSimple) (hn : 4 ≤ n) :
    ∃ a : Fin n, ∃ b : ℕ, 2 ≤ b ∧ b + 2 ≤ n ∧ ((p.rot a).left b).IsSimple ∧
      ((p.rot a).right b).IsSimple ∧
      Disjoint ((p.rot a).left b).inside ((p.rot a).right b).inside ∧
      (p.rot a).inside = ((p.rot a).left b).inside ∪ ((p.rot a).right b).inside ∪
        openSegment ℝ ((p.rot a).cyc 0) ((p.rot a).cyc b) := by
  obtain ⟨a, c, hac, h1, h2, hD⟩ := exists_diagonal hs hn
  -- shift so that `a` becomes the vertex `0`
  set q := p.rot a with hq
  have hqs : q.IsSimple := isSimple_rot hs a
  set b := ((c - a : Fin n) : ℕ) with hb
  have hcyc0 : q.cyc 0 = p a := by
    rw [hq, rot_cyc, Nat.zero_add, p.cyc_of_lt a.2]
  have hcycb : q.cyc b = p c := by
    rw [hq, rot_cyc, ← p.cyc_mod]
    have : (c - a + a : Fin n) = c := sub_add_cancel c a
    have h := congrArg Fin.val this
    rw [Fin.val_add] at h
    rw [show (b + (a : ℕ)) % n = c from h]
    exact p.cyc_of_lt c.2
  -- the position of `c` relative to `a`
  have ha := a.2
  have hc := c.2
  have hbv : ((a : ℕ) ≤ c ∧ b = (c : ℕ) - a) ∨ ((c : ℕ) < a ∧ b = c + n - a) := by
    have h : ((c - a : Fin n) : ℕ) = ((n - (a : ℕ)) + c) % n := Fin.val_sub c a
    rcases Nat.lt_or_ge (c : ℕ) a with hlt | hge
    · right
      refine ⟨hlt, ?_⟩
      rw [hb, h]
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    · left
      refine ⟨hge, ?_⟩
      rw [hb, h]
      have : n - (a : ℕ) + c = n + (c - a) := by omega
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hfa : ((finRotate n a : Fin n) : ℕ) = ((a : ℕ) + 1) % n := finRotate_val (by omega) a
  have hfc : ((finRotate n c : Fin n) : ℕ) = ((c : ℕ) + 1) % n := finRotate_val (by omega) c
  have hbne : (a : ℕ) ≠ c := fun h => hac (Fin.ext h)
  have hne1 : ((a : ℕ) + 1) % n ≠ c := fun h => h1 (Fin.ext (by rw [hfa]; exact h))
  have hne2 : ((c : ℕ) + 1) % n ≠ a := fun h => h2 (Fin.ext (by rw [hfc]; exact h))
  have key : ∀ m : ℕ, m < n → (m + 1) % n = if m + 1 < n then m + 1 else 0 := by
    intro m hm
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · have : m + 1 = n := by omega
      rw [this, Nat.mod_self]
  rw [key _ ha] at hne1
  rw [key _ hc] at hne2
  have hb2 : 2 ≤ b ∧ b + 2 ≤ n := by
    split_ifs at hne1 hne2 <;> omega
  obtain ⟨hb2, hb3⟩ := hb2
  have hopen : ∀ x ∈ openSegment ℝ (q.cyc 0) (q.cyc b), x ∉ q.carrier := by
    intro x hx hxc
    rw [hcyc0, hcycb] at hx
    rw [hq, carrier_rot] at hxc
    exact (hD hx).1 hxc
  have hD' : openSegment ℝ (q.cyc 0) (q.cyc b) ⊆ q.inside := by
    rw [hcyc0, hcycb, hq, inside_rot]; exact hD
  obtain ⟨hdis, hspl⟩ := inside_split hqs hb2 hb3 hD'
  exact ⟨a, b, hb2, hb3, isSimple_left hqs hb2 hb3 hopen,
    isSimple_right hqs hb2 hb3 hopen, hdis, hspl⟩

/-- **The two parts meet only along the diagonal.** The common points of the carriers of the left
and right parts lie on the closed diagonal. -/
lemma carrier_left_inter_right (hs : p.IsSimple) {b : ℕ} (hb : 2 ≤ b) (hbn : b + 2 ≤ n)
    {x : ℝ × ℝ} (hxL : x ∈ (p.left b).carrier) (hxR : x ∈ (p.right b).carrier) :
    x ∈ segment ℝ (p.cyc 0) (p.cyc b) := by
  have hn : 2 ≤ n := by omega
  obtain ⟨hs1, hs2, hs3⟩ := (isSimple_iff_nat hn).1 hs
  rw [mem_carrier_left_iff (by omega)] at hxL
  rw [mem_carrier_right_iff (by omega)] at hxR
  rcases hxL with ⟨k, hk, hx1⟩ | hx1
  · rcases hxR with ⟨k', hk1, hk2, hx2⟩ | hx2
    · by_cases hadj : k' = k + 1
      · have h := hs3 k (by omega)
        have e : (k + 1) % n = k' := by rw [hadj]; exact Nat.mod_eq_of_lt (by omega)
        rw [e] at h
        have hx : x ∈ segment ℝ (p.cyc k) (p.cyc (k + 1)) ∩
            segment ℝ (p.cyc k') (p.cyc (k' + 1)) := ⟨hx1, hx2⟩
        rw [h] at hx
        have : k + 1 = b := by omega
        rw [Set.mem_singleton_iff.1 hx, this]
        exact right_mem_segment ℝ _ _
      · by_cases hadj' : k' + 1 = n ∧ k = 0
        · have h := hs3 k' hk2
          have e : (k' + 1) % n = k := by rw [hadj'.1, Nat.mod_self]; exact hadj'.2.symm
          rw [e] at h
          have hx : x ∈ segment ℝ (p.cyc k') (p.cyc (k' + 1)) ∩
              segment ℝ (p.cyc k) (p.cyc (k + 1)) := ⟨hx2, hx1⟩
          rw [h] at hx
          have e0 : p.cyc n = p.cyc 0 := by simpa using p.cyc_self_add 0
          rw [Set.mem_singleton_iff.1 hx, hadj'.1, e0]
          exact left_mem_segment ℝ _ _
        · exfalso
          have hd := hs2 k k' (by omega) hk2 (by omega)
            (by rw [Nat.mod_eq_of_lt (by omega : k + 1 < n)]; omega)
            (by
              intro h
              rcases Nat.lt_or_ge (k' + 1) n with h3 | h3
              · rw [Nat.mod_eq_of_lt h3] at h; omega
              · have : k' + 1 = n := by omega
                rw [this, Nat.mod_self] at h
                exact hadj' ⟨this, h.symm⟩)
          exact Set.disjoint_left.1 hd hx1 hx2
    · exact hx2
  · rw [segment_symm]; exact hx1

/-- A point inside a polygon is off the carrier of any simple polygon whose inside is disjoint
from it. -/
lemma not_mem_carrier_of_disjoint_inside {m k : ℕ} [NeZero m] [NeZero k] {A : Polygon m}
    {B : Polygon k} (hsB : B.IsSimple) (hdis : Disjoint A.inside B.inside) {y : ℝ × ℝ}
    (hy : y ∈ A.inside) : y ∉ B.carrier := by
  intro hyc
  have hcl := carrier_subset_closure_class hsB 1 hyc
  obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 hcl _ (isOpen_inside A) hy
  exact Set.disjoint_left.1 hdis hz1 hz2

end Polygon

end Lightlike.PL

