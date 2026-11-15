import Lightlike.PL.PolygonInside

/-!
# The extreme vertex of a simple polygon

The first step towards a diagonal in the inside of a simple polygon: the vertex that is smallest
for the lexicographic order (leftmost, ties broken by lowest) is a corner of the convex hull, and
its two edges are not collinear.

## Main results

* `Lightlike.PL.Polygon.exists_extreme`: a vertex lexicographically below all vertices
* `Lightlike.PL.Polygon.corner_cross_ne`: at such a vertex the two edges are not parallel
-/

open Set

namespace Lightlike.PL
namespace Polygon

variable {n : ℕ} {p : Polygon n}

/-- `a` is **lexicographically positive**: to the right of the vertical line through the origin,
or on it and above the origin. -/
def LexPos (a : ℝ × ℝ) : Prop := 0 < a.1 ∨ (a.1 = 0 ∧ 0 < a.2)

/-- The point `x` is lexicographically at most `y`. -/
def LexLE (x y : ℝ × ℝ) : Prop := x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2)

/-- The lexicographic order is total. -/
lemma lexLE_total (x y : ℝ × ℝ) : LexLE x y ∨ LexLE y x := by
  unfold LexLE
  rcases lt_trichotomy x.1 y.1 with h | h | h
  · exact .inl (.inl h)
  · rcases le_total x.2 y.2 with h2 | h2
    · exact .inl (.inr ⟨h, h2⟩)
    · exact .inr (.inr ⟨h.symm, h2⟩)
  · exact .inr (.inl h)

lemma lexLE_trans {x y z : ℝ × ℝ} (h1 : LexLE x y) (h2 : LexLE y z) : LexLE x z := by
  unfold LexLE at *
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · exact .inl (h1.trans h2)
  · exact .inl (h2 ▸ h1)
  · exact .inl (h1 ▸ h2)
  · exact .inr ⟨h1.trans h2, h1'.trans h2'⟩

/-- **A polygon has a lexicographically smallest vertex.** -/
theorem exists_extreme [NeZero n] (p : Polygon n) : ∃ j, ∀ i, LexLE (p j) (p i) := by
  classical
  have key : ∀ (s : Finset (Fin n)), s.Nonempty → ∃ j ∈ s, ∀ i ∈ s, LexLE (p j) (p i) := by
    intro s hs
    induction s using Finset.induction_on with
    | empty => exact absurd hs (by simp)
    | insert a s ha ih =>
      rcases s.eq_empty_or_nonempty with rfl | hne
      · exact ⟨a, by simp, fun i hi => by
          obtain rfl : i = a := by simpa using hi
          exact .inr ⟨rfl, le_rfl⟩⟩
      · obtain ⟨j, hj, hjmin⟩ := ih hne
        rcases lexLE_total (p a) (p j) with h | h
        · refine ⟨a, by simp, fun i hi => ?_⟩
          rcases Finset.mem_insert.1 hi with rfl | hi
          · exact .inr ⟨rfl, le_rfl⟩
          · exact lexLE_trans h (hjmin i hi)
        · refine ⟨j, Finset.mem_insert_of_mem hj, fun i hi => ?_⟩
          rcases Finset.mem_insert.1 hi with rfl | hi
          · exact h
          · exact hjmin i hi
  obtain ⟨j, -, hj⟩ := key Finset.univ ⟨⟨0, NeZero.pos n⟩, Finset.mem_univ _⟩
  exact ⟨j, fun i => hj i (Finset.mem_univ i)⟩


/-- A point lexicographically above `v` and different from it is lexicographically positive
relative to `v`. -/
lemma lexPos_sub {v z : ℝ × ℝ} (hz : LexLE v z) (hne : z ≠ v) : LexPos (z - v) := by
  unfold LexLE at hz
  unfold LexPos
  rcases hz with h | ⟨h1, h2⟩
  · left; simp only [Prod.fst_sub]; linarith
  · right
    refine ⟨by simp only [Prod.fst_sub]; linarith, ?_⟩
    simp only [Prod.snd_sub]
    rcases h2.lt_or_eq with h2 | h2
    · linarith
    · exact absurd (Prod.ext h1.symm h2.symm) hne

lemma LexPos.fst_nonneg {a : ℝ × ℝ} (h : LexPos a) : 0 ≤ a.1 := by
  rcases h with h | ⟨h, -⟩ <;> linarith

/-- **Everything strictly to the left of the extreme vertex is outside.** The open half-plane to
the left of a vertex that is lexicographically smallest misses the polygon, is connected and is
unbounded, so it lies in the outside. -/
theorem left_subset_outside [NeZero n] {j : Fin n}
    (hext : ∀ i, LexLE (p j) (p i)) : {x : ℝ × ℝ | x.1 < (p j).1} ⊆ p.outside := by
  set L : Set (ℝ × ℝ) := {x | x.1 < (p j).1} with hL
  have hcar : ∀ x ∈ p.carrier, (p j).1 ≤ x.1 := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    have hge : ∀ i, (p j).1 ≤ (p i).1 := fun i => by
      rcases hext i with h | ⟨h, -⟩
      · exact h.le
      · exact h.le
    have hconv : Convex ℝ {y : ℝ × ℝ | (p j).1 ≤ y.1} := by
      intro x hx y hy a b ha hb hab
      have hx' : (p j).1 ≤ x.1 := hx
      have hy' : (p j).1 ≤ y.1 := hy
      show (p j).1 ≤ (a • x + b • y).1
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      obtain rfl : b = 1 - a := by linarith
      nlinarith [mul_nonneg ha (sub_nonneg.2 hx'), mul_nonneg hb (sub_nonneg.2 hy')]
    exact (hconv.segment_subset (hge i) (hge _)) hi
  have hLc : L ⊆ p.carrierᶜ := fun x hx hxc => by
    have := hcar x hxc; have hx' : x.1 < (p j).1 := hx; linarith
  have hLconv : Convex ℝ L := by
    intro x hx y hy a b ha hb hab
    have hx' : x.1 < (p j).1 := hx
    have hy' : y.1 < (p j).1 := hy
    show (a • x + b • y).1 < (p j).1
    simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    obtain rfl : b = 1 - a := by linarith
    rcases ha.eq_or_lt with rfl | ha'
    · simpa using hy'
    · nlinarith [mul_pos ha' (sub_pos.2 hx'), mul_nonneg hb (sub_nonneg.2 hy'.le)]
  have hLpre : IsPreconnected L := hLconv.isPreconnected
  have hLub : ¬ Bornology.IsBounded L := by
    intro hb
    obtain ⟨R, hR⟩ := hb.subset_closedBall (0 : ℝ × ℝ)
    have hmem : ((p j).1 - |R| - |(p j).1| - 1, (0 : ℝ)) ∈ L := by
      show (p j).1 - |R| - |(p j).1| - 1 < (p j).1
      linarith [abs_nonneg R, abs_nonneg (p j).1]
    have := hR hmem
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def] at this
    have h2 : |(p j).1 - |R| - |(p j).1| - 1| ≤ R := by
      have := (le_max_left _ _).trans this
      simpa using this
    have h3 : (p j).1 ≤ |(p j).1| := le_abs_self _
    have h4 : R ≤ |R| := le_abs_self _
    have h5 := neg_abs_le ((p j).1 - |R| - |(p j).1| - 1)
    linarith [abs_nonneg R, abs_nonneg (p j).1, abs_nonneg ((p j).1 - |R| - |(p j).1| - 1)]
  have hcov : L ⊆ p.outside ∪ p.inside := by rw [← compl_carrier_eq]; exact hLc
  rcases hLpre.subset_or_subset (isOpen_outside p) (isOpen_inside p) (disjoint_outside_inside p)
      hcov with h | h
  · exact h
  · exact absurd ((isBounded_inside p).subset h) hLub


/-- Two nonzero lexicographically positive vectors with vanishing cross product are positive
multiples of each other. -/
lemma exists_pos_smul {a b : ℝ × ℝ} (ha : LexPos a) (hb : LexPos b)
    (hc : a.1 * b.2 - a.2 * b.1 = 0) : ∃ c : ℝ, 0 < c ∧ b = c • a := by
  rcases ha with ha | ⟨ha1, ha2⟩
  · have hb1 : 0 < b.1 := by
      rcases hb with hb | ⟨hb1, hb2⟩
      · exact hb
      · exfalso
        rw [hb1] at hc
        nlinarith
    refine ⟨b.1 / a.1, div_pos hb1 ha, ?_⟩
    ext
    · simp only [Prod.smul_fst, smul_eq_mul]; field_simp
    · simp only [Prod.smul_snd, smul_eq_mul]
      field_simp
      linarith
  · have hb1 : b.1 = 0 := by
      rw [ha1] at hc
      nlinarith
    have hb2 : 0 < b.2 := by
      rcases hb with hb | ⟨-, hb2⟩
      · linarith
      · exact hb2
    refine ⟨b.2 / a.2, div_pos hb2 ha2, ?_⟩
    ext
    · simp only [Prod.smul_fst, smul_eq_mul, hb1, ha1]; simp
    · simp only [Prod.smul_snd, smul_eq_mul]; field_simp

/-- A point at parameter `c ∈ [0,1]` from `v` towards `u` lies on the segment. -/
lemma mem_segment_of_sub_eq {v u z : ℝ × ℝ} {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1)
    (hz : z - v = c • (u - v)) : z ∈ segment ℝ v u := by
  have hz' : z = (1 - c) • v + c • u := by
    have : z = v + c • (u - v) := by rw [← hz]; abel
    rw [this]; ext <;> simp <;> ring
  exact ⟨1 - c, c, by linarith, h0, by ring, hz'.symm⟩

/-- **The corner at the extreme vertex is not degenerate.** At a lexicographically smallest vertex
`p j` of a simple polygon, the edge vectors to the neighbouring vertices are not parallel. -/
theorem corner_cross_ne (hs : p.IsSimple) {j : Fin n} (hext : ∀ i, LexLE (p j) (p i)) :
    ((p ((finRotate n).symm j)).1 - (p j).1) * ((p (finRotate n j)).2 - (p j).2) -
      ((p ((finRotate n).symm j)).2 - (p j).2) * ((p (finRotate n j)).1 - (p j).1) ≠ 0 := by
  intro hc
  set k := (finRotate n).symm j with hk
  have hkj : finRotate n k = j := by rw [hk]; exact Equiv.apply_symm_apply _ _
  set v := p j with hv
  set u := p k with hu
  set w := p (finRotate n j) with hw
  have huv : u ≠ v := by have := hs.1 k; rwa [hkj] at this
  have hvw : v ≠ w := hs.1 j
  have hpos : ∀ z : ℝ × ℝ, LexLE v z → z ≠ v → LexPos (z - v) := by
    intro z hz hne
    unfold LexLE at hz
    unfold LexPos
    rcases hz with h | ⟨h1, h2⟩
    · left; simp only [Prod.fst_sub]; linarith
    · right
      refine ⟨by simp only [Prod.fst_sub]; linarith, ?_⟩
      simp only [Prod.snd_sub]
      rcases h2.lt_or_eq with h2 | h2
      · linarith
      · exact absurd (Prod.ext h1.symm h2.symm) hne
  obtain ⟨c, hc0, hbc⟩ := exists_pos_smul (hpos u (hext k) huv) (hpos w (hext _) hvw.symm) hc
  have hinter := hs.2.2 k
  rw [hkj] at hinter
  have e1 : p.edge k = segment ℝ u v := by simp only [edge, hkj, hu, hv]
  have e2 : p.edge j = segment ℝ v w := rfl
  rw [e1, e2] at hinter
  rcases le_or_gt c 1 with h1 | h1
  · have hwm : w ∈ segment ℝ v u := mem_segment_of_sub_eq hc0.le h1 hbc
    have : w ∈ segment ℝ u v ∩ segment ℝ v w :=
      ⟨by rwa [segment_symm], right_mem_segment ℝ v w⟩
    rw [hinter] at this
    exact hvw (Set.mem_singleton_iff.1 this).symm
  · have hum : u ∈ segment ℝ v w := by
      refine mem_segment_of_sub_eq (inv_nonneg.2 hc0.le) (inv_le_one_of_one_le₀ h1.le) ?_
      rw [hbc, smul_smul, inv_mul_cancel₀ hc0.ne', one_smul]
    have : u ∈ segment ℝ u v ∩ segment ℝ v w := ⟨left_mem_segment ℝ u v, hum⟩
    rw [hinter] at this
    exact huv (Set.mem_singleton_iff.1 this)

/-- A ray is unchanged by positive rescaling of its direction. -/
lemma ray0_smul {s : ℝ} (hs : 0 < s) (a : ℝ × ℝ) : ray0 (s • a) = ray0 a := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t * s, mul_nonneg ht hs.le, by rw [smul_smul]⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t / s, div_nonneg ht hs.le, by rw [smul_smul, div_mul_cancel₀ _ hs.ne']⟩

/-- The directions of two rays that start along edges at a vertex and lie in the carrier up to
a small ball are among the two rays of the local description. -/
lemma dir_mem_rays {v d a b : ℝ × ℝ} {ρ : ℝ} (hρ : 0 < ρ) (hd : d ≠ 0)
    (hcar : ∀ z ∈ Metric.ball v ρ, z ∈ p.carrier ↔ z - v ∈ ray0 a ∪ ray0 b)
    (hin : ∀ t : ℝ, 0 < t → t ≤ 1 → v + t • d ∈ p.carrier) : d ∈ ray0 a ∪ ray0 b := by
  set N := ‖d‖ with hN
  have hN0 : 0 ≤ N := norm_nonneg _
  set t := min 1 (ρ / (2 * (N + 1))) with ht
  have hden : 0 < 2 * (N + 1) := by positivity
  have ht0 : 0 < t := lt_min one_pos (div_pos hρ hden)
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t ≤ ρ / (2 * (N + 1)) := min_le_right _ _
  have hball : v + t • d ∈ Metric.ball v ρ := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0.le]
    have h1 : t * (2 * (N + 1)) ≤ ρ := by
      have := mul_le_mul_of_nonneg_right ht2 hden.le
      rwa [div_mul_cancel₀ _ hden.ne'] at this
    nlinarith
  have hm := (hcar _ hball).1 (hin t ht0 ht1)
  rw [add_sub_cancel_left] at hm
  have key : ∀ c : ℝ × ℝ, t • d ∈ ray0 c → d ∈ ray0 c := by
    rintro c ⟨r, hr, hrc⟩
    refine ⟨r / t, div_nonneg hr ht0.le, ?_⟩
    have : d = t⁻¹ • (t • d) := by rw [smul_smul, inv_mul_cancel₀ ht0.ne', one_smul]
    rw [this, hrc, smul_smul, div_eq_inv_mul]
  rcases hm with hm | hm
  · exact Or.inl (key _ hm)
  · exact Or.inr (key _ hm)

/-- **The carrier near a vertex is the union of its two edge rays.** At a vertex of a simple
polygon whose edge directions `u - v` and `w - v` are not parallel, the carrier agrees, in a
small ball around the vertex, with the union of the two rays from the vertex along the edges. -/
theorem carrier_near_vertex (hs : p.IsSimple) {j : Fin n}
    (hc : cross (p ((finRotate n).symm j) - p j) (p (finRotate n j) - p j) ≠ 0) :
    ∃ ρ > 0, ∀ z ∈ Metric.ball (p j) ρ, z ∈ p.carrier ↔
      z - p j ∈ ray0 (p ((finRotate n).symm j) - p j) ∪ ray0 (p (finRotate n j) - p j) := by
  set k := (finRotate n).symm j with hk
  have hkj : finRotate n k = j := by rw [hk]; exact Equiv.apply_symm_apply _ _
  set v := p j with hv
  set u := p k with hu
  set w := p (finRotate n j) with hw
  have huv : u ≠ v := by have := hs.1 k; rwa [hkj] at this
  have hvw : v ≠ w := hs.1 j
  obtain ⟨a, b, ha, hb, hnp, ρ, hρ, hcar⟩ := local_data_vertex hs (j := k) (w := v) (by rw [hkj])
  have hd1 : u - v ∈ ray0 a ∪ ray0 b := by
    refine dir_mem_rays hρ (sub_ne_zero.2 huv) hcar fun t ht0 ht1 => ?_
    have : v + t • (u - v) ∈ p.edge k := by
      have e1 : p.edge k = segment ℝ u v := by simp only [edge, hkj, hu, hv]
      rw [e1, segment_symm]
      have := mem_segment_of_sub_eq (v := v) (u := u) (z := v + t • (u - v)) ht0.le ht1
        (by rw [add_sub_cancel_left])
      exact this
    exact Set.mem_iUnion.2 ⟨k, this⟩
  have hd2 : w - v ∈ ray0 a ∪ ray0 b := by
    refine dir_mem_rays hρ (sub_ne_zero.2 hvw.symm) hcar fun t ht0 ht1 => ?_
    have : v + t • (w - v) ∈ p.edge j :=
      mem_segment_of_sub_eq (v := v) (u := w) (z := v + t • (w - v)) ht0.le ht1
        (by rw [add_sub_cancel_left])
    exact Set.mem_iUnion.2 ⟨j, this⟩
  have hcr : ∀ (s r : ℝ) (c : ℝ × ℝ), u - v = s • c → w - v = r • c → False := by
    intro s r c h1 h2
    apply hc
    rw [h1, h2]; simp [cross]; ring
  refine ⟨ρ, hρ, fun z hz => ?_⟩
  rw [hcar z hz]
  have hset : ray0 (u - v) ∪ ray0 (w - v) = ray0 a ∪ ray0 b := by
    obtain ⟨s1, hs1, h1⟩ | ⟨s1, hs1, h1⟩ := hd1 <;> obtain ⟨s2, hs2, h2⟩ | ⟨s2, hs2, h2⟩ := hd2
    · exact (hcr s1 s2 a h1 h2).elim
    · have p1 : 0 < s1 := hs1.lt_of_ne (fun h => huv (by
        rw [← h, zero_smul] at h1; exact (sub_eq_zero.1 h1)))
      have p2 : 0 < s2 := hs2.lt_of_ne (fun h => hvw (by
        rw [← h, zero_smul] at h2; exact (sub_eq_zero.1 h2).symm))
      rw [h1, h2, ray0_smul p1, ray0_smul p2]
    · have p1 : 0 < s1 := hs1.lt_of_ne (fun h => huv (by
        rw [← h, zero_smul] at h1; exact (sub_eq_zero.1 h1)))
      have p2 : 0 < s2 := hs2.lt_of_ne (fun h => hvw (by
        rw [← h, zero_smul] at h2; exact (sub_eq_zero.1 h2).symm))
      rw [h1, h2, ray0_smul p1, ray0_smul p2, Set.union_comm]
    · exact (hcr s1 s2 b h1 h2).elim
  rw [hset]


end Polygon
end Lightlike.PL
