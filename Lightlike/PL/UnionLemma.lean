import Lightlike.PL.Alexander

/-!
# Two compact sets meeting in one point

If `K₁` and `K₂` are compact sets of the plane with `K₁ ∩ K₂ = {R}`, and `P` is joined to `Q` by a path
off `K₁` and by a path off `K₂`, then `P` is joined to `Q` by a path off `K₁ ∪ K₂`
(`joinedIn_union_compl`; Janiszewski's theorem for a one-point intersection).

The proof puts the two chains of the path-to-chain step (`Grating.exists_chain_of_joinedIn`) on one
grating that is fine (all cells smaller than a constant fixed by the distance between the parts of the
sets away from `R`) and has a margin (the outer rectangle misses both sets), takes the 2-chain of the
cycle formed by the two chains (`Grating.exists_bdy₂`), and uses its complement when `R` lies inside it,
which costs the outer edges (the set `E` of `Grating.alexander`). The cells near `R` all lie in the
2-chain or all outside it (`Grating.near_const`: a walk along rows and columns through cells whose sides
stay away from the boundary), so the chosen 2-chain has no cell meeting both sets, and
`Grating.alexander` applies.

This is Corollary 9.11 of chapter 9 of J. McCleary, *A First Course in Topology: Continuity and Dimension*
(AMS, 2006), after M. H. A. Newman; the numbering is that of the lecture-notes version of the chapter
(`https://pages.vassar.edu/mccleary/files/2011/04/FinalChapter9.pdf`), not checked against the printed
book. The notes state the corollary with a one-sentence argument and take the complement 2-chain from
their Theorem 9.10 (a cycle bounds exactly two 2-chains, the second using an outer cell); here the
complement step is made explicit on a fixed rectangular grating. The statements and proofs are Lean's own.

## Main results

* `joinedIn_union_compl`: two compact sets meeting in one point do not separate two points that neither
  separates.
* `Grating.exists_fine`: a fine grating with a margin containing prescribed coordinates.
* `Grating.near_const`: the cells near a point are all in a 2-chain or all outside it.
* `Grating.outer_far`: the edges of the boundary of the 2-chain of all cells lie on the outer rectangle.

## References

* `mccleary-2006`: chapter "The Jordan Curve Theorem" (checked as a chapter with `scripts/sources.py verify`; the lemma-level numbering quoted above is that of the lecture-notes version and is not checked).
-/

open Set Finset Metric

namespace Lightlike.PL


/-- **A fine set of coordinates with a margin.** A finite set `Z₀` inside `(-M, M)` is contained in a
finite set `Z` inside `[-M, M]` that contains `-M` and `M` and has no gap larger than `ε` without a
point inside. -/
theorem exists_axis (Z₀ : Finset ℝ) {M ε : ℝ} (hM : 0 < M) (hε : 0 < ε) (hZ₀ : ∀ z ∈ Z₀, |z| < M) :
    ∃ Z : Finset ℝ, Z₀ ⊆ Z ∧ -M ∈ Z ∧ M ∈ Z ∧ (∀ z ∈ Z, |z| ≤ M) ∧
      ∀ z ∈ Z, ∀ z' ∈ Z, z < z' → z' - z ≤ ε ∨ ∃ u ∈ Z, z < u ∧ u < z' := by
  classical
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * M / ε)
  have hKpos : (0 : ℝ) < K := lt_of_le_of_lt (by positivity) hK
  set s : ℝ := 2 * M / K with hs
  have hspos : 0 < s := by positivity
  have hsε : s < ε := by
    rw [hs, div_lt_iff₀ hKpos]
    rw [div_lt_iff₀ hε] at hK
    linarith
  let net : Finset ℝ := (Finset.range (K + 1)).image fun k : ℕ => -M + k * s
  refine ⟨Z₀ ∪ net, Finset.subset_union_left, ?_, ?_, ?_, ?_⟩
  · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨0, by simp, by simp⟩)
  · refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨K, by simp, ?_⟩)
    rw [hs]; field_simp; ring
  · intro z hz
    rcases Finset.mem_union.1 hz with h | h
    · exact (hZ₀ z h).le
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 h
      have hk' : (k : ℝ) ≤ K := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      have : (k : ℝ) * s ≤ 2 * M := by
        calc (k : ℝ) * s ≤ K * s := by gcongr
          _ = 2 * M := by rw [hs]; field_simp
      rw [abs_le]; constructor <;> nlinarith [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hspos.le]
  · intro z hz z' hz' hlt
    by_contra hcon
    push Not at hcon
    obtain ⟨hgap, hno⟩ := hcon
    have hzM : -M ≤ z := by
      have : |z| ≤ M := by
        rcases Finset.mem_union.1 hz with h | h
        · exact (hZ₀ z h).le
        · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 h
          have hk' : (k : ℝ) ≤ K := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
          have : (k : ℝ) * s ≤ 2 * M := by
            calc (k : ℝ) * s ≤ K * s := by gcongr
              _ = 2 * M := by rw [hs]; field_simp
          rw [abs_le]; constructor <;> nlinarith [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hspos.le]
      exact (abs_le.1 this).1
    have hz'M : z' ≤ M := by
      have : |z'| ≤ M := by
        rcases Finset.mem_union.1 hz' with h | h
        · exact (hZ₀ z' h).le
        · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 h
          have hk' : (k : ℝ) ≤ K := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
          have : (k : ℝ) * s ≤ 2 * M := by
            calc (k : ℝ) * s ≤ K * s := by gcongr
              _ = 2 * M := by rw [hs]; field_simp
          rw [abs_le]; constructor <;> nlinarith [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hspos.le]
      exact (abs_le.1 this).2
    set x : ℝ := (z + M) / s with hx
    have hx0 : 0 ≤ x := by rw [hx]; apply div_nonneg <;> linarith
    set k : ℕ := ⌊x⌋₊ + 1 with hk
    have hk1 : x < k := by rw [hk]; push_cast; exact Nat.lt_floor_add_one x
    have hk2 : (k : ℝ) ≤ x + 1 := by rw [hk]; push_cast; linarith [Nat.floor_le hx0]
    have hxs : x * s = z + M := by rw [hx]; field_simp
    have hlow : z < -M + k * s := by nlinarith
    have hup : -M + k * s ≤ z + s := by nlinarith
    have hktop : -M + k * s < z' := by linarith
    have hkK : k ≤ K := by
      have hKs : (K : ℝ) * s = 2 * M := by rw [hs]; field_simp
      by_contra hc
      have hc' : (K : ℝ) + 1 ≤ k := by exact_mod_cast Nat.lt_of_not_le hc
      nlinarith
    exact absurd (hno (-M + k * s) (Finset.mem_union_right _
      (Finset.mem_image.2 ⟨k, by simp; omega, rfl⟩)) hlow) (not_le.2 hktop)

namespace Grating

/-- The gaps of a grating whose set of coordinates is `ε`-dense are at most `ε`. -/
lemma gap_le {k : ℕ} (a : Fin (k + 1) → ℝ) (ha : StrictMono a) {Z : Finset ℝ} (hZ : Set.range a = ↑Z)
    {ε : ℝ} (hdense : ∀ z ∈ Z, ∀ z' ∈ Z, z < z' → z' - z ≤ ε ∨ ∃ u ∈ Z, z < u ∧ u < z')
    (i : Fin k) : a i.succ - a i.castSucc ≤ ε := by
  have hmem : ∀ j, a j ∈ Z := fun j => by
    have : a j ∈ Set.range a := ⟨j, rfl⟩
    rw [hZ] at this; exact_mod_cast this
  rcases hdense _ (hmem i.castSucc) _ (hmem i.succ) (ha Fin.castSucc_lt_succ) with h | ⟨u, hu, h1, h2⟩
  · exact h
  · exfalso
    have : u ∈ Set.range a := by rw [hZ]; exact_mod_cast hu
    obtain ⟨j, rfl⟩ := this
    have h1' := ha.lt_iff_lt.1 h1
    have h2' := ha.lt_iff_lt.1 h2
    rw [Fin.lt_def] at h1' h2'
    simp at h1' h2'
    omega

/-- **A fine grating with a margin** containing prescribed coordinates. -/
theorem exists_fine (Xs Ys : Finset ℝ) {M ε : ℝ} (hM : 0 < M) (hε : 0 < ε)
    (hX : ∀ x ∈ Xs, |x| < M) (hY : ∀ y ∈ Ys, |y| < M) :
    ∃ G : Grating, ↑Xs ⊆ G.xs ∧ ↑Ys ⊆ G.ys ∧ G.a 0 ≤ -M ∧ M ≤ G.a (Fin.last _) ∧
      G.b 0 ≤ -M ∧ M ≤ G.b (Fin.last _) ∧
      (∀ i : Fin G.n, G.a i.succ - G.a i.castSucc ≤ ε) ∧
      (∀ j : Fin G.m, G.b j.succ - G.b j.castSucc ≤ ε) := by
  classical
  obtain ⟨ZX, hX1, hX2, hX3, -, hXd⟩ := exists_axis Xs hM hε hX
  obtain ⟨ZY, hY1, hY2, hY3, -, hYd⟩ := exists_axis Ys hM hε hY
  obtain ⟨G, hGx, hGy⟩ := exists_grating ZX ZY ⟨-M, hX2⟩ ⟨-M, hY2⟩
  refine ⟨G, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx; rw [hGx]; exact hX1 hx
  · intro x hx; rw [hGy]; exact hY1 hx
  · have : -M ∈ G.xs := by rw [hGx]; exact_mod_cast hX2
    obtain ⟨k, hk⟩ := this
    rw [← hk]; exact G.ha.monotone (Fin.zero_le _)
  · have : M ∈ G.xs := by rw [hGx]; exact_mod_cast hX3
    obtain ⟨k, hk⟩ := this
    rw [← hk]; exact G.ha.monotone (Fin.le_last _)
  · have : -M ∈ G.ys := by rw [hGy]; exact_mod_cast hY2
    obtain ⟨k, hk⟩ := this
    rw [← hk]; exact G.hb.monotone (Fin.zero_le _)
  · have : M ∈ G.ys := by rw [hGy]; exact_mod_cast hY3
    obtain ⟨k, hk⟩ := this
    rw [← hk]; exact G.hb.monotone (Fin.le_last _)
  · exact fun i => gap_le G.a G.ha hGx hXd i
  · exact fun j => gap_le G.b G.hb hGy hYd j

/-- A horizontal edge is in the boundary of a 2-chain exactly when one of the two cells above and below
it is in the chain and the other is not (a missing cell, at the border, counts as not in the chain). -/
theorem mem_bdy₂_h (G : Grating) (w : Finset G.Cell) (a : Fin G.n) (b : Fin (G.m + 1)) :
    Edge.h a b ∈ G.bdy₂ w ↔
      Xor (∃ j : Fin G.m, j.succ = b ∧ (a, j) ∈ w) (∃ j : Fin G.m, j.castSucc = b ∧ (a, j) ∈ w) := by
  classical
  have hset : w.filter (fun c => Edge.h a b ∈ G.sides c) =
      w.filter (fun c => c.1 = a ∧ c.2.succ = b) ∪ w.filter (fun c => c.1 = a ∧ c.2.castSucc = b) := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_union, sides, Finset.mem_insert, Finset.mem_singleton,
      reduceCtorEq, or_false, Edge.h.injEq]
    constructor
    · rintro ⟨hw, h1 | h1⟩
      · exact Or.inr ⟨hw, h1.1.symm, h1.2.symm⟩
      · exact Or.inl ⟨hw, h1.1.symm, h1.2.symm⟩
    · rintro (⟨hw, h1, h2⟩ | ⟨hw, h1, h2⟩)
      · exact ⟨hw, Or.inr ⟨h1.symm, h2.symm⟩⟩
      · exact ⟨hw, Or.inl ⟨h1.symm, h2.symm⟩⟩
  have hdisj : Disjoint (w.filter (fun c => c.1 = a ∧ c.2.succ = b))
      (w.filter (fun c => c.1 = a ∧ c.2.castSucc = b)) := by
    rw [Finset.disjoint_left]
    intro ⟨i, j⟩ h1 h2
    simp only [Finset.mem_filter] at h1 h2
    exact Fin.castSucc_lt_succ.ne (h2.2.2.trans h1.2.2.symm)
  have hle1 : (w.filter (fun c => c.1 = a ∧ c.2.succ = b)).card ≤ 1 := by
    rw [Finset.card_le_one]
    rintro ⟨i, j⟩ h1 ⟨i', j'⟩ h2
    simp only [Finset.mem_filter] at h1 h2
    exact Prod.ext (h1.2.1.trans h2.2.1.symm) (Fin.succ_injective _ (h1.2.2.trans h2.2.2.symm))
  have hle2 : (w.filter (fun c => c.1 = a ∧ c.2.castSucc = b)).card ≤ 1 := by
    rw [Finset.card_le_one]
    rintro ⟨i, j⟩ h1 ⟨i', j'⟩ h2
    simp only [Finset.mem_filter] at h1 h2
    exact Prod.ext (h1.2.1.trans h2.2.1.symm) (Fin.castSucc_injective _ (h1.2.2.trans h2.2.2.symm))
  have e1 := card_eq_one_iff_of_le hle1
  have e2 := card_eq_one_iff_of_le hle2
  have hP : (w.filter (fun c => c.1 = a ∧ c.2.succ = b)).Nonempty ↔
      ∃ j : Fin G.m, j.succ = b ∧ (a, j) ∈ w := by
    constructor
    · rintro ⟨⟨i, j⟩, h⟩
      simp only [Finset.mem_filter] at h
      exact ⟨j, h.2.2, by rw [← h.2.1]; exact h.1⟩
    · rintro ⟨j, hj, hw⟩
      exact ⟨(a, j), by simp [hj, hw]⟩
  have hQ : (w.filter (fun c => c.1 = a ∧ c.2.castSucc = b)).Nonempty ↔
      ∃ j : Fin G.m, j.castSucc = b ∧ (a, j) ∈ w := by
    constructor
    · rintro ⟨⟨i, j⟩, h⟩
      simp only [Finset.mem_filter] at h
      exact ⟨j, h.2.2, by rw [← h.2.1]; exact h.1⟩
    · rintro ⟨j, hj, hw⟩
      exact ⟨(a, j), by simp [hj, hw]⟩
  simp only [bdy₂, Finset.mem_filter, Finset.mem_univ, true_and, hset,
    Finset.card_union_of_disjoint hdisj, Nat.odd_iff]
  rw [← hP, ← hQ, ← e1, ← e2]
  generalize (w.filter (fun c => c.1 = a ∧ c.2.succ = b)).card = n1 at *
  generalize (w.filter (fun c => c.1 = a ∧ c.2.castSucc = b)).card = n2 at *
  simp only [Xor]
  omega

/-! ### Cells near a point -/

section Near

variable (G : Grating) (R : ℝ × ℝ) (r ε : ℝ)

/-- The cell `c` is close to `R`: its rectangle meets the ball of radius `r` about `R` (in
coordinates). -/
def Near (c : G.Cell) : Prop :=
  (G.a c.1.castSucc ≤ R.1 + r ∧ R.1 - r ≤ G.a c.1.succ) ∧
    (G.b c.2.castSucc ≤ R.2 + r ∧ R.2 - r ≤ G.b c.2.succ)

lemma dist_le_of_mem_cellSet {c : G.Cell} {p q : ℝ × ℝ} (hp : p ∈ G.cellSet c) (hq : q ∈ G.cellSet c)
    (hx : G.a c.1.succ - G.a c.1.castSucc ≤ ε) (hy : G.b c.2.succ - G.b c.2.castSucc ≤ ε) :
    dist p q ≤ ε := by
  rw [Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq]
  obtain ⟨⟨hp1, hp2⟩, ⟨hp3, hp4⟩⟩ := hp
  obtain ⟨⟨hq1, hq2⟩, ⟨hq3, hq4⟩⟩ := hq
  exact ⟨abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by linarith, by linarith⟩⟩

lemma exists_mem_of_near {c : G.Cell} (hr : 0 ≤ r) (h : G.Near R r c) :
    ∃ q ∈ G.cellSet c, dist q R ≤ r := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := h
  have ha : G.a c.1.castSucc ≤ G.a c.1.succ := G.ha.monotone Fin.castSucc_lt_succ.le
  have hb : G.b c.2.castSucc ≤ G.b c.2.succ := G.hb.monotone Fin.castSucc_lt_succ.le
  refine ⟨(max (G.a c.1.castSucc) (R.1 - r), max (G.b c.2.castSucc) (R.2 - r)), ⟨⟨le_max_left _ _, ?_⟩, ⟨le_max_left _ _, ?_⟩⟩, ?_⟩
  · exact max_le ha h2
  · exact max_le hb h4
  · have hx1 : max (G.a c.1.castSucc) (R.1 - r) ≤ R.1 + r := max_le h1 (by linarith)
    have hy1 : max (G.b c.2.castSucc) (R.2 - r) ≤ R.2 + r := max_le h3 (by linarith)
    have hx2 := le_max_right (G.a c.1.castSucc) (R.1 - r)
    have hy2 := le_max_right (G.b c.2.castSucc) (R.2 - r)
    rw [Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq]
    exact ⟨abs_le.2 ⟨by simp only []; linarith, by simp only []; linarith⟩,
      abs_le.2 ⟨by simp only []; linarith, by simp only []; linarith⟩⟩

/-- Every point of a side of a near cell is within `r + ε` of `R`. -/
lemma dist_side_le {c : G.Cell} (hr : 0 ≤ r) (h : G.Near R r c)
    (hx : G.a c.1.succ - G.a c.1.castSucc ≤ ε) (hy : G.b c.2.succ - G.b c.2.castSucc ≤ ε)
    {e : G.Edge} (he : e ∈ G.sides c) {p : ℝ × ℝ} (hp : p ∈ G.seg e) : dist p R ≤ r + ε := by
  obtain ⟨q, hq, hqR⟩ := G.exists_mem_of_near R r hr h
  have := G.dist_le_of_mem_cellSet ε (G.seg_subset_cellSet he hp) hq hx hy
  linarith [dist_triangle p q R]

variable {G R r ε}

/-- Two near cells side by side (in a row) have the same membership in a 2-chain whose boundary stays
away from `R`. -/
lemma adj_h {w : Finset G.Cell} (hr : 0 ≤ r)
    (hside : ∀ e ∈ G.bdy₂ w, ∀ p ∈ G.seg e, r + ε < dist p R)
    (i : Fin G.n) (hi : i.val + 1 < G.n) (j : Fin G.m) (hN : G.Near R r (i, j))
    (hx : G.a i.succ - G.a i.castSucc ≤ ε) (hy : G.b j.succ - G.b j.castSucc ≤ ε) :
    (i, j) ∈ w ↔ ((⟨i.val + 1, hi⟩ : Fin G.n), j) ∈ w := by
  have hnot : Edge.v i.succ j ∉ G.bdy₂ w := by
    intro hm
    have hs : Edge.v i.succ j ∈ G.sides (i, j) := by simp [sides]
    have h1 := hside _ hm _ (left_mem_segment ℝ _ _)
    have h2 := G.dist_side_le R r ε hr hN hx hy hs (left_mem_segment ℝ _ _)
    linarith
  rw [mem_bdy₂_v] at hnot
  have hP : (∃ i' : Fin G.n, i'.succ = i.succ ∧ (i', j) ∈ w) ↔ (i, j) ∈ w :=
    ⟨fun ⟨i', h1, h2⟩ => by rwa [Fin.succ_injective _ h1] at h2, fun h => ⟨i, rfl, h⟩⟩
  have hQ : (∃ i' : Fin G.n, i'.castSucc = i.succ ∧ (i', j) ∈ w) ↔
      ((⟨i.val + 1, hi⟩ : Fin G.n), j) ∈ w := by
    constructor
    · rintro ⟨i', h1, h2⟩
      have : i' = ⟨i.val + 1, hi⟩ := Fin.ext (by have := congrArg Fin.val h1; simpa using this)
      rwa [this] at h2
    · intro h; exact ⟨⟨i.val + 1, hi⟩, Fin.ext (by simp), h⟩
  rw [hP, hQ] at hnot
  simp only [Xor] at hnot
  tauto

/-- Two near cells one above the other have the same membership in a 2-chain whose boundary stays
away from `R`. -/
lemma adj_v {w : Finset G.Cell} (hr : 0 ≤ r)
    (hside : ∀ e ∈ G.bdy₂ w, ∀ p ∈ G.seg e, r + ε < dist p R)
    (i : Fin G.n) (j : Fin G.m) (hj : j.val + 1 < G.m) (hN : G.Near R r (i, j))
    (hx : G.a i.succ - G.a i.castSucc ≤ ε) (hy : G.b j.succ - G.b j.castSucc ≤ ε) :
    (i, j) ∈ w ↔ (i, (⟨j.val + 1, hj⟩ : Fin G.m)) ∈ w := by
  have hnot : Edge.h i j.succ ∉ G.bdy₂ w := by
    intro hm
    have hs : Edge.h i j.succ ∈ G.sides (i, j) := by simp [sides]
    have h1 := hside _ hm _ (left_mem_segment ℝ _ _)
    have h2 := G.dist_side_le R r ε hr hN hx hy hs (left_mem_segment ℝ _ _)
    linarith
  rw [mem_bdy₂_h] at hnot
  have hP : (∃ j' : Fin G.m, j'.succ = j.succ ∧ (i, j') ∈ w) ↔ (i, j) ∈ w :=
    ⟨fun ⟨j', h1, h2⟩ => by rwa [Fin.succ_injective _ h1] at h2, fun h => ⟨j, rfl, h⟩⟩
  have hQ : (∃ j' : Fin G.m, j'.castSucc = j.succ ∧ (i, j') ∈ w) ↔
      (i, (⟨j.val + 1, hj⟩ : Fin G.m)) ∈ w := by
    constructor
    · rintro ⟨j', h1, h2⟩
      have : j' = ⟨j.val + 1, hj⟩ := Fin.ext (by have := congrArg Fin.val h1; simpa using this)
      rwa [this] at h2
    · intro h; exact ⟨⟨j.val + 1, hj⟩, Fin.ext (by simp), h⟩
  rw [hP, hQ] at hnot
  simp only [Xor] at hnot
  tauto

/-- Walking along a row. -/
lemma walk_h {w : Finset G.Cell} (hr : 0 ≤ r)
    (hside : ∀ e ∈ G.bdy₂ w, ∀ p ∈ G.seg e, r + ε < dist p R)
    (hmx : ∀ i : Fin G.n, G.a i.succ - G.a i.castSucc ≤ ε)
    (hmy : ∀ j : Fin G.m, G.b j.succ - G.b j.castSucc ≤ ε) (j : Fin G.m)
    (hNJ : G.b j.castSucc ≤ R.2 + r ∧ R.2 - r ≤ G.b j.succ) :
    ∀ d : ℕ, ∀ i i' : Fin G.n, i.val + d = i'.val →
      (∀ k : Fin G.n, i.val ≤ k.val → k.val ≤ i'.val →
        G.a k.castSucc ≤ R.1 + r ∧ R.1 - r ≤ G.a k.succ) → ((i, j) ∈ w ↔ (i', j) ∈ w) := by
  intro d
  induction d with
  | zero =>
    intro i i' h _
    have : i = i' := Fin.ext (by omega)
    rw [this]
  | succ d ih =>
    intro i i' h hk
    have hi : i.val + 1 < G.n := by have := i'.2; omega
    refine (adj_h hr hside i hi j ⟨hk i le_rfl (by omega), hNJ⟩ (hmx i) (hmy j)).trans ?_
    exact ih ⟨i.val + 1, hi⟩ i' (by simp only []; omega) (fun k h1 h2 => hk k (by simp only [] at h1; omega) h2)

/-- Walking along a column. -/
lemma walk_v {w : Finset G.Cell} (hr : 0 ≤ r)
    (hside : ∀ e ∈ G.bdy₂ w, ∀ p ∈ G.seg e, r + ε < dist p R)
    (hmx : ∀ i : Fin G.n, G.a i.succ - G.a i.castSucc ≤ ε)
    (hmy : ∀ j : Fin G.m, G.b j.succ - G.b j.castSucc ≤ ε) (i : Fin G.n)
    (hNI : G.a i.castSucc ≤ R.1 + r ∧ R.1 - r ≤ G.a i.succ) :
    ∀ d : ℕ, ∀ j j' : Fin G.m, j.val + d = j'.val →
      (∀ k : Fin G.m, j.val ≤ k.val → k.val ≤ j'.val →
        G.b k.castSucc ≤ R.2 + r ∧ R.2 - r ≤ G.b k.succ) → ((i, j) ∈ w ↔ (i, j') ∈ w) := by
  intro d
  induction d with
  | zero =>
    intro j j' h _
    have : j = j' := Fin.ext (by omega)
    rw [this]
  | succ d ih =>
    intro j j' h hk
    have hj : j.val + 1 < G.m := by have := j'.2; omega
    refine (adj_v hr hside i j hj ⟨hNI, hk j le_rfl (by omega)⟩ (hmx i) (hmy j)).trans ?_
    exact ih ⟨j.val + 1, hj⟩ j' (by simp only []; omega) (fun k h1 h2 => hk k (by simp only [] at h1; omega) h2)

/-- **The cells near a point all lie in the 2-chain or all outside it**, when the boundary of the
2-chain stays away from the point and the cells are small. -/
theorem near_const {w : Finset G.Cell} (hr : 0 ≤ r)
    (hside : ∀ e ∈ G.bdy₂ w, ∀ p ∈ G.seg e, r + ε < dist p R)
    (hmx : ∀ i : Fin G.n, G.a i.succ - G.a i.castSucc ≤ ε)
    (hmy : ∀ j : Fin G.m, G.b j.succ - G.b j.castSucc ≤ ε)
    {c c' : G.Cell} (hc : G.Near R r c) (hc' : G.Near R r c') : c ∈ w ↔ c' ∈ w := by
  obtain ⟨i, j⟩ := c
  obtain ⟨i', j'⟩ := c'
  obtain ⟨⟨hi1, hi2⟩, hj⟩ := hc
  obtain ⟨⟨hi1', hi2'⟩, hj'⟩ := hc'
  -- first along the row of `c`, then along the column of `c'`
  have hrow : (i, j) ∈ w ↔ (i', j) ∈ w := by
    rcases le_total i.val i'.val with hle | hle
    · exact walk_h hr hside hmx hmy j hj (i'.val - i.val) i i' (by omega) (fun k h1 h2 =>
        ⟨(G.ha.monotone (Fin.castSucc_le_castSucc_iff.2 (Fin.le_def.2 h2))).trans hi1',
          hi2.trans (G.ha.monotone (Fin.succ_le_succ_iff.2 (Fin.le_def.2 h1)))⟩)
    · exact (walk_h hr hside hmx hmy j hj (i.val - i'.val) i' i (by omega) (fun k h1 h2 =>
        ⟨(G.ha.monotone (Fin.castSucc_le_castSucc_iff.2 (Fin.le_def.2 h2))).trans hi1,
          hi2'.trans (G.ha.monotone (Fin.succ_le_succ_iff.2 (Fin.le_def.2 h1)))⟩)).symm
  have hcol : (i', j) ∈ w ↔ (i', j') ∈ w := by
    rcases le_total j.val j'.val with hle | hle
    · exact walk_v hr hside hmx hmy i' ⟨hi1', hi2'⟩ (j'.val - j.val) j j' (by omega) (fun k h1 h2 =>
        ⟨(G.hb.monotone (Fin.castSucc_le_castSucc_iff.2 (Fin.le_def.2 h2))).trans hj'.1,
          hj.2.trans (G.hb.monotone (Fin.succ_le_succ_iff.2 (Fin.le_def.2 h1)))⟩)
    · exact (walk_v hr hside hmx hmy i' ⟨hi1', hi2'⟩ (j.val - j'.val) j' j (by omega) (fun k h1 h2 =>
        ⟨(G.hb.monotone (Fin.castSucc_le_castSucc_iff.2 (Fin.le_def.2 h2))).trans hj.1,
          hj'.2.trans (G.hb.monotone (Fin.succ_le_succ_iff.2 (Fin.le_def.2 h1)))⟩)).symm
  exact hrow.trans hcol

end Near

/-! ### The outer rectangle -/

lemma segment_fst_eq {u v p : ℝ × ℝ} (h : u.1 = v.1) (hp : p ∈ segment ℝ u v) : p.1 = u.1 := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hp
  simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
  rw [← h, ← add_mul, hst, one_mul]

lemma segment_snd_eq {u v p : ℝ × ℝ} (h : u.2 = v.2) (hp : p ∈ segment ℝ u v) : p.2 = u.2 := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hp
  simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
  rw [← h, ← add_mul, hst, one_mul]

/-- An edge of the boundary of the 2-chain of all cells lies on the outer rectangle: its points are
at distance at least `M` from the origin in one coordinate, when the grating reaches `-M` and `M` in
both directions. -/
theorem outer_far (G : Grating) {M : ℝ} (ha0 : G.a 0 ≤ -M) (haL : M ≤ G.a (Fin.last _))
    (hb0 : G.b 0 ≤ -M) (hbL : M ≤ G.b (Fin.last _)) {e : G.Edge}
    (he : e ∈ G.bdy₂ (Finset.univ : Finset G.Cell)) {p : ℝ × ℝ} (hp : p ∈ G.seg e) :
    M ≤ |p.1| ∨ M ≤ |p.2| := by
  cases e with
  | v a b =>
    rw [mem_bdy₂_v] at he
    have hp1 : p.1 = G.a a :=
      segment_fst_eq (u := G.pt (a, b.castSucc)) (v := G.pt (a, b.succ)) rfl hp
    by_cases h0 : a.val = 0
    · have : a = 0 := Fin.ext (by simpa using h0)
      subst this
      left; rw [hp1]; exact le_trans (by linarith) (neg_le_abs _)
    by_cases hL : a.val = G.n
    · have : a = Fin.last _ := Fin.ext (by simpa using hL)
      subst this
      left; rw [hp1]; exact le_trans haL (le_abs_self _)
    exfalso
    have hP : ∃ i : Fin G.n, i.succ = a ∧ (i, b) ∈ (Finset.univ : Finset G.Cell) :=
      ⟨⟨a.val - 1, by omega⟩, Fin.ext (by simp; omega), Finset.mem_univ _⟩
    have hQ : ∃ i : Fin G.n, i.castSucc = a ∧ (i, b) ∈ (Finset.univ : Finset G.Cell) :=
      ⟨⟨a.val, by have := a.2; omega⟩, Fin.ext rfl, Finset.mem_univ _⟩
    simp only [Xor] at he
    rcases he with ⟨_, h⟩ | ⟨_, h⟩
    · exact h hQ
    · exact h hP
  | h a b =>
    rw [mem_bdy₂_h] at he
    have hp2 : p.2 = G.b b :=
      segment_snd_eq (u := G.pt (a.castSucc, b)) (v := G.pt (a.succ, b)) rfl hp
    by_cases h0 : b.val = 0
    · have : b = 0 := Fin.ext (by simpa using h0)
      subst this
      right; rw [hp2]; exact le_trans (by linarith) (neg_le_abs _)
    by_cases hL : b.val = G.m
    · have : b = Fin.last _ := Fin.ext (by simpa using hL)
      subst this
      right; rw [hp2]; exact le_trans hbL (le_abs_self _)
    exfalso
    have hP : ∃ j : Fin G.m, j.succ = b ∧ (a, j) ∈ (Finset.univ : Finset G.Cell) :=
      ⟨⟨b.val - 1, by omega⟩, Fin.ext (by simp; omega), Finset.mem_univ _⟩
    have hQ : ∃ j : Fin G.m, j.castSucc = b ∧ (a, j) ∈ (Finset.univ : Finset G.Cell) :=
      ⟨⟨b.val, by have := b.2; omega⟩, Fin.ext rfl, Finset.mem_univ _⟩
    simp only [Xor] at he
    rcases he with ⟨_, h⟩ | ⟨_, h⟩
    · exact h hQ
    · exact h hP

lemma pt_injective (G : Grating) {x y : G.Vert} (h : G.pt x = G.pt y) : x = y := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  simp only [pt, Prod.mk.injEq] at h
  exact Prod.ext (G.ha.injective h.1) (G.hb.injective h.2)

lemma near_of_mem {G : Grating} {R : ℝ × ℝ} {r : ℝ} {c : G.Cell} {p : ℝ × ℝ}
    (hp : p ∈ G.cellSet c) (hd : dist p R ≤ r) : G.Near R r c := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hp
  rw [Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq] at hd
  obtain ⟨hd1, hd2⟩ := hd
  rw [abs_le] at hd1 hd2
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

end Grating

lemma exists_abs_lt (S : Finset ℝ) : ∃ M : ℝ, 0 < M ∧ ∀ x ∈ S, |x| < M := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a S _ ih =>
    obtain ⟨M, hM, h⟩ := ih
    refine ⟨max M (|a| + 1), lt_max_of_lt_left hM, ?_⟩
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact lt_max_of_lt_right (by linarith)
    · exact lt_max_of_lt_left (h x hx)



/-- **Two compact sets meeting in one point** (the corollary of the notes' "Alexander theorem" used
in the bisection; Janiszewski's theorem for a one-point intersection): if `P` is joined to `Q` off
each of `K₁` and `K₂`, and `K₁ ∩ K₂ = {R}`, then `P` is joined to `Q` off `K₁ ∪ K₂`. -/
theorem joinedIn_union_compl {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsCompact K₁) (h₂ : IsCompact K₂)
    {R : ℝ × ℝ} (hR : K₁ ∩ K₂ = {R}) {P Q : ℝ × ℝ}
    (hP : JoinedIn K₁ᶜ P Q) (hQ : JoinedIn K₂ᶜ P Q) : JoinedIn (K₁ ∪ K₂)ᶜ P Q := by
  classical
  have hPK₁ : P ∉ K₁ := hP.source_mem
  have hQK₁ : Q ∉ K₁ := hP.target_mem
  have hPK₂ : P ∉ K₂ := hQ.source_mem
  have hQK₂ : Q ∉ K₂ := hQ.target_mem
  have hR12 : R ∈ K₁ ∩ K₂ := by rw [hR]; rfl
  obtain ⟨ρ₁, hρ₁, Xs₁, Ys₁, H₁⟩ := Grating.exists_chain_of_joinedIn h₁ hP
  obtain ⟨ρ₂, hρ₂, Xs₂, Ys₂, H₂⟩ := Grating.exists_chain_of_joinedIn h₂ hQ
  set ρ := min ρ₁ ρ₂ with hρ
  have hρpos : 0 < ρ := lt_min hρ₁ hρ₂
  set r := ρ / 4 with hr
  have hrpos : 0 < r := by positivity
  -- the separation of the two sets away from `R`
  have hK₁' : IsCompact (K₁ \ ball R r) := h₁.diff isOpen_ball
  have hK₂' : IsCompact (K₂ \ ball R r) := h₂.diff isOpen_ball
  have hdisj : Disjoint (K₁ \ ball R r) (K₂ \ ball R r) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    have : x ∈ K₁ ∩ K₂ := ⟨hx1.1, hx2.1⟩
    rw [hR] at this
    exact hx1.2 (by rw [mem_singleton_iff.1 this]; exact mem_ball_self hrpos)
  obtain ⟨η, hη, hηd⟩ := exists_pos_forall_lt_edist hK₁' hK₂'.isClosed hdisj
  set ε : ℝ := min ((η : ℝ) / 2) r with hε
  have hεpos : 0 < ε := lt_min (by have : (0 : ℝ) < η := hη; positivity) hrpos
  -- a bound for all the coordinates
  obtain ⟨C, hC⟩ := (h₁.union h₂).isBounded.subset_closedBall (0 : ℝ × ℝ)
  obtain ⟨MX, hMX, hX⟩ := exists_abs_lt (Xs₁ ∪ Xs₂)
  obtain ⟨MY, hMY, hY⟩ := exists_abs_lt (Ys₁ ∪ Ys₂)
  set M := max (max MX MY) (C + 1) with hM
  have hMpos : 0 < M := lt_of_lt_of_le hMX ((le_max_left _ _).trans (le_max_left _ _))
  have hXM : ∀ x ∈ Xs₁ ∪ Xs₂, |x| < M := fun x hx =>
    (hX x hx).trans_le ((le_max_left _ _).trans (le_max_left _ _))
  have hYM : ∀ y ∈ Ys₁ ∪ Ys₂, |y| < M := fun y hy =>
    (hY y hy).trans_le ((le_max_right _ _).trans (le_max_left _ _))
  have hKM : ∀ p ∈ K₁ ∪ K₂, |p.1| < M ∧ |p.2| < M := by
    intro p hp
    have h := mem_closedBall_zero_iff.1 (hC hp)
    have hCM : C + 1 ≤ M := le_max_right _ _
    have h1 : |p.1| ≤ ‖p‖ := by simpa [Real.norm_eq_abs] using norm_fst_le p
    have h2 : |p.2| ≤ ‖p‖ := by simpa [Real.norm_eq_abs] using norm_snd_le p
    exact ⟨by linarith, by linarith⟩
  -- the grating and the two chains on it
  obtain ⟨G, hGx, hGy, ha0, haL, hb0, hbL, hmx, hmy⟩ :=
    Grating.exists_fine (Xs₁ ∪ Xs₂) (Ys₁ ∪ Ys₂) hMpos hεpos hXM hYM
  obtain ⟨x₁, y₁, l₁, hx₁, hy₁, hd₁, hb₁⟩ := H₁ G
    ((Finset.coe_subset.2 Finset.subset_union_left).trans hGx)
    ((Finset.coe_subset.2 Finset.subset_union_left).trans hGy)
  obtain ⟨x₂, y₂, l₂, hx₂, hy₂, hd₂, hb₂⟩ := H₂ G
    ((Finset.coe_subset.2 Finset.subset_union_right).trans hGx)
    ((Finset.coe_subset.2 Finset.subset_union_right).trans hGy)
  have hxx : x₁ = x₂ := Grating.pt_injective G (hx₁.trans hx₂.symm)
  have hyy : y₁ = y₂ := Grating.pt_injective G (hy₁.trans hy₂.symm)
  subst hxx hyy
  have hbZ : G.bdy (symmDiff l₁ l₂) = ∅ := by
    rw [Grating.bdy_symmDiff, hb₁, hb₂]; simp
  obtain ⟨w₀, hw₀⟩ := G.exists_bdy₂ hbZ
  -- the cycle stays away from `R`
  have hside : ∀ e ∈ G.bdy₂ w₀, ∀ p ∈ G.seg e, r + ε < dist p R := by
    intro e he p hp
    rw [hw₀] at he
    have hεr : ε ≤ r := min_le_right _ _
    have hρr : ρ = 4 * r := by rw [hr]; ring
    rcases Finset.mem_symmDiff.1 he with ⟨h, _⟩ | ⟨h, _⟩
    · have := hd₁ p (by simp only [Grating.locus, Set.mem_iUnion]; exact ⟨e, h, hp⟩) R hR12.1
      have := min_le_left ρ₁ ρ₂
      linarith
    · have := hd₂ p (by simp only [Grating.locus, Set.mem_iUnion]; exact ⟨e, h, hp⟩) R hR12.2
      have := min_le_right ρ₁ ρ₂
      linarith
  have hnearconst : ∀ {c c' : G.Cell}, G.Near R r c → G.Near R r c' → (c ∈ w₀ ↔ c' ∈ w₀) :=
    fun hc hc' => Grating.near_const hrpos.le hside hmx hmy hc hc'
  -- choose the side of the cycle away from `R`
  obtain ⟨w, E, hE, hw, hnear⟩ : ∃ (w : Finset G.Cell) (E : Finset G.Edge),
      (∀ e ∈ E, Disjoint (G.seg e) (K₁ ∪ K₂)) ∧ symmDiff (G.bdy₂ w) E = symmDiff l₁ l₂ ∧
        ∀ c ∈ w, ¬ G.Near R r c := by
    by_cases hN : ∃ c, G.Near R r c ∧ c ∈ w₀
    · obtain ⟨c₀, hc₀, hc₀w⟩ := hN
      refine ⟨Finset.univ \ w₀, G.bdy₂ Finset.univ, ?_, ?_, ?_⟩
      · intro e he
        refine Set.disjoint_left.2 fun p hp hpK => ?_
        have h1 := Grating.outer_far G ha0 haL hb0 hbL he hp
        have h2 := hKM p hpK
        rcases h1 with h | h <;> linarith [h2.1, h2.2]
      · have : (Finset.univ \ w₀ : Finset G.Cell) = symmDiff Finset.univ w₀ := by
          ext c; simp [Finset.mem_symmDiff]
        rw [this, Grating.bdy₂_symmDiff, hw₀]
        rw [symmDiff_comm]
        exact symmDiff_symmDiff_cancel_left (G.bdy₂ (Finset.univ : Finset G.Cell)) (symmDiff l₁ l₂)
      · intro c hc hnc
        exact (Finset.mem_sdiff.1 hc).2 ((hnearconst hc₀ hnc).1 hc₀w)
    · refine ⟨w₀, ∅, by simp, by rw [hw₀]; simp, ?_⟩
      intro c hc hnc
      exact hN ⟨c, hnc, hc⟩
  -- no cell of `w` meets both sets
  have hfine : ∀ c ∈ w, ¬ ((G.cellSet c ∩ K₁).Nonempty ∧ (G.cellSet c ∩ K₂).Nonempty) := by
    rintro c hc ⟨⟨p, hpc, hp1⟩, ⟨q, hqc, hq2⟩⟩
    have hpR : r < dist p R := by
      by_contra h; exact hnear c hc (Grating.near_of_mem hpc (not_lt.1 h))
    have hqR : r < dist q R := by
      by_contra h; exact hnear c hc (Grating.near_of_mem hqc (not_lt.1 h))
    have hp' : p ∈ K₁ \ ball R r := ⟨hp1, fun h => absurd (mem_ball.1 h) (not_lt.2 hpR.le)⟩
    have hq' : q ∈ K₂ \ ball R r := ⟨hq2, fun h => absurd (mem_ball.1 h) (not_lt.2 hqR.le)⟩
    have h1 := hηd p hp' q hq'
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal] at h1
    have h2 : (η : ℝ) < dist p q := (ENNReal.ofReal_lt_ofReal_iff'.1 h1).1
    have h3 : dist p q ≤ ε := G.dist_le_of_mem_cellSet ε hpc hqc (hmx c.1) (hmy c.2)
    have h4 : ε ≤ (η : ℝ) / 2 := min_le_left _ _
    have : (0 : ℝ) < η := hη
    linarith
  -- Alexander's theorem
  have hx : G.pt x₁ ∉ K₁ ∪ K₂ := by
    rw [hx₁]; rintro (h | h)
    · exact hPK₁ h
    · exact hPK₂ h
  have hseg₁ : ∀ e ∈ l₁, Disjoint (G.seg e) K₁ := fun e he =>
    Set.disjoint_left.2 fun p hp hpK => by
      have := hd₁ p (by simp only [Grating.locus, Set.mem_iUnion]; exact ⟨e, he, hp⟩) p hpK
      simp at this; linarith
  have hseg₂ : ∀ e ∈ l₂, Disjoint (G.seg e) K₂ := fun e he =>
    Set.disjoint_left.2 fun p hp hpK => by
      have := hd₂ p (by simp only [Grating.locus, Set.mem_iUnion]; exact ⟨e, he, hp⟩) p hpK
      simp at this; linarith
  have := G.alexander hx hb₁ hseg₁ hb₂ hseg₂ hE hw hfine
  rwa [hx₁, hy₁] at this

end Lightlike.PL
