import Lightlike.PL.Grating

/-!
# A path in the complement gives a chain of a grating

Let `A` be a compact set of the plane and let `P`, `Q` be joined by a path in the complement of `A`.
For every grating whose coordinates contain the coordinates of finitely many sample points of the
path, `P` and `Q` are vertices of the grating and some chain of the grating has boundary `{P, Q}`
and stays at a fixed distance `ρ > 0` from `A`. This is the direction from paths to chains of
Proposition 9.8 of chapter 9 of J. McCleary, *A First Course in Topology: Continuity and Dimension*
(AMS, 2006), after M. H. A. Newman; the numbering is that of the lecture-notes version of the chapter
(`https://pages.vassar.edu/mccleary/files/2011/04/FinalChapter9.pdf`), not checked against the printed
book. The statements and proofs are Lean's own. The converse, from chains to paths, is
`Lightlike.PL.Grating.joinedIn_of_bdy` in `Lightlike/PL/Grating.lean`.

The proof samples the path finely (uniform continuity and the distance of the compact path to `A`),
puts the coordinates of the samples on the grid, and joins consecutive samples by a stepwise chain
inside the box they span (`exists_chain_box`). So no mesh and no refinement of the grating is needed.

## Main results

* `Grating.exists_grating`: finite sets of coordinates are the coordinates of a grating.
* `Grating.exists_chain_box`: two vertices are the boundary of a chain inside the box they span.
* `Grating.exists_chain_of_joinedIn`: the chain of a path in the complement of a compact set.
-/

open Set Finset

namespace Lightlike.PL

namespace Grating

/-- The set of the `x`-coordinates of the vertical lines of a grating. -/
def xs (G : Grating) : Set ℝ := Set.range G.a
/-- The set of the `y`-coordinates of the horizontal lines of a grating. -/
def ys (G : Grating) : Set ℝ := Set.range G.b

/-- **A grating with prescribed coordinates.** -/
theorem exists_grating (X Y : Finset ℝ) (hX : X.Nonempty) (hY : Y.Nonempty) :
    ∃ G : Grating, G.xs = ↑X ∧ G.ys = ↑Y := by
  have hX' : X.card = (X.card - 1) + 1 := (Nat.succ_pred_eq_of_pos (Finset.card_pos.2 hX)).symm
  have hY' : Y.card = (Y.card - 1) + 1 := (Nat.succ_pred_eq_of_pos (Finset.card_pos.2 hY)).symm
  refine ⟨⟨X.card - 1, Y.card - 1, X.orderEmbOfFin hX', Y.orderEmbOfFin hY',
    (X.orderEmbOfFin hX').strictMono, (Y.orderEmbOfFin hY').strictMono⟩, ?_, ?_⟩
  · simp only [xs]
    exact Finset.range_orderEmbOfFin X hX'
  · simp only [ys]
    exact Finset.range_orderEmbOfFin Y hY'

instance (G : Grating) : Fintype G.Edge := by
  classical
  exact Fintype.ofEquiv (Sum (Fin G.n × Fin (G.m + 1)) (Fin (G.n + 1) × Fin G.m))
    { toFun := fun s => match s with | .inl (i, j) => .h i j | .inr (i, j) => .v i j
      invFun := fun e => match e with | .h i j => .inl (i, j) | .v i j => .inr (i, j)
      left_inv := fun s => by rcases s with ⟨i, j⟩ | ⟨i, j⟩ <;> rfl
      right_inv := fun e => by cases e <;> rfl }

/-- A single edge has its two ends as boundary. -/
theorem bdy_singleton (G : Grating) (e : G.Edge) :
    G.bdy {e} = symmDiff {(G.ends e).1} {(G.ends e).2} := by
  classical
  have hne := G.ends_ne e
  ext x
  simp only [bdy, deg, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_symmDiff,
    Finset.mem_singleton, Finset.filter_singleton]
  by_cases h1 : x = (G.ends e).1
  · simp [h1, hne]
  · by_cases h2 : x = (G.ends e).2
    · simp [h2, hne.symm]
    · simp [h1, h2]

/-- The closed box spanned by two points. -/
def Box (p q : ℝ × ℝ) : Set (ℝ × ℝ) := Set.uIcc p.1 q.1 ×ˢ Set.uIcc p.2 q.2

lemma convex_Box (p q : ℝ × ℝ) : Convex ℝ (Box p q) :=
  (convex_uIcc _ _).prod (convex_uIcc _ _)

lemma left_mem_Box (p q : ℝ × ℝ) : p ∈ Box p q := ⟨left_mem_uIcc, left_mem_uIcc⟩

lemma Box_mono {p q r : ℝ × ℝ} (h : r ∈ Box p q) : Box r q ⊆ Box p q :=
  Set.prod_mono (Set.uIcc_subset_uIcc_right h.1) (Set.uIcc_subset_uIcc_right h.2)

variable (G : Grating)

lemma a_mem_uIcc {p q r : Fin (G.n + 1)} (h : r ∈ Set.uIcc p q) :
    G.a r ∈ Set.uIcc (G.a p) (G.a q) := by
  rcases Set.mem_uIcc.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Set.mem_uIcc.2 (Or.inl ⟨G.ha.monotone h1, G.ha.monotone h2⟩)
  · exact Set.mem_uIcc.2 (Or.inr ⟨G.ha.monotone h1, G.ha.monotone h2⟩)

lemma b_mem_uIcc {p q r : Fin (G.m + 1)} (h : r ∈ Set.uIcc p q) :
    G.b r ∈ Set.uIcc (G.b p) (G.b q) := by
  rcases Set.mem_uIcc.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Set.mem_uIcc.2 (Or.inl ⟨G.hb.monotone h1, G.hb.monotone h2⟩)
  · exact Set.mem_uIcc.2 (Or.inr ⟨G.hb.monotone h1, G.hb.monotone h2⟩)

/-- The grid distance of two vertices. -/
def gdist (u v : G.Vert) : ℕ :=
  ((u.1 : ℕ) - (v.1 : ℕ) : ℤ).natAbs + ((u.2 : ℕ) - (v.2 : ℕ) : ℤ).natAbs

lemma pt_mem_Box {u v w : G.Vert} (h1 : w.1 ∈ Set.uIcc u.1 v.1) (h2 : w.2 ∈ Set.uIcc u.2 v.2) :
    G.pt w ∈ Box (G.pt u) (G.pt v) :=
  ⟨G.a_mem_uIcc h1, G.b_mem_uIcc h2⟩

/-- **One grid step towards `v`**: an edge from `u` to a neighbour that is closer to `v` and lies in
the box of `u` and `v`. -/
lemma exists_step {u v : G.Vert} (h : u ≠ v) :
    ∃ (e : G.Edge) (u' : G.Vert), (G.ends e = (u, u') ∨ G.ends e = (u', u)) ∧
      G.gdist u' v < G.gdist u v ∧ G.pt u' ∈ Box (G.pt u) (G.pt v) := by
  obtain ⟨u1, u2⟩ := u
  obtain ⟨v1, v2⟩ := v
  by_cases h1 : u1 = v1
  · subst h1
    have h2 : u2 ≠ v2 := fun h2 => h (by rw [h2])
    rcases lt_or_gt_of_ne h2 with hlt | hgt
    · have hv : (u2 : ℕ) < G.m := by have := v2.2; have := Fin.lt_def.1 hlt; omega
      refine ⟨.v u1 ⟨u2, hv⟩, (u1, (⟨u2, hv⟩ : Fin G.m).succ), Or.inl rfl, ?_, ?_⟩
      · simp only [gdist, Fin.val_succ]; have := Fin.lt_def.1 hlt; omega
      · refine G.pt_mem_Box (Set.left_mem_uIcc) ?_
        refine Set.mem_uIcc.2 (Or.inl ⟨Fin.le_def.2 (by simp), Fin.le_def.2 (by simp; have := Fin.lt_def.1 hlt; omega)⟩)
    · have hv : (u2 : ℕ) - 1 < G.m := by have := u2.2; omega
      refine ⟨.v u1 ⟨(u2 : ℕ) - 1, hv⟩, (u1, (⟨(u2 : ℕ) - 1, hv⟩ : Fin G.m).castSucc), Or.inr ?_, ?_, ?_⟩
      · have hu : (u2 : ℕ) ≥ 1 := by have := Fin.lt_def.1 hgt; omega
        exact Prod.ext rfl (Prod.ext rfl (Fin.ext (by simp [ends]; omega)))
      · simp only [gdist, Fin.val_castSucc]; have := Fin.lt_def.1 hgt; omega
      · refine G.pt_mem_Box (Set.left_mem_uIcc) ?_
        refine Set.mem_uIcc.2 (Or.inr ⟨Fin.le_def.2 (by simp; have := Fin.lt_def.1 hgt; omega), Fin.le_def.2 (by simp)⟩)
  · rcases lt_or_gt_of_ne h1 with hlt | hgt
    · have hv : (u1 : ℕ) < G.n := by have := v1.2; have := Fin.lt_def.1 hlt; omega
      refine ⟨.h ⟨u1, hv⟩ u2, ((⟨u1, hv⟩ : Fin G.n).succ, u2), Or.inl rfl, ?_, ?_⟩
      · simp only [gdist, Fin.val_succ]; have := Fin.lt_def.1 hlt; omega
      · refine G.pt_mem_Box ?_ (Set.left_mem_uIcc)
        refine Set.mem_uIcc.2 (Or.inl ⟨Fin.le_def.2 (by simp), Fin.le_def.2 (by simp; have := Fin.lt_def.1 hlt; omega)⟩)
    · have hv : (u1 : ℕ) - 1 < G.n := by have := u1.2; omega
      refine ⟨.h ⟨(u1 : ℕ) - 1, hv⟩ u2, ((⟨(u1 : ℕ) - 1, hv⟩ : Fin G.n).castSucc, u2), Or.inr ?_, ?_, ?_⟩
      · have hu : (u1 : ℕ) ≥ 1 := by have := Fin.lt_def.1 hgt; omega
        exact Prod.ext rfl (Prod.ext (Fin.ext (by simp [ends]; omega)) rfl)
      · simp only [gdist, Fin.val_castSucc]; have := Fin.lt_def.1 hgt; omega
      · refine G.pt_mem_Box ?_ (Set.left_mem_uIcc)
        refine Set.mem_uIcc.2 (Or.inr ⟨Fin.le_def.2 (by simp; have := Fin.lt_def.1 hgt; omega), Fin.le_def.2 (by simp)⟩)

lemma symmDiff_pair_trans {α : Type*} [DecidableEq α] (a b c : α) :
    symmDiff (symmDiff {a} {b}) (symmDiff {b} {c}) = (symmDiff {a} {c} : Finset α) := by
  ext x; simp only [Finset.mem_symmDiff, Finset.mem_singleton]; tauto

/-- **A chain between two vertices inside their box**: its boundary is `{u} ∆ {v}` (that is,
`{u, v}` for `u ≠ v` and empty for `u = v`) and its edges lie in the box spanned by `u` and `v`. -/
theorem exists_chain_box (u v : G.Vert) :
    ∃ c : Finset G.Edge, G.bdy c = symmDiff {u} {v} ∧ ∀ e ∈ c, G.seg e ⊆ Box (G.pt u) (G.pt v) := by
  classical
  induction' hd : G.gdist u v using Nat.strong_induction_on with d ih generalizing u v
  by_cases huv : u = v
  · subst huv
    exact ⟨∅, by simp [bdy, deg], by simp⟩
  · obtain ⟨e, u', hend, hlt, hbox⟩ := G.exists_step huv
    obtain ⟨c', hc'b, hc'⟩ := ih (G.gdist u' v) (hd ▸ hlt) u' v rfl
    have he : G.seg e ⊆ Box (G.pt u) (G.pt v) := by
      have h1 := left_mem_Box (G.pt u) (G.pt v)
      simp only [seg]
      rcases hend with h | h <;> rw [h]
      · exact (convex_Box _ _).segment_subset h1 hbox
      · simp only
        rw [segment_symm]
        exact (convex_Box _ _).segment_subset h1 hbox
    refine ⟨symmDiff {e} c', ?_, ?_⟩
    · rw [bdy_symmDiff, bdy_singleton, hc'b]
      rcases hend with h | h <;> rw [h]
      · exact symmDiff_pair_trans u u' v
      · simp only
        rw [symmDiff_comm ({u'} : Finset G.Vert) {u}]
        exact symmDiff_pair_trans u u' v
    · intro e' he'
      rcases Finset.mem_symmDiff.1 he' with ⟨h1, _⟩ | ⟨h1, _⟩
      · rw [Finset.mem_singleton.1 h1]; exact he
      · exact (hc' e' h1).trans (Box_mono hbox)

/-- A point of the box of two points is within the distance of the two points from the first. -/
lemma dist_le_of_mem_Box {p q z : ℝ × ℝ} (h : z ∈ Box p q) : dist z p ≤ dist q p := by
  rw [Prod.dist_eq, Prod.dist_eq]
  refine max_le_max ?_ ?_
  · rw [Real.dist_eq, Real.dist_eq]; exact Set.abs_sub_left_of_mem_uIcc h.1
  · rw [Real.dist_eq, Real.dist_eq]; exact Set.abs_sub_left_of_mem_uIcc h.2

/-- **A path in the complement gives a chain** (chapter 9 of McCleary, Proposition 9.8 of the
lecture-notes version, the direction from paths to chains). If `P` and `Q` are joined by a path in
the complement of the compact set `A`, there are a distance `ρ > 0` and two finite sets of
coordinates such that every grating whose coordinates contain them has `P` and `Q` as vertices and
a chain with boundary `{P, Q}` whose points are at distance at least `ρ` from `A`. -/
theorem exists_chain_of_joinedIn {A : Set (ℝ × ℝ)} (hA : IsCompact A) {P Q : ℝ × ℝ}
    (h : JoinedIn Aᶜ P Q) :
    ∃ ρ > 0, ∃ Xs Ys : Finset ℝ, ∀ G : Grating, ↑Xs ⊆ G.xs → ↑Ys ⊆ G.ys →
      ∃ (x y : G.Vert) (c : Finset G.Edge), G.pt x = P ∧ G.pt y = Q ∧
        (∀ p ∈ G.locus c, ∀ a ∈ A, ρ ≤ dist p a) ∧ G.bdy c = symmDiff {x} {y} := by
  classical
  set γ := h.somePath with hγdef
  have hmem : ∀ t, γ t ∈ Aᶜ := h.somePath_mem
  have hΓ : IsCompact (Set.range γ) := isCompact_range γ.continuous
  obtain ⟨δ, hδ, hth⟩ := hΓ.exists_thickening_subset_open hA.isClosed.isOpen_compl
    (by rintro _ ⟨t, rfl⟩; exact hmem t)
  obtain ⟨η, hη, hu⟩ := Metric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous γ.continuous) (δ / 2) (half_pos hδ)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hη
  set N : ℝ := (n : ℝ) + 1 with hN
  have hNpos : 0 < N := by positivity
  -- the points on the path
  let t : ℕ → unitInterval := fun i => Set.projIcc 0 1 zero_le_one ((i : ℝ) / N)
  let z : ℕ → ℝ × ℝ := fun i => γ (t i)
  have hz0 : z 0 = P := by
    have : t 0 = 0 := by simp [t]
    simp [z, this]
  have hzN : z (n + 1) = Q := by
    have : t (n + 1) = 1 := by
      simp only [t]
      have : (((n + 1 : ℕ) : ℝ) / N) = 1 := by rw [hN]; push_cast; exact div_self (by positivity)
      rw [this]; simp
    simp [z, this]
  have hzd : ∀ i, dist (z i) (z (i + 1)) < δ / 2 := by
    intro i
    refine hu ?_
    rw [Subtype.dist_eq, Real.dist_eq]
    refine lt_of_le_of_lt (Set.abs_projIcc_sub_projIcc zero_le_one) ?_
    have : |(i : ℝ) / N - ((i + 1 : ℕ) : ℝ) / N| = 1 / N := by
      rw [← sub_div, abs_div, abs_of_pos hNpos]; congr 1; push_cast; rw [abs_sub_comm]; simp
    rw [this]; exact hn
  have hzA : ∀ i, ∀ a ∈ A, δ ≤ dist a (z i) := by
    intro i a ha
    by_contra hlt
    push Not at hlt
    exact hth (Metric.mem_thickening_iff.2 ⟨z i, ⟨t i, rfl⟩, hlt⟩) ha
  refine ⟨δ / 2, half_pos hδ, (Finset.range (n + 2)).image fun i => (z i).1,
    (Finset.range (n + 2)).image fun i => (z i).2, ?_⟩
  intro G hGx hGy
  have hpx : ∀ i, i < n + 2 → ∃ p, G.a p = (z i).1 := fun i hi =>
    hGx (by simp only [Finset.coe_image]; exact ⟨i, by simpa using hi, rfl⟩)
  have hpy : ∀ i, i < n + 2 → ∃ p, G.b p = (z i).2 := fun i hi =>
    hGy (by simp only [Finset.coe_image]; exact ⟨i, by simpa using hi, rfl⟩)
  have hv : ∀ i, ∃ w : G.Vert, i < n + 2 → G.pt w = z i := by
    intro i
    by_cases hi : i < n + 2
    · obtain ⟨p, hp⟩ := hpx i hi
      obtain ⟨q, hq⟩ := hpy i hi
      exact ⟨(p, q), fun _ => Prod.ext hp hq⟩
    · exact ⟨(0, 0), fun h => absurd h hi⟩
  choose v hv using hv
  -- the chains
  have key : ∀ k, k ≤ n + 1 → ∃ c : Finset G.Edge, G.bdy c = symmDiff {v 0} {v k} ∧
      ∀ e ∈ c, ∀ p ∈ G.seg e, ∃ i < k, dist p (z i) < δ / 2 := by
    intro k
    induction k with
    | zero => intro _; exact ⟨∅, by simp [bdy, deg], by simp⟩
    | succ k ih =>
      intro hk
      obtain ⟨c, hcb, hc⟩ := ih (by omega)
      obtain ⟨c', hc'b, hc'⟩ := G.exists_chain_box (v k) (v (k + 1))
      refine ⟨symmDiff c c', ?_, ?_⟩
      · rw [bdy_symmDiff, hcb, hc'b]; exact symmDiff_pair_trans _ _ _
      · intro e he p hp
        rcases Finset.mem_symmDiff.1 he with ⟨h1, _⟩ | ⟨h1, _⟩
        · obtain ⟨i, hi, hd⟩ := hc e h1 p hp
          exact ⟨i, by omega, hd⟩
        · have hb := hc' e h1 hp
          rw [hv k (by omega), hv (k + 1) (by omega)] at hb
          refine ⟨k, by omega, lt_of_le_of_lt (dist_le_of_mem_Box hb) ?_⟩
          rw [dist_comm]; exact hzd k
  obtain ⟨c, hcb, hc⟩ := key (n + 1) le_rfl
  refine ⟨v 0, v (n + 1), c, ?_, ?_, ?_, hcb⟩
  · rw [hv 0 (by omega), hz0]
  · rw [hv (n + 1) (by omega), hzN]
  · intro p hp a ha
    simp only [locus, Set.mem_iUnion] at hp
    obtain ⟨e, he, hpe⟩ := hp
    obtain ⟨i, _, hd⟩ := hc e he p hpe
    have h1 := hzA i a ha
    have h2 := dist_triangle a p (z i)
    have h3 := dist_comm p a
    linarith

end Grating

end Lightlike.PL
