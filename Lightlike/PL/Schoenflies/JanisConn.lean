import Lightlike.PL.UnionLemma

/-!
# Two compact sets with connected intersection

Row G3-188 (PL5), step 1 of the pass-4 plan.  `joinedIn_union_compl_of_isPreconnected` is Janiszewski's
theorem for two compact sets of the plane whose intersection is connected: the proof of
`joinedIn_union_compl` with the point `R` replaced by the connected set `K₁ ∩ K₂` (the cells near the
intersection are all in the 2-chain or all outside it, by connectedness of the intersection and
`Grating.near_const` at each of its points).
-/

open Set Finset Metric

namespace Lightlike.PL

namespace Grating

/-- Every real in `[a 0, a (last)]` lies in some interval `[a i.castSucc, a i.succ]`. -/
lemma exists_index {n : ℕ} {a : Fin (n + 1) → ℝ} (ha : StrictMono a) {x : ℝ}
    (h0 : a 0 ≤ x) (hl : x ≤ a (Fin.last n)) (hn : a 0 < a (Fin.last n)) :
    ∃ i : Fin n, a i.castSucc ≤ x ∧ x ≤ a i.succ := by
  by_contra hno
  push Not at hno
  have key : ∀ k : ℕ, ∀ hk : k < n + 1, a ⟨k, hk⟩ ≤ x := by
    intro k
    induction k with
    | zero => intro hk; exact h0
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 := hno ⟨k, by omega⟩ h1
      exact (lt_of_not_ge fun h => absurd h (not_le.2 (by simpa using h2))) |>.le
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
    rcases n with _ | m
    · exact absurd hn (by simp)
    · exact ⟨m, rfl⟩
  have h1 := key m (by omega)
  have h2 := hno ⟨m, by omega⟩ h1
  have h3 : a (Fin.last (m + 1)) = a (Fin.succ ⟨m, by omega⟩) := rfl
  rw [h3] at hl
  exact absurd hl (not_le.2 h2)

end Grating

theorem joinedIn_union_compl_of_isPreconnected {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsCompact K₁) (h₂ : IsCompact K₂)
    (hD : IsPreconnected (K₁ ∩ K₂)) {P Q : ℝ × ℝ}
    (hP : JoinedIn K₁ᶜ P Q) (hQ : JoinedIn K₂ᶜ P Q) : JoinedIn (K₁ ∪ K₂)ᶜ P Q := by
  classical
  have hPK₁ : P ∉ K₁ := hP.source_mem
  have hQK₁ : Q ∉ K₁ := hP.target_mem
  have hPK₂ : P ∉ K₂ := hQ.source_mem
  have hQK₂ : Q ∉ K₂ := hQ.target_mem
  obtain ⟨ρ₁, hρ₁, Xs₁, Ys₁, H₁⟩ := Grating.exists_chain_of_joinedIn h₁ hP
  obtain ⟨ρ₂, hρ₂, Xs₂, Ys₂, H₂⟩ := Grating.exists_chain_of_joinedIn h₂ hQ
  set ρ := min ρ₁ ρ₂ with hρ
  have hρpos : 0 < ρ := lt_min hρ₁ hρ₂
  set r := ρ / 4 with hr
  have hrpos : 0 < r := by positivity
  -- the separation of the two sets away from the intersection
  have hK₁' : IsCompact (K₁ \ thickening r (K₁ ∩ K₂)) := h₁.diff isOpen_thickening
  have hK₂' : IsCompact (K₂ \ thickening r (K₁ ∩ K₂)) := h₂.diff isOpen_thickening
  have hdisj : Disjoint (K₁ \ thickening r (K₁ ∩ K₂)) (K₂ \ thickening r (K₁ ∩ K₂)) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    exact hx1.2 (self_subset_thickening hrpos _ ⟨hx1.1, hx2.1⟩)
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
  -- the cycle stays away from the intersection
  have hside : ∀ d ∈ K₁ ∩ K₂, ∀ e ∈ G.bdy₂ w₀, ∀ p ∈ G.seg e, r + ε < dist p d := by
    intro d hd e he p hp
    rw [hw₀] at he
    have hεr : ε ≤ r := min_le_right _ _
    have hρr : ρ = 4 * r := by rw [hr]; ring
    rcases Finset.mem_symmDiff.1 he with ⟨h, _⟩ | ⟨h, _⟩
    · have := hd₁ p (by simp only [Grating.locus, Set.mem_iUnion]; exact ⟨e, h, hp⟩) d hd.1
      have := min_le_left ρ₁ ρ₂
      linarith
    · have := hd₂ p (by simp only [Grating.locus, Set.mem_iUnion]; exact ⟨e, h, hp⟩) d hd.2
      have := min_le_right ρ₁ ρ₂
      linarith
  have hnearconst : ∀ d ∈ K₁ ∩ K₂, ∀ {c c' : G.Cell}, G.Near d r c → G.Near d r c' →
      (c ∈ w₀ ↔ c' ∈ w₀) :=
    fun d hd c c' hc hc' => Grating.near_const hrpos.le (hside d hd) hmx hmy hc hc'
  -- every point of the box lies in a cell
  have hcover : ∀ d ∈ K₁ ∪ K₂, ∃ c : G.Cell, G.Near d r c := by
    intro d hd
    have hdM := hKM d hd
    have h1 := abs_lt.1 hdM.1
    have h2 := abs_lt.1 hdM.2
    obtain ⟨i, hi⟩ := Grating.exists_index (x := d.1) G.ha (by linarith [h1.1]) (by linarith [h1.2]) (by linarith)
    obtain ⟨j, hj⟩ := Grating.exists_index (x := d.2) G.hb (by linarith [h2.1]) (by linarith [h2.2]) (by linarith)
    refine ⟨(i, j), ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp only [] <;> linarith [hi.1, hi.2, hj.1, hj.2, hrpos]
  have hclosedNear : ∀ c : G.Cell, IsClosed {d : ℝ × ℝ | G.Near d r c} := by
    intro c
    simp only [Grating.Near, Set.ofPred_and]
    refine ((isClosed_le ?_ ?_).inter (isClosed_le ?_ ?_)).inter
      ((isClosed_le ?_ ?_).inter (isClosed_le ?_ ?_)) <;> fun_prop
  -- the cells near the intersection are all in the 2-chain or all outside it
  have hconst : (∃ d ∈ K₁ ∩ K₂, ∃ c, G.Near d r c ∧ c ∈ w₀) →
      ∀ d ∈ K₁ ∩ K₂, ∀ c, G.Near d r c → c ∈ w₀ := by
    rintro ⟨d₀, hd₀, c₀, hc₀, hc₀w⟩
    have hS : IsClosed {d : ℝ × ℝ | ∃ c, c ∈ w₀ ∧ G.Near d r c} := by
      have : {d : ℝ × ℝ | ∃ c, c ∈ w₀ ∧ G.Near d r c} =
          ⋃ c : G.Cell, ⋃ _ : c ∈ w₀, {d : ℝ × ℝ | G.Near d r c} := by
        ext d; simp
      rw [this]
      exact isClosed_iUnion_of_finite fun c => isClosed_iUnion_of_finite fun _ => hclosedNear c
    have hT : IsClosed {d : ℝ × ℝ | ∃ c, c ∉ w₀ ∧ G.Near d r c} := by
      have : {d : ℝ × ℝ | ∃ c, c ∉ w₀ ∧ G.Near d r c} =
          ⋃ c : G.Cell, ⋃ _ : c ∉ w₀, {d : ℝ × ℝ | G.Near d r c} := by
        ext d; simp
      rw [this]
      exact isClosed_iUnion_of_finite fun c => isClosed_iUnion_of_finite fun _ => hclosedNear c
    have hsub : K₁ ∩ K₂ ⊆ {d : ℝ × ℝ | ∃ c, c ∈ w₀ ∧ G.Near d r c} ∪
        {d : ℝ × ℝ | ∃ c, c ∉ w₀ ∧ G.Near d r c} := by
      intro d hd
      obtain ⟨c, hc⟩ := hcover d (Or.inl hd.1)
      by_cases hcw : c ∈ w₀
      · exact Or.inl ⟨c, hcw, hc⟩
      · exact Or.inr ⟨c, hcw, hc⟩
    have hempty : ∀ d ∈ K₁ ∩ K₂, ¬ ((∃ c, c ∈ w₀ ∧ G.Near d r c) ∧ (∃ c, c ∉ w₀ ∧ G.Near d r c)) := by
      rintro d hd ⟨⟨c, hc, hcn⟩, ⟨c', hc', hcn'⟩⟩
      exact hc' ((hnearconst d hd hcn hcn').1 hc)
    have hne1 : ((K₁ ∩ K₂) ∩ {d : ℝ × ℝ | ∃ c, c ∈ w₀ ∧ G.Near d r c}).Nonempty :=
      ⟨d₀, hd₀, c₀, hc₀w, hc₀⟩
    intro d hd c hc
    by_contra hcw
    have hne2 : ((K₁ ∩ K₂) ∩ {d : ℝ × ℝ | ∃ c, c ∉ w₀ ∧ G.Near d r c}).Nonempty :=
      ⟨d, hd, c, hcw, hc⟩
    obtain ⟨d', hd', h1, h2⟩ := isPreconnected_closed_iff.1 hD _ _ hS hT hsub hne1 hne2
    exact hempty d' hd' ⟨h1, h2⟩
  -- choose the side of the cycle away from the intersection
  obtain ⟨w, E, hE, hw, hnear⟩ : ∃ (w : Finset G.Cell) (E : Finset G.Edge),
      (∀ e ∈ E, Disjoint (G.seg e) (K₁ ∪ K₂)) ∧ symmDiff (G.bdy₂ w) E = symmDiff l₁ l₂ ∧
        ∀ c ∈ w, ∀ d ∈ K₁ ∩ K₂, ¬ G.Near d r c := by
    by_cases hN : ∃ d ∈ K₁ ∩ K₂, ∃ c, G.Near d r c ∧ c ∈ w₀
    · have hall := hconst hN
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
      · intro c hc d hd hnc
        exact (Finset.mem_sdiff.1 hc).2 (hall d hd c hnc)
    · refine ⟨w₀, ∅, by simp, by rw [hw₀]; simp, ?_⟩
      intro c hc d hd hnc
      exact hN ⟨d, hd, c, hnc, hc⟩
  -- no cell of `w` meets both sets
  have hfine : ∀ c ∈ w, ¬ ((G.cellSet c ∩ K₁).Nonempty ∧ (G.cellSet c ∩ K₂).Nonempty) := by
    rintro c hc ⟨⟨p, hpc, hp1⟩, ⟨q, hqc, hq2⟩⟩
    have hfar : ∀ x ∈ G.cellSet c, x ∉ thickening r (K₁ ∩ K₂) := by
      intro x hx hxt
      obtain ⟨d, hd, hxd⟩ := Metric.mem_thickening_iff.1 hxt
      exact hnear c hc d hd (Grating.near_of_mem hx hxd.le)
    have hp' : p ∈ K₁ \ thickening r (K₁ ∩ K₂) := ⟨hp1, hfar p hpc⟩
    have hq' : q ∈ K₂ \ thickening r (K₁ ∩ K₂) := ⟨hq2, hfar q hqc⟩
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
