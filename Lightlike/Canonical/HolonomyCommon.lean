import Lightlike.Canonical.HolonomyALOrder

/-!
# The common refinement of two graphs of Ashtekar–Lewandowski

Two graphs `α₁`, `α₂` have a common refinement `α₃` (Ashtekar–Lewandowski, arXiv:gr-qc/0404018, p. 35: "we can introduce
a third graph `α3` which contains all the edges and vertices of `α1` and `α2`"). The construction cuts every edge at the
parameters mapped into a finite set of points `Z`: the end points and midpoints of all analytic pieces of both graphs and
the boundary points of the sets where a piece of one graph meets a piece of the other (finitely many,
`Edge.meetFrontier_finite`).

* Each segment between consecutive cut parameters lies in one analytic piece, and the path is injective on it
  (`CutData.segment_in_piece`, `CutData.injOn_segment`).
* A segment of `α₂` either meets `α₁` only at its end points, or its open part is the open part of a segment of `α₁`
  (`seg_classify`); the step uses `Edge.meet_dichotomy` and an open-closed argument (`image_Ioo_subset`).
* Two embedded arcs with the same open image differ by a continuous monotone or antitone reparametrisation
  (`exists_reparam`).
* `α₃` (`common`) has as edges the segments of `α₁` and the segments of `α₂` missing `α₁`; `α₁ ≤ α₃` and `α₂ ≤ α₃`
  (`le_common_left`, `le_common_right`), so the refinement order is directed (`directed`); `α₃` contains the vertices of
  both graphs (`vertices_subset_of_le`) and the holonomies of both graphs are products of holonomies along its edges
  (`exists_common_hol`).
-/

open Set Filter
open scoped Topology

noncomputable section

namespace Lightlike.Canonical

namespace ALEdge

variable (E : ALEdge)

/-- An embedded edge meets a finite set of points at finitely many parameters. -/
lemma finite_preimage (hIco : InjOn E.path (Ico E.t₀ E.t₁)) {Z : Set (Fin 3 → ℝ)} (hZ : Z.Finite) :
    {s | s ∈ Icc E.t₀ E.t₁ ∧ E.path s ∈ Z}.Finite := by
  have h1 : {s | s ∈ Ico E.t₀ E.t₁ ∧ E.path s ∈ Z}.Finite :=
    Set.Finite.of_finite_image (hZ.subset fun z ⟨s, hs, hsz⟩ => hsz ▸ hs.2)
      (hIco.mono fun s hs => hs.1)
  refine (h1.union (Set.finite_singleton E.t₁)).subset fun s hs => ?_
  rcases eq_or_lt_of_le hs.1.2 with h | h
  · exact Or.inr h
  · exact Or.inl ⟨⟨hs.1.1, h⟩, hs.2⟩

/-- The midpoint of a piece. -/
def mid (j : Fin E.k) : ℝ := (E.τ j.castSucc + E.τ j.succ) / 2

end ALEdge

namespace ALGraph

variable (α : ALGraph)

/-- The end points and midpoints of the analytic pieces of a graph, as points. -/
def piecePoints : Set (Fin 3 → ℝ) :=
  ⋃ p : α.PieceIdx, {(α.pieceOf p).source, (α.pieceOf p).target,
    (α.edge p.1).path ((α.edge p.1).mid p.2)}

/-- Finitely many. -/
lemma piecePoints_finite : α.piecePoints.Finite :=
  Set.finite_iUnion fun _ => (Set.toFinite _)

end ALGraph

/-- The **cut points** for two graphs: the end points and midpoints of all analytic pieces of both, and the images of the
boundary points of the sets where a piece of one meets a piece of the other. -/
def cutPoints (α₁ α₂ : ALGraph) : Set (Fin 3 → ℝ) :=
  α₁.piecePoints ∪ α₂.piecePoints ∪
    (⋃ p : α₁.PieceIdx, ⋃ q : α₂.PieceIdx, (α₁.pieceOf p).path '' Edge.meetFrontier (α₁.pieceOf p) (α₂.pieceOf q)) ∪
    (⋃ q : α₂.PieceIdx, ⋃ p : α₁.PieceIdx, (α₂.pieceOf q).path '' Edge.meetFrontier (α₂.pieceOf q) (α₁.pieceOf p))

/-- The pieces of an edge of Ashtekar–Lewandowski are regular analytic arcs. -/
lemma ALGraph.pieceOf_isAnalytic (α : ALGraph) (p : α.PieceIdx) : (α.pieceOf p).IsAnalytic :=
  (α.edge p.1).arc_analytic p.2

/-- **There are finitely many cut points.** -/
theorem cutPoints_finite (α₁ α₂ : ALGraph) : (cutPoints α₁ α₂).Finite := by
  refine ((α₁.piecePoints_finite.union α₂.piecePoints_finite).union ?_).union ?_
  · exact Set.finite_iUnion fun p => Set.finite_iUnion fun q =>
      (Edge.meetFrontier_finite (α₁.pieceOf_isAnalytic p) (α₂.pieceOf_isAnalytic q)).image _
  · exact Set.finite_iUnion fun q => Set.finite_iUnion fun p =>
      (Edge.meetFrontier_finite (α₂.pieceOf_isAnalytic q) (α₁.pieceOf_isAnalytic p)).image _

/-- **The open-closed step of the common refinement.** Let `g` be continuous on `[p₀, p₁] ⊇ [a, b]`, injective at the
points of `(a, b)` within `[p₀, p₁]`, and `h` continuous on `[c, d]` with `h((c, d))` inside `g([p₀, p₁])` and avoiding
`g(a)`, `g(b)`. If `h((c, d))` meets `g((a, b))`, then `h((c, d)) ⊆ g((a, b))`. -/
lemma image_Ioo_subset {g h : ℝ → Fin 3 → ℝ} {a b c d p₀ p₁ : ℝ} (hg : ContinuousOn g (Icc p₀ p₁))
    (hh : ContinuousOn h (Icc c d)) (hab : Icc a b ⊆ Icc p₀ p₁)
    (hinj : ∀ s ∈ Ioo a b, ∀ s' ∈ Icc p₀ p₁, g s' = g s → s' = s)
    (hP : ∀ t ∈ Ioo c d, h t ∈ g '' Icc p₀ p₁) (hend : ∀ t ∈ Ioo c d, h t ≠ g a ∧ h t ≠ g b)
    (hne : ∃ t ∈ Ioo c d, h t ∈ g '' Ioo a b) : ∀ t ∈ Ioo c d, h t ∈ g '' Ioo a b := by
  classical
  set χ : ℝ → Bool := fun t => decide (h t ∈ g '' Ioo a b) with hχ
  have hcont : ∀ t ∈ Ioo c d, ContinuousAt h t := fun t ht =>
    (hh t (Ioo_subset_Icc_self ht)).continuousAt (Icc_mem_nhds ht.1 ht.2)
  have hloc : ContinuousOn χ (Ioo c d) := by
    intro t ht
    refine tendsto_nhds_of_eventually_eq (nhdsWithin_le_nhds ?_)
    by_cases hT : h t ∈ g '' Ioo a b
    · -- `T` is open
      have hχt : χ t = true := by simp only [hχ, decide_eq_true_eq]; exact hT
      obtain ⟨s₀, hs₀, hgs₀⟩ := hT
      by_contra hcon
      obtain ⟨u, hu, hu'⟩ := exists_seq_forall_of_frequently (Filter.not_eventually.1 hcon)
      have huev : ∀ᶠ n in atTop, u n ∈ Ioo c d := hu.eventually (isOpen_Ioo.mem_nhds ht)
      obtain ⟨N, hN⟩ := huev.exists_forall_of_atTop
      have hmem : ∀ n, h (u (n + N)) ∈ g '' Icc p₀ p₁ := fun n => hP _ (hN _ (Nat.le_add_left _ _))
      choose v hv hgv using hmem
      obtain ⟨s', hs', φ, hφ, hvφ⟩ := isCompact_Icc.tendsto_subseq hv
      have hlim : g s' = h t := by
        have h1 : Tendsto (fun n => g (v (φ n))) atTop (𝓝 (g s')) :=
          ((hg s' hs').tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hvφ, Eventually.of_forall fun n => hv _⟩))
        have h2 : Tendsto (fun n => h (u (φ n + N))) atTop (𝓝 (h t)) :=
          (hcont t ht).tendsto.comp (hu.comp ((tendsto_add_atTop_nat N).comp hφ.tendsto_atTop))
        refine tendsto_nhds_unique h1 ?_
        simpa only [hgv] using h2
      have hs'eq : s' = s₀ := hinj s₀ hs₀ s' hs' (hlim.trans hgs₀.symm)
      have hev : ∀ᶠ n in atTop, v (φ n) ∈ Ioo a b := hvφ.eventually (hs'eq ▸ isOpen_Ioo.mem_nhds hs₀)
      obtain ⟨n, hn⟩ := hev.exists
      exact (hu' (φ n + N)) (by rw [hχt]; simp only [hχ, decide_eq_true_eq]; exact ⟨v (φ n), hn, hgv _⟩)
    · -- the complement of `T` is open
      have hχt : χ t = false := by simp only [hχ, decide_eq_false_iff_not]; exact hT
      by_contra hcon
      obtain ⟨u, hu, hu'⟩ := exists_seq_forall_of_frequently (Filter.not_eventually.1 hcon)
      have hmem : ∀ n, h (u n) ∈ g '' Ioo a b := fun n => by
        have := hu' n; rw [hχt] at this
        simp only [hχ, decide_eq_false_iff_not, not_not] at this
        exact this
      choose v hv hgv using hmem
      obtain ⟨s', hs', φ, hφ, hvφ⟩ := isCompact_Icc.tendsto_subseq (fun n => Ioo_subset_Icc_self (hv n))
      have hlim : g s' = h t := by
        have h1 : Tendsto (fun n => g (v (φ n))) atTop (𝓝 (g s')) :=
          ((hg s' (hab hs')).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hvφ, Eventually.of_forall fun n =>
            hab (Ioo_subset_Icc_self (hv _))⟩))
        have h2 : Tendsto (fun n => h (u (φ n))) atTop (𝓝 (h t)) :=
          (hcont t ht).tendsto.comp (hu.comp hφ.tendsto_atTop)
        refine tendsto_nhds_unique h1 ?_
        simpa only [hgv] using h2
      rcases eq_or_lt_of_le hs'.1 with h1 | h1
      · exact (hend t ht).1 (by rw [← hlim, h1])
      rcases eq_or_lt_of_le hs'.2 with h2 | h2
      · exact (hend t ht).2 (by rw [← hlim, h2])
      exact hT ⟨s', ⟨h1, h2⟩, hlim⟩
  obtain ⟨t₀, ht₀, hT₀⟩ := hne
  intro t ht
  have h1 : χ t₀ = true := by simp only [hχ, decide_eq_true_eq]; exact hT₀
  have h2 : χ t = true := (isPreconnected_Ioo.constant hloc ht ht₀).trans h1
  simpa only [hχ, decide_eq_true_eq] using h2

/-- **Two embedded arcs with the same open image are reparametrisations of each other.** If `g` and `h` are continuous
and injective on `[a, b]` and `[c, d]`, their open parts have the same image, and `h(c)`, `h(d)` are not in it, then
`h = g ∘ ψ` on `[c, d]` for a continuous `ψ` that is monotone from `a` to `b` or antitone from `b` to `a`. -/
lemma exists_reparam {g h : ℝ → Fin 3 → ℝ} {a b c d : ℝ} (hab : a < b) (hcd : c < d) (hg : ContinuousOn g (Icc a b))
    (hgi : InjOn g (Icc a b)) (hh : ContinuousOn h (Icc c d)) (hhi : InjOn h (Icc c d))
    (heq : g '' Ioo a b = h '' Ioo c d) (hc : h c ∉ g '' Ioo a b) (hd : h d ∉ g '' Ioo a b) :
    ∃ ψ : ℝ → ℝ, ContinuousOn ψ (Icc c d) ∧ EqOn h (g ∘ ψ) (Icc c d) ∧
      ((MonotoneOn ψ (Icc c d) ∧ ψ c = a ∧ ψ d = b) ∨ (AntitoneOn ψ (Icc c d) ∧ ψ c = b ∧ ψ d = a)) := by
  classical
  -- `h` maps `[c, d]` into `g([a, b])`
  have hImg : h '' Icc c d ⊆ g '' Icc a b := by
    have hcl : IsClosed (g '' Icc a b) := (isCompact_Icc.image_of_continuousOn hg).isClosed
    rw [← closure_Ioo hcd.ne]
    refine ((closure_Ioo hcd.ne).symm ▸ hh).image_closure.trans ?_
    rw [← heq]
    exact closure_minimal (image_mono Ioo_subset_Icc_self) hcl
  -- the inverse of `g` on `[a, b]`, composed with `h`
  set g' : Icc a b → Fin 3 → ℝ := fun x => g x with hg'
  have hg'c : Continuous g' := continuousOn_iff_continuous_domRestrict.1 hg
  have hg'i : Function.Injective g' := fun x y hxy => Subtype.ext (hgi x.2 y.2 hxy)
  have hind : Topology.IsInducing g' := (hg'c.isClosedEmbedding hg'i).isInducing
  set f : ℝ → Icc a b := fun t => if ht : h t ∈ g '' Icc a b then ⟨ht.choose, ht.choose_spec.1⟩
    else ⟨a, left_mem_Icc.2 hab.le⟩ with hf
  have hfg : ∀ t ∈ Icc c d, g' (f t) = h t := fun t ht => by
    have ht' : h t ∈ g '' Icc a b := hImg ⟨t, ht, rfl⟩
    simp only [hg', hf, ht', ↓reduceDIte]
    exact ht'.choose_spec.2
  have hfc : ContinuousOn f (Icc c d) := by
    rw [hind.continuousOn_iff]
    exact hh.congr fun t ht => hfg t ht
  set ψ : ℝ → ℝ := fun t => (f t : ℝ) with hψ
  have hψc : ContinuousOn ψ (Icc c d) := continuous_subtype_val.comp_continuousOn hfc
  have hψe : EqOn h (g ∘ ψ) (Icc c d) := fun t ht => (hfg t ht).symm
  have hψI : ∀ t, ψ t ∈ Icc a b := fun t => (f t).2
  have hψi : InjOn ψ (Icc c d) := fun x hx y hy hxy => hhi hx hy (by rw [hψe hx, hψe hy]; simp [hxy])
  have hend : ∀ t ∈ Icc c d, h t ∉ g '' Ioo a b → ψ t = a ∨ ψ t = b := fun t ht hn => by
    by_contra hcon
    push Not at hcon
    exact hn ⟨ψ t, ⟨lt_of_le_of_ne (hψI t).1 hcon.1.symm, lt_of_le_of_ne (hψI t).2 hcon.2⟩, (hψe ht).symm⟩
  have hcI : c ∈ Icc c d := left_mem_Icc.2 hcd.le
  have hdI : d ∈ Icc c d := right_mem_Icc.2 hcd.le
  have hc' := hend c hcI hc
  have hd' := hend d hdI hd
  refine ⟨ψ, hψc, hψe, ?_⟩
  rcases hψc.strictMonoOn_of_injOn_Icc' hcd.le hψi with hm | hm
  · left
    have hlt := hm hcI hdI hcd
    refine ⟨hm.monotoneOn, ?_, ?_⟩
    · rcases hc' with h1 | h1
      · exact h1
      · exfalso; linarith [(hψI d).2]
    · rcases hd' with h1 | h1
      · exfalso; linarith [(hψI c).1]
      · exact h1
  · right
    have hlt := hm hcI hdI hcd
    refine ⟨hm.antitoneOn, ?_, ?_⟩
    · rcases hc' with h1 | h1
      · exfalso; linarith [(hψI d).1]
      · exact h1
    · rcases hd' with h1 | h1
      · exact h1
      · exfalso; linarith [(hψI c).2]

namespace ALGraph

/-- A finite set of points containing the end points and midpoints of the pieces of `α`: the data of a cutting. -/
structure CutData (α : ALGraph) where
  /-- The cut points. -/
  Z : Set (Fin 3 → ℝ)
  /-- Finitely many. -/
  finite : Z.Finite
  /-- Containing the end points and midpoints of the pieces. -/
  sub : α.piecePoints ⊆ Z

namespace CutData

variable {α : ALGraph} (D : α.CutData)

/-- The **cut parameters** of the edge `i`: those mapped into `Z`. -/
def cutSet (i : Fin α.m) : Finset ℝ := ((α.edge i).finite_preimage (α.injOn_Ico i) D.finite).toFinset

/-- The cut parameters are the parameters of the edge mapped into `Z`. -/
lemma mem_cutSet {i : Fin α.m} {s : ℝ} :
    s ∈ D.cutSet i ↔ s ∈ Icc (α.edge i).t₀ (α.edge i).t₁ ∧ (α.edge i).path s ∈ D.Z := by
  simp [cutSet]

/-- The subdivision points of an edge are cut parameters. -/
lemma τ_mem_cutSet (i : Fin α.m) (σ : Fin ((α.edge i).k + 1)) : (α.edge i).τ σ ∈ D.cutSet i := by
  rw [mem_cutSet]
  refine ⟨⟨(α.edge i).τ_mono.monotone (Fin.zero_le _), (α.edge i).τ_mono.monotone (Fin.le_last _)⟩, D.sub ?_⟩
  induction σ using Fin.cases with
  | zero =>
    refine mem_iUnion.2 ⟨⟨i, α.first i⟩, Or.inl ?_⟩
    exact ((α.edge i).arc_eq _ ⟨le_rfl, ((α.edge i).piece_lt (α.first i)).le⟩)
  | succ j =>
    refine mem_iUnion.2 ⟨⟨i, j⟩, Or.inr (Or.inl ?_)⟩
    exact ((α.edge i).arc_eq j ⟨((α.edge i).piece_lt j).le, le_rfl⟩)

/-- The midpoints of the pieces are cut parameters. -/
lemma mid_mem_cutSet (i : Fin α.m) (j : Fin (α.edge i).k) : (α.edge i).mid j ∈ D.cutSet i := by
  rw [mem_cutSet]
  have h1 := (α.edge i).piece_lt j
  have h2 := (α.edge i).piece_subset j
  refine ⟨h2 ⟨?_, ?_⟩, D.sub (mem_iUnion.2 ⟨⟨i, j⟩, Or.inr (Or.inr rfl)⟩)⟩ <;>
    simp only [ALEdge.mid, ALEdge.piece] at h1 ⊢ <;> linarith

/-- There are at least two cut parameters. -/
lemma two_le_card (i : Fin α.m) : 2 ≤ (D.cutSet i).card := by
  have hne : (α.edge i).τ 0 ≠ (α.edge i).τ (Fin.last _) := (α.edge i).t₀_lt_t₁.ne
  exact Finset.one_lt_card.2 ⟨_, D.τ_mem_cutSet i 0, _, D.τ_mem_cutSet i (Fin.last _), hne⟩

/-- The number of segments of the edge `i`. -/
def nSeg (i : Fin α.m) : ℕ := (D.cutSet i).card - 1

/-- The number of cut parameters is one more than the number of segments. -/
lemma card_cutSet (i : Fin α.m) : (D.cutSet i).card = D.nSeg i + 1 := by
  have := D.two_le_card i
  unfold nSeg; omega

/-- The cut parameters of the edge `i`, in increasing order. -/
def cutPt (i : Fin α.m) : Fin (D.nSeg i + 1) ↪o ℝ := (D.cutSet i).orderEmbOfFin (D.card_cutSet i)

/-- The sorted cut parameters are cut parameters. -/
lemma cutPt_mem (i : Fin α.m) (l : Fin (D.nSeg i + 1)) : D.cutPt i l ∈ D.cutSet i :=
  Finset.orderEmbOfFin_mem _ _ _

/-- The cut parameters lie in the parameter interval. -/
lemma cutPt_Icc (i : Fin α.m) (l : Fin (D.nSeg i + 1)) : D.cutPt i l ∈ Icc (α.edge i).t₀ (α.edge i).t₁ :=
  ((mem_cutSet D).1 (D.cutPt_mem i l)).1

/-- The path maps the cut parameters into `Z`. -/
lemma cutPt_Z (i : Fin α.m) (l : Fin (D.nSeg i + 1)) : (α.edge i).path (D.cutPt i l) ∈ D.Z :=
  ((mem_cutSet D).1 (D.cutPt_mem i l)).2

/-- The first cut parameter is the initial parameter `t₀`. -/
lemma cutPt_zero (i : Fin α.m) : D.cutPt i 0 = (α.edge i).t₀ := by
  have h := Finset.orderEmbOfFin_zero (D.card_cutSet i) (Nat.succ_pos _)
  refine le_antisymm ?_ (D.cutPt_Icc i 0).1
  rw [cutPt, show (0 : Fin (D.nSeg i + 1)) = ⟨0, Nat.succ_pos _⟩ from rfl, h]
  exact Finset.min'_le _ _ (D.τ_mem_cutSet i 0)

/-- The last cut parameter is the final parameter `t₁`. -/
lemma cutPt_last (i : Fin α.m) : D.cutPt i (Fin.last _) = (α.edge i).t₁ := by
  have h := Finset.orderEmbOfFin_last (D.card_cutSet i) (Nat.succ_pos _)
  refine le_antisymm (D.cutPt_Icc i _).2 ?_
  rw [cutPt, show (Fin.last (D.nSeg i)) = ⟨D.nSeg i + 1 - 1, by omega⟩ from Fin.ext (by simp), h]
  exact Finset.le_max' _ _ (D.τ_mem_cutSet i (Fin.last _))

/-- Consecutive cut parameters are increasing. -/
lemma cutPt_lt (i : Fin α.m) (l : Fin (D.nSeg i)) : D.cutPt i l.castSucc < D.cutPt i l.succ :=
  (D.cutPt i).strictMono Fin.castSucc_lt_succ

/-- No cut parameter lies strictly between two consecutive ones. -/
lemma not_mem_between (i : Fin α.m) (l : Fin (D.nSeg i)) {x : ℝ} (h₁ : D.cutPt i l.castSucc < x)
    (h₂ : x < D.cutPt i l.succ) : x ∉ D.cutSet i := by
  intro hx
  have : x ∈ Set.range (D.cutPt i) := by
    rw [cutPt, Finset.range_orderEmbOfFin]; exact hx
  obtain ⟨m, rfl⟩ := this
  have e1 := (D.cutPt i).lt_iff_lt.1 h₁
  have e2 := (D.cutPt i).lt_iff_lt.1 h₂
  rw [Fin.lt_def] at e1 e2
  simp at e1 e2
  omega

/-- The path strictly inside a segment avoids the cut points. -/
lemma path_not_mem (i : Fin α.m) (l : Fin (D.nSeg i)) {x : ℝ}
    (hx : x ∈ Ioo (D.cutPt i l.castSucc) (D.cutPt i l.succ)) : (α.edge i).path x ∉ D.Z := fun h =>
  D.not_mem_between i l hx.1 hx.2 ((mem_cutSet D).2
    ⟨⟨(D.cutPt_Icc i _).1.trans hx.1.le, hx.2.le.trans (D.cutPt_Icc i _).2⟩, h⟩)

/-- **Each segment lies in one analytic piece**, on one side of its midpoint. -/
lemma segment_in_piece (i : Fin α.m) (l : Fin (D.nSeg i)) : ∃ j : Fin (α.edge i).k,
    (α.edge i).τ j.castSucc ≤ D.cutPt i l.castSucc ∧ D.cutPt i l.succ ≤ (α.edge i).τ j.succ ∧
    (D.cutPt i l.succ ≤ (α.edge i).mid j ∨ (α.edge i).mid j ≤ D.cutPt i l.castSucc) := by
  have hlt := D.cutPt_lt i l
  have ha := D.cutPt_Icc i l.castSucc
  have hb := D.cutPt_Icc i l.succ
  obtain ⟨j, hj1, hj2⟩ := (α.edge i).exists_piece ⟨ha.1, hlt.trans_le hb.2⟩
  refine ⟨j, hj1, ?_, ?_⟩
  · by_contra h
    exact D.not_mem_between i l hj2 (not_le.1 h) (D.τ_mem_cutSet i _)
  · by_contra h
    push Not at h
    exact D.not_mem_between i l h.2 h.1 (D.mid_mem_cutSet i j)

/-- **The path is injective on each closed segment.** -/
lemma injOn_segment (i : Fin α.m) (l : Fin (D.nSeg i)) :
    InjOn (α.edge i).path (Icc (D.cutPt i l.castSucc) (D.cutPt i l.succ)) := by
  intro x hx y hy hxy
  have hsub : Icc (D.cutPt i l.castSucc) (D.cutPt i l.succ) ⊆ Icc (α.edge i).t₀ (α.edge i).t₁ :=
    Icc_subset_Icc (D.cutPt_Icc i _).1 (D.cutPt_Icc i _).2
  obtain ⟨j, hj1, hj2, hj3⟩ := D.segment_in_piece i l
  have hp := (α.edge i).piece_lt j
  have ht0 := ((α.edge i).piece_subset j ⟨le_rfl, hp.le⟩).1
  have ht1 := ((α.edge i).piece_subset j ⟨hp.le, le_rfl⟩).2
  simp only [ALEdge.piece, ALEdge.mid] at hp ht0 ht1 hj3
  rcases (α.edge i).eq_or_ends (hsub hx) (hsub hy) (α.injOn_Ico i) (α.injOn_Ioc i) hxy with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h
  · exfalso
    have : D.cutPt i l.castSucc ≤ (α.edge i).t₀ := h1 ▸ hx.1
    have : (α.edge i).t₁ ≤ D.cutPt i l.succ := h2 ▸ hy.2
    rcases hj3 with h | h <;> linarith
  · exfalso
    have : D.cutPt i l.castSucc ≤ (α.edge i).t₀ := h2 ▸ hy.1
    have : (α.edge i).t₁ ≤ D.cutPt i l.succ := h1 ▸ hx.2
    rcases hj3 with h | h <;> linarith

end CutData

end ALGraph

namespace ALGraph

/-- The cut data of `α₁` for the pair `(α₁, α₂)`. -/
def cut₁ (α₁ α₂ : ALGraph) : α₁.CutData :=
  ⟨cutPoints α₁ α₂, cutPoints_finite α₁ α₂, fun _ h => Or.inl (Or.inl (Or.inl h))⟩

/-- The cut data of `α₂` for the pair `(α₁, α₂)`. -/
def cut₂ (α₁ α₂ : ALGraph) : α₂.CutData :=
  ⟨cutPoints α₁ α₂, cutPoints_finite α₁ α₂, fun _ h => Or.inl (Or.inl (Or.inr h))⟩

variable {α : ALGraph}

/-- The path of an edge is continuous on each piece. -/
lemma continuousOn_path_piece (i : Fin α.m) (j : Fin (α.edge i).k) :
    ContinuousOn (α.edge i).path (Icc ((α.edge i).piece j).t₀ ((α.edge i).piece j).t₁) :=
  ((α.edge i).arc_smooth j).continuous.continuousOn.congr fun _ hx => (α.edge i).arc_eq j hx

/-- The image of a piece is the image of the edge path on the piece. -/
lemma pieceOf_image (p : α.PieceIdx) :
    (α.pieceOf p).path '' Icc (α.pieceOf p).t₀ (α.pieceOf p).t₁ =
      (α.edge p.1).path '' Icc (α.pieceOf p).t₀ (α.pieceOf p).t₁ :=
  Set.image_congr fun _ hx => ((α.edge p.1).arc_eq p.2 hx).symm

namespace CutData

variable (D : α.CutData)

/-- **A segment meets a piece of another graph on its open part only if it lies in it**, provided the boundary points of
the meeting set are cut points. -/
lemma seg_dichotomy (i : Fin α.m) (l : Fin (D.nSeg i)) (j : Fin (α.edge i).k)
    (hj : Icc (D.cutPt i l.castSucc) (D.cutPt i l.succ) ⊆ Icc ((α.edge i).piece j).t₀ ((α.edge i).piece j).t₁)
    (f : Edge) (hfr : (α.pieceOf ⟨i, j⟩).path '' Edge.meetFrontier (α.pieceOf ⟨i, j⟩) f ⊆ D.Z) :
    (∀ s ∈ Ioo (D.cutPt i l.castSucc) (D.cutPt i l.succ), (α.edge i).path s ∉ f.path '' Icc f.t₀ f.t₁) ∨
      (∀ s ∈ Icc (D.cutPt i l.castSucc) (D.cutPt i l.succ), (α.edge i).path s ∈ f.path '' Icc f.t₀ f.t₁) := by
  have hdich := Edge.meet_dichotomy (e := α.pieceOf ⟨i, j⟩) (f := f) (D.cutPt_lt i l) hj fun s hs hfs =>
    D.path_not_mem i l hs (by
      have := hfr ⟨s, hfs, rfl⟩
      rwa [show (α.pieceOf ⟨i, j⟩).path s = (α.edge i).path s from
        ((α.edge i).arc_eq j (hj (Ioo_subset_Icc_self hs))).symm] at this)
  rcases hdich with h | h
  · left
    intro s hs
    have := h s hs
    rwa [show (α.pieceOf ⟨i, j⟩).path s = (α.edge i).path s from
      ((α.edge i).arc_eq j (hj (Ioo_subset_Icc_self hs))).symm] at this
  · right
    intro s hs
    have := h s hs
    rwa [show (α.pieceOf ⟨i, j⟩).path s = (α.edge i).path s from ((α.edge i).arc_eq j (hj hs)).symm] at this

end CutData

end ALGraph

namespace ALGraph

namespace CutData

variable {α : ALGraph} (D : α.CutData)

/-- The segments cover the edge. -/
lemma exists_seg (i : Fin α.m) {s : ℝ} (hs : s ∈ Icc (α.edge i).t₀ (α.edge i).t₁) :
    ∃ l : Fin (D.nSeg i), s ∈ Icc (D.cutPt i l.castSucc) (D.cutPt i l.succ) := by
  classical
  set P : ℕ → Prop := fun σ => ∃ h : σ < D.nSeg i + 1, D.cutPt i ⟨σ, h⟩ ≤ s with hP
  have hP0 : P 0 := ⟨Nat.succ_pos _, by rw [show (⟨0, _⟩ : Fin (D.nSeg i + 1)) = 0 from rfl, D.cutPt_zero]; exact hs.1⟩
  set σ₀ := Nat.findGreatest P (D.nSeg i) with hσ₀
  obtain ⟨hlt, hle⟩ := Nat.findGreatest_spec (P := P) (Nat.zero_le _) hP0
  have hle' : σ₀ ≤ D.nSeg i := Nat.findGreatest_le _
  rcases eq_or_lt_of_le hle' with heq | hlt'
  · -- `s` is `t₁`; take the last segment
    have hpos : 0 < D.nSeg i := by
      have := D.two_le_card i; rw [D.card_cutSet] at this; omega
    refine ⟨⟨D.nSeg i - 1, by omega⟩, ?_, ?_⟩
    · have : D.cutPt i ⟨σ₀, hlt⟩ ≤ s := hle
      have hmono : D.cutPt i (Fin.castSucc ⟨D.nSeg i - 1, by omega⟩) ≤ D.cutPt i ⟨σ₀, hlt⟩ :=
        (D.cutPt i).monotone (Fin.le_def.2 (by simp; omega))
      exact hmono.trans this
    · have h1 : (Fin.succ (⟨D.nSeg i - 1, by omega⟩ : Fin (D.nSeg i))) = Fin.last _ := Fin.ext (by simp; omega)
      rw [h1, D.cutPt_last]; exact hs.2
  · refine ⟨⟨σ₀, hlt'⟩, hle, ?_⟩
    by_contra hcon
    push Not at hcon
    exact Nat.findGreatest_is_greatest (Nat.lt_succ_self σ₀) hlt' ⟨by omega, hcon.le⟩

end CutData

variable {β β' : ALGraph} (D : β.CutData) (D' : β'.CutData)

/-- **Half of the sharing lemma.** For cut data with the same points, containing the boundary points of the meeting sets
of the pieces of `β'` with the pieces of `β`: if a segment `ρ` of `β'` meets a segment `σ` of `β` at an interior point of
both, the open part of `ρ` lies in the open part of `σ`. -/
lemma seg_half (hZ : D.Z = D'.Z)
    (hfr' : ∀ q p, (β'.pieceOf q).path '' Edge.meetFrontier (β'.pieceOf q) (β.pieceOf p) ⊆ D'.Z)
    (i : Fin β.m) (l : Fin (D.nSeg i)) (i' : Fin β'.m) (l' : Fin (D'.nSeg i'))
    (hmeet : ∃ t ∈ Ioo (D'.cutPt i' l'.castSucc) (D'.cutPt i' l'.succ),
      (β'.edge i').path t ∈ (β.edge i).path '' Ioo (D.cutPt i l.castSucc) (D.cutPt i l.succ)) :
    ∀ t ∈ Ioo (D'.cutPt i' l'.castSucc) (D'.cutPt i' l'.succ),
      (β'.edge i').path t ∈ (β.edge i).path '' Ioo (D.cutPt i l.castSucc) (D.cutPt i l.succ) := by
  obtain ⟨j, hj1, hj2, -⟩ := D.segment_in_piece i l
  obtain ⟨j', hj1', hj2', -⟩ := D'.segment_in_piece i' l'
  have hsub : Icc (D.cutPt i l.castSucc) (D.cutPt i l.succ) ⊆
      Icc ((β.edge i).piece j).t₀ ((β.edge i).piece j).t₁ := Icc_subset_Icc hj1 hj2
  have hsub' : Icc (D'.cutPt i' l'.castSucc) (D'.cutPt i' l'.succ) ⊆
      Icc ((β'.edge i').piece j').t₀ ((β'.edge i').piece j').t₁ := Icc_subset_Icc hj1' hj2'
  obtain ⟨t₀, ht₀, s₀, hs₀, hst⟩ := hmeet
  -- `ρ` lies in the piece of `σ`
  have hP : ∀ t ∈ Icc (D'.cutPt i' l'.castSucc) (D'.cutPt i' l'.succ),
      (β'.edge i').path t ∈ (β.pieceOf ⟨i, j⟩).path '' Icc (β.pieceOf ⟨i, j⟩).t₀ (β.pieceOf ⟨i, j⟩).t₁ := by
    rcases D'.seg_dichotomy i' l' j' hsub' (β.pieceOf ⟨i, j⟩) (hfr' ⟨i', j'⟩ ⟨i, j⟩) with h | h
    · exfalso
      refine h t₀ ht₀ ?_
      rw [pieceOf_image, ← hst]
      exact ⟨s₀, hsub (Ioo_subset_Icc_self hs₀), rfl⟩
    · exact h
  have hEsub : Icc ((β.edge i).piece j).t₀ ((β.edge i).piece j).t₁ ⊆ Icc (β.edge i).t₀ (β.edge i).t₁ :=
    (β.edge i).piece_subset j
  refine image_Ioo_subset (p₀ := ((β.edge i).piece j).t₀) (p₁ := ((β.edge i).piece j).t₁)
    (continuousOn_path_piece i j) ((continuousOn_path_piece i' j').mono hsub') hsub ?_ ?_ ?_ ⟨t₀, ht₀, s₀, hs₀, hst⟩
  · intro s hs s' hs' hss
    have hsI : s ∈ Icc (β.edge i).t₀ (β.edge i).t₁ := hEsub (hsub (Ioo_subset_Icc_self hs))
    rcases (β.edge i).eq_or_ends (hEsub hs') hsI (β.injOn_Ico i) (β.injOn_Ioc i) hss with h | ⟨_, h⟩ | ⟨_, h⟩
    · exact h
    · exfalso; have := (D.cutPt_Icc i l.succ).2; linarith [hs.2]
    · exfalso; have := (D.cutPt_Icc i l.castSucc).1; linarith [hs.1]
  · intro t ht
    have := hP t (Ioo_subset_Icc_self ht)
    rwa [pieceOf_image] at this
  · intro t ht
    have hnot := D'.path_not_mem i' l' ht
    rw [← hZ] at hnot
    exact ⟨fun h => hnot (h ▸ D.cutPt_Z i _), fun h => hnot (h ▸ D.cutPt_Z i _)⟩

end ALGraph

namespace ALGraph

variable (α₁ α₂ : ALGraph)

/-- The image of a graph: the union of the images of its edges. -/
def image (α : ALGraph) : Set (Fin 3 → ℝ) := ⋃ i, (α.edge i).path '' Icc (α.edge i).t₀ (α.edge i).t₁

/-- The boundary points of the meeting sets of the pieces of `α₁` with those of `α₂` are cut points. -/
lemma frontier₁₂ (p : α₁.PieceIdx) (q : α₂.PieceIdx) :
    (α₁.pieceOf p).path '' Edge.meetFrontier (α₁.pieceOf p) (α₂.pieceOf q) ⊆ (cut₁ α₁ α₂).Z :=
  fun _ hx => Or.inl (Or.inr (mem_iUnion.2 ⟨p, mem_iUnion.2 ⟨q, hx⟩⟩))

/-- The boundary points of the meeting sets of the pieces of `α₂` with those of `α₁` are cut points. -/
lemma frontier₂₁ (q : α₂.PieceIdx) (p : α₁.PieceIdx) :
    (α₂.pieceOf q).path '' Edge.meetFrontier (α₂.pieceOf q) (α₁.pieceOf p) ⊆ (cut₂ α₁ α₂).Z :=
  fun _ hx => Or.inr (mem_iUnion.2 ⟨q, mem_iUnion.2 ⟨p, hx⟩⟩)

/-- **The sharing lemma**: if a segment of `α₂` meets a segment of `α₁` at an interior point of the first, the open parts
of the two segments have the same image. -/
theorem seg_share (i : Fin α₁.m) (l : Fin ((cut₁ α₁ α₂).nSeg i)) (i' : Fin α₂.m) (l' : Fin ((cut₂ α₁ α₂).nSeg i'))
    (hmeet : ∃ t ∈ Ioo ((cut₂ α₁ α₂).cutPt i' l'.castSucc) ((cut₂ α₁ α₂).cutPt i' l'.succ),
      (α₂.edge i').path t ∈ (α₁.edge i).path '' Icc ((cut₁ α₁ α₂).cutPt i l.castSucc) ((cut₁ α₁ α₂).cutPt i l.succ)) :
    (α₁.edge i).path '' Ioo ((cut₁ α₁ α₂).cutPt i l.castSucc) ((cut₁ α₁ α₂).cutPt i l.succ) =
      (α₂.edge i').path '' Ioo ((cut₂ α₁ α₂).cutPt i' l'.castSucc) ((cut₂ α₁ α₂).cutPt i' l'.succ) := by
  obtain ⟨t, ht, s, hs, hst⟩ := hmeet
  have hnot := (cut₂ α₁ α₂).path_not_mem i' l' ht
  have hsI : s ∈ Ioo ((cut₁ α₁ α₂).cutPt i l.castSucc) ((cut₁ α₁ α₂).cutPt i l.succ) := by
    refine ⟨lt_of_le_of_ne hs.1 fun h => hnot ?_, lt_of_le_of_ne hs.2 fun h => hnot ?_⟩
    · rw [← hst, ← h]; exact (cut₁ α₁ α₂).cutPt_Z i _
    · rw [← hst, h]; exact (cut₁ α₁ α₂).cutPt_Z i _
  have h1 := seg_half (cut₁ α₁ α₂) (cut₂ α₁ α₂) rfl (frontier₂₁ α₁ α₂) i l i' l'
    ⟨t, ht, s, hsI, hst⟩
  have h2 := seg_half (cut₂ α₁ α₂) (cut₁ α₁ α₂) rfl (frontier₁₂ α₁ α₂) i' l' i l
    ⟨s, hsI, t, ht, hst.symm⟩
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩; exact h2 x hx
  · rintro _ ⟨x, hx, rfl⟩; exact h1 x hx

/-- **Every segment of `α₂` is a segment of `α₁` or meets `α₁` only at its end points**: either its open part misses
the image of `α₁`, or its open part is the open part of a segment of `α₁`. -/
theorem seg_classify (i' : Fin α₂.m) (l' : Fin ((cut₂ α₁ α₂).nSeg i')) :
    (∀ t ∈ Ioo ((cut₂ α₁ α₂).cutPt i' l'.castSucc) ((cut₂ α₁ α₂).cutPt i' l'.succ),
      (α₂.edge i').path t ∉ α₁.image) ∨
    ∃ (i : Fin α₁.m) (l : Fin ((cut₁ α₁ α₂).nSeg i)),
      (α₁.edge i).path '' Ioo ((cut₁ α₁ α₂).cutPt i l.castSucc) ((cut₁ α₁ α₂).cutPt i l.succ) =
        (α₂.edge i').path '' Ioo ((cut₂ α₁ α₂).cutPt i' l'.castSucc) ((cut₂ α₁ α₂).cutPt i' l'.succ) := by
  by_cases h : ∃ t ∈ Ioo ((cut₂ α₁ α₂).cutPt i' l'.castSucc) ((cut₂ α₁ α₂).cutPt i' l'.succ),
      (α₂.edge i').path t ∈ α₁.image
  · right
    obtain ⟨t, ht, hti⟩ := h
    obtain ⟨i, hi⟩ := mem_iUnion.1 hti
    obtain ⟨s, hs, hst⟩ := hi
    obtain ⟨l, hl⟩ := (cut₁ α₁ α₂).exists_seg i hs
    exact ⟨i, l, seg_share α₁ α₂ i l i' l' ⟨t, ht, s, hl, hst⟩⟩
  · left
    push Not at h
    exact h

end ALGraph

namespace ALGraph

namespace CutData

variable {β : ALGraph} (D : β.CutData)

/-- The analytic piece containing a segment. -/
def segPiece (i : Fin β.m) (l : Fin (D.nSeg i)) : Fin (β.edge i).k := (D.segment_in_piece i l).choose

/-- A segment lies in its analytic piece. -/
lemma segPiece_sub (i : Fin β.m) (l : Fin (D.nSeg i)) :
    Icc (D.cutPt i l.castSucc) (D.cutPt i l.succ) ⊆
      Icc ((β.edge i).τ (D.segPiece i l).castSucc) ((β.edge i).τ (D.segPiece i l).succ) :=
  Icc_subset_Icc (D.segment_in_piece i l).choose_spec.1 (D.segment_in_piece i l).choose_spec.2.1

/-- The first entry of a two-point subdivision. -/
lemma vec_castSucc {a b : ℝ} (j : Fin 1) : (![a, b] : Fin 2 → ℝ) j.castSucc = a := by
  rw [Fin.fin_one_eq_zero j]; rfl

/-- The second entry of a two-point subdivision. -/
lemma vec_succ {a b : ℝ} (j : Fin 1) : (![a, b] : Fin 2 → ℝ) j.succ = b := by
  rw [Fin.fin_one_eq_zero j]; rfl

/-- The **segment** `l` of the edge `i` as an edge with one analytic piece: the same path on the parameter interval
between two consecutive cut parameters. -/
def segEdge (i : Fin β.m) (l : Fin (D.nSeg i)) : ALEdge where
  path := (β.edge i).path
  k := 1
  k_pos := one_pos
  τ := ![D.cutPt i l.castSucc, D.cutPt i l.succ]
  τ_mono := Fin.strictMono_iff_lt_succ.2 fun j => by rw [vec_castSucc, vec_succ]; exact D.cutPt_lt i l
  arc _ := (β.edge i).arc (D.segPiece i l)
  arc_smooth _ := (β.edge i).arc_smooth _
  arc_analytic j t ht := (β.edge i).arc_analytic _ t (D.segPiece_sub i l (by rwa [vec_castSucc, vec_succ] at ht))
  arc_eq j t ht := (β.edge i).arc_eq _ (D.segPiece_sub i l (by rwa [vec_castSucc, vec_succ] at ht))

/-- The segment edge runs along the path of its edge. -/
@[simp] lemma segEdge_path (i : Fin β.m) (l : Fin (D.nSeg i)) : (D.segEdge i l).path = (β.edge i).path := rfl

/-- The initial parameter of a segment edge. -/
@[simp] lemma segEdge_t₀ (i : Fin β.m) (l : Fin (D.nSeg i)) : (D.segEdge i l).t₀ = D.cutPt i l.castSucc := rfl

/-- The final parameter of a segment edge. -/
@[simp] lemma segEdge_t₁ (i : Fin β.m) (l : Fin (D.nSeg i)) : (D.segEdge i l).t₁ = D.cutPt i l.succ := rfl

/-- A segment lies in the parameter interval of its edge. -/
lemma seg_sub (i : Fin β.m) (l : Fin (D.nSeg i)) :
    Icc (D.cutPt i l.castSucc) (D.cutPt i l.succ) ⊆ Icc (β.edge i).t₀ (β.edge i).t₁ :=
  Icc_subset_Icc (D.cutPt_Icc i _).1 (D.cutPt_Icc i _).2

/-- **Distinct segments of one graph meet at no interior point.** -/
lemma seg_meet {i i₂ : Fin β.m} {l : Fin (D.nSeg i)} {l₂ : Fin (D.nSeg i₂)}
    (hne : (⟨i, l⟩ : Σ i, Fin (D.nSeg i)) ≠ ⟨i₂, l₂⟩) {s t : ℝ} (hs : s ∈ Ioo (D.cutPt i l.castSucc) (D.cutPt i l.succ))
    (ht : t ∈ Icc (D.cutPt i₂ l₂.castSucc) (D.cutPt i₂ l₂.succ)) (h : (β.edge i).path s = (β.edge i₂).path t) :
    False := by
  have hs0 := (D.cutPt_Icc i l.castSucc).1
  have hs1 := (D.cutPt_Icc i l.succ).2
  by_cases hi : i = i₂
  · subst hi
    have hl : l ≠ l₂ := fun h' => hne (by rw [h'])
    rcases (β.edge i).eq_or_ends (D.seg_sub i l (Ioo_subset_Icc_self hs)) (D.seg_sub i l₂ ht) (β.injOn_Ico i)
      (β.injOn_Ioc i) h with h' | ⟨h', -⟩ | ⟨h', -⟩
    · subst h'
      rcases lt_or_gt_of_ne hl with hl' | hl'
      · have : D.cutPt i l.succ ≤ D.cutPt i l₂.castSucc :=
          (D.cutPt i).monotone (Fin.le_def.2 (by simp; omega))
        linarith [hs.2, ht.1]
      · have : D.cutPt i l₂.succ ≤ D.cutPt i l.castSucc :=
          (D.cutPt i).monotone (Fin.le_def.2 (by simp; omega))
        linarith [hs.1, ht.2]
    · linarith [hs.1]
    · linarith [hs.2]
  · rcases (β.meet i i₂ hi s (D.seg_sub i l (Ioo_subset_Icc_self hs)) t (D.seg_sub i₂ l₂ ht) h).1 with h' | h'
    · linarith [hs.1]
    · linarith [hs.2]

end CutData

/-- A point of `[a, b]` outside `(a, b)` is `a` or `b`. -/
lemma eq_or_eq_of_not_mem_Ioo {s a b : ℝ} (hs : s ∈ Icc a b) (h : s ∉ Ioo a b) : s = a ∨ s = b := by
  by_contra hcon
  push Not at hcon
  exact h ⟨lt_of_le_of_ne hs.1 (Ne.symm hcon.1), lt_of_le_of_ne hs.2 hcon.2⟩

end ALGraph

namespace ALGraph

variable (α₁ α₂ : ALGraph)

/-- The segments of `α₂` whose open part misses `α₁`. -/
abbrev FreeSeg : Type :=
  {p : Σ i' : Fin α₂.m, Fin ((cut₂ α₁ α₂).nSeg i') //
    ∀ t ∈ Ioo ((cut₂ α₁ α₂).cutPt p.1 p.2.castSucc) ((cut₂ α₁ α₂).cutPt p.1 p.2.succ), (α₂.edge p.1).path t ∉ α₁.image}

/-- The edges of the common refinement: the segments of `α₁` and the segments of `α₂` missing `α₁`. -/
abbrev SegIdx : Type := (Σ i : Fin α₁.m, Fin ((cut₁ α₁ α₂).nSeg i)) ⊕ FreeSeg α₁ α₂

/-- The edge of the common refinement with a given index. -/
def segE : SegIdx α₁ α₂ → ALEdge
  | .inl p => (cut₁ α₁ α₂).segEdge p.1 p.2
  | .inr q => (cut₂ α₁ α₂).segEdge q.1.1 q.1.2

variable {α₁ α₂}

/-- The edges of the common refinement are injective on their parameter intervals. -/
lemma segE_injOn (x : SegIdx α₁ α₂) : InjOn (segE α₁ α₂ x).path (Icc (segE α₁ α₂ x).t₀ (segE α₁ α₂ x).t₁) := by
  rcases x with ⟨i, l⟩ | ⟨⟨i, l⟩, _⟩
  · exact (cut₁ α₁ α₂).injOn_segment i l
  · exact (cut₂ α₁ α₂).injOn_segment i l

/-- A segment of `α₁` and a segment of `α₂` missing `α₁` meet only at end points. -/
lemma seg_meet_mixed (p : Σ i : Fin α₁.m, Fin ((cut₁ α₁ α₂).nSeg i)) (q : FreeSeg α₁ α₂) {s t : ℝ}
    (hs : s ∈ Icc ((cut₁ α₁ α₂).cutPt p.1 p.2.castSucc) ((cut₁ α₁ α₂).cutPt p.1 p.2.succ))
    (ht : t ∈ Icc ((cut₂ α₁ α₂).cutPt q.1.1 q.1.2.castSucc) ((cut₂ α₁ α₂).cutPt q.1.1 q.1.2.succ))
    (h : (α₁.edge p.1).path s = (α₂.edge q.1.1).path t) :
    (s = (cut₁ α₁ α₂).cutPt p.1 p.2.castSucc ∨ s = (cut₁ α₁ α₂).cutPt p.1 p.2.succ) ∧
      (t = (cut₂ α₁ α₂).cutPt q.1.1 q.1.2.castSucc ∨ t = (cut₂ α₁ α₂).cutPt q.1.1 q.1.2.succ) := by
  have ht' := eq_or_eq_of_not_mem_Ioo ht fun ht' =>
    q.2 t ht' (h ▸ mem_iUnion.2 ⟨p.1, s, (cut₁ α₁ α₂).seg_sub _ _ hs, rfl⟩)
  refine ⟨eq_or_eq_of_not_mem_Ioo hs fun hs' => (cut₁ α₁ α₂).path_not_mem p.1 p.2 hs' ?_, ht'⟩
  rw [h]
  rcases ht' with h' | h' <;> rw [h'] <;> exact (cut₂ α₁ α₂).cutPt_Z _ _

/-- Distinct edges of the common refinement meet only at end points. -/
lemma segE_meet {x y : SegIdx α₁ α₂} (hxy : x ≠ y) {s t : ℝ} (hs : s ∈ Icc (segE α₁ α₂ x).t₀ (segE α₁ α₂ x).t₁)
    (ht : t ∈ Icc (segE α₁ α₂ y).t₀ (segE α₁ α₂ y).t₁) (h : (segE α₁ α₂ x).path s = (segE α₁ α₂ y).path t) :
    (s = (segE α₁ α₂ x).t₀ ∨ s = (segE α₁ α₂ x).t₁) ∧ (t = (segE α₁ α₂ y).t₀ ∨ t = (segE α₁ α₂ y).t₁) := by
  rcases x with ⟨i, l⟩ | ⟨⟨i, l⟩, hq⟩ <;> rcases y with ⟨i₂, l₂⟩ | ⟨⟨i₂, l₂⟩, hq₂⟩
  · have hne : (⟨i, l⟩ : Σ i, Fin ((cut₁ α₁ α₂).nSeg i)) ≠ ⟨i₂, l₂⟩ := fun h' => hxy (by rw [h'])
    exact ⟨eq_or_eq_of_not_mem_Ioo hs fun hs' => (cut₁ α₁ α₂).seg_meet hne hs' ht h,
      eq_or_eq_of_not_mem_Ioo ht fun ht' => (cut₁ α₁ α₂).seg_meet (Ne.symm hne) ht' hs h.symm⟩
  · exact seg_meet_mixed ⟨i, l⟩ ⟨⟨i₂, l₂⟩, hq₂⟩ hs ht h
  · exact (seg_meet_mixed ⟨i₂, l₂⟩ ⟨⟨i, l⟩, hq⟩ ht hs h.symm).symm
  · have hne : (⟨i, l⟩ : Σ i, Fin ((cut₂ α₁ α₂).nSeg i)) ≠ ⟨i₂, l₂⟩ := fun h' => hxy (by
      congr 1; exact Subtype.ext h')
    exact ⟨eq_or_eq_of_not_mem_Ioo hs fun hs' => (cut₂ α₁ α₂).seg_meet hne hs' ht h,
      eq_or_eq_of_not_mem_Ioo ht fun ht' => (cut₂ α₁ α₂).seg_meet (Ne.symm hne) ht' hs h.symm⟩

variable (α₁ α₂)

/-- **The common refinement** `α₃` of two graphs (Ashtekar–Lewandowski, p. 35): its edges are the segments of the edges
of `α₁` between consecutive cut points, and the segments of the edges of `α₂` whose open part misses `α₁`. -/
def common : ALGraph where
  m := Nat.card (SegIdx α₁ α₂)
  edge j := segE α₁ α₂ ((Finite.equivFin _).symm j)
  injOn_Ico _ := (segE_injOn _).mono Ico_subset_Icc_self
  injOn_Ioc _ := (segE_injOn _).mono Ioc_subset_Icc_self
  meet _ _ h _ hs _ ht hst := segE_meet ((Finite.equivFin _).symm.injective.ne h) hs ht hst

/-- The edge of the common refinement with index `x`. -/
lemma common_edge (x : SegIdx α₁ α₂) : (common α₁ α₂).edge (Finite.equivFin _ x) = segE α₁ α₂ x := by
  show segE α₁ α₂ ((Finite.equivFin _).symm (Finite.equivFin _ x)) = _
  rw [Equiv.symm_apply_apply]

/-- **`α₁ ≤ α₃`**: each edge of `α₁` is the composition of its segments, edges of `α₃`. -/
theorem le_common_left : α₁.Le (common α₁ α₂) := fun i => by
  refine ⟨(cut₁ α₁ α₂).nSeg i, (cut₁ α₁ α₂).cutPt i, fun l => (Finite.equivFin _ (Sum.inl ⟨i, l⟩), true),
    ((cut₁ α₁ α₂).cutPt i).strictMono, (cut₁ α₁ α₂).cutPt_zero i, (cut₁ α₁ α₂).cutPt_last i, fun l => ?_⟩
  have h := common_edge α₁ α₂ (Sum.inl ⟨i, l⟩)
  refine ⟨id, continuousOn_id, monotoneOn_id, ?_, ?_, ?_⟩
  · show _ = (((common α₁ α₂).edge (Finite.equivFin _ (Sum.inl ⟨i, l⟩))).orient true).t₀
    rw [h]; rfl
  · show _ = (((common α₁ α₂).edge (Finite.equivFin _ (Sum.inl ⟨i, l⟩))).orient true).t₁
    rw [h]; rfl
  · intro x _
    show _ = (((common α₁ α₂).edge (Finite.equivFin _ (Sum.inl ⟨i, l⟩))).orient true).path (id x)
    rw [h]; rfl

/-- **`α₂ ≤ α₃`**: each segment of `α₂` is an edge of `α₃`, or a reparametrisation of a segment of `α₁` in one of
its orientations. -/
theorem le_common_right : α₂.Le (common α₁ α₂) := fun i' => by
  set D₁ := cut₁ α₁ α₂
  set D₂ := cut₂ α₁ α₂
  have key : ∀ l' : Fin (D₂.nSeg i'), ∃ (x : SegIdx α₁ α₂) (b : Bool) (φ : ℝ → ℝ),
      ContinuousOn φ (Icc (D₂.cutPt i' l'.castSucc) (D₂.cutPt i' l'.succ)) ∧
      MonotoneOn φ (Icc (D₂.cutPt i' l'.castSucc) (D₂.cutPt i' l'.succ)) ∧
      φ (D₂.cutPt i' l'.castSucc) = ((segE α₁ α₂ x).orient b).t₀ ∧
      φ (D₂.cutPt i' l'.succ) = ((segE α₁ α₂ x).orient b).t₁ ∧
      EqOn (α₂.edge i').path (((segE α₁ α₂ x).orient b).path ∘ φ)
        (Icc (D₂.cutPt i' l'.castSucc) (D₂.cutPt i' l'.succ)) := fun l' => by
    by_cases hfree : ∀ t ∈ Ioo (D₂.cutPt i' l'.castSucc) (D₂.cutPt i' l'.succ), (α₂.edge i').path t ∉ α₁.image
    · exact ⟨Sum.inr ⟨⟨i', l'⟩, hfree⟩, true, id, continuousOn_id, monotoneOn_id, rfl, rfl, fun _ _ => rfl⟩
    rcases seg_classify α₁ α₂ i' l' with h | ⟨i, l, himg⟩
    · exact absurd h hfree
    have hg : ContinuousOn (α₁.edge i).path (Icc (D₁.cutPt i l.castSucc) (D₁.cutPt i l.succ)) :=
      (continuousOn_path_piece i (D₁.segPiece i l)).mono (D₁.segPiece_sub i l)
    have hh : ContinuousOn (α₂.edge i').path (Icc (D₂.cutPt i' l'.castSucc) (D₂.cutPt i' l'.succ)) :=
      (continuousOn_path_piece i' (D₂.segPiece i' l')).mono (D₂.segPiece_sub i' l')
    have hend : ∀ m : Fin (D₂.nSeg i' + 1),
        (α₂.edge i').path (D₂.cutPt i' m) ∉ (α₁.edge i).path '' Ioo (D₁.cutPt i l.castSucc) (D₁.cutPt i l.succ) :=
      fun m ⟨s, hs, hseq⟩ => D₁.path_not_mem i l hs (hseq ▸ D₂.cutPt_Z i' m)
    obtain ⟨ψ, hψc, hψe, hψ⟩ := exists_reparam (D₁.cutPt_lt i l) (D₂.cutPt_lt i' l') hg (D₁.injOn_segment i l) hh
      (D₂.injOn_segment i' l') himg (hend _) (hend _)
    rcases hψ with ⟨hm, h0, h1⟩ | ⟨hm, h0, h1⟩
    · exact ⟨Sum.inl ⟨i, l⟩, true, ψ, hψc, hm, h0, h1, hψe⟩
    · refine ⟨Sum.inl ⟨i, l⟩, false, fun t => D₁.cutPt i l.castSucc + D₁.cutPt i l.succ - ψ t,
        continuousOn_const.sub hψc, fun x hx y hy hxy => by have := hm hx hy hxy; linarith, ?_, ?_, ?_⟩
      · show _ = (segE α₁ α₂ (Sum.inl ⟨i, l⟩)).rev.t₀
        rw [ALEdge.rev_t₀]; show _ + _ - ψ _ = D₁.cutPt i l.castSucc; rw [h0]; ring
      · show _ = (segE α₁ α₂ (Sum.inl ⟨i, l⟩)).rev.t₁
        rw [ALEdge.rev_t₁]; show _ + _ - ψ _ = D₁.cutPt i l.succ; rw [h1]; ring
      · intro t ht
        show _ = (α₁.edge i).path (D₁.cutPt i l.castSucc + D₁.cutPt i l.succ -
          (D₁.cutPt i l.castSucc + D₁.cutPt i l.succ - ψ t))
        rw [hψe ht, Function.comp_apply]
        congr 1; ring
  choose x b φ hφ using key
  refine ⟨D₂.nSeg i', D₂.cutPt i', fun l => (Finite.equivFin _ (x l), b l), (D₂.cutPt i').strictMono,
    D₂.cutPt_zero i', D₂.cutPt_last i', fun l => ⟨φ l, ?_⟩⟩
  have := hφ l
  rw [← common_edge α₁ α₂ (x l)] at this
  exact this

/-- **Directedness of the refinement order** (Ashtekar–Lewandowski, p. 35): any two graphs have a common upper bound. -/
theorem directed (α₁ α₂ : ALGraph) : ∃ α₃ : ALGraph, α₁.Le α₃ ∧ α₂.Le α₃ :=
  ⟨common α₁ α₂, le_common_left α₁ α₂, le_common_right α₁ α₂⟩

end ALGraph

namespace ALEdge

/-- The end points of an oriented edge are the end points of the edge. -/
lemma orient_ends (E : ALEdge) (b : Bool) :
    ((E.orient b).path (E.orient b).t₀ = E.path E.t₀ ∨ (E.orient b).path (E.orient b).t₀ = E.path E.t₁) ∧
      ((E.orient b).path (E.orient b).t₁ = E.path E.t₀ ∨ (E.orient b).path (E.orient b).t₁ = E.path E.t₁) := by
  cases b
  · refine ⟨Or.inr ?_, Or.inl ?_⟩
    · show E.path (E.t₀ + E.t₁ - E.rev.t₀) = _
      rw [rev_t₀]; congr 1; ring
    · show E.path (E.t₀ + E.t₁ - E.rev.t₁) = _
      rw [rev_t₁]; congr 1; ring
  · exact ⟨Or.inl rfl, Or.inr rfl⟩

end ALEdge

namespace ALGraph

/-- **Under refinement the vertices are kept**: if `α ≤ α'`, every vertex of `α` is a vertex of `α'`. -/
theorem vertices_subset_of_le {α α' : ALGraph} (h : α.Le α') : α.vertices ⊆ α'.vertices := by
  rintro v ⟨i, hv⟩
  obtain ⟨K, s, c, hs, hs0, hsK, hφ⟩ := h i
  have hK : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h0 | h0
    · subst h0
      have : s 0 = s (Fin.last 0) := rfl
      have := (α.edge i).t₀_lt_t₁
      rw [← hs0, ← hsK] at this
      exact absurd this (by rw [show (Fin.last 0) = 0 from rfl]; exact lt_irrefl _)
    · exact h0
  have hvert : ∀ (l : Fin K) (x : ℝ), x = ((α'.edge (c l).1).orient (c l).2).t₀ ∨
      x = ((α'.edge (c l).1).orient (c l).2).t₁ →
      ((α'.edge (c l).1).orient (c l).2).path x ∈ α'.vertices := fun l x hx => by
    obtain ⟨h0, h1⟩ := (α'.edge (c l).1).orient_ends (c l).2
    rcases hx with rfl | rfl
    · rcases h0 with h' | h' <;> rw [h'] <;> exact ⟨(c l).1, by simp⟩
    · rcases h1 with h' | h' <;> rw [h'] <;> exact ⟨(c l).1, by simp⟩
  rcases hv with rfl | rfl
  · obtain ⟨φ, -, hm, h0, -, he⟩ := hφ ⟨0, hK⟩
    have hlt : s (Fin.castSucc ⟨0, hK⟩) < s (Fin.succ ⟨0, hK⟩) := hs Fin.castSucc_lt_succ
    have hcs : (Fin.castSucc (⟨0, hK⟩ : Fin K)) = 0 := rfl
    rw [← hs0, ← hcs, he ⟨le_rfl, hlt.le⟩, Function.comp_apply]
    exact hvert _ _ (Or.inl h0)
  · obtain ⟨φ, -, hm, -, h1, he⟩ := hφ ⟨K - 1, by omega⟩
    have hlt : s (Fin.castSucc ⟨K - 1, by omega⟩) < s (Fin.succ ⟨K - 1, by omega⟩) := hs Fin.castSucc_lt_succ
    have hcs : (Fin.succ (⟨K - 1, by omega⟩ : Fin K)) = Fin.last K := Fin.ext (by simp; omega)
    rw [← hsK, ← hcs, he ⟨hlt.le, le_rfl⟩, Function.comp_apply]
    exact hvert _ _ (Or.inr h1)

/-- **The third graph of Ashtekar–Lewandowski** (p. 35): for two graphs `α₁`, `α₂` there is a graph `α₃` that contains
all their vertices, and the holonomy along each edge of `α₁` or of `α₂` is an ordered product of holonomies along edges of
`α₃` or their inverses (so functions cylindrical over `α₁` or `α₂` are cylindrical over `α₃`). -/
theorem exists_common_hol {n : ℕ} {A : MatConn n} (hA : ∀ a, Continuous fun x => A x a) (α₁ α₂ : ALGraph) :
    ∃ α₃ : ALGraph, α₁.vertices ⊆ α₃.vertices ∧ α₂.vertices ⊆ α₃.vertices ∧
      (∀ i, ∃ (K : ℕ) (c : Fin K → Fin α₃.m × Bool), (α₁.edge i).hol A =
        (List.ofFn fun l => if (c l).2 then (α₃.edge (c l).1).hol A else ((α₃.edge (c l).1).hol A)⁻¹).reverse.prod) ∧
      ∀ i, ∃ (K : ℕ) (c : Fin K → Fin α₃.m × Bool), (α₂.edge i).hol A =
        (List.ofFn fun l => if (c l).2 then (α₃.edge (c l).1).hol A else ((α₃.edge (c l).1).hol A)⁻¹).reverse.prod :=
  ⟨common α₁ α₂, vertices_subset_of_le (le_common_left α₁ α₂), vertices_subset_of_le (le_common_right α₁ α₂),
    hol_of_le hA (le_common_left α₁ α₂), hol_of_le hA (le_common_right α₁ α₂)⟩

end ALGraph

end Lightlike.Canonical
