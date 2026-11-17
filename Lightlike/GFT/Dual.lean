import Lightlike.GFT.PseudoComplex

/-!
# The dual of a colored graph as a pseudo-complex

The gluing `Δ_G` dual to a colored graph `G` of dimension `D` (Gurau, *Lost in translation: topological
singularities in group field theory*, Class. Quantum Grav. 27 (2010) 235023, arXiv:1006.0714, Section 5,
eqs. (37) and (38)) has one simplex for each pair `(S, B)` of a set `S` of colors and a bubble `B` of the
other colors: the simplex with the vertices `(i, B_i)`, `i ∈ S`, where `B_i` is the bubble of the colors
other than `i` containing `B`. A simplex `(S', B')` is a face of `(S, B)` when `S' ⊆ S` and `B ⊆ B'`. The
rank of `(S, B)` is `#S`, so the top simplices, of rank `D + 1`, are the duals of the vertices of `G`, and
the simplices of rank `D` are the duals of the lines. `DualSimplex G` is the type of these pairs and
`dual G` the graded poset of `Lightlike.GFT.PseudoComplex`, so two simplices with the same vertex set stay
distinct, as they must (the graph with two vertices and three lines).

## Main results

* `dual_isPure`: every simplex is a face of a top simplex.
* `dual_isNonBranching`: a simplex of rank `D` is a face of exactly two top simplices, the two ends of its
  line (`card_bubble_singleton`).
* `dual_isStronglyConnected`: for a connected graph, any two top simplices are joined by a chain of lines.
* `dual_isNormal`: the link of every simplex of rank at most `D - 1` is a pseudo-manifold. No connectedness
  is needed: the bubble of the simplex is connected under the lines of the colors outside it.
* `faceIso`, `dual_isSimplicial`: every lower interval is a Boolean lattice: the faces of a simplex are the
  subsets of its colors, so `Δ_G` is a simplicial poset.
* `dual_isNormalPseudoManifold`: for a connected graph `Δ_G` is a normal pseudo-manifold of top rank `D + 1`,
  which is Theorem 2 of Gurau for the indexed complex.

## Not proved here

Theorem 1, that the link of a simplex is the dual of the bubble as a colored
graph (`ColoredGraph.restrict`), which is stated by an isomorphism of graded posets not constructed here.
-/

open Finset

namespace Lightlike.GFT

variable {D : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

namespace ColoredGraph

/-- A bubble is the bubble of each of its vertices. -/
lemma bubble_eq_of_mem (G : ColoredGraph D V) (S : Finset (Fin (D + 1))) {v w : V}
    (h : w ∈ G.bubble S v) : G.bubble S w = G.bubble S v := by
  rw [mem_bubble_iff] at h
  ext x
  rw [mem_bubble_iff, mem_bubble_iff]
  constructor
  · intro hx
    exact h.trans hx
  · intro hx
    exact (reflTransGen_adj_symm G S h).trans hx

/-- The line of a color `c ∈ S` at a vertex of an `S`-bubble stays in the bubble. -/
lemma inv_mem_bubble_of_mem (G : ColoredGraph D V) {S : Finset (Fin (D + 1))} {c : Fin (D + 1)}
    (hc : c ∈ S) {v w : V} (h : w ∈ G.bubble S v) : G.inv c w ∈ G.bubble S v := by
  rw [mem_bubble_iff] at h ⊢
  exact h.tail ⟨c, hc, rfl⟩

/-- **The simplices of the dual `Δ_G`** (Gurau 2010, eqs. (37), (38)): a set `S` of colors and a bubble `B`
of the other colors. The simplex has the vertices `(i, B_i)`, `i ∈ S`, with `B_i` the bubble of the colors
other than `i` that contains `B`; its dimension is `#S - 1`. -/
def DualSimplex (G : ColoredGraph D V) : Type _ :=
  {p : Finset (Fin (D + 1)) × Finset V // ∃ v, p.2 = G.bubble (univ \ p.1) v}

namespace DualSimplex

variable {G : ColoredGraph D V}

/-- The set of colors of a simplex. -/
def colors (σ : DualSimplex G) : Finset (Fin (D + 1)) := σ.1.1

/-- The bubble of a simplex. -/
def bub (σ : DualSimplex G) : Finset V := σ.1.2

lemma ext' {a b : DualSimplex G} (h1 : a.colors = b.colors) (h2 : a.bub = b.bub) : a = b :=
  Subtype.ext (Prod.ext h1 h2)

/-- `a ≤ b` when `a` is a face of `b`: fewer colors and a larger bubble. -/
instance : PartialOrder (DualSimplex G) where
  le a b := a.colors ⊆ b.colors ∧ b.bub ⊆ a.bub
  le_refl a := ⟨subset_rfl, subset_rfl⟩
  le_trans a b c h1 h2 := ⟨h1.1.trans h2.1, h2.2.trans h1.2⟩
  le_antisymm a b h1 h2 := ext' (subset_antisymm h1.1 h2.1) (subset_antisymm h2.2 h1.2)

lemma le_def {a b : DualSimplex G} : a ≤ b ↔ a.colors ⊆ b.colors ∧ b.bub ⊆ a.bub := Iff.rfl

lemma bub_eq (σ : DualSimplex G) : ∃ v, σ.bub = G.bubble (univ \ σ.colors) v := σ.2

lemma exists_mem_bub (σ : DualSimplex G) : ∃ v, v ∈ σ.bub := by
  obtain ⟨v, hv⟩ := σ.2
  exact ⟨v, by rw [bub, hv]; exact mem_bubble_self G _ v⟩

/-- **The top simplex of a vertex** `v`, dual to the `0`-bubble `{v}`: all colors. -/
def top (G : ColoredGraph D V) (v : V) : DualSimplex G :=
  ⟨(univ, {v}), ⟨v, by simp [bubble_empty]⟩⟩

@[simp] lemma colors_top (v : V) : (top G v).colors = univ := rfl
@[simp] lemma bub_top (v : V) : (top G v).bub = {v} := rfl

lemma le_top_iff (σ : DualSimplex G) (v : V) : σ ≤ top G v ↔ v ∈ σ.bub := by
  rw [le_def]
  simp [colors_top, bub_top]

/-- **The edge simplex** of the line of color `c` at `a`, dual to the `1`-bubble `{a, inv c a}`: all the
colors except `c`. -/
def edge (G : ColoredGraph D V) (c : Fin (D + 1)) (a : V) : DualSimplex G :=
  ⟨(univ \ {c}, {a, G.inv c a}), ⟨a, by
    show {a, G.inv c a} = G.bubble (univ \ (univ \ {c})) a
    rw [Finset.sdiff_sdiff_eq_self (subset_univ _), bubble_singleton]⟩⟩

lemma colors_edge (c : Fin (D + 1)) (a : V) : (edge G c a).colors = univ \ {c} := rfl
lemma bub_edge (c : Fin (D + 1)) (a : V) : (edge G c a).bub = {a, G.inv c a} := rfl

lemma le_edge_iff (σ : DualSimplex G) (c : Fin (D + 1)) (a : V) :
    σ ≤ edge G c a ↔ c ∉ σ.colors ∧ a ∈ σ.bub ∧ G.inv c a ∈ σ.bub := by
  rw [le_def, colors_edge, bub_edge]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun hc => ?_, h2 (by simp), h2 (by simp)⟩
    have := h1 hc
    simp at this
  · rintro ⟨hc, ha, hb⟩
    refine ⟨fun i hi => ?_, ?_⟩
    · simp only [mem_sdiff, mem_univ, mem_singleton, true_and]
      rintro rfl
      exact hc hi
    · intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hb

lemma edge_le_top (c : Fin (D + 1)) (a : V) : edge G c a ≤ top G a := by
  rw [le_top_iff, bub_edge]; simp

lemma edge_le_top' (c : Fin (D + 1)) (a : V) : edge G c a ≤ top G (G.inv c a) := by
  rw [le_top_iff, bub_edge]; simp

/-- A face with the same colors has the same bubble. -/
lemma bub_eq_of_le {a b : DualSimplex G} (h : a ≤ b) (hc : a.colors = b.colors) : a.bub = b.bub := by
  obtain ⟨w, hw⟩ := exists_mem_bub b
  obtain ⟨v, hv⟩ := a.bub_eq
  obtain ⟨w', hw'⟩ := b.bub_eq
  have hwa : w ∈ a.bub := h.2 hw
  have h1 : G.bubble (univ \ a.colors) w = a.bub := by
    rw [hv] at hwa ⊢
    exact bubble_eq_of_mem G _ hwa
  have h2 : G.bubble (univ \ b.colors) w = b.bub := by
    rw [hw'] at hw ⊢
    exact bubble_eq_of_mem G _ hw
  rw [← h1, ← h2, hc]

/-- A simplex with all colors is the top simplex of a vertex. -/
lemma eq_top_of_card (τ : DualSimplex G) (h : τ.colors.card = D + 1) : ∃ v, τ = top G v := by
  have hc : τ.colors = univ := Finset.eq_univ_of_card _ (by simpa using h)
  obtain ⟨v, hv⟩ := τ.bub_eq
  refine ⟨v, ext' (by simpa using hc) ?_⟩
  rw [hv, hc]
  simp [bubble_empty]

end DualSimplex

/-- **The dual `Δ_G` of a colored graph as a graded poset**: the rank of a simplex is its number of
colors, the number of its vertices. The top rank is `D + 1`, the simplices of top dimension being the
`top` simplices. -/
def dual (G : ColoredGraph D V) : GradedPoset (DualSimplex G) where
  rk σ := σ.colors.card
  rk_lt {a b} h := by
    have hle : a ≤ b := h.le
    have hsub : a.colors ⊆ b.colors := hle.1
    by_contra hnlt
    have hcard : a.colors.card = b.colors.card :=
      le_antisymm (card_le_card hsub) (not_lt.1 hnlt)
    have hc : a.colors = b.colors := eq_of_subset_of_card_le hsub hcard.ge
    have hb := DualSimplex.bub_eq_of_le hle hc
    exact h.not_ge ⟨hc.ge, hb.le⟩

variable {G : ColoredGraph D V}

lemma dual_rk (σ : DualSimplex G) : (dual G).rk σ = σ.colors.card := rfl

lemma dual_rk_top (v : V) : (dual G).rk (DualSimplex.top G v) = D + 1 := by
  simp [dual_rk]

variable (G) in
/-- **The dual is pure** (Gurau 2010, Section 2): every simplex is a face of a top simplex, the dual of a
vertex of the graph in its bubble. -/
theorem dual_isPure : (dual G).IsPure (D + 1) := fun σ => by
  obtain ⟨v, hv⟩ := σ.exists_mem_bub
  exact ⟨DualSimplex.top G v, (DualSimplex.le_top_iff σ v).2 hv, dual_rk_top v⟩

lemma top_injective : Function.Injective (DualSimplex.top G) := fun a b h => by
  have := congrArg DualSimplex.bub h
  simpa using this

/-- A simplex of rank `D` is a face of exactly two top simplices, the two ends of its line. -/
lemma card_tops_above (ρ : DualSimplex G) (hρ : ρ.colors.card = D) :
    Nat.card {τ : DualSimplex G // ρ ≤ τ ∧ (dual G).rk τ = D + 1} = 2 := by
  have hcard : ρ.bub.card = 2 := by
    obtain ⟨v, hv⟩ := ρ.bub_eq
    have h1 : (univ \ ρ.colors).card = 1 := by
      rw [card_sdiff_of_subset (subset_univ _)]
      simp [hρ]
    obtain ⟨c, hc⟩ := card_eq_one.1 h1
    rw [hv, hc]
    exact card_bubble_singleton G c v
  let f : {w // w ∈ ρ.bub} → {τ : DualSimplex G // ρ ≤ τ ∧ (dual G).rk τ = D + 1} :=
    fun w => ⟨DualSimplex.top G w.1, (DualSimplex.le_top_iff ρ w.1).2 w.2, dual_rk_top w.1⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      exact Subtype.ext (top_injective (congrArg Subtype.val h))
    · rintro ⟨τ, hτ, hr⟩
      obtain ⟨v, rfl⟩ := DualSimplex.eq_top_of_card τ (by simpa [dual_rk] using hr)
      exact ⟨⟨v, (DualSimplex.le_top_iff ρ v).1 hτ⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  simp [hcard]

variable (G) in
/-- **The dual is non-branching** (Gurau 2010, Section 2): a simplex of rank `D` is the dual of a line
(`inv_ne`: a line has two ends) and is a face of exactly two top simplices. -/
theorem dual_isNonBranching : (dual G).IsNonBranching (D + 1) := fun σ h =>
  card_tops_above σ (by simpa [dual_rk] using h)

lemma card_edge_colors (c : Fin (D + 1)) (a : V) : (DualSimplex.edge G c a).colors.card = D := by
  rw [DualSimplex.colors_edge, card_sdiff_of_subset (subset_univ _)]
  simp

/-- The tops of two ends of a line are adjacent: they share the simplex of the line. -/
lemma adjacent_top (c : Fin (D + 1)) (a : V) :
    (dual G).Adjacent (D + 1) (DualSimplex.top G a) (DualSimplex.top G (G.inv c a)) := by
  refine ⟨dual_rk_top a, dual_rk_top _, fun h => G.inv_ne c a (top_injective h).symm,
    DualSimplex.edge G c a, ?_, DualSimplex.edge_le_top c a, DualSimplex.edge_le_top' c a⟩
  simp [dual_rk, card_edge_colors]

variable (G) in
/-- **The dual of a connected colored graph is strongly connected** (Gurau 2010, Section 2): two top
simplices, the duals of two vertices, are joined by a strong chain, a chain of lines. -/
theorem dual_isStronglyConnected (h : G.IsConnected) : (dual G).IsStronglyConnected (D + 1) := by
  intro a b ha hb
  obtain ⟨v, rfl⟩ := DualSimplex.eq_top_of_card a (by simpa [dual_rk] using ha)
  obtain ⟨w, rfl⟩ := DualSimplex.eq_top_of_card b (by simpa [dual_rk] using hb)
  have hch := strongChain_of_connected G h v w
  refine Relation.ReflTransGen.lift (DualSimplex.top G) (fun x y hxy => ?_) _ _ hch
  obtain ⟨c, -, rfl⟩ := hxy
  exact adjacent_top c x

/-- The lines of a color not in `σ` stay in the bubble of `σ`. -/
lemma inv_mem_bub (σ : DualSimplex G) {b : V} (hb : b ∈ σ.bub) {c : Fin (D + 1)}
    (hc : c ∉ σ.colors) : G.inv c b ∈ σ.bub := by
  obtain ⟨v0, hv⟩ := σ.bub_eq
  rw [hv] at hb ⊢
  exact inv_mem_bubble_of_mem G (by simpa using hc) hb

lemma link_rk (σ : DualSimplex G) (τ : Set.Ici σ) :
    ((dual G).link σ).rk τ = τ.1.colors.card - σ.colors.card := rfl

/-- The tops of the two ends of a line of a color outside `σ`, both faces-above `σ`, are adjacent in the
link of `σ`. -/
lemma adjacent_top_link (σ : DualSimplex G) (hσ : σ.colors.card + 2 ≤ D + 1) {b : V}
    (hb : b ∈ σ.bub) {c : Fin (D + 1)} (hc : c ∉ σ.colors) :
    ((dual G).link σ).Adjacent (D + 1 - σ.colors.card)
      ⟨DualSimplex.top G b, (DualSimplex.le_top_iff σ b).2 hb⟩
      ⟨DualSimplex.top G (G.inv c b), (DualSimplex.le_top_iff σ _).2 (inv_mem_bub σ hb hc)⟩ := by
  have hσ' : σ.colors.card ≤ D + 1 := by omega
  refine ⟨?_, ?_, ?_, ⟨DualSimplex.edge G c b,
    (DualSimplex.le_edge_iff σ c b).2 ⟨hc, hb, inv_mem_bub σ hb hc⟩⟩, ?_, ?_, ?_⟩
  · simp [link_rk]
  · simp [link_rk]
  · intro h
    exact G.inv_ne c b (top_injective (congrArg Subtype.val h)).symm
  · simp [link_rk, card_edge_colors]
    have := σ.colors.card_le_univ
    simp at this
    omega
  · exact DualSimplex.edge_le_top c b
  · exact DualSimplex.edge_le_top' c b

variable (G) in
/-- **The dual of a colored graph is normal** (Gurau 2010, Section 5, Theorem 2): the link of every simplex
of rank at most `D - 1` is a pseudo-manifold. The link of `σ` is pure and non-branching as the dual
is, and strongly connected because the bubble of `σ` is connected under the lines of the colors
not in `σ`. No connectedness of the graph is needed. -/
theorem dual_isNormal : (dual G).IsNormal (D + 1) := by
  intro σ hσ
  have hσ' : σ.colors.card + 2 ≤ D + 1 := hσ
  refine ⟨?_, ?_, ?_⟩
  · intro τ
    obtain ⟨v, hv⟩ := DualSimplex.exists_mem_bub τ.1
    have hσv : v ∈ σ.bub := τ.2.2 hv
    refine ⟨⟨DualSimplex.top G v, (DualSimplex.le_top_iff σ v).2 hσv⟩,
      (DualSimplex.le_top_iff τ.1 v).2 hv, ?_⟩
    simp [link_rk]
    rfl
  · rintro ⟨ρ, hρσ⟩ hρ
    have hle : σ.colors.card ≤ ρ.colors.card := card_le_card hρσ.1
    have hρ' : ρ.colors.card = D := by
      simp only [link_rk] at hρ
      show _ = _
      change ρ.colors.card - σ.colors.card + 1 = D + 1 - σ.colors.card at hρ
      omega
    let e : {τ : Set.Ici σ // (⟨ρ, hρσ⟩ : Set.Ici σ) ≤ τ ∧ ((dual G).link σ).rk τ = D + 1 - (dual G).rk σ} ≃
        {τ : DualSimplex G // ρ ≤ τ ∧ (dual G).rk τ = D + 1} :=
      { toFun := fun τ => ⟨τ.1.1, τ.2.1, by
          have h2 := τ.2.2
          have h3 : σ.colors.card ≤ τ.1.1.colors.card := card_le_card τ.1.2.1
          change τ.1.1.colors.card - σ.colors.card = D + 1 - σ.colors.card at h2
          change τ.1.1.colors.card = D + 1
          omega⟩
        invFun := fun τ => ⟨⟨τ.1, hρσ.trans τ.2.1⟩, τ.2.1, by
          have h2 := τ.2.2
          change τ.1.colors.card = D + 1 at h2
          change τ.1.colors.card - σ.colors.card = D + 1 - σ.colors.card
          rw [h2]⟩
        left_inv := fun τ => rfl
        right_inv := fun τ => rfl }
    rw [Nat.card_congr e]
    exact card_tops_above ρ hρ'
  · rintro ⟨a, haσ⟩ ⟨b, hbσ⟩ ha hb
    have hca : σ.colors.card ≤ a.colors.card := card_le_card haσ.1
    have hcb : σ.colors.card ≤ b.colors.card := card_le_card hbσ.1
    change a.colors.card - σ.colors.card = D + 1 - σ.colors.card at ha
    change b.colors.card - σ.colors.card = D + 1 - σ.colors.card at hb
    obtain ⟨v, rfl⟩ := DualSimplex.eq_top_of_card a (by omega)
    obtain ⟨w, rfl⟩ := DualSimplex.eq_top_of_card b (by omega)
    have hv : v ∈ σ.bub := (DualSimplex.le_top_iff σ v).1 haσ
    have hw : w ∈ σ.bub := (DualSimplex.le_top_iff σ w).1 hbσ
    obtain ⟨v0, hv0⟩ := σ.bub_eq
    have hwv : w ∈ G.bubble (univ \ σ.colors) v := by
      rw [hv0] at hv hw
      rw [bubble_eq_of_mem G _ hv]
      exact hw
    have hch := (mem_bubble_iff G _ v w).1 hwv
    have key : ∀ x, Relation.ReflTransGen (G.Adj (univ \ σ.colors)) v x →
        ∃ hx : x ∈ σ.bub, Relation.ReflTransGen (((dual G).link σ).Adjacent (D + 1 - σ.colors.card))
          ⟨DualSimplex.top G v, haσ⟩ ⟨DualSimplex.top G x, (DualSimplex.le_top_iff σ x).2 hx⟩ := by
      intro x hx
      induction hx with
      | refl => exact ⟨hv, Relation.ReflTransGen.refl⟩
      | tail _ hadj ih =>
        obtain ⟨hb', hr⟩ := ih
        obtain ⟨c0, hc0, rfl⟩ := hadj
        have hc0' : c0 ∉ σ.colors := by simpa using hc0
        exact ⟨inv_mem_bub σ hb' hc0',
          hr.tail (adjacent_top_link σ hσ' hb' hc0')⟩
    obtain ⟨_, hr⟩ := key w hch
    exact hr

variable (G) in
/-- **The dual of a connected colored graph is a normal pseudo-manifold** (Gurau 2010, Section 5,
Theorem 2, for the indexed complex `Δ_G`): pure, non-branching, strongly connected, with every link a
pseudo-manifold. **Differences from the source** (the statement of Theorem 2 and the definitions of its
Section 2 were read in arXiv:1006.0714; the proof was not compared): Gurau states that `Δ_G` is a normal
*simplicial* pseudo-manifold, a collection of subsets of a vertex set that may repeat; here `Δ_G` is a graded
poset with indexed simplices, whose vertex sets are not part of the structure, and the simplicial property
appears only as the Boolean lower intervals of `faceIso`. The two readings are not proved equivalent. Pending
the owner's approval of this form, the result counts as partial. -/
theorem dual_isNormalPseudoManifold (h : G.IsConnected) : (dual G).IsNormalPseudoManifold (D + 1) :=
  ⟨⟨dual_isPure G, dual_isNonBranching G, dual_isStronglyConnected G h⟩, dual_isNormal G⟩

/-- A bubble for more colors is larger. -/
lemma bubble_mono (G : ColoredGraph D V) {S S' : Finset (Fin (D + 1))} (h : S ⊆ S') (v : V) :
    G.bubble S v ⊆ G.bubble S' v := by
  intro w hw
  rw [mem_bubble_iff] at hw ⊢
  exact Relation.ReflTransGen.mono (p := G.Adj S') (fun a b hab => by
    obtain ⟨c, hc, e⟩ := hab
    exact ⟨c, h hc, e⟩) _ _ hw

variable {G : ColoredGraph D V}

/-- **Every lower interval of `Δ_G` is a Boolean lattice**: the faces of `σ` are in order-preserving
bijection with the subsets of its set of colors, so `σ` has `rk σ` vertices and `2 ^ rk σ` faces. This is
what makes `Δ_G` a simplicial complex in the multiset sense of Gurau 2010, Section 2. -/
noncomputable def faceIso (σ : DualSimplex G) :
    Set.Iic σ ≃o {T : Finset (Fin (D + 1)) // T ⊆ σ.colors} :=
  let v := Classical.choose (DualSimplex.exists_mem_bub σ)
  have hv : v ∈ σ.bub := Classical.choose_spec (DualSimplex.exists_mem_bub σ)
  have hσ : σ.bub = G.bubble (univ \ σ.colors) v := by
    obtain ⟨v0, hv0⟩ := σ.bub_eq
    rw [hv0] at hv ⊢
    exact (bubble_eq_of_mem G _ hv).symm
  have key : ∀ τ : DualSimplex G, τ ≤ σ → τ.bub = G.bubble (univ \ τ.colors) v := by
    intro τ hτ
    obtain ⟨w, hw⟩ := τ.bub_eq
    have hvτ : v ∈ τ.bub := hτ.2 hv
    rw [hw] at hvτ ⊢
    exact (bubble_eq_of_mem G _ hvτ).symm
  { toFun := fun τ => ⟨τ.1.colors, τ.2.1⟩
    invFun := fun T => ⟨⟨(T.1, G.bubble (univ \ T.1) v), ⟨v, rfl⟩⟩, by
      refine ⟨T.2, ?_⟩
      show G.bubble (univ \ T.1) v ⊇ σ.bub
      rw [hσ]
      exact bubble_mono G (sdiff_subset_sdiff subset_rfl T.2) v⟩
    left_inv := fun τ => by
      apply Subtype.ext
      exact Subtype.ext (Prod.ext rfl (key τ.1 τ.2).symm)
    right_inv := fun T => rfl
    map_rel_iff' := by
      intro a b
      constructor
      · intro h
        refine ⟨h, ?_⟩
        rw [key a.1 a.2, key b.1 b.2]
        exact bubble_mono G (sdiff_subset_sdiff subset_rfl h) v
      · intro h
        exact h.1 }

/-- **`Δ_G` is a simplicial poset**: each lower interval has `2 ^ rk σ` elements, those of the powerset of the
`rk σ` colors. -/
theorem dual_isSimplicial (σ : DualSimplex G) :
    Nonempty (Set.Iic σ ≃o {T : Finset (Fin (D + 1)) // T ⊆ σ.colors}) := ⟨faceIso σ⟩

end ColoredGraph

/-- **Trust check**: the dual of the graph with two vertices and three lines, whose two top simplices have
the same vertices, is a normal pseudo-manifold of top rank `3`. -/
example : (theta.dual).IsNormalPseudoManifold 3 :=
  ColoredGraph.dual_isNormalPseudoManifold theta (by unfold ColoredGraph.IsConnected; decide +kernel)

end Lightlike.GFT
