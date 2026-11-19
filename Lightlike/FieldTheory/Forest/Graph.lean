import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Basic.Real.Basic
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Finset.Max

/-!
# Links, forests and the ultrametric of a forest

The `n` points `Fin n`, the links `Link n` (unordered pairs of distinct points, the set `P_n` of Abdesselam–Rivasseau),
the graph of a set of links, forests (sets of links with no cycle), and for a forest `F` with parameters `w` on its
links the value `ultra F w a b`: the largest parameter `t = w l` (`l ∈ F`) such that `a` and `b` are joined by the
links of `F` with parameter at least `t`, and `0` if there is none. (It is the infimum of `w` over the path of `F`
joining `a` to `b`, `ultra_eq_path_inf`.)

The key property (`ultra_insert_of_joined`, `ultra_insert_of_not_joined`): adding to `F` a link `l*` whose parameter
is at most every parameter of `F` does not change the value for points already joined in `F`, and gives the value
`w l*` to the points it newly joins.
-/

open Finset SimpleGraph

namespace Lightlike.FieldTheory.Forest

variable (n : ℕ)

/-- **A link**: an unordered pair of distinct points of `Fin n`. -/
abbrev Link := {e : Sym2 (Fin n) // ¬ e.IsDiag}

variable {n}

/-- The graph on `Fin n` whose edges are a set of links. -/
def graphOf (S : Finset (Link n)) : SimpleGraph (Fin n) := fromEdgeSet {e | ∃ l ∈ S, l.1 = e}

/-- **A forest**: a set of links without cycles. -/
def IsForest (F : Finset (Link n)) : Prop := (graphOf F).IsAcyclic

/-- `a` and `b` are joined by the links of `S`. -/
def Joined (S : Finset (Link n)) (a b : Fin n) : Prop := (graphOf S).Reachable a b

lemma joined_symm {S : Finset (Link n)} {a b : Fin n} : Joined S a b ↔ Joined S b a :=
  ⟨Reachable.symm, Reachable.symm⟩

/-- The endpoints of the link `e` are joined by the links of `S`. -/
def Linked (S : Finset (Link n)) (e : Link n) : Prop :=
  Sym2.lift ⟨fun a b => Joined S a b, fun _ _ => propext joined_symm⟩ e.1

lemma graphOf_mono {S S' : Finset (Link n)} (h : S ⊆ S') : graphOf S ≤ graphOf S' :=
  fromEdgeSet_mono fun _ ⟨l, hl, he⟩ => ⟨l, h hl, he⟩

lemma Joined.mono {S S' : Finset (Link n)} (h : S ⊆ S') {a b : Fin n} (hj : Joined S a b) : Joined S' a b :=
  SimpleGraph.Reachable.mono (graphOf_mono h) hj

lemma joined_self (S : Finset (Link n)) (a : Fin n) : Joined S a a := Reachable.refl a

lemma linked_mk {S : Finset (Link n)} {a b : Fin n} (h : ¬ (s(a, b) : Sym2 (Fin n)).IsDiag) :
    Linked S ⟨s(a, b), h⟩ ↔ Joined S a b := Iff.rfl

lemma Linked.mono {S S' : Finset (Link n)} (h : S ⊆ S') {e : Link n} (he : Linked S e) : Linked S' e := by
  obtain ⟨e, he'⟩ := e
  induction e using Sym2.ind with
  | _ a b => exact Joined.mono h he

lemma linked_of_mem {S : Finset (Link n)} {e : Link n} (he : e ∈ S) : Linked S e := by
  obtain ⟨e, hd⟩ := e
  induction e using Sym2.ind with
  | _ a b =>
    have hab : a ≠ b := fun h => hd (by simp [h])
    exact Adj.reachable ((fromEdgeSet_adj _).2 ⟨⟨_, he, rfl⟩, hab⟩)

lemma graphOf_insert (S : Finset (Link n)) {a b : Fin n} (h : ¬ (s(a, b) : Sym2 (Fin n)).IsDiag) :
    graphOf (insert ⟨s(a, b), h⟩ S) = graphOf S ⊔ edge a b := by
  rw [edge, graphOf, graphOf, ← fromEdgeSet_union]
  congr 1
  ext e
  simp only [Finset.mem_insert, Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨l, hl | hl, rfl⟩
    · exact Or.inr (by rw [hl])
    · exact Or.inl ⟨l, hl, rfl⟩
  · rintro (⟨l, hl, rfl⟩ | rfl)
    · exact ⟨l, Or.inr hl, rfl⟩
    · exact ⟨_, Or.inl rfl, rfl⟩

/-- **Adding a link to a forest gives a forest exactly when its endpoints were not yet joined.** -/
lemma isForest_insert_iff {F : Finset (Link n)} (hF : IsForest F) {l : Link n} (hl : l ∉ F) :
    IsForest (insert l F) ↔ ¬ Linked F l := by
  obtain ⟨e, hd⟩ := l
  induction e using Sym2.ind with
  | _ a b =>
    have hab : a ≠ b := fun h => hd (by simp [h])
    have hadj : ¬ (graphOf F).Adj a b := by
      rw [graphOf, fromEdgeSet_adj]
      rintro ⟨⟨l', hl', he⟩, -⟩
      exact hl (by rwa [show (⟨s(a, b), hd⟩ : Link n) = l' from Subtype.ext he.symm])
    have hF' : (graphOf F).IsAcyclic := hF
    rw [IsForest, graphOf_insert F hd, isAcyclic_sup_fromEdgeSet_iff]
    simp only [hF', true_and]
    constructor
    · intro h hj
      rcases h hj with h | h
      · exact hab h
      · exact hadj h
    · intro h hj; exact absurd hj h

/-- The links of `F` with parameter at least `t`. -/
noncomputable def above (F : Finset (Link n)) (w : Link n → ℝ) (t : ℝ) : Finset (Link n) := by
  classical exact F.filter fun l => t ≤ w l

lemma mem_above {F : Finset (Link n)} {w : Link n → ℝ} {t : ℝ} {l : Link n} :
    l ∈ above F w t ↔ l ∈ F ∧ t ≤ w l := by
  classical simp [above]

lemma above_subset (F : Finset (Link n)) (w : Link n → ℝ) (t : ℝ) : above F w t ⊆ F := fun _ hl =>
  (mem_above.1 hl).1

/-- **The ultrametric of a forest**: the largest parameter `t = w l`, `l ∈ F`, such that `a` and `b` are joined by
the links of `F` with parameter at least `t`; `0` if there is none. -/
noncomputable def ultra (F : Finset (Link n)) (w : Link n → ℝ) (a b : Fin n) : ℝ := by
  classical
  exact (insert 0 ((F.filter fun l => Joined (above F w (w l)) a b).image w)).max' (Finset.insert_nonempty _ _)

lemma ultra_symm (F : Finset (Link n)) (w : Link n → ℝ) (a b : Fin n) :
    ultra F w a b = ultra F w b a := by
  classical
  unfold ultra
  congr 3
  ext l
  simp only [Finset.mem_filter]
  exact and_congr_right fun _ => joined_symm

/-- The ultrametric value on a link. -/
noncomputable def ultraL (F : Finset (Link n)) (w : Link n → ℝ) (e : Link n) : ℝ :=
  Sym2.lift ⟨ultra F w, ultra_symm F w⟩ e.1

lemma le_ultra {F : Finset (Link n)} {w : Link n → ℝ} {a b : Fin n} {l : Link n} (hl : l ∈ F)
    (hj : Joined (above F w (w l)) a b) : w l ≤ ultra F w a b := by
  classical
  unfold ultra
  exact Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨l, Finset.mem_filter.2 ⟨hl, hj⟩, rfl⟩))

lemma ultra_cases (F : Finset (Link n)) (w : Link n → ℝ) (a b : Fin n) :
    ultra F w a b = 0 ∨ ∃ l ∈ F, Joined (above F w (w l)) a b ∧ ultra F w a b = w l := by
  classical
  unfold ultra
  have h := Finset.max'_mem (insert 0 ((F.filter fun l => Joined (above F w (w l)) a b).image w))
    (Finset.insert_nonempty _ _)
  rcases Finset.mem_insert.1 h with h | h
  · exact Or.inl h
  · obtain ⟨l, hl, he⟩ := Finset.mem_image.1 h
    exact Or.inr ⟨l, (Finset.mem_filter.1 hl).1, (Finset.mem_filter.1 hl).2, he.symm⟩

lemma ultra_nonneg (F : Finset (Link n)) (w : Link n → ℝ) (a b : Fin n) : 0 ≤ ultra F w a b := by
  classical
  unfold ultra
  exact Finset.le_max' _ _ (Finset.mem_insert_self _ _)

lemma above_insert_of_lt {F : Finset (Link n)} {w : Link n → ℝ} {l : Link n} {t : ℝ} (ht : w l < t) :
    above (insert l F) w t = above F w t := by
  ext m
  simp only [mem_above, Finset.mem_insert]
  constructor
  · rintro ⟨rfl | hm, h⟩
    · exact absurd h (not_le.2 ht)
    · exact ⟨hm, h⟩
  · rintro ⟨hm, h⟩; exact ⟨Or.inr hm, h⟩

lemma above_of_le_min {F : Finset (Link n)} {w : Link n → ℝ} {t : ℝ} (ht : ∀ m ∈ F, t ≤ w m) :
    above F w t = F := by
  ext m; simp only [mem_above]; exact ⟨fun h => h.1, fun h => ⟨h, ht m h⟩⟩

lemma nonempty_of_joined {S : Finset (Link n)} {a b : Fin n} (hab : a ≠ b) (h : Joined S a b) : S.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  rintro rfl
  obtain ⟨p⟩ := h
  cases p with
  | nil => exact hab rfl
  | cons hadj _ =>
    rw [graphOf, fromEdgeSet_adj] at hadj
    obtain ⟨⟨l, hl, _⟩, _⟩ := hadj
    simp at hl

/-- **Adding a link of smallest parameter keeps the ultrametric of points already joined.** -/
lemma ultra_insert_of_joined {F : Finset (Link n)} {w : Link n → ℝ} {l : Link n} (hl : l ∉ F)
    (hmin : ∀ m ∈ F, w l ≤ w m) {a b : Fin n} (hab : a ≠ b) (hj : Joined F a b) :
    ultra (insert l F) w a b = ultra F w a b := by
  have hjF' : Joined (insert l F) a b := hj.mono (Finset.subset_insert _ _)
  -- some link of `F` of smallest parameter gives a candidate `≥ w l`
  obtain ⟨m₀, hm₀, hm₀min⟩ := F.exists_min_image w (nonempty_of_joined hab hj)
  have hc₀ : w m₀ ≤ ultra F w a b := le_ultra hm₀ (by rwa [above_of_le_min hm₀min])
  have hl₀ : w l ≤ ultra F w a b := (hmin m₀ hm₀).trans hc₀
  apply le_antisymm
  · rcases ultra_cases (insert l F) w a b with h | ⟨m, hm, hjm, he⟩
    · rw [h]; exact ultra_nonneg _ _ _ _
    · rw [he]
      rcases Finset.mem_insert.1 hm with rfl | hm
      · exact hl₀
      · rcases lt_or_ge (w l) (w m) with hlt | hge
        · rw [above_insert_of_lt hlt] at hjm
          exact le_ultra hm hjm
        · exact (le_antisymm hge (hmin m hm) ▸ hl₀ :)
  · rcases ultra_cases F w a b with h | ⟨m, hm, hjm, he⟩
    · rw [h]; exact ultra_nonneg _ _ _ _
    · rw [he]
      rcases lt_or_ge (w l) (w m) with hlt | hge
      · exact le_ultra (Finset.mem_insert_of_mem hm) (by rwa [above_insert_of_lt hlt])
      · have hwm : w m = w l := le_antisymm hge (hmin m hm)
        refine le_ultra (Finset.mem_insert_of_mem hm) ?_
        rw [above_of_le_min (t := w m) (fun m' hm' => ?_)]
        · exact hjF'
        · rcases Finset.mem_insert.1 hm' with rfl | hm'
          · exact hwm.le
          · exact hwm ▸ hmin m' hm'

/-- **Adding a link of smallest parameter gives it as the ultrametric of the points it newly joins.** -/
lemma ultra_insert_of_not_joined {F : Finset (Link n)} {w : Link n → ℝ} {l : Link n} (hl : l ∉ F)
    (hmin : ∀ m ∈ F, w l ≤ w m) (hl0 : 0 ≤ w l) {a b : Fin n} (hj : ¬ Joined F a b)
    (hj' : Joined (insert l F) a b) : ultra (insert l F) w a b = w l := by
  apply le_antisymm
  · rcases ultra_cases (insert l F) w a b with h | ⟨m, hm, hjm, he⟩
    · rw [h]; exact hl0
    · rw [he]
      rcases Finset.mem_insert.1 hm with rfl | hm
      · exact le_rfl
      · by_contra hlt
        rw [above_insert_of_lt (not_le.1 hlt)] at hjm
        exact hj (hjm.mono (above_subset F w _))
  · refine le_ultra (Finset.mem_insert_self l F) ?_
    rw [above_of_le_min (fun m hm => ?_)]
    · exact hj'
    · rcases Finset.mem_insert.1 hm with rfl | hm
      · exact le_rfl
      · exact hmin m hm

lemma mem_edgeSet_graphOf {S : Finset (Link n)} {e : Sym2 (Fin n)} :
    e ∈ (graphOf S).edgeSet ↔ ∃ l ∈ S, l.1 = e := by
  rw [graphOf, edgeSet_fromEdgeSet]
  constructor
  · exact fun h => h.1
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, hl, rfl⟩, l.2⟩

/-- The links of `F` on a walk of `graphOf F`. -/
noncomputable def walkLinks (F : Finset (Link n)) {a b : Fin n} (p : (graphOf F).Walk a b) : Finset (Link n) := by
  classical exact F.filter fun l => l.1 ∈ p.edges

lemma mem_walkLinks {F : Finset (Link n)} {a b : Fin n} {p : (graphOf F).Walk a b} {l : Link n} :
    l ∈ walkLinks F p ↔ l ∈ F ∧ l.1 ∈ p.edges := by
  classical simp [walkLinks]

lemma walkLinks_nonempty {F : Finset (Link n)} {a b : Fin n} (hab : a ≠ b) (p : (graphOf F).Walk a b) :
    (walkLinks F p).Nonempty := by
  have hne : p.edges ≠ [] := by
    intro h
    exact hab (Walk.eq_of_length_eq_zero (by rw [← Walk.length_edges, h]; rfl))
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨l, hl, rfl⟩ := mem_edgeSet_graphOf.1 (p.edges_subset_edgeSet he)
  exact ⟨l, mem_walkLinks.2 ⟨hl, he⟩⟩

/-- **For a forest, the ultrametric is the infimum of the parameters along the path**: for the (unique) path `p` of
`F` from `a` to `b`, `ultra F w a b = max 0 (min_{l ∈ p} w l)`. -/
lemma ultra_eq_path_inf {F : Finset (Link n)} (hF : IsForest F) {a b : Fin n} (hab : a ≠ b)
    (p : (graphOf F).Walk a b) (hpath : p.IsPath) (w : Link n → ℝ) :
    ultra F w a b = max 0 ((walkLinks F p).inf' (walkLinks_nonempty hab p) w) := by
  classical
  set E := walkLinks F p
  have hEne : E.Nonempty := walkLinks_nonempty hab p
  have hEF : E ⊆ F := fun l hl => (mem_walkLinks.1 hl).1
  have hmemE : ∀ e ∈ p.edges, ∃ l ∈ E, l.1 = e := fun e he => by
    obtain ⟨l, hl, rfl⟩ := mem_edgeSet_graphOf.1 (p.edges_subset_edgeSet he)
    exact ⟨l, mem_walkLinks.2 ⟨hl, he⟩, rfl⟩
  refine le_antisymm ?_ ?_
  · -- every candidate is at most the infimum along the path
    rcases ultra_cases F w a b with h | ⟨l, hl, hjl, he⟩
    · rw [h]; exact le_max_left _ _
    · rw [he]
      refine le_max_of_le_right (Finset.le_inf' _ _ fun l' hl' => ?_)
      obtain ⟨r⟩ := hjl
      let r' := r.mapLe (graphOf_mono (above_subset F w (w l)))
      have huniq := (hF.subsingleton_path a b).elim ⟨r'.bypass, r'.bypass_isPath⟩ ⟨p, hpath⟩
      have hedges : p.edges ⊆ r.edges := by
        have h1 : r'.bypass.edges = p.edges := congrArg (fun π : (graphOf F).Path a b => π.1.edges) huniq
        have hsub : r'.edges = r.edges := by simp [r']
        intro e he
        rw [← h1] at he
        have := r'.edges_bypass_subset_edges he
        rwa [hsub] at this
      have hl'e : l'.1 ∈ p.edges := (mem_walkLinks.1 hl').2
      obtain ⟨m, hm, hme⟩ := mem_edgeSet_graphOf.1 (r.edges_subset_edgeSet (hedges hl'e))
      rw [show m = l' from Subtype.ext hme] at hm
      exact (mem_above.1 hm).2
  · -- the link of smallest parameter on the path is a candidate
    obtain ⟨l₀, hl₀, he₀⟩ := Finset.exists_mem_eq_inf' hEne w
    have hj₀ : Joined (above F w (w l₀)) a b := by
      refine ⟨p.transfer (graphOf (above F w (w l₀))) fun e he => ?_⟩
      obtain ⟨l, hl, rfl⟩ := hmemE e he
      refine mem_edgeSet_graphOf.2 ⟨l, mem_above.2 ⟨hEF hl, ?_⟩, rfl⟩
      rw [← he₀]
      exact Finset.inf'_le _ hl
    rw [he₀]
    exact max_le (ultra_nonneg _ _ _ _) (le_ultra (hEF hl₀) hj₀)

/-- For a forest, the ultrametric of two joined points is continuous in the parameters. -/
lemma continuous_ultra {F : Finset (Link n)} (hF : IsForest F) {a b : Fin n} (hab : a ≠ b) (hj : Joined F a b) :
    Continuous fun w : Link n → ℝ => ultra F w a b := by
  obtain ⟨q⟩ := hj
  simp_rw [ultra_eq_path_inf hF hab q.bypass q.bypass_isPath]
  exact continuous_const.max (Continuous.finset_inf'_apply _ fun l _ => continuous_apply l)

end Lightlike.FieldTheory.Forest
