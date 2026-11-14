import Lightlike.Regge.Manifold
import Lightlike.PonzanoRegge.SphereConverse

/-!
# Combinatorial 3-manifolds are edge-manifolds

`IsEdgeManifold K` (`Lightlike/Regge/Manifold.lean`) asks the link of every edge to be a circle or
an arc; it is the condition Regge calculus uses. The core library defines closed combinatorial
3-manifolds (`Lightlike.PR.IsCombManifold`: the link of every vertex is a combinatorial 2-sphere
`Lightlike.PR.IsSphere2`, obtained from the boundary of a tetrahedron by bistellar moves). This file
shows that every closed combinatorial 3-manifold is an edge-manifold, so that all results of
`Regge/` stated for edge-manifolds apply to it, and gives a decision procedure for the edge
condition on examples.

## Main results

* `exists_cycle_of_two_regular`: a finite connected set of edges in which every vertex lies in
  exactly two edges is a single cycle (through Mathlib's `SimpleGraph.IsCycles`).
* `lk2_cycle_of_isSurfaceSphere`: in a triangulated 2-sphere (over any vertex type) the link of
  a vertex is a cycle; `star_eq_of_lk2`: a cycle or path in the link of `b` inside the link of `a`
  gives the tetrahedra around the edge `ab`. Both are also used for manifolds with boundary
  (`Lightlike/Regge/Disc.lean`).
* `isCycleLink_of_isSurfaceSphere`: if the link of the vertex `a` is a triangulated 2-sphere
  (`Lightlike.PR.IsSurfaceSphere`), every edge `ab` has a cycle link. In the link of `a`, the link of `b`
  is the link of the edge `ab` (`mem_lk2_link`), and in a closed surface with connected vertex
  links it is a connected edge set in which every vertex has degree two.
* `IsCombManifold.isEdgeManifold`: every closed combinatorial 3-manifold is an edge-manifold, with
  every edge interior (`IsCombManifold.mem_intEdges`).
* `isEdgeManifold_of_check`: a decision procedure: lists of link vertices that pass the computable
  checks `cycleCheck` or `pathCheck` give cycle and path links; `finLinkWitness` computes candidate
  lists for vertices `Fin n`, so that the kernel can decide the condition on examples.
-/

open Finset

namespace Lightlike.Regge

open Lightlike.PR (Complex3 IsSurfaceSphere IsConnEdges lk2 verts2 edges2 mem_verts2)

variable {V : Type*} [DecidableEq V]

/-! ## A connected set of edges in which every vertex has degree two is a cycle -/

/-- **A connected 2-regular set of edges is a cycle.** Let `G` be a nonempty finite set of
2-element sets (edges) such that every vertex lies in exactly two edges and any two vertices are
joined by a path of edges. Then the vertices can be listed as a cycle `w 0, …, w (n-1)`,
`w n = w 0`, `n ≥ 3`, with `G` exactly the edges `{w i, w (i+1)}`. -/
theorem exists_cycle_of_two_regular {G : Finset (Finset V)} (hcard : ∀ e ∈ G, #e = 2)
    (hdeg : ∀ x ∈ verts2 G, #(G.filter (x ∈ ·)) = 2) (hconn : IsConnEdges G) (hne : G.Nonempty) :
    ∃ (n : ℕ) (w : ℕ → V), 3 ≤ n ∧ Set.InjOn w (range n) ∧ w n = w 0 ∧
      (∀ i, w i ∈ verts2 G) ∧ G = (range n).image fun i => ({w i, w (i + 1)} : Finset V) := by
  classical
  let W := {x // x ∈ verts2 G}
  let Γ : SimpleGraph W := SimpleGraph.fromRel fun x y => ({x.1, y.1} : Finset V) ∈ G
  have hadj : ∀ x y : W, Γ.Adj x y ↔ ({x.1, y.1} : Finset V) ∈ G := by
    intro x y
    simp only [Γ, SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨-, h | h⟩
      · exact h
      · rwa [pair_comm]
    · intro h
      refine ⟨fun hxy => ?_, Or.inl h⟩
      have := hcard _ h
      subst hxy
      simp at this
  -- every vertex has exactly two neighbours
  have pair : ∀ (x : V), ∀ e ∈ G, x ∈ e → ∃ y, y ≠ x ∧ e = {x, y} := by
    intro x e heG hx
    obtain ⟨p, q, hpq, rfl⟩ := card_eq_two.mp (hcard e heG)
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ⟨q, hpq.symm, rfl⟩
    · exact ⟨p, hpq, pair_comm _ _⟩
  have hnbr : ∀ x : W, ∃ y z : W, y ≠ z ∧ Γ.neighborSet x = {y, z} := by
    intro x
    obtain ⟨e₁, e₂, he, hfe⟩ := card_eq_two.mp (hdeg x.1 x.2)
    have m₁ : e₁ ∈ G.filter (x.1 ∈ ·) := by rw [hfe]; simp
    have m₂ : e₂ ∈ G.filter (x.1 ∈ ·) := by rw [hfe]; simp
    rw [mem_filter] at m₁ m₂
    obtain ⟨y₁, hy₁, he₁⟩ := pair x.1 e₁ m₁.1 m₁.2
    obtain ⟨y₂, hy₂, he₂⟩ := pair x.1 e₂ m₂.1 m₂.2
    have g₁ : y₁ ∈ verts2 G := mem_verts2.mpr ⟨_, m₁.1, by rw [he₁]; simp⟩
    have g₂ : y₂ ∈ verts2 G := mem_verts2.mpr ⟨_, m₂.1, by rw [he₂]; simp⟩
    refine ⟨⟨y₁, g₁⟩, ⟨y₂, g₂⟩, fun h => he ?_, ?_⟩
    · rw [he₁, he₂, show y₁ = y₂ from congrArg Subtype.val h]
    · ext y
      simp only [SimpleGraph.mem_neighborSet, hadj, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hy
        have hyx : y.1 ≠ x.1 := by
          intro h
          have := hcard _ hy
          rw [h] at this
          simp at this
        have : ({x.1, y.1} : Finset V) ∈ G.filter (x.1 ∈ ·) := mem_filter.mpr ⟨hy, by simp⟩
        rw [hfe, mem_insert, mem_singleton] at this
        rcases this with h | h
        · left
          apply Subtype.ext
          have : y.1 ∈ ({x.1, y₁} : Finset V) := by rw [← he₁, ← h]; simp
          simp only [mem_insert, mem_singleton] at this
          exact this.resolve_left hyx
        · right
          apply Subtype.ext
          have : y.1 ∈ ({x.1, y₂} : Finset V) := by rw [← he₂, ← h]; simp
          simp only [mem_insert, mem_singleton] at this
          exact this.resolve_left hyx
      · rintro (rfl | rfl)
        · rw [← he₁]; exact m₁.1
        · rw [← he₂]; exact m₂.1
  have hcyc : Γ.IsCycles := fun v _ => by
    obtain ⟨y, z, hyz, h⟩ := hnbr v
    rw [h, Set.ncard_pair hyz]
  -- `Γ` is connected
  have hreach : ∀ x y : W, Γ.Reachable x y := by
    intro x y
    have key : ∀ q, Relation.ReflTransGen (fun p q => ({p, q} : Finset V) ∈ G) x.1 q →
        ∀ hq : q ∈ verts2 G, Γ.Reachable x ⟨q, hq⟩ := by
      intro q hxq
      induction hxq with
      | refl => intro _; exact SimpleGraph.Reachable.refl _
      | tail _ hbc ih =>
        rename_i b c _
        intro hc
        have hb : b ∈ verts2 G := mem_verts2.mpr ⟨_, hbc, by simp⟩
        exact (ih hb).trans (SimpleGraph.Adj.reachable ((hadj ⟨b, hb⟩ ⟨c, hc⟩).mpr hbc))
    exact key y.1 (hconn x.1 x.2 y.1 y.2) y.2
  -- a cycle through all vertices
  obtain ⟨e₀, he₀⟩ := hne
  obtain ⟨p₀, q₀, -, hpq₀⟩ := card_eq_two.mp (hcard e₀ he₀)
  have hx₀ : p₀ ∈ verts2 G := mem_verts2.mpr ⟨_, he₀, by rw [hpq₀]; simp⟩
  let x₀ : W := ⟨p₀, hx₀⟩
  have hn₀ : (Γ.neighborSet x₀).Nonempty := by
    obtain ⟨y, z, -, h⟩ := hnbr x₀
    rw [h]
    exact Set.insert_nonempty _ _
  obtain ⟨p, hp, hverts⟩ := hcyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c := Γ.connectedComponentMk x₀) ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl) hn₀
  have hsupp : ∀ v : W, v ∈ p.support := by
    intro v
    rw [← SimpleGraph.Walk.mem_verts_toSubgraph, hverts,
      SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact SimpleGraph.ConnectedComponent.eq.mpr (hreach v x₀)
  refine ⟨p.length, fun i => (p.getVert i).1, hp.three_le_length, ?_, ?_, fun i => (p.getVert i).2,
    ?_⟩
  · intro i hi j hj hij
    simp only [coe_range, Set.mem_Iio] at hi hj
    exact hp.getVert_injOn' (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) (Subtype.ext hij)
  · simp only [SimpleGraph.Walk.getVert_length, SimpleGraph.Walk.getVert_zero]
  · ext e
    simp only [mem_image, mem_range]
    constructor
    · intro he
      obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp (hcard e he)
      have ha : a ∈ verts2 G := mem_verts2.mpr ⟨_, he, by simp⟩
      have hb : b ∈ verts2 G := mem_verts2.mpr ⟨_, he, by simp⟩
      have hΓ : Γ.Adj ⟨a, ha⟩ ⟨b, hb⟩ := (hadj _ _).mpr he
      have hsub : p.toSubgraph.neighborSet ⟨a, ha⟩ = Γ.neighborSet ⟨a, ha⟩ := by
        apply Set.eq_of_subset_of_ncard_le
        · intro y hy
          exact p.toSubgraph.adj_sub hy
        · rw [hp.ncard_neighborSet_toSubgraph_eq_two (hsupp _)]
          obtain ⟨y, z, hyz, h⟩ := hnbr ⟨a, ha⟩
          rw [h, Set.ncard_pair hyz]
        · exact Set.toFinite _
      have hsA : p.toSubgraph.Adj ⟨a, ha⟩ ⟨b, hb⟩ := by
        have : (⟨b, hb⟩ : W) ∈ p.toSubgraph.neighborSet ⟨a, ha⟩ := by rw [hsub]; exact hΓ
        exact this
      obtain ⟨i, hi, hlt⟩ := (SimpleGraph.Walk.toSubgraph_adj_iff p).mp hsA
      refine ⟨i, hlt, ?_⟩
      rcases Sym2.eq_iff.mp hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
      · rw [h1, h2, pair_comm]
    · rintro ⟨i, hi, rfl⟩
      exact (hadj _ _).mp (p.adj_getVert_succ hi)

/-! ## Closed combinatorial 3-manifolds -/

/-- In the link of the vertex `a`, the link of `b ≠ a` is the link of the edge `ab`: its edges are
the sets `e`, disjoint from `{a, b}`, with `{a, b} ∪ e` a tetrahedron. -/
theorem mem_lk2_link {K : Complex3 V} {a b : V} (hab : a ≠ b) {e : Finset V} :
    e ∈ lk2 (K.link a) b ↔ a ∉ e ∧ b ∉ e ∧ insert a (insert b e) ∈ K.tets := by
  rw [Lightlike.PR.mem_lk2, Lightlike.PR.Complex3.mem_link]
  constructor
  · rintro ⟨hb, ha, ht⟩
    simp only [mem_insert, not_or] at ha
    exact ⟨ha.2, hb, ht⟩
  · rintro ⟨ha, hb, ht⟩
    exact ⟨hb, by simp [hab, ha], ht⟩

/-- **In a triangulated 2-sphere the link of a vertex is a cycle.** For a vertex `b` of `L` with
`Lightlike.PR.IsSurfaceSphere L`, the link `lk2 L b` is a cycle `w 0, …, w (n-1)`, `w n = w 0`, `n ≥ 3`:
its edges are exactly the `{w i, w (i+1)}`. -/
theorem lk2_cycle_of_isSurfaceSphere {W : Type*} [DecidableEq W] {L : Finset (Finset W)}
    (hS : IsSurfaceSphere L) {b : W} (hb : b ∈ verts2 L) :
    ∃ (n : ℕ) (w : ℕ → W), 3 ≤ n ∧ Set.InjOn w (range n) ∧ w n = w 0 ∧
      (∀ i, w i ∈ verts2 (lk2 L b)) ∧
      lk2 L b = (range n).image fun i => ({w i, w (i + 1)} : Finset W) := by
  have hcard : ∀ e ∈ lk2 L b, #e = 2 := by
    intro e he'
    obtain ⟨hbe, hins⟩ := Lightlike.PR.mem_lk2.mp he'
    have := hS.card _ hins
    rw [card_insert_of_notMem hbe] at this
    omega
  have hdeg : ∀ x ∈ verts2 (lk2 L b), #((lk2 L b).filter (x ∈ ·)) = 2 := by
    intro x hx
    obtain ⟨e, he', hxe⟩ := mem_verts2.mp hx
    obtain ⟨hbe, hins⟩ := Lightlike.PR.mem_lk2.mp he'
    have hxb : x ≠ b := fun h => hbe (h ▸ hxe)
    have hedge : ({b, x} : Finset W) ∈ edges2 L :=
      Lightlike.PR.mem_edges2.mpr ⟨_, hins, by simp [insert_subset_iff, hxe], card_pair hxb.symm⟩
    have h2 := hS.closed _ hedge
    rw [← h2]
    refine card_nbij' (fun e => insert b e) (fun τ => τ.erase b) ?_ ?_ ?_ ?_
    · intro e he
      simp only [coe_filter, Set.mem_ofPred_eq] at he ⊢
      exact ⟨(Lightlike.PR.mem_lk2.mp he.1).2, by simp [insert_subset_iff, he.2]⟩
    · intro τ hτ
      simp only [coe_filter, Set.mem_ofPred_eq] at hτ ⊢
      have hbτ : b ∈ τ := hτ.2 (by simp)
      refine ⟨Lightlike.PR.mem_lk2.mpr ⟨notMem_erase b τ, by rw [insert_erase hbτ]; exact hτ.1⟩, ?_⟩
      exact mem_erase.mpr ⟨hxb, hτ.2 (by simp)⟩
    · intro e he
      simp only [coe_filter, Set.mem_ofPred_eq] at he
      exact erase_insert (Lightlike.PR.mem_lk2.mp he.1).1
    · intro τ hτ
      simp only [coe_filter, Set.mem_ofPred_eq] at hτ
      exact insert_erase (hτ.2 (by simp))
  have hne : (lk2 L b).Nonempty := by
    obtain ⟨τ, hτ, hbτ⟩ := mem_verts2.mp hb
    exact ⟨τ.erase b, Lightlike.PR.mem_lk2.mpr ⟨notMem_erase b _, by rw [insert_erase hbτ]; exact hτ⟩⟩
  exact exists_cycle_of_two_regular hcard hdeg (hS.link b hb) hne

/-- **The star of an edge from a link in a vertex link.** If, in the link of the vertex `a`, the link
of `b` consists of the edges `{w i, w (i+1)}`, `i < n`, then the tetrahedra of `K` containing
`{a, b}` are the `{a, b, w i, w (i+1)}`. -/
theorem star_eq_of_lk2 {K : Complex3 V} {a b : V} (hab : a ≠ b) {n : ℕ} {w : ℕ → V}
    (hG : lk2 (K.link a) b = (range n).image fun i => ({w i, w (i + 1)} : Finset V)) :
    star K {a, b} = (range n).image fun i => ({a, b, w i, w (i + 1)} : Finset V) := by
  ext s
  simp only [star, mem_filter, mem_image, mem_range]
  constructor
  · rintro ⟨hs, hsab⟩
    have has : a ∈ s := hsab (by simp)
    have hbs : b ∈ s := hsab (by simp)
    have hmem : (s.erase a).erase b ∈ lk2 (K.link a) b := by
      refine (mem_lk2_link hab).mpr ⟨?_, notMem_erase b _, ?_⟩
      · exact fun h => notMem_erase a s (mem_of_mem_erase h)
      · rw [insert_erase (mem_erase.mpr ⟨hab.symm, hbs⟩), insert_erase has]
        exact hs
    rw [hG, mem_image] at hmem
    obtain ⟨i, hi, hi'⟩ := hmem
    refine ⟨i, mem_range.mp hi, ?_⟩
    rw [show ({a, b, w i, w (i + 1)} : Finset V) = insert a (insert b {w i, w (i + 1)}) from rfl,
      hi', insert_erase (mem_erase.mpr ⟨hab.symm, hbs⟩), insert_erase has]
  · rintro ⟨i, hi, rfl⟩
    have hmem : ({w i, w (i + 1)} : Finset V) ∈ lk2 (K.link a) b := by
      rw [hG]
      exact mem_image.mpr ⟨i, mem_range.mpr hi, rfl⟩
    exact ⟨((mem_lk2_link hab).mp hmem).2.2, by simp [insert_subset_iff]⟩

/-- **A sphere link gives cycle links.** If the link of the vertex `a` of `K` is a triangulated
2-sphere, every edge `ab` of `K` has a cycle link. -/
theorem isCycleLink_of_isSurfaceSphere {K : Complex3 V} {a b : V} (hab : a ≠ b)
    (he : ({a, b} : Finset V) ∈ K.edges) (hS : IsSurfaceSphere (K.link a)) :
    ∃ n w, IsCycleLink K a b n w := by
  obtain ⟨t, ht, hsub, -⟩ := Complex3.mem_edges.mp he
  have hat : a ∈ t := hsub (by simp)
  have hbt : b ∈ t := hsub (by simp)
  have htl : t.erase a ∈ K.link a :=
    Lightlike.PR.Complex3.mem_link.mpr ⟨notMem_erase a t, by rwa [insert_erase hat]⟩
  have hb : b ∈ verts2 (K.link a) := mem_verts2.mpr ⟨_, htl, mem_erase.mpr ⟨hab.symm, hbt⟩⟩
  obtain ⟨n, w, h3, hinj, hcl, hw, hG⟩ := lk2_cycle_of_isSurfaceSphere hS hb
  have hwab : ∀ i, w i ≠ a ∧ w i ≠ b := by
    intro i
    obtain ⟨e, he', hwe⟩ := mem_verts2.mp (hw i)
    obtain ⟨ha, hb', -⟩ := (mem_lk2_link hab).mp he'
    exact ⟨fun h => ha (h ▸ hwe), fun h => hb' (h ▸ hwe)⟩
  exact ⟨n, w, hab, h3, fun i _ => (hwab i).1, fun i _ => (hwab i).2, hinj, hcl,
    star_eq_of_lk2 hab hG⟩

/-- **Every closed combinatorial 3-manifold is an edge-manifold**: in a complex whose vertex links
are combinatorial 2-spheres (`Lightlike.PR.IsCombManifold`), every edge has a cycle link. -/
theorem IsCombManifold.isEdgeManifold {K : Complex3 V} (h : Lightlike.PR.IsCombManifold K) :
    IsEdgeManifold K := by
  intro e he
  obtain ⟨t, ht, hsub, he2⟩ := Complex3.mem_edges.mp he
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp he2
  have ha : a ∈ K.verts := mem_biUnion.mpr ⟨t, ht, hsub (by simp)⟩
  obtain ⟨n, w, hc⟩ := isCycleLink_of_isSurfaceSphere hab he (h a ha).isSurfaceSphere
  exact ⟨a, b, n, w, rfl, Or.inl hc⟩

/-- In a closed combinatorial 3-manifold every edge is interior. -/
theorem IsCombManifold.mem_intEdges {K : Complex3 V} (h : Lightlike.PR.IsCombManifold K) {e : Finset V}
    (he : e ∈ K.edges) : e ∈ intEdges K := by
  obtain ⟨a, b, n, w, rfl, hc | hp⟩ := IsCombManifold.isEdgeManifold h e he
  · exact hc.mem_intEdges
  · obtain ⟨t, ht, hsub, -⟩ := Complex3.mem_edges.mp he
    have ha : a ∈ K.verts := mem_biUnion.mpr ⟨t, ht, hsub (by simp)⟩
    obtain ⟨n', w', hc'⟩ := isCycleLink_of_isSurfaceSphere hp.ne he (h a ha).isSurfaceSphere
    exact hc'.mem_intEdges

/-! ## A decision procedure for edge links -/

/-- Computable check that the list `L` is the link of the edge `{a, b}`, as a cycle. -/
def cycleCheck (K : Complex3 V) (a b : V) (L : List V) : Prop :=
  a ≠ b ∧ 3 ≤ L.length ∧ L.Nodup ∧ a ∉ L ∧ b ∉ L ∧
    star K {a, b} = (range L.length).image fun i =>
      ({a, b, L.getD i a, L.getD ((i + 1) % L.length) a} : Finset V)

/-- Computable check that the list `L` is the link of the edge `{a, b}`, as a path. -/
def pathCheck (K : Complex3 V) (a b : V) (L : List V) : Prop :=
  a ≠ b ∧ 2 ≤ L.length ∧ L.Nodup ∧ a ∉ L ∧ b ∉ L ∧
    star K {a, b} = (range (L.length - 1)).image fun i =>
      ({a, b, L.getD i a, L.getD (i + 1) a} : Finset V)

instance (K : Complex3 V) (a b : V) (L : List V) : Decidable (cycleCheck K a b L) := by
  unfold cycleCheck; infer_instance

instance (K : Complex3 V) (a b : V) (L : List V) : Decidable (pathCheck K a b L) := by
  unfold pathCheck; infer_instance

/-- A list passing `cycleCheck` is a cycle link. -/
theorem IsCycleLink.of_check {K : Complex3 V} {a b : V} {L : List V} (h : cycleCheck K a b L) :
    IsCycleLink K a b L.length fun i => L.getD (i % L.length) a := by
  obtain ⟨hab, h3, hnd, ha, hb, hstar⟩ := h
  have hget : ∀ i (hi : i < L.length), L.getD (i % L.length) a = L[i]'hi := by
    intro i hi
    rw [Nat.mod_eq_of_lt hi, List.getD_eq_getElem _ _ hi]
  refine ⟨hab, h3, fun i hi => ?_, fun i hi => ?_, fun i hi j hj hij => ?_, ?_, ?_⟩
  · rw [hget i hi]
    exact fun h => ha (h ▸ List.getElem_mem hi)
  · rw [hget i hi]
    exact fun h => hb (h ▸ List.getElem_mem hi)
  · simp only [coe_range, Set.mem_Iio] at hi hj
    simp only [hget i hi, hget j hj] at hij
    exact (hnd.getElem_inj_iff).mp hij
  · simp
  · rw [hstar]
    refine image_congr fun i hi => ?_
    simp only [coe_range, Set.mem_Iio] at hi
    simp only [Nat.mod_eq_of_lt hi]

/-- A list passing `pathCheck` is a path link. -/
theorem IsPathLink.of_check {K : Complex3 V} {a b : V} {L : List V} (h : pathCheck K a b L) :
    IsPathLink K a b (L.length - 1) fun i => L.getD i a := by
  obtain ⟨hab, h2, hnd, ha, hb, hstar⟩ := h
  have hget : ∀ i (hi : i ≤ L.length - 1), L.getD i a = L[i]'(by omega) := fun i hi =>
    List.getD_eq_getElem _ _ (by omega)
  refine ⟨hab, by omega, fun i hi => ?_, fun i hi => ?_, fun i hi j hj hij => ?_, hstar⟩
  · rw [hget i hi]
    exact fun h => ha (h ▸ List.getElem_mem _)
  · rw [hget i hi]
    exact fun h => hb (h ▸ List.getElem_mem _)
  · simp only [coe_range, Set.mem_Iio] at hi hj
    simp only [hget i (by omega), hget j (by omega)] at hij
    exact (hnd.getElem_inj_iff).mp hij

/-- **A decision procedure for `IsEdgeManifold`**: if for every edge some ordered labelling `a, b`
and the candidate list `W a b` pass `cycleCheck` or `pathCheck`, the complex is an
edge-manifold. -/
theorem isEdgeManifold_of_check (K : Complex3 V) (W : V → V → List V)
    (h : ∀ e ∈ K.edges, ∃ a ∈ e, ∃ b ∈ e, cycleCheck K a b (W a b) ∨ pathCheck K a b (W a b)) :
    IsEdgeManifold K := by
  intro e he
  obtain ⟨a, ha, b, hb, hc | hp⟩ := h e he
  · have hab := hc.1
    have he2 : #e = 2 := (Complex3.mem_edges.mp he).choose_spec.2.2
    have : e = {a, b} := (eq_of_subset_of_card_le (by simp [insert_subset_iff, ha, hb])
      (by rw [he2, card_pair hab])).symm
    exact ⟨a, b, _, _, this, Or.inl (IsCycleLink.of_check hc)⟩
  · have hab := hp.1
    have he2 : #e = 2 := (Complex3.mem_edges.mp he).choose_spec.2.2
    have : e = {a, b} := (eq_of_subset_of_card_le (by simp [insert_subset_iff, ha, hb])
      (by rw [he2, card_pair hab])).symm
    exact ⟨a, b, _, _, this, Or.inr (IsPathLink.of_check hp)⟩

/-! ### Candidate link lists for vertices `Fin n`

The candidates are computed by structural recursion only, so that the kernel can evaluate them in
`decide`; their correctness is never assumed, since `isEdgeManifold_of_check` verifies them. -/

/-- The vertices of the link of the edge `{a, b}`, in increasing order. -/
def finLinkVerts {n : ℕ} (K : Complex3 (Fin n)) (a b : Fin n) : List (Fin n) :=
  (List.finRange n).filter fun x => decide (x ≠ a ∧ x ≠ b ∧ ∃ t ∈ K.tets, ({a, b, x} : Finset (Fin n)) ⊆ t)

/-- The neighbours of `x` in the link of the edge `{a, b}`: the `y` with `{a, b, x, y}` a
tetrahedron. -/
def finLinkNbrs {n : ℕ} (K : Complex3 (Fin n)) (a b x : Fin n) : List (Fin n) :=
  (List.finRange n).filter fun y =>
    decide (y ≠ x ∧ y ≠ a ∧ y ≠ b ∧ ({a, b, x, y} : Finset (Fin n)) ∈ K.tets)

/-- Walk along the link of the edge `{a, b}` for at most `k` steps, always to the first
neighbour not visited yet; `acc` holds the visited vertices, most recent first. -/
def finWalk {n : ℕ} (K : Complex3 (Fin n)) (a b : Fin n) : ℕ → Fin n → List (Fin n) → List (Fin n)
  | 0, _, acc => acc.reverse
  | k + 1, x, acc =>
    match (finLinkNbrs K a b x).find? (fun y => decide (y ∉ acc)) with
    | some y => finWalk K a b k y (y :: acc)
    | none => acc.reverse

/-- The candidate link list of the edge `{a, b}`: the walk from an end of the link if it has one
(a path), otherwise from its first vertex (a cycle). -/
def finLinkWitness {n : ℕ} (K : Complex3 (Fin n)) (a b : Fin n) : List (Fin n) :=
  match (finLinkVerts K a b).find? (fun x => decide ((finLinkNbrs K a b x).length = 1)) with
  | some x => finWalk K a b n x [x]
  | none =>
    match (finLinkVerts K a b).head? with
    | some x => finWalk K a b n x [x]
    | none => []

end Lightlike.Regge
