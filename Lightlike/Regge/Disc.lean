import Lightlike.Regge.CombManifold
import Lightlike.PonzanoRegge.SphereRecognition
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Combinatorial 3-manifolds with boundary

In a combinatorial 3-manifold with boundary the link of an interior vertex is a 2-sphere and the
link of a boundary vertex is a 2-disc. The core library has the spheres (`Lightlike.PR.IsSphere2`: reached
from the boundary of a tetrahedron by bistellar moves) and the closed manifolds
(`Lightlike.PR.IsCombManifold`). This file adds the discs and the manifolds with boundary, in the same
framework, and shows that they satisfy the edge condition of Regge calculus.

A disc is defined through its **cone completion**: glue the cone from a new vertex onto the
boundary circle. A 2-complex `L` with a nonempty boundary is a disc when its cone completion is a
combinatorial 2-sphere. (A PL disc becomes a sphere this way, and conversely a sphere minus the
open star of a vertex is a disc.) The new vertex is `none : Option V`; the old vertices are
`some x`.

## Main results

* `bdryEdges2 L`: the edges of `L` lying in exactly one triangle.
* `coneComplete L`: the triangles of `L` together with the triangles `{none, x, y}` over the
  boundary edges `{x, y}`.
* `IsDisc2 L`: the boundary is nonempty and the cone completion is a combinatorial 2-sphere.
* `IsCombManifoldBd K`: every vertex link of `K` is a combinatorial 2-sphere or a 2-disc.
* `IsSurfaceDisc L`: the intrinsic conditions of a triangulated disc.

* `exists_rotate`: a cycle can be started at any of its vertices.
* `exists_edgeLink_of_coneComplete`: if the link of the vertex `a` has a sphere as cone completion,
  every edge `ab` has a cycle link or a path link.
* `IsCombManifoldBd.isEdgeManifold`: every combinatorial 3-manifold with boundary is an
  edge-manifold. Closed ones are included (`IsCombManifold.isCombManifoldBd`).
* `isDisc2_iff_isSurfaceDisc` (**recognition of discs**): `L` is a combinatorial 2-disc exactly when
  it is a triangulated disc in the intrinsic sense (`IsSurfaceDisc`): triangles, every edge in at
  most two of them, connected vertex links, connected, the boundary a single circle, Euler
  characteristic `1`. Through `euler2_coneComplete` (coning off the boundary adds `1` to the Euler
  characteristic) and the core's recognition of spheres (`Lightlike.PR.isSphere2_iff_isSurfaceSphere`).
  Without connected vertex links a disc with a pinch point would pass
  (`Lightlike/Regge/Tests.lean`).
* `isCombManifoldBd_of_check`: a decision procedure (`manifoldBdCheck`, from `sphereCheck`,
  `discCheck` and the reachability check `connCheck`), proven sound, for examples.
-/

open Finset

namespace Lightlike.Regge

open Lightlike.PR (Complex3 IsSurfaceSphere IsSphere2 IsConnEdges IsConnected2 IsLinkConn IsClosed2 lk2
  verts2 edges2 euler2 mem_verts2 mem_edges2 mem_lk2)

variable {V : Type*} [DecidableEq V]

/-! ## Boundary edges and the cone completion -/

/-- The **boundary edges** of a 2-complex `L`, given by its triangles: the edges lying in exactly
one triangle. -/
def bdryEdges2 (L : Finset (Finset V)) : Finset (Finset V) :=
  (edges2 L).filter fun f => #(L.filter (f ⊆ ·)) = 1

/-- A set of vertices of `V` as a set of vertices of `Option V` (the old vertices `some x`). -/
def liftOpt (s : Finset V) : Finset (Option V) := s.map Function.Embedding.some

/-- The **cone completion** of `L`: the triangles of `L` together with the cone, from the new vertex
`none`, on the boundary edges of `L`. -/
def coneComplete (L : Finset (Finset V)) : Finset (Finset (Option V)) :=
  L.image liftOpt ∪ (bdryEdges2 L).image fun f => insert none (liftOpt f)

/-- `L` is a **combinatorial 2-disc**: it has a boundary edge, and its cone completion is a
combinatorial 2-sphere. -/
def IsDisc2 (L : Finset (Finset V)) : Prop := (bdryEdges2 L).Nonempty ∧ IsSphere2 (coneComplete L)

/-- `K` is a **combinatorial 3-manifold with boundary**: the link of every vertex is a combinatorial
2-sphere (interior vertex) or a combinatorial 2-disc (boundary vertex). -/
def IsCombManifoldBd (K : Complex3 V) : Prop :=
  ∀ v ∈ K.verts, IsSphere2 (K.link v) ∨ IsDisc2 (K.link v)

lemma mem_bdryEdges2 {L : Finset (Finset V)} {f : Finset V} :
    f ∈ bdryEdges2 L ↔ f ∈ edges2 L ∧ #(L.filter (f ⊆ ·)) = 1 := mem_filter

omit [DecidableEq V] in
lemma none_notMem_liftOpt (s : Finset V) : none ∉ liftOpt s := by simp [liftOpt]

omit [DecidableEq V] in
lemma some_mem_liftOpt {x : V} {s : Finset V} : some x ∈ liftOpt s ↔ x ∈ s := by simp [liftOpt]

omit [DecidableEq V] in
lemma liftOpt_injective : Function.Injective (liftOpt (V := V)) := map_injective _

lemma liftOpt_insert (x : V) (s : Finset V) : liftOpt (insert x s) = insert (some x) (liftOpt s) :=
  by simp [liftOpt, map_insert]

lemma liftOpt_pair (x y : V) : liftOpt ({x, y} : Finset V) = {some x, some y} := by
  simp [liftOpt]

omit [DecidableEq V] in
lemma card_liftOpt (s : Finset V) : #(liftOpt s) = #s := card_map _

omit [DecidableEq V] in
lemma liftOpt_subset_liftOpt {s t : Finset V} : liftOpt s ⊆ liftOpt t ↔ s ⊆ t := map_subset_map

lemma liftOpt_mem_coneComplete {L : Finset (Finset V)} {s : Finset V} :
    liftOpt s ∈ coneComplete L ↔ s ∈ L := by
  simp only [coneComplete, mem_union, mem_image]
  constructor
  · rintro (⟨t, ht, h⟩ | ⟨f, -, h⟩)
    · rwa [← liftOpt_injective h]
    · exact absurd (h ▸ mem_insert_self none _) (none_notMem_liftOpt s)
  · intro h
    exact Or.inl ⟨s, h, rfl⟩

lemma insert_none_inj {s t : Finset V} (h : insert none (liftOpt s) = insert none (liftOpt t)) :
    s = t := by
  apply liftOpt_injective
  have := congrArg (·.erase none) h
  simpa only [erase_insert (none_notMem_liftOpt _)] using this

lemma insert_none_mem_coneComplete {L : Finset (Finset V)} {f : Finset V} :
    insert none (liftOpt f) ∈ coneComplete L ↔ f ∈ bdryEdges2 L := by
  simp only [coneComplete, mem_union, mem_image]
  constructor
  · rintro (⟨t, -, h⟩ | ⟨g, hg, h⟩)
    · exact absurd (h ▸ mem_insert_self none _) (none_notMem_liftOpt t)
    · rwa [← insert_none_inj h]
  · intro h
    exact Or.inr ⟨f, h, rfl⟩

lemma mem_coneComplete {L : Finset (Finset V)} {T : Finset (Option V)} :
    T ∈ coneComplete L ↔
      (∃ τ ∈ L, T = liftOpt τ) ∨ ∃ f ∈ bdryEdges2 L, T = insert none (liftOpt f) := by
  simp only [coneComplete, mem_union, mem_image]
  constructor
  · rintro (⟨τ, hτ, rfl⟩ | ⟨f, hf, rfl⟩)
    · exact Or.inl ⟨τ, hτ, rfl⟩
    · exact Or.inr ⟨f, hf, rfl⟩
  · rintro (⟨τ, hτ, rfl⟩ | ⟨f, hf, rfl⟩)
    · exact Or.inl ⟨τ, hτ, rfl⟩
    · exact Or.inr ⟨f, hf, rfl⟩

/-- The old vertices of the cone completion are the vertices of `L`. -/
lemma some_mem_verts2_coneComplete {L : Finset (Finset V)} {x : V} :
    some x ∈ verts2 (coneComplete L) ↔ x ∈ verts2 L := by
  simp only [mem_verts2, mem_coneComplete]
  constructor
  · rintro ⟨T, ⟨τ, hτ, rfl⟩ | ⟨f, hf, rfl⟩, hx⟩
    · exact ⟨τ, hτ, some_mem_liftOpt.mp hx⟩
    · obtain ⟨τ, hτ, hfτ, -⟩ := mem_edges2.mp (mem_bdryEdges2.mp hf).1
      rw [mem_insert, some_mem_liftOpt] at hx
      exact ⟨τ, hτ, hfτ (hx.resolve_left (Option.some_ne_none x))⟩
  · rintro ⟨τ, hτ, hx⟩
    exact ⟨_, Or.inl ⟨τ, hτ, rfl⟩, some_mem_liftOpt.mpr hx⟩

/-- In the cone completion, the link of an old vertex `b` contains the link of `b` in `L`. -/
lemma liftOpt_mem_lk2_coneComplete {L : Finset (Finset V)} {b : V} {e : Finset V} :
    liftOpt e ∈ lk2 (coneComplete L) (some b) ↔ e ∈ lk2 L b := by
  rw [mem_lk2, mem_lk2, ← liftOpt_insert, liftOpt_mem_coneComplete, some_mem_liftOpt]

/-- The link of the cone vertex is the boundary of `L`. -/
theorem lk2_coneComplete_none (L : Finset (Finset V)) :
    lk2 (coneComplete L) none = (bdryEdges2 L).image liftOpt := by
  ext e
  rw [mem_lk2, mem_image]
  constructor
  · rintro ⟨hn, he⟩
    rcases mem_coneComplete.mp he with ⟨τ, -, h⟩ | ⟨f, hf, h⟩
    · exact absurd (h ▸ mem_insert_self none e) (none_notMem_liftOpt τ)
    · refine ⟨f, hf, ?_⟩
      have := congrArg (·.erase none) h
      simpa only [erase_insert hn, erase_insert (none_notMem_liftOpt _)] using this.symm
  · rintro ⟨f, hf, rfl⟩
    exact ⟨none_notMem_liftOpt f, insert_none_mem_coneComplete.mpr hf⟩

/-- A disc is not closed: no combinatorial 2-sphere is a combinatorial 2-disc. -/
theorem IsDisc2.not_isSphere2 {L : Finset (Finset V)} (hD : IsDisc2 L) : ¬ IsSphere2 L := by
  intro hS
  obtain ⟨f, hf⟩ := hD.1
  obtain ⟨hfe, h1⟩ := mem_bdryEdges2.mp hf
  rw [hS.isSurfaceSphere.closed f hfe] at h1
  exact absurd h1 (by norm_num)

/-! ## Rotating a cycle -/

/-- **A cycle can be started at any vertex.** If `w 0, …, w (n-1)`, `w n = w 0` is a cycle with
edges `{w i, w (i+1)}`, then so is `w k, w (k+1), …`, with the same edges. -/
theorem exists_rotate {W : Type*} [DecidableEq W] {n k : ℕ} {w : ℕ → W} (hk : k < n)
    (hinj : Set.InjOn w (range n)) (hcl : w n = w 0) :
    ∃ u : ℕ → W, Set.InjOn u (range n) ∧ u n = u 0 ∧ u 0 = w k ∧ (∀ i, ∃ j, u i = w j) ∧
      (range n).image (fun i => ({u i, u (i + 1)} : Finset W)) =
        (range n).image fun i => ({w i, w (i + 1)} : Finset W) := by
  let r : ℕ → ℕ := fun i => if i + k < n then i + k else i + k - n
  have hr : ∀ i < n, r i < n := fun i hi => by simp only [r]; split_ifs <;> omega
  have hrinj : ∀ i < n, ∀ j < n, r i = r j → i = j := fun i hi j hj h => by
    simp only [r] at h; split_ifs at h <;> omega
  have hsucc : ∀ i < n, w (r (i + 1)) = w (r i + 1) := by
    intro i hi
    simp only [r]
    by_cases h1 : i + 1 + k < n
    · rw [ite_eq_left h1, ite_eq_left (by omega), show i + 1 + k = i + k + 1 by omega]
    · by_cases h2 : i + k < n
      · rw [ite_eq_right h1, ite_eq_left h2, show i + 1 + k - n = 0 by omega, show i + k + 1 = n by omega,
          hcl]
      · rw [ite_eq_right h1, ite_eq_right h2, show i + 1 + k - n = i + k - n + 1 by omega]
  refine ⟨fun i => w (r i), ?_, ?_, ?_, fun i => ⟨r i, rfl⟩, ?_⟩
  · intro i hi j hj h
    simp only [coe_range, Set.mem_Iio] at hi hj
    exact hrinj i hi j hj (hinj (by simp [hr i hi]) (by simp [hr j hj]) h)
  · simp only [r]
    rw [ite_eq_right (by omega), ite_eq_left (by omega), show n + k - n = 0 + k by omega]
  · simp only [r]
    rw [ite_eq_left (by omega), zero_add]
  · have himg : (range n).image r = range n := by
      refine eq_of_subset_of_card_le (fun x hx => ?_) ?_
      · obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
        exact mem_range.mpr (hr i (mem_range.mp hi))
      · rw [card_image_of_injOn fun i hi j hj h => hrinj i (mem_range.mp hi) j (mem_range.mp hj) h]
    calc (range n).image (fun i => ({w (r i), w (r (i + 1))} : Finset W))
        = (range n).image ((fun j => ({w j, w (j + 1)} : Finset W)) ∘ r) :=
          image_congr fun i hi => by simp only [Function.comp, hsucc i (mem_range.mp hi)]
      _ = _ := by rw [← image_image, himg]

/-! ## Edge links in a manifold with boundary -/

omit [DecidableEq V] in
lemma eq_some_getD {o : Option V} (h : o ≠ none) (d : V) : o = some (o.getD d) := by
  cases o with
  | none => exact absurd rfl h
  | some x => rfl

/-- **From a cycle in the cone completion to the link in `L`.** If the link of `b` in the cone
completion is the cycle `u`, and the consecutive vertices `u s, …, u (m+s)` are old vertices
`some (v 0), …, some (v m)` that carry all edges of the cycle avoiding the cone vertex, then the link
of `b` in `L` consists of the edges `{v i, v (i+1)}`, `i < m`. -/
theorem lk2_eq_of_coneComplete {L : Finset (Finset V)} {b : V} {N m s : ℕ} {u : ℕ → Option V}
    {v : ℕ → V}
    (hG : lk2 (coneComplete L) (some b) = (range N).image fun i => ({u i, u (i + 1)} : Finset _))
    (hv : ∀ i ≤ m, u (i + s) = some (v i)) (hmN : m + s ≤ N)
    (hout : ∀ i < N, none ∉ ({u i, u (i + 1)} : Finset (Option V)) → s ≤ i ∧ i < m + s) :
    lk2 L b = (range m).image fun i => ({v i, v (i + 1)} : Finset V) := by
  ext e
  constructor
  · intro he
    have h1 := liftOpt_mem_lk2_coneComplete.mpr he
    rw [hG, mem_image] at h1
    obtain ⟨i, hi, hi'⟩ := h1
    rw [mem_range] at hi
    have hn : none ∉ ({u i, u (i + 1)} : Finset (Option V)) := hi' ▸ none_notMem_liftOpt e
    obtain ⟨hsi, him⟩ := hout i hi hn
    refine mem_image.mpr ⟨i - s, mem_range.mpr (by omega), liftOpt_injective ?_⟩
    rw [liftOpt_pair, ← hi', ← hv (i - s) (by omega), ← hv (i - s + 1) (by omega),
      show i - s + s = i by omega, show i - s + 1 + s = i + 1 by omega]
  · intro he
    obtain ⟨j, hj, rfl⟩ := mem_image.mp he
    rw [mem_range] at hj
    rw [← liftOpt_mem_lk2_coneComplete, hG, liftOpt_pair, ← hv j (by omega),
      ← hv (j + 1) (by omega)]
    exact mem_image.mpr ⟨j + s, mem_range.mpr (by omega), by rw [show j + 1 + s = j + s + 1 by omega]⟩

/-- **Vertex links when the cone completion is a sphere.** If the cone completion of `L` is a
triangulated 2-sphere, the link of a vertex `b` of `L` is a cycle or a path. The link of `b` in
the cone completion is a cycle `u`; either it avoids the cone vertex, and then it is the link of `b`
in `L`, or it can be started at the cone vertex, and then the rest of it, `u 1, …, u (n-1)`, is the
link of `b` in `L`. The old vertices are read off with `Option.getD d`. -/
theorem lk2_cycle_or_path_of_coneComplete {L : Finset (Finset V)}
    (hS : IsSurfaceSphere (coneComplete L)) {b : V} (hb : b ∈ verts2 L) (d : V) :
    ∃ (n : ℕ) (u : ℕ → Option V), 3 ≤ n ∧ Set.InjOn u (range n) ∧ u n = u 0 ∧
      (∀ i, u i ∈ verts2 (lk2 (coneComplete L) (some b))) ∧
      (((∀ i ≤ n, u i = some ((u i).getD d)) ∧
          lk2 L b = (range n).image fun i => ({(u i).getD d, (u (i + 1)).getD d} : Finset V)) ∨
        (u 0 = none ∧ (∀ i ≤ n - 2, u (i + 1) = some ((u (i + 1)).getD d)) ∧
          lk2 L b = (range (n - 2)).image fun i =>
            ({(u (i + 1)).getD d, (u (i + 1 + 1)).getD d} : Finset V))) := by
  obtain ⟨n, w, h3, hinj, hcl, hw, hG⟩ :=
    lk2_cycle_of_isSurfaceSphere hS (some_mem_verts2_coneComplete.mpr hb)
  by_cases hnone : ∃ k < n, w k = none
  · -- the cycle passes through the cone vertex: start it there; the rest is a path
    obtain ⟨k, hk, hwk⟩ := hnone
    obtain ⟨u, uinj, ucl, u0, uw, uG⟩ := exists_rotate hk hinj hcl
    rw [← uG] at hG
    have hu : ∀ i, 1 ≤ i → i < n → u i ≠ none := by
      intro i h1 h2 h
      have := uinj (by simp; omega) (by simp; omega) (h.trans (u0.trans hwk).symm)
      omega
    have hv : ∀ i ≤ n - 2, u (i + 1) = some ((u (i + 1)).getD d) := fun i hi =>
      eq_some_getD (hu (i + 1) (by omega) (by omega)) d
    refine ⟨n, u, h3, uinj, ucl, fun i => ?_, Or.inr ⟨u0.trans hwk, hv, ?_⟩⟩
    · obtain ⟨j, hj⟩ := uw i
      rw [hj]
      exact hw j
    · refine lk2_eq_of_coneComplete (s := 1) hG hv (by omega) fun i hi hn => ?_
      have hn0 : none = u 0 := (u0.trans hwk).symm
      constructor
      · by_contra h0
        exact hn (by rw [show i = 0 by omega, ← hn0]; simp)
      · by_contra h1
        exact hn (by rw [show i + 1 = n by omega, ucl, ← hn0]; simp)
  · -- the cycle avoids the cone vertex: it is the link of `b` in `L`
    have hne : ∀ i < n, w i ≠ none := fun i hi h => hnone ⟨i, hi, h⟩
    have hv : ∀ i ≤ n, w i = some ((w i).getD d) := by
      intro i hi
      rcases Nat.lt_or_ge i n with h | h
      · exact eq_some_getD (hne i h) d
      · rw [show i = n by omega, hcl]
        exact eq_some_getD (hne 0 (by omega)) d
    have hv0 : ∀ i ≤ n, w (i + 0) = some ((w i).getD d) := fun i hi => by
      rw [add_zero]
      exact hv i hi
    exact ⟨n, w, h3, hinj, hcl, hw, Or.inl ⟨hv, lk2_eq_of_coneComplete (s := 0) hG hv0 (by omega)
      fun i hi _ => ⟨by omega, by omega⟩⟩⟩

/-- **Edge links from a sphere cone completion.** If the cone completion of the link of the vertex
`a` is a combinatorial 2-sphere, every edge `ab` has a cycle link or a path link (a path when the
link of `b` in the cone completion passes through the cone vertex). -/
theorem exists_edgeLink_of_coneComplete {K : Complex3 V} {a b : V} (hab : a ≠ b)
    (he : ({a, b} : Finset V) ∈ K.edges) (hD : IsSphere2 (coneComplete (K.link a))) :
    ∃ n w, IsCycleLink K a b n w ∨ IsPathLink K a b n w := by
  obtain ⟨t, ht, hsub, -⟩ := Complex3.mem_edges.mp he
  have hat : a ∈ t := hsub (by simp)
  have hbt : b ∈ t := hsub (by simp)
  have htl : t.erase a ∈ K.link a :=
    Lightlike.PR.Complex3.mem_link.mpr ⟨notMem_erase a t, by rwa [insert_erase hat]⟩
  have hb : b ∈ verts2 (K.link a) := mem_verts2.mpr ⟨_, htl, mem_erase.mpr ⟨hab.symm, hbt⟩⟩
  obtain ⟨n, u, h3, uinj, ucl, hw, hcase⟩ :=
    lk2_cycle_or_path_of_coneComplete hD.isSurfaceSphere hb a
  have huv : ∀ i (x : V), u i = some x → x ≠ a ∧ x ≠ b := by
    intro i x hx
    obtain ⟨f, hf, hwf⟩ := mem_verts2.mp (hw i)
    obtain ⟨hbf, hins⟩ := mem_lk2.mp hf
    rw [hx] at hwf
    have hxv : x ∈ verts2 (K.link a) :=
      some_mem_verts2_coneComplete.mp (mem_verts2.mpr ⟨_, hins, mem_insert_of_mem hwf⟩)
    obtain ⟨τ, hτ, hxτ⟩ := mem_verts2.mp hxv
    exact ⟨fun h => (Lightlike.PR.Complex3.mem_link.mp hτ).1 (h ▸ hxτ), fun h => hbf (h ▸ hwf)⟩
  rcases hcase with ⟨hv, hG⟩ | ⟨-, hv, hG⟩
  · refine ⟨n, fun i => (u i).getD a, Or.inl ⟨hab, h3, fun i hi => (huv _ _ (hv i hi.le)).1,
      fun i hi => (huv _ _ (hv i hi.le)).2, ?_, by simp only [ucl], star_eq_of_lk2 hab hG⟩⟩
    intro i hi j hj h
    simp only [coe_range, Set.mem_Iio] at hi hj
    exact uinj (by simp [hi]) (by simp [hj])
      ((hv i hi.le).trans ((congrArg some h).trans (hv j hj.le).symm))
  · refine ⟨n - 2, fun i => (u (i + 1)).getD a, Or.inr ⟨hab, by omega, fun i hi =>
      (huv _ _ (hv i hi)).1, fun i hi => (huv _ _ (hv i hi)).2, ?_, star_eq_of_lk2 hab hG⟩⟩
    intro i hi j hj h
    simp only [coe_range, Set.mem_Iio] at hi hj
    have := uinj (by simp; omega) (by simp; omega)
      ((hv i (by omega)).trans ((congrArg some h).trans (hv j (by omega)).symm))
    omega

/-- **Every combinatorial 3-manifold with boundary is an edge-manifold**: in a complex whose vertex
links are combinatorial 2-spheres or 2-discs, every edge has a cycle link or a path link. -/
theorem IsCombManifoldBd.isEdgeManifold {K : Complex3 V} (h : IsCombManifoldBd K) :
    IsEdgeManifold K := by
  intro e he
  obtain ⟨t, ht, hsub, he2⟩ := Complex3.mem_edges.mp he
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp he2
  have ha : a ∈ K.verts := mem_biUnion.mpr ⟨t, ht, hsub (by simp)⟩
  rcases h a ha with hS | hD
  · obtain ⟨n, w, hc⟩ := isCycleLink_of_isSurfaceSphere hab he hS.isSurfaceSphere
    exact ⟨a, b, n, w, rfl, Or.inl hc⟩
  · obtain ⟨n, w, hc⟩ := exists_edgeLink_of_coneComplete hab he hD.2
    exact ⟨a, b, n, w, rfl, hc⟩

/-- Closed combinatorial 3-manifolds are combinatorial 3-manifolds with boundary (with empty
boundary). -/
theorem IsCombManifold.isCombManifoldBd {K : Complex3 V} (h : Lightlike.PR.IsCombManifold K) :
    IsCombManifoldBd K :=
  fun v hv => Or.inl (h v hv)

/-! ## Paths of edges -/

/-- Reachability along an edge set is symmetric. -/
lemma reach_symm {W : Type*} [DecidableEq W] {S : Finset (Finset W)} {p q : W}
    (h : Relation.ReflTransGen (fun x y => ({x, y} : Finset W) ∈ S) p q) :
    Relation.ReflTransGen (fun x y => ({x, y} : Finset W) ∈ S) q p :=
  Relation.ReflTransGen.mono (fun x y hxy => by simpa only [Function.swap, pair_comm] using hxy) _ _
    (Relation.ReflTransGen.swap _ _ h)

/-- **Connectivity through a hub**: if every vertex of `N` reaches `c`, any two vertices of `N` are
joined by a path of edges. -/
lemma reach_of_hub {W : Type*} [DecidableEq W] {S : Finset (Finset W)} {N : Finset W} (c : W)
    (h : ∀ p ∈ N, Relation.ReflTransGen (fun x y => ({x, y} : Finset W) ∈ S) p c) :
    ∀ u ∈ N, ∀ w ∈ N, Relation.ReflTransGen (fun x y => ({x, y} : Finset W) ∈ S) u w :=
  fun u hu w hw => (h u hu).trans (reach_symm (h w hw))

/-- The edges `{v i, v (i+1)}`, `i < m`, of a path form a connected set. -/
lemma isConnEdges_image_pairs {W : Type*} [DecidableEq W] (v : ℕ → W) (m : ℕ) :
    IsConnEdges ((range m).image fun i => ({v i, v (i + 1)} : Finset W)) := by
  have h0 : ∀ j ≤ m, Relation.ReflTransGen
      (fun x y => ({x, y} : Finset W) ∈ (range m).image fun i => ({v i, v (i + 1)} : Finset W))
      (v j) (v 0) := by
    intro j hj
    induction j with
    | zero => exact .refl
    | succ j ih =>
      refine Relation.ReflTransGen.head ?_ (ih (by omega))
      rw [pair_comm]
      exact mem_image.mpr ⟨j, mem_range.mpr (by omega), rfl⟩
  refine reach_of_hub (v 0) fun p hp => ?_
  obtain ⟨e, he, hpe⟩ := mem_verts2.mp hp
  obtain ⟨i, hi, rfl⟩ := mem_image.mp he
  rw [mem_range] at hi
  rw [mem_insert, mem_singleton] at hpe
  rcases hpe with rfl | rfl
  · exact h0 i (by omega)
  · exact h0 (i + 1) (by omega)

omit [DecidableEq V] in
lemma mem_liftOpt {z : Option V} {s : Finset V} : z ∈ liftOpt s ↔ ∃ x ∈ s, some x = z := by
  simp [liftOpt]

/-- A connected edge set stays connected under `liftOpt`. -/
lemma isConnEdges_image_liftOpt {S : Finset (Finset V)} (h : IsConnEdges S) :
    IsConnEdges (S.image liftOpt) := by
  have hv : ∀ p ∈ verts2 (S.image liftOpt), ∃ y ∈ verts2 S, p = some y := by
    intro p hp
    obtain ⟨e, he, hpe⟩ := mem_verts2.mp hp
    obtain ⟨f, hf, rfl⟩ := mem_image.mp he
    obtain ⟨y, hy, rfl⟩ := mem_liftOpt.mp hpe
    exact ⟨y, mem_verts2.mpr ⟨f, hf, hy⟩, rfl⟩
  intro p hp q hq
  obtain ⟨y, hy, rfl⟩ := hv p hp
  obtain ⟨y', hy', rfl⟩ := hv q hq
  exact (h y hy y' hy').lift some fun a b hab => mem_image.mpr ⟨{a, b}, hab, liftOpt_pair a b⟩

/-- Conversely, an edge set is connected if its image under `liftOpt` is. -/
lemma isConnEdges_of_image_liftOpt {S : Finset (Finset V)} (h : IsConnEdges (S.image liftOpt)) :
    IsConnEdges S := by
  have hv : ∀ y ∈ verts2 S, some y ∈ verts2 (S.image liftOpt) := fun y hy => by
    obtain ⟨e, he, hye⟩ := mem_verts2.mp hy
    exact mem_verts2.mpr ⟨_, mem_image_of_mem _ he, some_mem_liftOpt.mpr hye⟩
  intro u hu w hw
  have key : ∀ z, Relation.ReflTransGen (fun x y => ({x, y} : Finset (Option V)) ∈ S.image liftOpt)
      (some u) z → ∀ y, z = some y →
        Relation.ReflTransGen (fun x y => ({x, y} : Finset V) ∈ S) u y := by
    intro z hz
    induction hz with
    | refl =>
      intro y hy
      cases Option.some_inj.mp hy
      exact .refl
    | @tail b c _ hbc ih =>
      intro y hy
      subst hy
      obtain ⟨e, he, hee⟩ := mem_image.mp hbc
      obtain ⟨b', -, rfl⟩ := mem_liftOpt.mp (hee ▸ mem_insert_self b {some y})
      have : e = {b', y} := liftOpt_injective (by rw [hee, liftOpt_pair])
      exact (ih b' rfl).tail (this ▸ he)
  exact key _ (h _ (hv u hu) _ (hv w hw)) w rfl

/-! ## Counting in the cone completion -/

lemma card_of_mem_bdryEdges2 {L : Finset (Finset V)} {f : Finset V} (hf : f ∈ bdryEdges2 L) :
    #f = 2 := by
  obtain ⟨τ, -, -, h⟩ := mem_edges2.mp (mem_bdryEdges2.mp hf).1
  exact h

/-- The cone vertex is a vertex of the cone completion exactly when `L` has a boundary edge. -/
lemma none_mem_verts2_coneComplete {L : Finset (Finset V)} :
    none ∈ verts2 (coneComplete L) ↔ (bdryEdges2 L).Nonempty := by
  constructor
  · intro h
    obtain ⟨T, hT, hn⟩ := mem_verts2.mp h
    rcases mem_coneComplete.mp hT with ⟨τ, -, rfl⟩ | ⟨f, hf, -⟩
    · exact absurd hn (none_notMem_liftOpt τ)
    · exact ⟨f, hf⟩
  · rintro ⟨f, hf⟩
    exact mem_verts2.mpr ⟨_, insert_none_mem_coneComplete.mpr hf, mem_insert_self _ _⟩

omit [DecidableEq V] in
lemma subset_liftOpt_iff {f : Finset (Option V)} {t : Finset V} :
    f ⊆ liftOpt t ↔ ∃ g ⊆ t, f = liftOpt g := subset_map_iff

/-- **The edges of the cone completion**: the edges of `L`, and the edges `{none, x}` from the cone
vertex to the boundary vertices. -/
lemma mem_edges2_coneComplete {L : Finset (Finset V)} {f : Finset (Option V)} :
    f ∈ edges2 (coneComplete L) ↔
      (∃ g ∈ edges2 L, f = liftOpt g) ∨ ∃ x ∈ verts2 (bdryEdges2 L), f = {none, some x} := by
  constructor
  · intro hf
    obtain ⟨T, hT, hfT, hf2⟩ := mem_edges2.mp hf
    by_cases hn : none ∈ f
    · right
      rcases mem_coneComplete.mp hT with ⟨τ, -, rfl⟩ | ⟨e, he, rfl⟩
      · exact absurd (hfT hn) (none_notMem_liftOpt τ)
      · obtain ⟨p, hp⟩ := card_eq_one.mp (by rw [card_erase_of_mem hn, hf2] : #(f.erase none) = 1)
        have hpf : p ∈ f.erase none := hp ▸ mem_singleton_self p
        obtain ⟨hpn, hpf'⟩ := mem_erase.mp hpf
        obtain ⟨x, rfl⟩ := Option.ne_none_iff_exists'.mp hpn
        have hx : x ∈ e := by
          have := hfT hpf'
          rw [mem_insert, some_mem_liftOpt] at this
          exact this.resolve_left (Option.some_ne_none x)
        refine ⟨x, mem_verts2.mpr ⟨e, he, hx⟩, ?_⟩
        rw [← insert_erase hn, hp]
    · left
      obtain ⟨τ', ⟨τ, hτ, hτ'τ⟩, hfτ'⟩ : ∃ τ', (∃ τ ∈ L, τ' ⊆ τ) ∧ f ⊆ liftOpt τ' := by
        rcases mem_coneComplete.mp hT with ⟨τ, hτ, rfl⟩ | ⟨e, he, rfl⟩
        · exact ⟨τ, ⟨τ, hτ, subset_rfl⟩, hfT⟩
        · obtain ⟨τ, hτ, heτ, -⟩ := mem_edges2.mp (mem_bdryEdges2.mp he).1
          exact ⟨e, ⟨τ, hτ, heτ⟩, (subset_insert_iff_of_notMem hn).mp hfT⟩
      obtain ⟨g, hgτ', rfl⟩ := subset_liftOpt_iff.mp hfτ'
      exact ⟨g, mem_edges2.mpr ⟨τ, hτ, hgτ'.trans hτ'τ, by rwa [card_liftOpt] at hf2⟩, rfl⟩
  · rintro (⟨g, hg, rfl⟩ | ⟨x, hx, rfl⟩)
    · obtain ⟨τ, hτ, hgτ, hg2⟩ := mem_edges2.mp hg
      exact mem_edges2.mpr ⟨_, liftOpt_mem_coneComplete.mpr hτ, liftOpt_subset_liftOpt.mpr hgτ,
        by rw [card_liftOpt, hg2]⟩
    · obtain ⟨e, he, hxe⟩ := mem_verts2.mp hx
      refine mem_edges2.mpr ⟨_, insert_none_mem_coneComplete.mpr he, ?_,
        card_pair (Option.some_ne_none x).symm⟩
      exact insert_subset_insert none (singleton_subset_iff.mpr (some_mem_liftOpt.mpr hxe))

lemma disjoint_coneComplete (L : Finset (Finset V)) :
    Disjoint (L.image liftOpt) ((bdryEdges2 L).image fun f => insert none (liftOpt f)) := by
  rw [disjoint_left]
  intro T hT hT'
  obtain ⟨τ, -, rfl⟩ := mem_image.mp hT
  obtain ⟨f, -, hf⟩ := mem_image.mp hT'
  exact none_notMem_liftOpt τ (hf ▸ mem_insert_self none _)

lemma insert_none_liftOpt_injective :
    Function.Injective fun f : Finset V => insert none (liftOpt f) :=
  fun _ _ h => insert_none_inj h

/-- The triangles of the cone completion on an old edge `g`: those of `L`, and the cone triangle
when `g` is a boundary edge. -/
lemma card_filter_coneComplete_liftOpt (L : Finset (Finset V)) (g : Finset V) :
    #((coneComplete L).filter (liftOpt g ⊆ ·)) =
      #(L.filter (g ⊆ ·)) + #((bdryEdges2 L).filter (g ⊆ ·)) := by
  rw [coneComplete, filter_union,
    card_union_of_disjoint (disjoint_filter_filter (disjoint_coneComplete L)), filter_image,
    filter_image, card_image_of_injective _ liftOpt_injective,
    card_image_of_injective _ insert_none_liftOpt_injective]
  congr 2
  · exact filter_congr fun τ _ => liftOpt_subset_liftOpt
  · exact filter_congr fun f _ => by
      rw [subset_insert_iff_of_notMem (none_notMem_liftOpt g), liftOpt_subset_liftOpt]

/-- The triangles of the cone completion on a cone edge `{none, x}`: one for each boundary edge
at `x`. -/
lemma card_filter_coneComplete_none (L : Finset (Finset V)) (x : V) :
    #((coneComplete L).filter (({none, some x} : Finset (Option V)) ⊆ ·)) =
      #((bdryEdges2 L).filter (x ∈ ·)) := by
  rw [coneComplete, filter_union,
    card_union_of_disjoint (disjoint_filter_filter (disjoint_coneComplete L)), filter_image,
    filter_image, card_image_of_injective _ liftOpt_injective,
    card_image_of_injective _ insert_none_liftOpt_injective]
  have h1 : L.filter (fun τ => ({none, some x} : Finset (Option V)) ⊆ liftOpt τ) = ∅ :=
    filter_eq_empty_iff.mpr fun τ _ h => none_notMem_liftOpt τ (h (mem_insert_self _ _))
  rw [h1, card_empty, zero_add]
  congr 1
  exact filter_congr fun f _ => by simp [insert_subset_iff, some_mem_liftOpt]

lemma card_filter_bdryEdges2_subset {L : Finset (Finset V)} {g : Finset V} (hg : #g = 2) :
    #((bdryEdges2 L).filter (g ⊆ ·)) = if g ∈ bdryEdges2 L then 1 else 0 := by
  have : (bdryEdges2 L).filter (g ⊆ ·) = (bdryEdges2 L).filter (g = ·) :=
    filter_congr fun f hf => ⟨fun h => eq_of_subset_of_card_le h
      (by rw [card_of_mem_bdryEdges2 hf, hg]), fun h => h ▸ subset_rfl⟩
  rw [this, filter_eq]
  split_ifs <;> simp

/-- An edge of `L` lies in exactly two triangles of the cone completion exactly when it lies in at
most two triangles of `L`. -/
lemma card_filter_coneComplete_edge {L : Finset (Finset V)} {g : Finset V} (hg : g ∈ edges2 L) :
    #((coneComplete L).filter (liftOpt g ⊆ ·)) = 2 ↔ #(L.filter (g ⊆ ·)) ≤ 2 := by
  obtain ⟨τ, hτ, hgτ, hg2⟩ := mem_edges2.mp hg
  have hpos : 1 ≤ #(L.filter (g ⊆ ·)) := card_pos.mpr ⟨τ, mem_filter.mpr ⟨hτ, hgτ⟩⟩
  rw [card_filter_coneComplete_liftOpt, card_filter_bdryEdges2_subset hg2]
  by_cases hb : g ∈ bdryEdges2 L
  · rw [ite_eq_left hb, (mem_bdryEdges2.mp hb).2]
    simp
  · rw [ite_eq_right hb]
    have : #(L.filter (g ⊆ ·)) ≠ 1 := fun h => hb (mem_bdryEdges2.mpr ⟨hg, h⟩)
    constructor <;> intro <;> omega

/-- In a finite edge set in which every vertex lies in exactly two edges, there are as many
vertices as edges. -/
lemma card_verts2_of_two_regular {W : Type*} [DecidableEq W] {S : Finset (Finset W)}
    (hcard : ∀ e ∈ S, #e = 2) (hdeg : ∀ x ∈ verts2 S, #(S.filter (x ∈ ·)) = 2) :
    #(verts2 S) = #S := by
  have h := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := verts2 S) (t := S)
    (r := fun x e => x ∈ e)
  simp only [bipartiteAbove, bipartiteBelow] at h
  have h2 : ∀ e ∈ S, #((verts2 S).filter (· ∈ e)) = 2 := fun e he => by
    rw [filter_mem_eq_inter, inter_eq_right.mpr fun y hy => mem_verts2.mpr ⟨e, he, hy⟩,
      hcard e he]
  rw [sum_congr rfl hdeg, sum_congr rfl h2] at h
  simp only [sum_const, smul_eq_mul] at h
  omega

lemma verts2_coneComplete {L : Finset (Finset V)} (hne : (bdryEdges2 L).Nonempty) :
    verts2 (coneComplete L) = insert none ((verts2 L).image some) := by
  ext z
  cases z with
  | none => simp [none_mem_verts2_coneComplete, hne]
  | some x => rw [some_mem_verts2_coneComplete]; simp

lemma edges2_coneComplete (L : Finset (Finset V)) :
    edges2 (coneComplete L) =
      (edges2 L).image liftOpt ∪ (verts2 (bdryEdges2 L)).image fun x => {none, some x} := by
  ext f
  rw [mem_edges2_coneComplete, mem_union, mem_image, mem_image]
  constructor
  · rintro (⟨g, hg, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact Or.inl ⟨g, hg, rfl⟩
    · exact Or.inr ⟨x, hx, rfl⟩
  · rintro (⟨g, hg, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact Or.inl ⟨g, hg, rfl⟩
    · exact Or.inr ⟨x, hx, rfl⟩

/-- **The Euler characteristic of the cone completion**: if every boundary vertex lies in exactly
two boundary edges, coning off the boundary adds `1`. -/
theorem euler2_coneComplete {L : Finset (Finset V)} (hne : (bdryEdges2 L).Nonempty)
    (hdeg : ∀ x ∈ verts2 (bdryEdges2 L), #((bdryEdges2 L).filter (x ∈ ·)) = 2) :
    euler2 (coneComplete L) = euler2 L + 1 := by
  have hV : #(verts2 (coneComplete L)) = #(verts2 L) + 1 := by
    rw [verts2_coneComplete hne, card_insert_of_notMem (by simp),
      card_image_of_injective _ (Option.some_injective _)]
  have hE : #(edges2 (coneComplete L)) = #(edges2 L) + #(verts2 (bdryEdges2 L)) := by
    rw [edges2_coneComplete, card_union_of_disjoint, card_image_of_injective _ liftOpt_injective,
      card_image_of_injective]
    · intro x y h
      have h' : ({none, some x} : Finset (Option V)) = {none, some y} := h
      have : some x ∈ ({none, some y} : Finset (Option V)) := by rw [← h']; simp
      simpa using this
    · rw [disjoint_left]
      intro f hf hf'
      obtain ⟨g, -, rfl⟩ := mem_image.mp hf
      obtain ⟨x, -, hx⟩ := mem_image.mp hf'
      exact none_notMem_liftOpt g (hx ▸ mem_insert_self none _)
  have hF : #(coneComplete L) = #L + #(bdryEdges2 L) := by
    rw [coneComplete, card_union_of_disjoint (disjoint_coneComplete L),
      card_image_of_injective _ liftOpt_injective,
      card_image_of_injective _ insert_none_liftOpt_injective]
  have hB : #(verts2 (bdryEdges2 L)) = #(bdryEdges2 L) :=
    card_verts2_of_two_regular (fun e he => card_of_mem_bdryEdges2 he) hdeg
  unfold euler2
  rw [hV, hE, hF, hB]
  push_cast
  ring

/-! ## Recognising discs -/

/-- A **triangulated disc** in the intrinsic sense: triangles have three vertices; every edge lies
in at most two triangles; the link of every vertex is connected; the 1-skeleton is connected; the
boundary edges (those in one triangle) form a nonempty connected set in which every vertex lies in
exactly two edges, i.e. a single circle; and the Euler characteristic is `1`. -/
structure IsSurfaceDisc (L : Finset (Finset V)) : Prop where
  /-- Triangles have three vertices. -/
  card : ∀ τ ∈ L, #τ = 3
  /-- Every edge lies in at most two triangles. -/
  edge_le : ∀ f ∈ edges2 L, #(L.filter (f ⊆ ·)) ≤ 2
  /-- The link of every vertex is connected. -/
  link : IsLinkConn L
  /-- The 1-skeleton is connected. -/
  connected : IsConnected2 L
  /-- There is a boundary edge. -/
  bdry_nonempty : (bdryEdges2 L).Nonempty
  /-- Every boundary vertex lies in exactly two boundary edges. -/
  bdry_deg : ∀ x ∈ verts2 (bdryEdges2 L), #((bdryEdges2 L).filter (x ∈ ·)) = 2
  /-- The boundary is connected. -/
  bdry_conn : IsConnEdges (bdryEdges2 L)
  /-- The Euler characteristic is `1`. -/
  euler : euler2 L = 1

/-- In the link of an old vertex `x` in the cone completion, the old vertices are those of the link
of `x` in `L`. -/
lemma some_mem_verts2_lk2_coneComplete {L : Finset (Finset V)} {x y : V}
    (h : some y ∈ verts2 (lk2 (coneComplete L) (some x))) : y ∈ verts2 (lk2 L x) := by
  obtain ⟨f, hf, hyf⟩ := mem_verts2.mp h
  obtain ⟨hxf, hins⟩ := mem_lk2.mp hf
  have hxy : x ≠ y := fun h => hxf (h ▸ hyf)
  obtain ⟨τ, hτ, hxτ, hyτ⟩ : ∃ τ ∈ L, x ∈ τ ∧ y ∈ τ := by
    have hxT : some x ∈ insert (some x) f := mem_insert_self _ _
    have hyT : some y ∈ insert (some x) f := mem_insert_of_mem hyf
    rcases mem_coneComplete.mp hins with ⟨τ, hτ, hT⟩ | ⟨e, he, hT⟩
    · rw [hT, some_mem_liftOpt] at hxT hyT
      exact ⟨τ, hτ, hxT, hyT⟩
    · obtain ⟨τ, hτ, heτ, -⟩ := mem_edges2.mp (mem_bdryEdges2.mp he).1
      rw [hT, mem_insert, some_mem_liftOpt] at hxT hyT
      exact ⟨τ, hτ, heτ (hxT.resolve_left (Option.some_ne_none x)),
        heτ (hyT.resolve_left (Option.some_ne_none y))⟩
  exact mem_verts2.mpr ⟨τ.erase x, mem_lk2.mpr ⟨notMem_erase x τ, by rwa [insert_erase hxτ]⟩,
    mem_erase.mpr ⟨hxy.symm, hyτ⟩⟩

lemma card_mem_coneComplete {L : Finset (Finset V)} (hcard : ∀ τ ∈ L, #τ = 3) :
    ∀ T ∈ coneComplete L, #T = 3 := by
  intro T hT
  rcases mem_coneComplete.mp hT with ⟨τ, hτ, rfl⟩ | ⟨f, hf, rfl⟩
  · rw [card_liftOpt, hcard τ hτ]
  · rw [card_insert_of_notMem (none_notMem_liftOpt f), card_liftOpt, card_of_mem_bdryEdges2 hf]

/-- **Intrinsic discs are discs**: coning off the boundary of a triangulated disc gives a
triangulated 2-sphere. -/
theorem IsSurfaceDisc.isSurfaceSphere_coneComplete {L : Finset (Finset V)}
    (hD : IsSurfaceDisc L) : IsSurfaceSphere (coneComplete L) where
  card := card_mem_coneComplete hD.card
  closed := by
    intro f hf
    rcases mem_edges2_coneComplete.mp hf with ⟨g, hg, rfl⟩ | ⟨x, hx, rfl⟩
    · exact (card_filter_coneComplete_edge hg).mpr (hD.edge_le g hg)
    · rw [card_filter_coneComplete_none]
      exact hD.bdry_deg x hx
  link := by
    intro z hz
    cases z with
    | none =>
      rw [lk2_coneComplete_none]
      exact isConnEdges_image_liftOpt hD.bdry_conn
    | some x =>
      have hx := some_mem_verts2_coneComplete.mp hz
      obtain ⟨τ, hτ, hxτ⟩ := mem_verts2.mp hx
      -- a vertex `y₀` of the link of `x` in `L` serves as the hub
      obtain ⟨y₀, hy₀⟩ : (τ.erase x).Nonempty := by
        rw [← card_pos, card_erase_of_mem hxτ, hD.card τ hτ]
        norm_num
      have hy₀L : y₀ ∈ verts2 (lk2 L x) :=
        mem_verts2.mpr ⟨_, mem_lk2.mpr ⟨notMem_erase x τ, by rwa [insert_erase hxτ]⟩, hy₀⟩
      have hlift : ∀ y ∈ verts2 (lk2 L x), Relation.ReflTransGen
          (fun p q => ({p, q} : Finset (Option V)) ∈ lk2 (coneComplete L) (some x))
          (some y) (some y₀) := fun y hy =>
        (hD.link x hx y hy y₀ hy₀L).lift some fun a b hab => by
          show ({some a, some b} : Finset (Option V)) ∈ _
          rw [← liftOpt_pair]
          exact liftOpt_mem_lk2_coneComplete.mpr hab
      refine reach_of_hub (some y₀) fun p hp => ?_
      cases p with
      | some y => exact hlift y (some_mem_verts2_lk2_coneComplete hp)
      | none =>
        obtain ⟨f, hf, hnf⟩ := mem_verts2.mp hp
        obtain ⟨hxf, hins⟩ := mem_lk2.mp hf
        have hf2 : #f = 2 := by
          have := card_mem_coneComplete hD.card _ hins
          rw [card_insert_of_notMem hxf] at this
          omega
        obtain ⟨q, hq⟩ := card_eq_one.mp (by rw [card_erase_of_mem hnf, hf2] : #(f.erase none) = 1)
        have hqf : q ∈ f.erase none := hq ▸ mem_singleton_self q
        obtain ⟨hqn, hqf'⟩ := mem_erase.mp hqf
        obtain ⟨y, rfl⟩ := Option.ne_none_iff_exists'.mp hqn
        have hfe : f = {none, some y} := by
          rw [← insert_erase hnf, hq]
        exact Relation.ReflTransGen.head (hfe ▸ hf)
          (hlift y (some_mem_verts2_lk2_coneComplete (mem_verts2.mpr ⟨f, hf, hqf'⟩)))
  connected := by
    obtain ⟨e₀, he₀⟩ := hD.bdry_nonempty
    obtain ⟨τ₀, hτ₀, he₀τ₀, he₀2⟩ := mem_edges2.mp (mem_bdryEdges2.mp he₀).1
    obtain ⟨x₀, hx₀⟩ : e₀.Nonempty := by
      rw [← card_pos, he₀2]
      norm_num
    have hx₀L : x₀ ∈ verts2 L := mem_verts2.mpr ⟨τ₀, hτ₀, he₀τ₀ hx₀⟩
    refine reach_of_hub (some x₀) fun p hp => ?_
    cases p with
    | some y =>
      exact (hD.connected y (some_mem_verts2_coneComplete.mp hp) x₀ hx₀L).lift some
        fun a b hab => by
          show ({some a, some b} : Finset (Option V)) ∈ _
          rw [← liftOpt_pair]
          exact mem_edges2_coneComplete.mpr (Or.inl ⟨_, hab, rfl⟩)
    | none =>
      exact Relation.ReflTransGen.single
        (mem_edges2_coneComplete.mpr (Or.inr ⟨x₀, mem_verts2.mpr ⟨e₀, he₀, hx₀⟩, rfl⟩))
  euler := by
    rw [euler2_coneComplete hD.bdry_nonempty hD.bdry_deg, hD.euler]
    norm_num

/-- **Discs are intrinsic discs**: if `L` has a boundary edge and its cone completion is a
triangulated 2-sphere, `L` is a triangulated disc. -/
theorem isSurfaceDisc_of_coneComplete {L : Finset (Finset V)}
    (hS : IsSurfaceSphere (coneComplete L)) (hne : (bdryEdges2 L).Nonempty) : IsSurfaceDisc L := by
  have hdeg : ∀ x ∈ verts2 (bdryEdges2 L), #((bdryEdges2 L).filter (x ∈ ·)) = 2 := fun x hx => by
    rw [← card_filter_coneComplete_none]
    exact hS.closed _ (mem_edges2_coneComplete.mpr (Or.inr ⟨x, hx, rfl⟩))
  have hbconn : IsConnEdges (bdryEdges2 L) := by
    have := hS.link none (none_mem_verts2_coneComplete.mpr hne)
    rw [lk2_coneComplete_none] at this
    exact isConnEdges_of_image_liftOpt this
  refine ⟨fun τ hτ => ?_, fun g hg => ?_, fun x hx => ?_, ?_, hne, hdeg, hbconn, ?_⟩
  · have := hS.card _ (liftOpt_mem_coneComplete.mpr hτ)
    rwa [card_liftOpt] at this
  · exact (card_filter_coneComplete_edge hg).mp
      (hS.closed _ (mem_edges2_coneComplete.mpr (Or.inl ⟨g, hg, rfl⟩)))
  · obtain ⟨n, u, -, -, -, -, ⟨-, hG⟩ | ⟨-, -, hG⟩⟩ := lk2_cycle_or_path_of_coneComplete hS hx x
    · rw [hG]
      exact isConnEdges_image_pairs (fun i => (u i).getD x) _
    · rw [hG]
      exact isConnEdges_image_pairs (fun i => (u (i + 1)).getD x) _
  · intro u hu w hw
    have hbdry : ∀ y ∈ verts2 (bdryEdges2 L), ∀ y' ∈ verts2 (bdryEdges2 L),
        Relation.ReflTransGen (fun p q => ({p, q} : Finset V) ∈ edges2 L) y y' :=
      fun y hy y' hy' => Relation.ReflTransGen.mono (fun p q h => (mem_bdryEdges2.mp h).1) _ _
        (hbconn y hy y' hy')
    -- follow a path of the cone completion; a passage through the cone vertex is replaced by a
    -- path along the boundary
    have key : ∀ z, Relation.ReflTransGen
        (fun p q => ({p, q} : Finset (Option V)) ∈ edges2 (coneComplete L)) (some u) z →
        (∀ y, z = some y → Relation.ReflTransGen (fun p q => ({p, q} : Finset V) ∈ edges2 L) u y) ∧
        (z = none → ∃ y ∈ verts2 (bdryEdges2 L),
          Relation.ReflTransGen (fun p q => ({p, q} : Finset V) ∈ edges2 L) u y) := by
      intro z hz
      induction hz with
      | refl =>
        refine ⟨fun y hy => ?_, fun h => absurd h (Option.some_ne_none u)⟩
        cases Option.some_inj.mp hy
        exact .refl
      | @tail b c _ hbc ih =>
        rcases mem_edges2_coneComplete.mp hbc with ⟨g, hg, hgeq⟩ | ⟨x, hx, hxeq⟩
        · have hb : b ∈ liftOpt g := by rw [← hgeq]; exact mem_insert_self _ _
          have hc : c ∈ liftOpt g := by rw [← hgeq]; exact mem_insert_of_mem (mem_singleton_self _)
          obtain ⟨b', -, rfl⟩ := mem_liftOpt.mp hb
          obtain ⟨c', -, rfl⟩ := mem_liftOpt.mp hc
          have hg' : g = {b', c'} := liftOpt_injective (by rw [← hgeq, liftOpt_pair])
          refine ⟨fun y hy => ?_, fun h => absurd h (Option.some_ne_none c')⟩
          cases Option.some_inj.mp hy
          exact (ih.1 b' rfl).tail (hg' ▸ hg)
        · have hb : b ∈ ({none, some x} : Finset (Option V)) := by
            rw [← hxeq]; exact mem_insert_self _ _
          have hc : c ∈ ({none, some x} : Finset (Option V)) := by
            rw [← hxeq]; exact mem_insert_of_mem (mem_singleton_self _)
          rw [mem_insert, mem_singleton] at hb hc
          rcases hb with rfl | rfl <;> rcases hc with rfl | rfl
          · have : some x ∈ ({none, none} : Finset (Option V)) := by rw [hxeq]; simp
            simp at this
          · refine ⟨fun y hy => ?_, fun h => absurd h (Option.some_ne_none x)⟩
            cases Option.some_inj.mp hy
            obtain ⟨y₀, hy₀, hr⟩ := ih.2 rfl
            exact hr.trans (hbdry y₀ hy₀ x hx)
          · exact ⟨fun y hy => (by cases hy), fun _ => ⟨x, hx, ih.1 x rfl⟩⟩
          · have : none ∈ ({some x, some x} : Finset (Option V)) := by rw [hxeq]; simp
            simp at this
    exact (key _ (hS.connected _ (some_mem_verts2_coneComplete.mpr hu) _
      (some_mem_verts2_coneComplete.mpr hw))).1 w rfl
  · have := euler2_coneComplete hne hdeg
    rw [hS.euler] at this
    omega

/-- **Recognition of discs**: a 2-complex is a combinatorial 2-disc (its cone completion is reached
from the boundary of a tetrahedron by bistellar moves) exactly when it is a triangulated disc in
the intrinsic sense. -/
theorem isDisc2_iff_isSurfaceDisc {L : Finset (Finset V)} : IsDisc2 L ↔ IsSurfaceDisc L :=
  ⟨fun h => isSurfaceDisc_of_coneComplete h.2.isSurfaceSphere h.1,
    fun h => ⟨h.bdry_nonempty, h.isSurfaceSphere_coneComplete.isSphere2⟩⟩

/-! ## Deciding the conditions on examples -/

/-- The vertices reached from `R` in at most `k` steps along the edges `S`. -/
def reachIter {W : Type*} [DecidableEq W] (S : Finset (Finset W)) : ℕ → Finset W → Finset W
  | 0, R => R
  | k + 1, R => reachIter S k (R ∪ (S.filter fun e => (R ∩ e).Nonempty).biUnion id)

/-- Every vertex found by `reachIter` is joined by a path of edges to the starting set. -/
lemma reach_of_mem_reachIter {W : Type*} [DecidableEq W] {S : Finset (Finset W)}
    (hS : ∀ e ∈ S, #e = 2) {u : W} : ∀ (k : ℕ) (R : Finset W),
      (∀ x ∈ R, Relation.ReflTransGen (fun p q => ({p, q} : Finset W) ∈ S) u x) →
      ∀ y ∈ reachIter S k R, Relation.ReflTransGen (fun p q => ({p, q} : Finset W) ∈ S) u y
  | 0, R, hR => hR
  | k + 1, R, hR => by
    refine reach_of_mem_reachIter hS k _ fun y hy => ?_
    rcases mem_union.mp hy with hy | hy
    · exact hR y hy
    · obtain ⟨e, he, hye⟩ := mem_biUnion.mp hy
      obtain ⟨he, p, hp⟩ := mem_filter.mp he
      obtain ⟨hpR, hpe⟩ := mem_inter.mp hp
      by_cases hpy : p = y
      · exact hpy ▸ hR p hpR
      · have hsub : ({p, y} : Finset W) ⊆ e := by
          rw [insert_subset_iff, singleton_subset_iff]
          exact ⟨hpe, hye⟩
        have : ({p, y} : Finset W) = e :=
          eq_of_subset_of_card_le hsub (by rw [hS e he, card_pair hpy])
        exact (hR p hpR).tail (this ▸ he)

/-- Computable check that any two vertices of `N` are joined by a path of edges of `S`. -/
def connCheck {W : Type*} [DecidableEq W] (S : Finset (Finset W)) (N : Finset W) : Prop :=
  ∀ u ∈ N, N ⊆ reachIter S #N {u}

instance {W : Type*} [DecidableEq W] (S : Finset (Finset W)) (N : Finset W) :
    Decidable (connCheck S N) := by
  unfold connCheck; infer_instance

/-- `connCheck` is sound. -/
lemma reach_of_connCheck {W : Type*} [DecidableEq W] {S : Finset (Finset W)} {N : Finset W}
    (hS : ∀ e ∈ S, #e = 2) (h : connCheck S N) :
    ∀ u ∈ N, ∀ w ∈ N, Relation.ReflTransGen (fun p q => ({p, q} : Finset W) ∈ S) u w :=
  fun u hu w hw => reach_of_mem_reachIter hS _ {u}
    (fun x hx => by rw [mem_singleton.mp hx]) w (h u hu hw)

/-- **No path leaves a closed set of vertices**: if every edge meeting `A` lies in `A`, no path of
edges leads from a vertex of `A` to a vertex outside it. Used to refute connectivity. -/
lemma not_reach_of_closed {W : Type*} [DecidableEq W] {S : Finset (Finset W)} {A : Finset W}
    (hA : ∀ e ∈ S, ∀ p ∈ e, ∀ q ∈ e, p ∈ A → q ∈ A) {u w : W} (hu : u ∈ A) (hw : w ∉ A) :
    ¬ Relation.ReflTransGen (fun p q => ({p, q} : Finset W) ∈ S) u w := by
  intro h
  have : ∀ z, Relation.ReflTransGen (fun p q => ({p, q} : Finset W) ∈ S) u z → z ∈ A := by
    intro z hz
    induction hz with
    | refl => exact hu
    | @tail b c _ hbc ih =>
      exact hA {b, c} hbc b (mem_insert_self b {c}) c (mem_insert_of_mem (mem_singleton_self c)) ih
  exact hw (this w h)

lemma card_of_mem_lk2 {L : Finset (Finset V)} (hcard : ∀ τ ∈ L, #τ = 3) {v : V} {e : Finset V}
    (he : e ∈ lk2 L v) : #e = 2 := by
  obtain ⟨hve, hins⟩ := mem_lk2.mp he
  have := hcard _ hins
  rw [card_insert_of_notMem hve] at this
  omega

lemma card_of_mem_edges2 {L : Finset (Finset V)} {e : Finset V} (he : e ∈ edges2 L) : #e = 2 := by
  obtain ⟨-, -, -, h⟩ := mem_edges2.mp he
  exact h

/-- Computable check of the conditions of a triangulated 2-sphere (`Lightlike.PR.IsSurfaceSphere`). -/
def sphereCheck (L : Finset (Finset V)) : Prop :=
  (∀ τ ∈ L, #τ = 3) ∧ (∀ f ∈ edges2 L, #(L.filter (f ⊆ ·)) = 2) ∧
    (∀ v ∈ verts2 L, connCheck (lk2 L v) (verts2 (lk2 L v))) ∧ connCheck (edges2 L) (verts2 L) ∧
    euler2 L = 2

instance (L : Finset (Finset V)) : Decidable (sphereCheck L) := by
  unfold sphereCheck; infer_instance

/-- Computable check of the conditions of a triangulated disc (`IsSurfaceDisc`). -/
def discCheck (L : Finset (Finset V)) : Prop :=
  (∀ τ ∈ L, #τ = 3) ∧ (∀ f ∈ edges2 L, #(L.filter (f ⊆ ·)) ≤ 2) ∧
    (∀ v ∈ verts2 L, connCheck (lk2 L v) (verts2 (lk2 L v))) ∧ connCheck (edges2 L) (verts2 L) ∧
    (bdryEdges2 L).Nonempty ∧
    (∀ x ∈ verts2 (bdryEdges2 L), #((bdryEdges2 L).filter (x ∈ ·)) = 2) ∧
    connCheck (bdryEdges2 L) (verts2 (bdryEdges2 L)) ∧ euler2 L = 1

instance (L : Finset (Finset V)) : Decidable (discCheck L) := by
  unfold discCheck; infer_instance

/-- `sphereCheck` is sound: it gives a combinatorial 2-sphere (through the core's recognition
theorem `Lightlike.PR.IsSurfaceSphere.isSphere2`). -/
theorem isSphere2_of_check {L : Finset (Finset V)} (h : sphereCheck L) : IsSphere2 L := by
  obtain ⟨hc, hcl, hl, hconn, he⟩ := h
  exact IsSurfaceSphere.isSphere2 ⟨hc, hcl,
    fun v hv => reach_of_connCheck (fun e he => card_of_mem_lk2 hc he) (hl v hv),
    reach_of_connCheck (fun e he => card_of_mem_edges2 he) hconn, he⟩

/-- `discCheck` is sound: it gives a triangulated disc, hence a combinatorial 2-disc. -/
theorem isSurfaceDisc_of_check {L : Finset (Finset V)} (h : discCheck L) : IsSurfaceDisc L := by
  obtain ⟨hc, hle, hl, hconn, hne, hdeg, hbc, he⟩ := h
  exact ⟨hc, hle, fun v hv => reach_of_connCheck (fun e he => card_of_mem_lk2 hc he) (hl v hv),
    reach_of_connCheck (fun e he => card_of_mem_edges2 he) hconn, hne, hdeg,
    reach_of_connCheck (fun e he => card_of_mem_bdryEdges2 he) hbc, he⟩

/-- Computable check that `K` is a combinatorial 3-manifold with boundary. -/
def manifoldBdCheck (K : Complex3 V) : Prop :=
  ∀ v ∈ K.verts, sphereCheck (K.link v) ∨ discCheck (K.link v)

instance (K : Complex3 V) : Decidable (manifoldBdCheck K) := by
  unfold manifoldBdCheck; infer_instance

/-- `manifoldBdCheck` is sound. -/
theorem isCombManifoldBd_of_check {K : Complex3 V} (h : manifoldBdCheck K) : IsCombManifoldBd K :=
  fun v hv => (h v hv).imp isSphere2_of_check fun hd =>
    isDisc2_iff_isSurfaceDisc.mpr (isSurfaceDisc_of_check hd)

end Lightlike.Regge
