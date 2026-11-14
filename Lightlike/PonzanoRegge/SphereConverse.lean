module

public import Lightlike.PonzanoRegge.SphereInvariants

/-!
# Combinatorial 2-spheres: the converse

`IsSphere2` (bistellar moves from the boundary of a tetrahedron) is shown here to coincide with
the intrinsic description of a triangulated 2-sphere, `IsSurfaceSphere`: a closed surface (every
edge in exactly two triangles, the link of every vertex connected) whose 1-skeleton is connected
and whose Euler characteristic is `2`.

* `IsSphere2.isSurfaceSphere`: the forward direction, from the invariants of
  `SphereInvariants.lean` and the invariance of link connectivity under the moves.
* `IsSurfaceSphere.isSphere2`: the converse (Steinitz, Wagner). Every closed edge path is a
  boundary mod 2 (`H₁(L; ℤ/2) = 0`, from the Euler characteristic); hence two "crossing" diagonals
  around a vertex cannot both be edges, so some edge at a vertex of degree `≥ 4` can be flipped;
  flipping lowers the degree to `3`, and then the vertex is removed by the inverse of a
  subdivision. Induction on the number of vertices ends at the boundary of a tetrahedron.
-/

@[expose] public section

open Finset

namespace Lightlike.PR

variable {V : Type*} [DecidableEq V]

/-! ## Connectivity of a graph after subdividing an edge -/

/-- **Subdividing an edge keeps a graph connected, in both directions.** `G'` is `G` with the edge
`cd` replaced by the path `c x d` through a new vertex `x`. -/
lemma conn_subdivide {N : Finset V} {G G' : V → V → Prop} {c d x : V}
    (hcd : G c d) (hsym : ∀ p q, G p q → G q p) (hc : c ∈ N) (hd : d ∈ N) (hx : x ∉ N)
    (hGN : ∀ p q, G p q → p ∈ N ∧ q ∈ N)
    (hG' : ∀ p q, G' p q ↔ (G p q ∧ ¬ ((p = c ∧ q = d) ∨ (p = d ∧ q = c))) ∨
      (p = c ∧ q = x) ∨ (p = x ∧ q = c) ∨ (p = x ∧ q = d) ∨ (p = d ∧ q = x)) :
    (∀ u ∈ N, ∀ w ∈ N, Relation.ReflTransGen G u w) ↔
      (∀ u ∈ insert x N, ∀ w ∈ insert x N, Relation.ReflTransGen G' u w) := by
  have cx : G' c x := (hG' c x).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  have xc : G' x c := (hG' x c).mpr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  have xd : G' x d := (hG' x d).mpr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
  have dx : G' d x := (hG' d x).mpr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
  have hxc : x ≠ c := fun h => hx (h ▸ hc)
  have hxd : x ≠ d := fun h => hx (h ▸ hd)
  constructor
  · intro H
    -- every `G`-step becomes a `G'`-path (the step `cd` becomes `c x d`)
    have step : ∀ p q, G p q → Relation.ReflTransGen G' p q := by
      intro p q hpq
      by_cases h : (p = c ∧ q = d) ∨ (p = d ∧ q = c)
      · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact .tail (.single cx) xd
        · exact .tail (.single dx) xc
      · exact .single ((hG' p q).mpr (Or.inl ⟨hpq, h⟩))
    have mono : ∀ {u w}, Relation.ReflTransGen G u w → Relation.ReflTransGen G' u w := fun h =>
      Relation.ReflTransGen.lift' id step _ _ h
    have toC : ∀ u ∈ insert x N, Relation.ReflTransGen G' u c := by
      intro u hu
      rcases mem_insert.mp hu with h | h
      · rw [h]; exact .single xc
      · exact mono (H u h c hc)
    have fromC : ∀ u ∈ insert x N, Relation.ReflTransGen G' c u := by
      intro u hu
      rcases mem_insert.mp hu with h | h
      · rw [h]; exact .single cx
      · exact mono (H c hc u h)
    exact fun u hu w hw => (toC u hu).trans (fromC w hw)
  · intro H u hu w hw
    -- send `x` to `c`; every `G'`-step becomes a `G`-path
    let f : V → V := fun y => if y = x then c else y
    have hf : ∀ y, y ≠ x → f y = y := fun y hy => by simp [f, hy]
    have fx : f x = c := by simp [f]
    have step : ∀ p q, G' p q → Relation.ReflTransGen G (f p) (f q) := by
      intro p q hpq
      rcases (hG' p q).mp hpq with ⟨hG, -⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hp : p ≠ x := fun h => hx (h ▸ (hGN p q hG).1)
        have hq : q ≠ x := fun h => hx (h ▸ (hGN p q hG).2)
        rw [hf p hp, hf q hq]
        exact .single hG
      · rw [hf _ hxc.symm, fx]
      · rw [hf _ hxc.symm, fx]
      · rw [fx, hf _ hxd.symm]; exact .single hcd
      · rw [hf _ hxd.symm, fx]
        exact .single (hsym _ _ hcd)
    have := Relation.ReflTransGen.lift' f step _ _ (H u (mem_insert_of_mem hu) w (mem_insert_of_mem hw))
    simp only [Function.onFun, hf u (fun h => hx (h ▸ hu)), hf w (fun h => hx (h ▸ hw))] at this
    exact this

/-- A set of edges is **connected**: any two of its vertices are joined by a path of its edges. -/
def IsConnEdges (S : Finset (Finset V)) : Prop :=
  ∀ u ∈ verts2 S, ∀ w ∈ verts2 S, Relation.ReflTransGen (fun p q => ({p, q} : Finset V) ∈ S) u w

/-- **Subdividing an edge `cd` of an edge set by a new vertex `x` keeps it connected, in both
directions.** -/
lemma connEdges_subdivide {S : Finset (Finset V)} {c d x : V} (hcd' : c ≠ d)
    (hcd : ({c, d} : Finset V) ∈ S) (hx : x ∉ verts2 S) :
    IsConnEdges S ↔ IsConnEdges (insert {c, x} (insert {d, x} (S.erase {c, d}))) := by
  have hc : c ∈ verts2 S := mem_verts2.mpr ⟨_, hcd, by simp⟩
  have hd : d ∈ verts2 S := mem_verts2.mpr ⟨_, hcd, by simp⟩
  have hxc : x ≠ c := fun h => hx (h ▸ hc)
  have hxd : x ≠ d := fun h => hx (h ▸ hd)
  have hverts : verts2 (insert {c, x} (insert {d, x} (S.erase {c, d}))) = insert x (verts2 S) := by
    ext y
    simp only [mem_verts2, mem_insert, mem_erase]
    constructor
    · rintro ⟨τ, hτ, hy⟩
      rcases hτ with rfl | rfl | ⟨-, hτS⟩
      · simp only [mem_insert, mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact Or.inr ⟨_, hcd, by simp⟩
        · exact Or.inl rfl
      · simp only [mem_insert, mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact Or.inr ⟨_, hcd, by simp⟩
        · exact Or.inl rfl
      · exact Or.inr ⟨τ, hτS, hy⟩
    · rintro (rfl | ⟨τ, hτS, hy⟩)
      · exact ⟨{c, y}, Or.inl rfl, by simp⟩
      · by_cases h : τ = {c, d}
        · subst h
          simp only [mem_insert, mem_singleton] at hy
          rcases hy with rfl | rfl
          · exact ⟨{y, x}, Or.inl rfl, by simp⟩
          · exact ⟨{y, x}, Or.inr (Or.inl rfl), by simp⟩
        · exact ⟨τ, Or.inr (Or.inr ⟨h, hτS⟩), hy⟩
  unfold IsConnEdges
  rw [hverts]
  refine conn_subdivide (G := fun p q => ({p, q} : Finset V) ∈ S) hcd
    (fun p q h => by rwa [pair_comm]) hc hd hx
    (fun p q h => ⟨mem_verts2.mpr ⟨_, h, by simp⟩, mem_verts2.mpr ⟨_, h, by simp⟩⟩) ?_
  intro p q
  simp only [mem_insert, mem_erase, ne_eq, pair_eq_pair_iff']
  constructor
  · rintro (h | h | ⟨hne, hm⟩)
    · exact Or.inr (h.elim (fun h => Or.inl h) (fun h => Or.inr (Or.inl h)))
    · rcases h with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inl ⟨hm, hne⟩
  · rintro (⟨hm, hne⟩ | h | h | h | h)
    · exact Or.inr (Or.inr ⟨hne, hm⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inl (Or.inr h))
    · exact Or.inr (Or.inl (Or.inl h))

/-! ## Links of a 2-complex -/

/-- The **link** of `v` in a 2-complex: the edges opposite `v` in the triangles through `v`. -/
def lk2 (L : Finset (Finset V)) (v : V) : Finset (Finset V) := (L.filter (v ∈ ·)).image (·.erase v)

lemma mem_lk2 {L : Finset (Finset V)} {v : V} {e : Finset V} :
    e ∈ lk2 L v ↔ v ∉ e ∧ insert v e ∈ L := by
  simp only [lk2, mem_image, mem_filter]
  constructor
  · rintro ⟨t, ⟨ht, hv⟩, rfl⟩
    exact ⟨notMem_erase v t, by rwa [insert_erase hv]⟩
  · rintro ⟨hv, ht⟩
    exact ⟨insert v e, ⟨ht, mem_insert_self v e⟩, erase_insert hv⟩

/-- **The link of every vertex is connected** (with closedness: every vertex link is a cycle). -/
def IsLinkConn (L : Finset (Finset V)) : Prop := ∀ v ∈ verts2 L, IsConnEdges (lk2 L v)

/-- A **triangulated 2-sphere** in the intrinsic sense: triangles have three vertices, every edge
lies in exactly two triangles, every vertex link is connected, the 1-skeleton is connected, and the
Euler characteristic is `2`. -/
structure IsSurfaceSphere (L : Finset (Finset V)) : Prop where
  card : ∀ τ ∈ L, #τ = 3
  closed : IsClosed2 L
  link : IsLinkConn L
  connected : IsConnected2 L
  euler : euler2 L = 2

/-! ## How the links change under the moves -/

-- The generated proofs pass every distinctness fact to `simp`; each uses only some.
set_option linter.unusedSimpArgs false

/-- Subdividing `bcd` by `x` subdivides the edge `cd` of the link of `b` by `x`. -/
lemma lk2_sub13_b {L : Finset (Finset V)} {b c d x : V} (hbc : b ≠ c) (hbd : b ≠ d) (hxb : x ≠ b) :
    lk2 (insert {b, c, x} (insert {c, d, x} (insert {b, d, x} (L.erase {b, c, d})))) b = insert {c, x} (insert {d, x} ((lk2 L b).erase {c, d})) := by
  ext f
  simp only [mem_lk2]
  by_cases hv : b ∈ f
  · simp only [hv, not_true_eq_false, false_and, false_iff]
    intro hm
    simp only [mem_insert, mem_erase, mem_lk2] at hm
    rcases hm with rfl | rfl | ⟨-, hX', -⟩ <;>
      first | exact hX' hv | simp [hbc, hbd, hxb, hbc.symm, hbd.symm, hxb.symm] at hv
  simp only [hv, not_false_eq_true, true_and, mem_insert, mem_singleton, mem_erase, ne_eq,
    mem_lk2, insert_eq_iff_of_notMem hv]
  have e0 : ({b, c, x} : Finset V).erase b = {c, x} := by fset_eq
  have e1 : ({b, d, x} : Finset V).erase b = {d, x} := by fset_eq
  have e2 : ({b, c, d} : Finset V).erase b = {c, d} := by fset_eq
  simp only [e0, e1, e2, hbc, hbd, hxb, hbc.symm, hbd.symm, hxb.symm, or_true, true_and, or_false, false_and, false_or,
    true_or, and_true, ne_eq, mem_insert, mem_singleton]

/-- Subdividing `bcd` by `x` subdivides the edge `bd` of the link of `c` by `x`. -/
lemma lk2_sub13_c {L : Finset (Finset V)} {b c d x : V} (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (hxb : x ≠ b) (hxc : x ≠ c)
    (hxd : x ≠ d) :
    lk2 (insert {b, c, x} (insert {c, d, x} (insert {b, d, x} (L.erase {b, c, d})))) c = insert {b, x} (insert {d, x} ((lk2 L c).erase {b, d})) := by
  ext f
  simp only [mem_lk2]
  by_cases hv : c ∈ f
  · simp only [hv, not_true_eq_false, false_and, false_iff]
    intro hm
    simp only [mem_insert, mem_erase, mem_lk2] at hm
    rcases hm with rfl | rfl | ⟨-, hX', -⟩ <;>
      first | exact hX' hv | simp [hbc, hbd, hcd, hxb, hxc, hxd, hbc.symm, hbd.symm, hcd.symm, hxb.symm, hxc.symm, hxd.symm] at hv
  simp only [hv, not_false_eq_true, true_and, mem_insert, mem_singleton, mem_erase, ne_eq,
    mem_lk2, insert_eq_iff_of_notMem hv]
  have e0 : ({b, c, x} : Finset V).erase c = {b, x} := by fset_eq
  have e1 : ({c, d, x} : Finset V).erase c = {d, x} := by fset_eq
  have e2 : ({b, c, d} : Finset V).erase c = {b, d} := by fset_eq
  simp only [e0, e1, e2, hbc, hbd, hcd, hxb, hxc, hxd, hbc.symm, hbd.symm, hcd.symm, hxb.symm, hxc.symm, hxd.symm, or_true, true_and, or_false, false_and, false_or,
    true_or, and_true, ne_eq, mem_insert, mem_singleton]

/-- Subdividing `bcd` by `x` subdivides the edge `bc` of the link of `d` by `x`. -/
lemma lk2_sub13_d {L : Finset (Finset V)} {b c d x : V} (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (hxb : x ≠ b) (hxc : x ≠ c)
    (hxd : x ≠ d) :
    lk2 (insert {b, c, x} (insert {c, d, x} (insert {b, d, x} (L.erase {b, c, d})))) d = insert {b, x} (insert {c, x} ((lk2 L d).erase {b, c})) := by
  ext f
  simp only [mem_lk2]
  by_cases hv : d ∈ f
  · simp only [hv, not_true_eq_false, false_and, false_iff]
    intro hm
    simp only [mem_insert, mem_erase, mem_lk2] at hm
    rcases hm with rfl | rfl | ⟨-, hX', -⟩ <;>
      first | exact hX' hv | simp [hbc, hbd, hcd, hxb, hxc, hxd, hbc.symm, hbd.symm, hcd.symm, hxb.symm, hxc.symm, hxd.symm] at hv
  simp only [hv, not_false_eq_true, true_and, mem_insert, mem_singleton, mem_erase, ne_eq,
    mem_lk2, insert_eq_iff_of_notMem hv]
  have e0 : ({c, d, x} : Finset V).erase d = {c, x} := by fset_eq
  have e1 : ({b, d, x} : Finset V).erase d = {b, x} := by fset_eq
  have e2 : ({b, c, d} : Finset V).erase d = {b, c} := by fset_eq
  simp only [e0, e1, e2, hbc, hbd, hcd, hxb, hxc, hxd, hbc.symm, hbd.symm, hcd.symm, hxb.symm, hxc.symm, hxd.symm, or_true, true_and, or_false, false_and, false_or,
    true_or, and_true, ne_eq, mem_insert, mem_singleton]
  all_goals tauto

/-- After flipping `bc` to `de`, the link of `b` in `L` is its new link with the edge `de` subdivided by `c`. -/
lemma lk2_flip22_b {L : Finset (Finset V)} {b c d e : V} (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d)
    (hce : c ≠ e) (hde : d ≠ e) (hbde : {b, d, e} ∉ L) (hcde : {c, d, e} ∉ L) (h₁ : {b, c, d} ∈ L) (h₂ : {b, c, e} ∈ L) :
    lk2 L b = insert {d, c} (insert {e, c} ((lk2 (insert {b, d, e} (insert {c, d, e} ((L.erase {b, c, d}).erase {b, c, e}))) b).erase {d, e})) := by
  ext f
  simp only [mem_lk2]
  by_cases hv : b ∈ f
  · simp only [hv, not_true_eq_false, false_and, false_iff]
    intro hm
    simp only [mem_insert, mem_erase, mem_lk2] at hm
    rcases hm with rfl | rfl | ⟨-, hX', -⟩ <;>
      first | exact hX' hv | simp [hbc, hbd, hbe, hcd, hce, hde, hbc.symm, hbd.symm, hbe.symm, hcd.symm, hce.symm, hde.symm] at hv
  simp only [hv, not_false_eq_true, true_and, mem_insert, mem_singleton, mem_erase, ne_eq,
    mem_lk2, insert_eq_iff_of_notMem hv]
  have e0 : ({b, c, d} : Finset V).erase b = {d, c} := by fset_eq
  have e1 : ({b, c, e} : Finset V).erase b = {e, c} := by fset_eq
  have e2 : ({b, d, e} : Finset V).erase b = {d, e} := by fset_eq
  simp only [e0, e1, e2, hbc, hbd, hbe, hcd, hce, hde, hbc.symm, hbd.symm, hbe.symm, hcd.symm, hce.symm, hde.symm, or_true, true_and, or_false, false_and, false_or,
    true_or, and_true, ne_eq, mem_insert, mem_singleton]
  have k1 : insert b ({d, c} : Finset V) ∈ L := by
    rw [show insert b ({d, c} : Finset V) = {b, c, d} by fset_eq]; exact h₁
  have k2 : insert b ({e, c} : Finset V) ∈ L := by
    rw [show insert b ({e, c} : Finset V) = {b, c, e} by fset_eq]; exact h₂
  have k3 : insert b ({d, e} : Finset V) ∉ L := hbde
  constructor
  · intro h
    by_cases h1 : f = {d, c}
    · exact Or.inl h1
    by_cases h2 : f = {e, c}
    · exact Or.inr (Or.inl h2)
    by_cases h3 : f = {d, e}
    · subst h3; exact absurd h k3
    · exact Or.inr (Or.inr ⟨h3, Or.inr ⟨h2, h1, h⟩⟩)
  · rintro (rfl | rfl | ⟨h3, rfl | ⟨-, -, h⟩⟩)
    · exact k1
    · exact k2
    · exact absurd rfl h3
    · exact h

/-- After flipping `bc` to `de`, the link of `c` in `L` is its new link with the edge `de` subdivided by `b`. -/
lemma lk2_flip22_c {L : Finset (Finset V)} {b c d e : V} (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d)
    (hce : c ≠ e) (hde : d ≠ e) (hbde : {b, d, e} ∉ L) (hcde : {c, d, e} ∉ L) (h₁ : {b, c, d} ∈ L) (h₂ : {b, c, e} ∈ L) :
    lk2 L c = insert {d, b} (insert {e, b} ((lk2 (insert {b, d, e} (insert {c, d, e} ((L.erase {b, c, d}).erase {b, c, e}))) c).erase {d, e})) := by
  ext f
  simp only [mem_lk2]
  by_cases hv : c ∈ f
  · simp only [hv, not_true_eq_false, false_and, false_iff]
    intro hm
    simp only [mem_insert, mem_erase, mem_lk2] at hm
    rcases hm with rfl | rfl | ⟨-, hX', -⟩ <;>
      first | exact hX' hv | simp [hbc, hbd, hbe, hcd, hce, hde, hbc.symm, hbd.symm, hbe.symm, hcd.symm, hce.symm, hde.symm] at hv
  simp only [hv, not_false_eq_true, true_and, mem_insert, mem_singleton, mem_erase, ne_eq,
    mem_lk2, insert_eq_iff_of_notMem hv]
  have e0 : ({b, c, d} : Finset V).erase c = {d, b} := by fset_eq
  have e1 : ({b, c, e} : Finset V).erase c = {e, b} := by fset_eq
  have e2 : ({c, d, e} : Finset V).erase c = {d, e} := by fset_eq
  simp only [e0, e1, e2, hbc, hbd, hbe, hcd, hce, hde, hbc.symm, hbd.symm, hbe.symm, hcd.symm, hce.symm, hde.symm, or_true, true_and, or_false, false_and, false_or,
    true_or, and_true, ne_eq, mem_insert, mem_singleton]
  have k1 : insert c ({d, b} : Finset V) ∈ L := by
    rw [show insert c ({d, b} : Finset V) = {b, c, d} by fset_eq]; exact h₁
  have k2 : insert c ({e, b} : Finset V) ∈ L := by
    rw [show insert c ({e, b} : Finset V) = {b, c, e} by fset_eq]; exact h₂
  have k3 : insert c ({d, e} : Finset V) ∉ L := hcde
  constructor
  · intro h
    by_cases h1 : f = {d, b}
    · exact Or.inl h1
    by_cases h2 : f = {e, b}
    · exact Or.inr (Or.inl h2)
    by_cases h3 : f = {d, e}
    · subst h3; exact absurd h k3
    · exact Or.inr (Or.inr ⟨h3, Or.inr ⟨h2, h1, h⟩⟩)
  · rintro (rfl | rfl | ⟨h3, rfl | ⟨-, -, h⟩⟩)
    · exact k1
    · exact k2
    · exact absurd rfl h3
    · exact h

/-- Flipping `bc` to `de` subdivides the edge `bc` of the link of `d` by `e`. -/
lemma lk2_flip22_d {L : Finset (Finset V)} {b c d e : V} (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d)
    (hce : c ≠ e) (hde : d ≠ e) (hbde : {b, d, e} ∉ L) (hcde : {c, d, e} ∉ L) :
    lk2 (insert {b, d, e} (insert {c, d, e} ((L.erase {b, c, d}).erase {b, c, e}))) d = insert {b, e} (insert {c, e} ((lk2 L d).erase {b, c})) := by
  ext f
  simp only [mem_lk2]
  by_cases hv : d ∈ f
  · simp only [hv, not_true_eq_false, false_and, false_iff]
    intro hm
    simp only [mem_insert, mem_erase, mem_lk2] at hm
    rcases hm with rfl | rfl | ⟨-, hX', -⟩ <;>
      first | exact hX' hv | simp [hbc, hbd, hbe, hcd, hce, hde, hbc.symm, hbd.symm, hbe.symm, hcd.symm, hce.symm, hde.symm] at hv
  simp only [hv, not_false_eq_true, true_and, mem_insert, mem_singleton, mem_erase, ne_eq,
    mem_lk2, insert_eq_iff_of_notMem hv]
  have e0 : ({b, d, e} : Finset V).erase d = {b, e} := by fset_eq
  have e1 : ({c, d, e} : Finset V).erase d = {c, e} := by fset_eq
  have e2 : ({b, c, d} : Finset V).erase d = {b, c} := by fset_eq
  simp only [e0, e1, e2, hbc, hbd, hbe, hcd, hce, hde, hbc.symm, hbd.symm, hbe.symm, hcd.symm, hce.symm, hde.symm, or_true, true_and, or_false, false_and, false_or,
    true_or, and_true, ne_eq, mem_insert, mem_singleton]
  all_goals tauto

/-- Flipping `bc` to `de` subdivides the edge `bc` of the link of `e` by `d`. -/
lemma lk2_flip22_e {L : Finset (Finset V)} {b c d e : V} (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d)
    (hce : c ≠ e) (hde : d ≠ e) (hbde : {b, d, e} ∉ L) (hcde : {c, d, e} ∉ L) :
    lk2 (insert {b, d, e} (insert {c, d, e} ((L.erase {b, c, d}).erase {b, c, e}))) e = insert {b, d} (insert {c, d} ((lk2 L e).erase {b, c})) := by
  ext f
  simp only [mem_lk2]
  by_cases hv : e ∈ f
  · simp only [hv, not_true_eq_false, false_and, false_iff]
    intro hm
    simp only [mem_insert, mem_erase, mem_lk2] at hm
    rcases hm with rfl | rfl | ⟨-, hX', -⟩ <;>
      first | exact hX' hv | simp [hbc, hbd, hbe, hcd, hce, hde, hbc.symm, hbd.symm, hbe.symm, hcd.symm, hce.symm, hde.symm] at hv
  simp only [hv, not_false_eq_true, true_and, mem_insert, mem_singleton, mem_erase, ne_eq,
    mem_lk2, insert_eq_iff_of_notMem hv]
  have e0 : ({b, d, e} : Finset V).erase e = {b, d} := by fset_eq
  have e1 : ({c, d, e} : Finset V).erase e = {c, d} := by fset_eq
  have e2 : ({b, c, e} : Finset V).erase e = {b, c} := by fset_eq
  simp only [e0, e1, e2, hbc, hbd, hbe, hcd, hce, hde, hbc.symm, hbd.symm, hbe.symm, hcd.symm, hce.symm, hde.symm, or_true, true_and, or_false, false_and, false_or,
    true_or, and_true, ne_eq, mem_insert, mem_singleton]
  all_goals tauto

/-- The edges of a triangle `pqr` form a connected edge set. -/
lemma connEdges_triangle {p q r : V} :
    IsConnEdges ({{p, q}, {q, r}, {p, r}} : Finset (Finset V)) := by
  have hv : ∀ y ∈ verts2 ({{p, q}, {q, r}, {p, r}} : Finset (Finset V)), y = p ∨ y = q ∨ y = r := by
    intro y hy
    obtain ⟨τ, hτ, hyτ⟩ := mem_verts2.mp hy
    simp only [mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl <;> simp only [mem_insert, mem_singleton] at hyτ <;>
      rcases hyτ with h | h <;> simp [h]
  have e1 : ({p, q} : Finset V) ∈ ({{p, q}, {q, r}, {p, r}} : Finset (Finset V)) := by simp
  have e2 : ({q, r} : Finset V) ∈ ({{p, q}, {q, r}, {p, r}} : Finset (Finset V)) := by simp
  have e3 : ({p, r} : Finset V) ∈ ({{p, q}, {q, r}, {p, r}} : Finset (Finset V)) := by simp
  have e1' : ({q, p} : Finset V) ∈ ({{p, q}, {q, r}, {p, r}} : Finset (Finset V)) := by
    rw [pair_comm q p]; exact e1
  have e2' : ({r, q} : Finset V) ∈ ({{p, q}, {q, r}, {p, r}} : Finset (Finset V)) := by
    rw [pair_comm r q]; exact e2
  have e3' : ({r, p} : Finset V) ∈ ({{p, q}, {q, r}, {p, r}} : Finset (Finset V)) := by
    rw [pair_comm r p]; exact e3
  intro u hu w hw
  rcases hv u hu with h | h | h <;> rcases hv w hw with h' | h' | h' <;> subst h <;> subst h'
  all_goals first | exact .refl | exact .single e1 | exact .single e2 | exact .single e3 |
    exact .single e1' | exact .single e2' | exact .single e3'

lemma lk2_sub13_new {L : Finset (Finset V)} {b c d x : V} (hx : x ∉ verts2 L) (hxb : x ≠ b)
    (hxc : x ≠ c) (hxd : x ≠ d) :
    lk2 (insert {b, c, x} (insert {c, d, x} (insert {b, d, x} (L.erase {b, c, d})))) x =
      {{b, c}, {c, d}, {b, d}} := by
  ext f
  simp only [mem_lk2]
  by_cases hv : x ∈ f
  · simp only [hv, not_true_eq_false, false_and, false_iff, mem_insert, mem_singleton, not_or]
    refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> simp [hxb, hxc, hxd] at hv
  simp only [hv, not_false_eq_true, true_and, mem_insert, mem_singleton, mem_erase, ne_eq,
    insert_eq_iff_of_notMem hv]
  have e0 : ({b, c, x} : Finset V).erase x = {b, c} := by fset_eq
  have e1 : ({c, d, x} : Finset V).erase x = {c, d} := by fset_eq
  have e2 : ({b, d, x} : Finset V).erase x = {b, d} := by fset_eq
  have hold : insert x f ∉ L := fun hm => hx (mem_verts2.mpr ⟨_, hm, mem_insert_self _ _⟩)
  simp only [e0, e1, e2, hold, and_false, or_false]
  simp

lemma lk2_sub13_other {L : Finset (Finset V)} {b c d x v : V} (hvb : v ≠ b) (hvc : v ≠ c)
    (hvd : v ≠ d) (hvx : v ≠ x) :
    lk2 (insert {b, c, x} (insert {c, d, x} (insert {b, d, x} (L.erase {b, c, d})))) v = lk2 L v := by
  ext f
  simp only [mem_lk2]
  by_cases hv : v ∈ f
  · simp [hv]
  simp only [hv, not_false_eq_true, true_and, mem_insert, mem_singleton, mem_erase, ne_eq,
    insert_eq_iff_of_notMem hv, hvb, hvc, hvd, hvx, false_or, or_false, false_and,
    not_false_eq_true, and_true]

lemma lk2_flip22_other {L : Finset (Finset V)} {b c d e v : V} (hvb : v ≠ b) (hvc : v ≠ c)
    (hvd : v ≠ d) (hve : v ≠ e) :
    lk2 (insert {b, d, e} (insert {c, d, e} ((L.erase {b, c, d}).erase {b, c, e}))) v = lk2 L v := by
  ext f
  simp only [mem_lk2]
  by_cases hv : v ∈ f
  · simp [hv]
  simp only [hv, not_false_eq_true, true_and, mem_insert, mem_singleton, mem_erase, ne_eq,
    insert_eq_iff_of_notMem hv, hvb, hvc, hvd, hve, false_or, or_false, false_and,
    not_false_eq_true, and_true]

/-- A vertex `y` of the link of `v` in `L` lies in a triangle of `L` with `v`. -/
lemma mem_verts2_of_mem_lk2 {L : Finset (Finset V)} {v y : V} (hy : y ∈ verts2 (lk2 L v)) :
    y ∈ verts2 L := by
  obtain ⟨f, hf, hyf⟩ := mem_verts2.mp hy
  exact mem_verts2.mpr ⟨_, (mem_lk2.mp hf).2, mem_insert_of_mem hyf⟩

/-- **A 2-dimensional move keeps every vertex link connected, in both directions.** -/
theorem Move2.linkConn_iff {L L' : Finset (Finset V)} (h : Move2 L L') :
    IsLinkConn L ↔ IsLinkConn L' := by
  cases h with
  | @sub13 b c d x hbc hbd hcd hτ hx =>
    obtain ⟨hxb, hxc, hxd⟩ := sub13_fresh hτ hx
    have fresh : ∀ v, x ∉ verts2 (lk2 L v) := fun v hm => hx (mem_verts2_of_mem_lk2 hm)
    have kb : IsConnEdges (lk2 L b) ↔ IsConnEdges (lk2 (insert {b, c, x} (insert {c, d, x}
        (insert {b, d, x} (L.erase {b, c, d})))) b) := by
      rw [lk2_sub13_b hbc hbd hxb]
      exact connEdges_subdivide hcd (mem_lk2.mpr ⟨by simp [hbc, hbd, hcd, hxb, hxc, hxd, hbc.symm, hbd.symm, hcd.symm, hxb.symm, hxc.symm, hxd.symm], hτ⟩) (fresh b)
    have kc : IsConnEdges (lk2 L c) ↔ IsConnEdges (lk2 (insert {b, c, x} (insert {c, d, x}
        (insert {b, d, x} (L.erase {b, c, d})))) c) := by
      rw [lk2_sub13_c hbc hbd hcd hxb hxc hxd]
      refine connEdges_subdivide hbd (mem_lk2.mpr ⟨by simp [hbc, hbd, hcd, hxb, hxc, hxd, hbc.symm, hbd.symm, hcd.symm, hxb.symm, hxc.symm, hxd.symm], ?_⟩) (fresh c)
      rw [show insert c ({b, d} : Finset V) = {b, c, d} by fset_eq]; exact hτ
    have kd : IsConnEdges (lk2 L d) ↔ IsConnEdges (lk2 (insert {b, c, x} (insert {c, d, x}
        (insert {b, d, x} (L.erase {b, c, d})))) d) := by
      rw [lk2_sub13_d hbc hbd hcd hxb hxc hxd]
      refine connEdges_subdivide hbc (mem_lk2.mpr ⟨by simp [hbc, hbd, hcd, hxb, hxc, hxd, hbc.symm, hbd.symm, hcd.symm, hxb.symm, hxc.symm, hxd.symm], ?_⟩) (fresh d)
      rw [show insert d ({b, c} : Finset V) = {b, c, d} by fset_eq]; exact hτ
    unfold IsLinkConn
    rw [verts2_sub13 hτ]
    constructor
    · intro H v hv
      by_cases hvx : v = x
      · rw [hvx, lk2_sub13_new hx hxb hxc hxd]; exact connEdges_triangle
      have hv' : v ∈ verts2 L := (mem_insert.mp hv).resolve_left hvx
      by_cases hvb : v = b
      · rw [hvb] at hv' ⊢; exact kb.mp (H b hv')
      by_cases hvc : v = c
      · rw [hvc] at hv' ⊢; exact kc.mp (H c hv')
      by_cases hvd : v = d
      · rw [hvd] at hv' ⊢; exact kd.mp (H d hv')
      rw [lk2_sub13_other hvb hvc hvd hvx]; exact H v hv'
    · intro H v hv
      have hvx : v ≠ x := fun h => hx (h ▸ hv)
      by_cases hvb : v = b
      · rw [hvb] at hv ⊢; exact kb.mpr (H b (mem_insert_of_mem hv))
      by_cases hvc : v = c
      · rw [hvc] at hv ⊢; exact kc.mpr (H c (mem_insert_of_mem hv))
      by_cases hvd : v = d
      · rw [hvd] at hv ⊢; exact kd.mpr (H d (mem_insert_of_mem hv))
      have := H v (mem_insert_of_mem hv)
      rwa [lk2_sub13_other hvb hvc hvd hvx] at this
  | @flip22 b c d e hbc hbd hbe hcd hce hde h₁ h₂ hstar hfresh =>
    have hbde : ({b, d, e} : Finset V) ∉ L := fun hm => hfresh _ hm (by small_subset)
    have hcde : ({c, d, e} : Finset V) ∉ L := fun hm => hfresh _ hm (by small_subset)
    -- `c` is not a neighbour of `b` after the flip, nor `b` of `c`
    have noC : c ∉ verts2 (lk2 (insert {b, d, e} (insert {c, d, e}
        ((L.erase {b, c, d}).erase {b, c, e}))) b) := fun hm => by
      obtain ⟨f, hf, hcf⟩ := mem_verts2.mp hm
      obtain ⟨hbf, hmem⟩ := mem_lk2.mp hf
      simp only [mem_insert, mem_erase] at hmem
      rcases hmem with h | h | ⟨h2, h1, hL⟩
      · have : c ∈ ({b, d, e} : Finset V) := h ▸ mem_insert_of_mem hcf
        simp [hbc, hbd, hbe, hcd, hce, hde, hbc.symm, hbd.symm, hbe.symm, hcd.symm, hce.symm, hde.symm] at this
      · have : b ∈ ({c, d, e} : Finset V) := h ▸ mem_insert_self b f
        simp [hbc, hbd, hbe, hcd, hce, hde, hbc.symm, hbd.symm, hbe.symm, hcd.symm, hce.symm, hde.symm] at this
      · rcases hstar _ hL (fun y hy => by
          simp only [mem_insert, mem_singleton] at hy
          rcases hy with rfl | rfl
          · exact mem_insert_self _ _
          · exact mem_insert_of_mem hcf) with h | h
        exacts [h1 h, h2 h]
    have noB : b ∉ verts2 (lk2 (insert {b, d, e} (insert {c, d, e}
        ((L.erase {b, c, d}).erase {b, c, e}))) c) := fun hm => by
      obtain ⟨f, hf, hbf⟩ := mem_verts2.mp hm
      obtain ⟨hcf, hmem⟩ := mem_lk2.mp hf
      simp only [mem_insert, mem_erase] at hmem
      rcases hmem with h | h | ⟨h2, h1, hL⟩
      · have : c ∈ ({b, d, e} : Finset V) := h ▸ mem_insert_self c f
        simp [hbc, hbd, hbe, hcd, hce, hde, hbc.symm, hbd.symm, hbe.symm, hcd.symm, hce.symm, hde.symm] at this
      · have : b ∈ ({c, d, e} : Finset V) := h ▸ mem_insert_of_mem hbf
        simp [hbc, hbd, hbe, hcd, hce, hde, hbc.symm, hbd.symm, hbe.symm, hcd.symm, hce.symm, hde.symm] at this
      · rcases hstar _ hL (fun y hy => by
          simp only [mem_insert, mem_singleton] at hy
          rcases hy with rfl | rfl
          · exact mem_insert_of_mem hbf
          · exact mem_insert_self _ _) with h | h
        exacts [h1 h, h2 h]
    have noE : ∀ v ∈ ({d, e} : Finset V), ∀ y ∈ ({d, e} : Finset V), y ≠ v →
        y ∉ verts2 (lk2 L v) := fun v hv y hy hyv hm => by
      obtain ⟨f, hf, hyf⟩ := mem_verts2.mp hm
      obtain ⟨-, hL⟩ := mem_lk2.mp hf
      refine hfresh _ hL (fun z hz => ?_)
      simp only [mem_insert, mem_singleton] at hv hy hz
      rcases hz with rfl | rfl <;> rcases hv with rfl | rfl <;> rcases hy with rfl | rfl <;>
        first | exact absurd rfl hyv | exact mem_insert_self _ _ | exact mem_insert_of_mem hyf
    have kb : IsConnEdges (lk2 L b) ↔ IsConnEdges (lk2 (insert {b, d, e} (insert {c, d, e}
        ((L.erase {b, c, d}).erase {b, c, e}))) b) := by
      rw [lk2_flip22_b hbc hbd hbe hcd hce hde hbde hcde h₁ h₂]
      refine (connEdges_subdivide hde (mem_lk2.mpr ⟨by simp [hbc, hbd, hbe, hcd, hce, hde, hbc.symm, hbd.symm, hbe.symm, hcd.symm, hce.symm, hde.symm], by simp⟩) noC).symm
    have kc : IsConnEdges (lk2 L c) ↔ IsConnEdges (lk2 (insert {b, d, e} (insert {c, d, e}
        ((L.erase {b, c, d}).erase {b, c, e}))) c) := by
      rw [lk2_flip22_c hbc hbd hbe hcd hce hde hbde hcde h₁ h₂]
      refine (connEdges_subdivide hde (mem_lk2.mpr ⟨by simp [hbc, hbd, hbe, hcd, hce, hde, hbc.symm, hbd.symm, hbe.symm, hcd.symm, hce.symm, hde.symm], by simp⟩) noB).symm
    have kd : IsConnEdges (lk2 L d) ↔ IsConnEdges (lk2 (insert {b, d, e} (insert {c, d, e}
        ((L.erase {b, c, d}).erase {b, c, e}))) d) := by
      rw [lk2_flip22_d hbc hbd hbe hcd hce hde hbde hcde]
      refine connEdges_subdivide hbc (mem_lk2.mpr ⟨by simp [hbc, hbd, hbe, hcd, hce, hde, hbc.symm, hbd.symm, hbe.symm, hcd.symm, hce.symm, hde.symm], ?_⟩)
        (noE d (by simp) e (by simp) hde.symm)
      rw [show insert d ({b, c} : Finset V) = {b, c, d} by fset_eq]; exact h₁
    have ke : IsConnEdges (lk2 L e) ↔ IsConnEdges (lk2 (insert {b, d, e} (insert {c, d, e}
        ((L.erase {b, c, d}).erase {b, c, e}))) e) := by
      rw [lk2_flip22_e hbc hbd hbe hcd hce hde hbde hcde]
      refine connEdges_subdivide hbc (mem_lk2.mpr ⟨by simp [hbc, hbd, hbe, hcd, hce, hde, hbc.symm, hbd.symm, hbe.symm, hcd.symm, hce.symm, hde.symm], ?_⟩)
        (noE e (by simp) d (by simp) hde)
      rw [show insert e ({b, c} : Finset V) = {b, c, e} by fset_eq]; exact h₂
    unfold IsLinkConn
    rw [verts2_flip22 h₁ h₂]
    refine forall₂_congr fun v _ => ?_
    by_cases hvb : v = b
    · rw [hvb]; exact kb
    by_cases hvc : v = c
    · rw [hvc]; exact kc
    by_cases hvd : v = d
    · rw [hvd]; exact kd
    by_cases hve : v = e
    · rw [hve]; exact ke
    rw [lk2_flip22_other hvb hvc hvd hve]

/-! ## The forward direction -/

/-- Every triangle of `L` has three vertices. -/
def IsTri2 (L : Finset (Finset V)) : Prop := ∀ τ ∈ L, #τ = 3

/-- A 2-dimensional move keeps every triangle 3-element, in both directions. -/
theorem Move2.tri_iff {L L' : Finset (Finset V)} (h : Move2 L L') : IsTri2 L ↔ IsTri2 L' := by
  cases h with
  | @sub13 b c d x hbc hbd hcd hτ hx =>
    obtain ⟨hxb, hxc, hxd⟩ := sub13_fresh hτ hx
    constructor
    · intro H τ hτ'
      simp only [mem_insert, mem_erase] at hτ'
      rcases hτ' with rfl | rfl | rfl | ⟨-, hτL⟩
      · exact card_three hbc hxb.symm hxc.symm
      · exact card_three hcd hxc.symm hxd.symm
      · exact card_three hbd hxb.symm hxd.symm
      · exact H τ hτL
    · intro H τ hτL
      by_cases h : τ = {b, c, d}
      · rw [h]; exact card_three hbc hbd hcd
      · exact H τ (mem_insert_of_mem (mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨h, hτL⟩))))
  | @flip22 b c d e hbc hbd hbe hcd hce hde h₁ h₂ hstar hfresh =>
    constructor
    · intro H τ hτ'
      simp only [mem_insert, mem_erase] at hτ'
      rcases hτ' with rfl | rfl | ⟨-, -, hτL⟩
      · exact card_three hbd hbe hde
      · exact card_three hcd hce hde
      · exact H τ hτL
    · intro H τ hτL
      by_cases h1 : τ = {b, c, d}
      · rw [h1]; exact card_three hbc hbd hcd
      by_cases h2 : τ = {b, c, e}
      · rw [h2]; exact card_three hbc hbe hce
      exact H τ (mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨h2, mem_erase.mpr ⟨h1, hτL⟩⟩)))

section bdryLinks

-- The generated proofs pass every distinctness fact to `simp`; each uses only some.
set_option linter.unusedSimpArgs false

variable {a b c d : V} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
  (hcd : c ≠ d)
include hab hac had hbc hbd hcd

omit hbc hbd hcd in
lemma lk2_bdry_a : lk2 (bdry a b c d) a = {{b, c}, {c, d}, {b, d}} := by
  ext f
  simp only [mem_lk2]
  by_cases hv : a ∈ f
  · simp only [hv, not_true_eq_false, false_and, false_iff, mem_insert, mem_singleton, not_or]
    refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> simp [hab, hac, had, hab.symm, hac.symm, had.symm] at hv
  simp only [hv, not_false_eq_true, true_and, bdry, mem_insert, mem_singleton,
    insert_eq_iff_of_notMem hv]
  have e0 : ({a, b, c} : Finset V).erase a = {b, c} := by fset_eq
  have e1 : ({a, b, d} : Finset V).erase a = {b, d} := by fset_eq
  have e2 : ({a, c, d} : Finset V).erase a = {c, d} := by fset_eq
  have n : a ∉ ({b, c, d} : Finset V) := by simp [hab, hac, had, hab.symm, hac.symm, had.symm]
  simp only [e0, e1, e2, n, false_and, or_false, false_or, mem_insert, mem_singleton,
    hab, hac, had, hab.symm, hac.symm, had.symm, or_true, true_and, and_true]
  all_goals tauto
lemma lk2_bdry_b : lk2 (bdry a b c d) b = {{a, c}, {c, d}, {a, d}} := by
  ext f
  simp only [mem_lk2]
  by_cases hv : b ∈ f
  · simp only [hv, not_true_eq_false, false_and, false_iff, mem_insert, mem_singleton, not_or]
    refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> simp [hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm, had.symm, hbc.symm, hbd.symm, hcd.symm] at hv
  simp only [hv, not_false_eq_true, true_and, bdry, mem_insert, mem_singleton,
    insert_eq_iff_of_notMem hv]
  have e0 : ({a, b, c} : Finset V).erase b = {a, c} := by fset_eq
  have e1 : ({a, b, d} : Finset V).erase b = {a, d} := by fset_eq
  have e2 : ({b, c, d} : Finset V).erase b = {c, d} := by fset_eq
  have n : b ∉ ({a, c, d} : Finset V) := by simp [hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm, had.symm, hbc.symm, hbd.symm, hcd.symm]
  simp only [e0, e1, e2, n, false_and, or_false, false_or, mem_insert, mem_singleton,
    hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm, had.symm, hbc.symm, hbd.symm, hcd.symm, or_true, true_and, and_true]
  all_goals tauto
lemma lk2_bdry_c : lk2 (bdry a b c d) c = {{a, b}, {b, d}, {a, d}} := by
  ext f
  simp only [mem_lk2]
  by_cases hv : c ∈ f
  · simp only [hv, not_true_eq_false, false_and, false_iff, mem_insert, mem_singleton, not_or]
    refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> simp [hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm, had.symm, hbc.symm, hbd.symm, hcd.symm] at hv
  simp only [hv, not_false_eq_true, true_and, bdry, mem_insert, mem_singleton,
    insert_eq_iff_of_notMem hv]
  have e0 : ({a, b, c} : Finset V).erase c = {a, b} := by fset_eq
  have e1 : ({a, c, d} : Finset V).erase c = {a, d} := by fset_eq
  have e2 : ({b, c, d} : Finset V).erase c = {b, d} := by fset_eq
  have n : c ∉ ({a, b, d} : Finset V) := by simp [hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm, had.symm, hbc.symm, hbd.symm, hcd.symm]
  simp only [e0, e1, e2, n, false_and, or_false, false_or, mem_insert, mem_singleton,
    hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm, had.symm, hbc.symm, hbd.symm, hcd.symm, or_true, true_and, and_true]
  all_goals tauto
lemma lk2_bdry_d : lk2 (bdry a b c d) d = {{a, b}, {b, c}, {a, c}} := by
  ext f
  simp only [mem_lk2]
  by_cases hv : d ∈ f
  · simp only [hv, not_true_eq_false, false_and, false_iff, mem_insert, mem_singleton, not_or]
    refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> simp [hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm, had.symm, hbc.symm, hbd.symm, hcd.symm] at hv
  simp only [hv, not_false_eq_true, true_and, bdry, mem_insert, mem_singleton,
    insert_eq_iff_of_notMem hv]
  have e0 : ({a, b, d} : Finset V).erase d = {a, b} := by fset_eq
  have e1 : ({a, c, d} : Finset V).erase d = {a, c} := by fset_eq
  have e2 : ({b, c, d} : Finset V).erase d = {b, c} := by fset_eq
  have n : d ∉ ({a, b, c} : Finset V) := by simp [hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm, had.symm, hbc.symm, hbd.symm, hcd.symm]
  simp only [e0, e1, e2, n, false_and, or_false, false_or, mem_insert, mem_singleton,
    hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm, had.symm, hbc.symm, hbd.symm, hcd.symm, or_true, true_and, and_true]
  all_goals tauto

/-- The boundary of a tetrahedron is a triangulated 2-sphere in the intrinsic sense. -/
theorem isSurfaceSphere_bdry : IsSurfaceSphere (bdry a b c d) where
  card τ hτ := by
    simp only [bdry, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl
    · exact card_three hab hac hbc
    · exact card_three hab had hbd
    · exact card_three hac had hcd
    · exact card_three hbc hbd hcd
  closed := closed_bdry hab hac had hbc hbd hcd
  link v hv := by
    rcases mem_verts2_bdry hv with rfl | rfl | rfl | rfl
    · rw [lk2_bdry_a hab hac had]; exact connEdges_triangle
    · rw [lk2_bdry_b hab hac had hbc hbd hcd]; exact connEdges_triangle
    · rw [lk2_bdry_c hab hac had hbc hbd hcd]; exact connEdges_triangle
    · rw [lk2_bdry_d hab hac had hbc hbd hcd]; exact connEdges_triangle
  connected := (isSphere2_bdry hab hac had hbc hbd hcd).connected
  euler := euler2_bdry hab hac had hbc hbd hcd

end bdryLinks

/-- **Every combinatorial 2-sphere is a triangulated 2-sphere in the intrinsic sense.** -/
theorem IsSphere2.isSurfaceSphere {L : Finset (Finset V)} (hL : IsSphere2 L) :
    IsSurfaceSphere L := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, h⟩ := hL
  have key : ∀ L L' : Finset (Finset V), Relation.EqvGen Move2 L L' →
      ((IsTri2 L ↔ IsTri2 L') ∧ (IsLinkConn L ↔ IsLinkConn L')) := by
    intro L L' h
    induction h with
    | rel _ _ h => exact ⟨h.tri_iff, h.linkConn_iff⟩
    | refl => exact ⟨Iff.rfl, Iff.rfl⟩
    | symm _ _ _ ih => exact ⟨ih.1.symm, ih.2.symm⟩
    | trans _ _ _ _ _ ih₁ ih₂ => exact ⟨ih₁.1.trans ih₂.1, ih₁.2.trans ih₂.2⟩
  have hb := isSurfaceSphere_bdry hab hac had hbc hbd hcd
  have hS : IsSphere2 L := ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, h⟩
  exact ⟨(key _ _ h).1.mp hb.card, hS.closed, (key _ _ h).2.mp hb.link, hS.connected, hS.euler⟩

end Lightlike.PR
