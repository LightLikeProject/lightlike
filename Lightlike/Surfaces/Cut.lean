import Lightlike.Surfaces.Split
import Lightlike.Surfaces.Surgery

/-!
# Cutting a surface along a non-facial 3-cycle

Let `v` be a vertex of a closed surface `L` with consecutive link vertices `v₁, v₂, v₃, v₄`
(`v₁ ≠ v₄`) such that `v₁v₃` and `v₂v₄` are both edges. Then the 3-cycle `γ = v v₁ v₃` bounds no
triangle, and `L` is cut open along `γ` by 2D moves: three vertex splits (`Split.lean`) separate
the two sides of `γ` and leave a thin band of six triangles between them. Two cases occur.

* **Two-sided:** after one more flip the band is a tube `tube((v,v₁,v₃),(v',v₁',v₃'))`; replacing it
  by the two end triangles gives a surface `L'` with `χ(L') = χ(L) + 2` (the crossing edge `v₂v₄`
  keeps `L'` connected).
* **One-sided:** the band is a Möbius band whose boundary is the hexagon `v' v₁' v₃ v v₁ v₃'`;
  replacing it by a fan of four triangles from `v'` gives a surface `L'` with
  `χ(L') = χ(L) + 1`.

Both replacements are instances of the checked surgery of `Surgery.lean`.

* `cutTube`, `cutEnds`, `cutBand`, `cutCap`: the four templates, on the labels `0 = v`,
  `1 = v₁`, `2 = v₃`, `3 = v'`, `4 = v₁'`, `5 = v₃'`;
* `CutTo`: the outcome of a cut;
* `IsSurface.cut`: the cut exists.
-/

open Finset

namespace Lightlike.Surfaces

open Lightlike.PR

variable {V : Type*} [DecidableEq V]

/-! ## Embeddings with prescribed values -/

/-- With infinitely many vertices, a list of distinct vertices extends to an embedding of `ℕ`
whose values beyond the list avoid a given finite set. -/
lemma exists_emb [Infinite V] (l : List V) (hl : l.Nodup) (F : Finset V) :
    ∃ g : ℕ ↪ V, (∀ i (h : i < l.length), g i = l[i]) ∧ ∀ n, l.length ≤ n → g n ∉ F := by
  set F' := F ∪ l.toFinset
  have hinf : ((F' : Set V)ᶜ).Infinite := F'.finite_toSet.infinite_compl
  have := hinf.to_subtype
  let e : ℕ ↪ ((F' : Set V)ᶜ : Set V) := Infinite.natEmbedding _
  have he : ∀ n, (e n : V) ∉ F' := fun n => (e n).2
  let g : ℕ → V := fun n => if h : n < l.length then l[n] else (e (n - l.length) : V)
  have hg : Function.Injective g := by
    intro a b hab
    simp only [g] at hab
    by_cases ha : a < l.length <;> by_cases hb : b < l.length <;>
      simp only [ha, hb, ↓reduceDIte] at hab
    · exact (hl.getElem_inj_iff).mp hab
    · exact absurd (hab ▸ mem_union_right F (List.mem_toFinset.mpr (List.getElem_mem ha)))
        (he _)
    · exact absurd (hab ▸ mem_union_right F (List.mem_toFinset.mpr (List.getElem_mem hb)))
        (he _)
    · have := e.injective (Subtype.ext hab)
      omega
  refine ⟨⟨g, hg⟩, fun i h => by simp [g, h], fun n hn => ?_⟩
  have hn' : ¬ n < l.length := by omega
  simp only [Function.Embedding.coeFn_mk, g, hn', ↓reduceDIte]
  exact fun h => he _ (mem_union_left _ h)

/-! ## The vertices of a split complex -/

/-- The vertices of the split complex are those of `L` and the new vertex. -/
lemma mem_verts2_splitV {L : Finset (Finset V)} {u u' p q : V} {l : List V}
    (hu : u ∈ verts2 L) (hp : p ∈ verts2 L) (hq : q ∈ verts2 L) (hl : ∀ x ∈ l, x ∈ verts2 L)
    {x : V} (hx : x ∈ verts2 (splitV L u u' p q l)) : x = u' ∨ x ∈ verts2 L := by
  obtain ⟨τ, hτ, hxτ⟩ := mem_verts2.mp hx
  simp only [splitV, mem_insert, mem_union, mem_sdiff] at hτ
  rcases hτ with rfl | rfl | h | h
  · simp only [mem_insert, mem_singleton] at hxτ
    rcases hxτ with rfl | rfl | rfl
    · exact Or.inr hu
    · exact Or.inl rfl
    · exact Or.inr hp
  · simp only [mem_insert, mem_singleton] at hxτ
    rcases hxτ with rfl | rfl | rfl
    · exact Or.inr hu
    · exact Or.inl rfl
    · exact Or.inr hq
  · exact Or.inr (mem_verts2.mpr ⟨τ, h.1, hxτ⟩)
  · rcases (mem_fanT h).2 x hxτ with h' | h'
    · exact Or.inl h'
    · exact Or.inr (hl x h')

/-- A vertex `x ≠ u` of a triangle at `u` is a vertex of the link of `u`. -/
lemma mem_verts2_lk2 {M : Finset (Finset V)} {τ : Finset V} {u x : V} (hτ : τ ∈ M) (hu : u ∈ τ)
    (hx : x ∈ τ) (hxu : x ≠ u) : x ∈ verts2 (lk2 M u) :=
  mem_verts2.mpr ⟨τ.erase u, mem_lk2.mpr ⟨notMem_erase u τ, by rwa [insert_erase hu]⟩,
    mem_erase.mpr ⟨hxu, hx⟩⟩

/-! ## The templates -/

/-- The tube between the two sides of the cut, `tube((v,v₁,v₃),(v',v₁',v₃'))`. -/
def cutTube : Finset (Finset ℕ) := {{0, 1, 3}, {1, 3, 4}, {1, 2, 4}, {2, 4, 5}, {2, 0, 5}, {0, 5, 3}}

/-- The two end triangles `{v, v₁, v₃}` and `{v', v₁', v₃'}` of the tube. -/
def cutEnds : Finset (Finset ℕ) := {{0, 1, 2}, {3, 4, 5}}

/-- The Möbius band of the one-sided case. -/
def cutBand : Finset (Finset ℕ) := {{0, 3, 4}, {0, 3, 5}, {1, 4, 0}, {1, 4, 5}, {2, 5, 0}, {2, 5, 4}}

/-- The fan from `v'` over the boundary hexagon `v' v₁' v₃ v v₁ v₃'` of the Möbius band. -/
def cutCap : Finset (Finset ℕ) := {{3, 4, 2}, {3, 2, 0}, {3, 0, 1}, {3, 1, 5}}

set_option maxRecDepth 100000 in
/-- Replacing the tube by its two ends is an accepted surgery. -/
theorem surgOK_tube : SurgOK cutTube cutEnds [] := by decide +kernel

set_option maxRecDepth 100000 in
/-- Replacing the Möbius band by the fan is an accepted surgery, the two chords `v'v₃` and `v'v₁`
of the fan being safe. -/
theorem surgOK_band : SurgOK cutBand cutCap [(3, 2), (3, 1)] := by decide +kernel

lemma euler2_cutTube : euler2 cutTube = 0 := by decide +kernel
lemma euler2_cutEnds : euler2 cutEnds = 2 := by decide +kernel
lemma euler2_cutBand : euler2 cutBand = 0 := by decide +kernel
lemma euler2_cutCap : euler2 cutCap = 1 := by decide +kernel

set_option maxRecDepth 100000 in
lemma reach_cutCap : ∀ m ∈ verts2 cutCap, m ∈ reachAll (edges2 cutCap) 3 := by decide +kernel

lemma verts2_cutEnds : verts2 cutEnds = {0, 1, 2, 3, 4, 5} := by decide +kernel
lemma verts2_cutEnds_sub : ∀ n ∈ verts2 cutEnds, n ∈ verts2 cutTube := by decide +kernel
lemma verts2_cutCap_sub : ∀ n ∈ verts2 cutCap, n ∈ verts2 cutBand := by decide +kernel
lemma cutTube_lt : ∀ s ∈ cutTube, ∀ i ∈ s, i < 6 := by decide +kernel

/-! ## The outcome of a cut -/

/-- The **outcome of a cut** of `L`: `L` is related by moves to `A ∪ X` (the template `X` placed
by `g`), and replacing `X` by `Y` gives a closed surface `A ∪ Y` whose Euler characteristic is
that of `L` plus `k`. The labels from `6` on are fresh for `A`, and the pairs of `S` span no
triangle of `A`. -/
structure CutTo (L : Finset (Finset V)) (X Y : Finset (Finset ℕ)) (S : List (ℕ × ℕ)) (k : ℤ)
    (A : Finset (Finset V)) (g : ℕ ↪ V) : Prop where
  eqv : Relation.EqvGen Move2 L (A ∪ liftK g X)
  disjX : Disjoint A (liftK g X)
  disjY : Disjoint A (liftK g Y)
  surf : IsSurface (A ∪ liftK g Y)
  euler : euler2 (A ∪ liftK g Y) = euler2 L + k
  fresh : ∀ n, 6 ≤ n → g n ∉ verts2 A
  safe : ∀ p ∈ S, ∀ t ∈ A, ¬ ({g p.1, g p.2} : Finset V) ⊆ t

/-- A checked surgery on a surface `K` related to `L` by moves is the outcome of a cut. -/
lemma CutTo.of_surgery {L K : Finset (Finset V)} {g : ℕ ↪ V} {X Y : Finset (Finset ℕ)}
    {S S' : List (ℕ × ℕ)} {k : ℤ} (hL : Relation.EqvGen Move2 L K) (hK : IsSurface K)
    (hC : SurgCtx K g X Y S') (hok : SurgOK X Y S')
    (hconn : ∀ m₁ ∈ verts2 Y, ∀ m₂ ∈ verts2 Y,
      Relation.ReflTransGen (fun x y => ({x, y} : Finset V) ∈ edges2 (surg K g X Y)) (g m₁) (g m₂))
    (hk : euler2 Y = euler2 X + k) (hfr : ∀ n, 6 ≤ n → g n ∉ verts2 K)
    (hsafe : ∀ p ∈ S, ∀ t ∈ K, ¬ ({g p.1, g p.2} : Finset V) ⊆ t) :
    CutTo L X Y S k (K \ liftK g X) g where
  eqv := by rwa [sdiff_union_of_subset hC.sub]
  disjX := sdiff_disjoint
  disjY := disjoint_of_subset_left sdiff_subset hC.disj_Y
  surf := hK.surgery hC hok hconn
  euler := by
    have h1 := hC.euler2_surg hok hK.closed
    have h2 := euler2_eq_of_eqvGen hL
    rw [surg] at h1
    linarith
  fresh n hn := fun h => hfr n hn (verts2_mono sdiff_subset h)
  safe p hp t ht := hsafe p hp t (mem_sdiff.mp ht).1

omit [DecidableEq V] in
/-- Two finite sets differ when one has an element the other lacks. -/
lemma ne_of_witness {s t : Finset V} {x : V} (hs : x ∈ s) (ht : x ∉ t) : s ≠ t :=
  fun h => ht (h ▸ hs)

/-- **One-sided cut.** If the Möbius band sits in a surface `M` related to `L` by moves, with the
two chords `v'v₃`, `v'v₁` of the cap spanning no triangle, then replacing the band by the cap is a
cut raising the Euler characteristic by one. -/
lemma cut_one {L M : Finset (Finset V)} {g : ℕ ↪ V} (hL : Relation.EqvGen Move2 L M)
    (hM : IsSurface M) (hX : liftK g cutBand ⊆ M)
    (h32 : ∀ t ∈ M, ¬ ({g 3, g 2} : Finset V) ⊆ t) (h31 : ∀ t ∈ M, ¬ ({g 3, g 1} : Finset V) ⊆ t)
    (hfr : ∀ n, 6 ≤ n → g n ∉ verts2 M) :
    CutTo L cutBand cutCap [(3, 2), (3, 1)] 1 (M \ liftK g cutBand) g := by
  have hS : ∀ p ∈ [(3, 2), (3, 1)], ∀ t ∈ M, ¬ ({g p.1, g p.2} : Finset V) ⊆ t := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact h32
    · exact h31
  have hC : SurgCtx M g cutBand cutCap [(3, 2), (3, 1)] := by
    refine ⟨hX, fun n hn hn' => absurd (verts2_cutCap_sub n hn) hn', hS, ?_⟩
    intro t ht h
    simp only [cutCap, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl <;> simp only [map_insert, map_singleton] at h
    · exact h32 _ h (by simp [insert_subset_iff])
    · exact h32 _ h (by simp [insert_subset_iff])
    · exact h31 _ h (by simp [insert_subset_iff])
    · exact h31 _ h (by simp [insert_subset_iff])
  refine CutTo.of_surgery hL hM hC surgOK_band ?_ (by rw [euler2_cutBand, euler2_cutCap]; rfl)
    hfr hS
  exact hconn_of_reach subset_union_right reach_cutCap

/-- Proves an equality of two explicit sets of three elements listed in different orders. -/
macro "perm3" : tactic =>
  `(tactic| (clear * -; ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto))

/-- **Two-sided cut.** If the band between the two sides of the cut sits in a surface `M` related
to `L` by moves, one flip turns it into a tube; replacing the tube by its two ends is a cut raising
the Euler characteristic by two. The two sides stay joined through vertices `w₂`, `w₄` outside the
band. -/
lemma cut_two {L M : Finset (Finset V)} {g : ℕ ↪ V} {w₂ w₄ : V} (hL : Relation.EqvGen Move2 L M)
    (hM : IsSurface M)
    (h034 : ({g 0, g 3, g 4} : Finset V) ∈ M) (h035 : ({g 0, g 3, g 5} : Finset V) ∈ M)
    (h140 : ({g 1, g 4, g 0} : Finset V) ∈ M) (h250 : ({g 2, g 5, g 0} : Finset V) ∈ M)
    (h254 : ({g 2, g 5, g 4} : Finset V) ∈ M) (h142 : ({g 1, g 4, g 2} : Finset V) ∈ M)
    (hσ : ({g 0, g 1, g 2} : Finset V) ∉ M) (hσ' : ({g 3, g 4, g 5} : Finset V) ∉ M)
    (h31 : ∀ t ∈ M, ¬ (g 3 ∈ t ∧ g 1 ∈ t)) (h23 : ∀ t ∈ M, ¬ (g 2 ∈ t ∧ g 3 ∈ t))
    (h15 : ∀ t ∈ M, ¬ (g 1 ∈ t ∧ g 5 ∈ t))
    (hw₂ : ∀ i < 6, w₂ ≠ g i) (hw₄ : ∀ i < 6, w₄ ≠ g i) (hw : w₂ ≠ w₄)
    (e04 : ∃ t ∈ M, g 0 ∈ t ∧ w₄ ∈ t) (e42 : ∃ t ∈ M, w₄ ∈ t ∧ w₂ ∈ t)
    (e23 : ∃ t ∈ M, w₂ ∈ t ∧ g 3 ∈ t)
    (hfr : ∀ n, 6 ≤ n → g n ∉ verts2 M) :
    ∃ A, CutTo L cutTube cutEnds [(0, 4), (1, 5), (2, 3)] 2 A g := by
  have gne : ∀ i j, i ≠ j → g i ≠ g j := fun i j h => g.injective.ne h
  have h₁ : ({g 0, g 4, g 3} : Finset V) ∈ M := by
    rwa [show ({g 0, g 4, g 3} : Finset V) = {g 0, g 3, g 4} by perm3]
  have h₂ : ({g 0, g 4, g 1} : Finset V) ∈ M := by
    rwa [show ({g 0, g 4, g 1} : Finset V) = {g 1, g 4, g 0} by perm3]
  have hstar := hM.tris_at_edge h₁ h₂ (gne 3 1 (by decide))
  have hmv := Move2.flip22 (gne 0 4 (by decide)) (gne 0 3 (by decide)) (gne 0 1 (by decide))
    (gne 4 3 (by decide)) (gne 4 1 (by decide)) (gne 3 1 (by decide)) h₁ h₂ hstar
    (fun t ht hsub => h31 t ht ⟨hsub (by simp), hsub (by simp)⟩)
  obtain ⟨K, hKdef⟩ : ∃ K : Finset (Finset V), K = insert {g 0, g 3, g 1}
      (insert {g 4, g 3, g 1} ((M.erase {g 0, g 4, g 3}).erase {g 0, g 4, g 1})) := ⟨_, rfl⟩
  rw [← hKdef] at hmv
  have hK : IsSurface K := (Move2.isSurface_iff hmv).mp hM
  have hLK : Relation.EqvGen Move2 L K := hL.trans _ _ _ (.rel _ _ hmv)
  have hK1 : ({g 0, g 3, g 1} : Finset V) ∈ K := by rw [hKdef]; exact mem_insert_self _ _
  have hK2 : ({g 4, g 3, g 1} : Finset V) ∈ K := by
    rw [hKdef]; exact mem_insert_of_mem (mem_insert_self _ _)
  have keep : ∀ t ∈ M, t ≠ {g 0, g 4, g 3} → t ≠ {g 0, g 4, g 1} → t ∈ K := fun t ht h1 h2 => by
    rw [hKdef]
    exact mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨h2, mem_erase.mpr ⟨h1, ht⟩⟩))
  have cases : ∀ t ∈ K, t = {g 0, g 3, g 1} ∨ t = {g 4, g 3, g 1} ∨
      (t ∈ M ∧ t ≠ {g 0, g 4, g 3} ∧ t ≠ {g 0, g 4, g 1}) := by
    intro t ht
    rw [hKdef, mem_insert, mem_insert, mem_erase, mem_erase] at ht
    rcases ht with h | h | ⟨h2, h1, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨h, h1, h2⟩)
  -- the tube lies in `K`
  have hX : liftK g cutTube ⊆ K := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := mem_liftK.mp ht
    simp only [cutTube, mem_insert, mem_singleton] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [map_insert, map_singleton]
    · rwa [show ({g 0, g 1, g 3} : Finset V) = {g 0, g 3, g 1} by perm3]
    · rwa [show ({g 1, g 3, g 4} : Finset V) = {g 4, g 3, g 1} by perm3]
    · refine keep _ (by rwa [show ({g 1, g 2, g 4} : Finset V) = {g 1, g 4, g 2} by perm3]) ?_ ?_
      · exact ne_of_witness (x := g 1) (by simp) (by simp)
      · exact ne_of_witness (x := g 2) (by simp) (by simp)
    · refine keep _ (by rwa [show ({g 2, g 4, g 5} : Finset V) = {g 2, g 5, g 4} by perm3]) ?_ ?_ <;>
        exact ne_of_witness (x := g 2) (by simp) (by simp)
    · refine keep _ (by rwa [show ({g 2, g 0, g 5} : Finset V) = {g 2, g 5, g 0} by perm3]) ?_ ?_ <;>
        exact ne_of_witness (x := g 2) (by simp) (by simp)
    · refine keep _ (by rwa [show ({g 0, g 5, g 3} : Finset V) = {g 0, g 3, g 5} by perm3]) ?_ ?_ <;>
        exact ne_of_witness (x := g 5) (by simp) (by simp)
  -- the two ends are not in `K`
  have hnew : ∀ t ∈ cutEnds, t.map g ∉ K := by
    intro t ht h
    simp only [cutEnds, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl <;> simp only [map_insert, map_singleton] at h <;>
      rcases cases _ h with h | h | ⟨h, -, -⟩
    · exact ne_of_witness (x := g 2) (by simp) (by simp) h
    · exact ne_of_witness (x := g 0) (by simp) (by simp) h
    · exact hσ h
    · exact ne_of_witness (x := g 4) (by simp) (by simp) h
    · exact ne_of_witness (x := g 5) (by simp) (by simp) h
    · exact hσ' h
  have hC : SurgCtx K g cutTube cutEnds [] :=
    ⟨hX, fun n hn hn' => absurd (verts2_cutEnds_sub n hn) hn', by simp, hnew⟩
  -- the pairs `v v₁'`, `v₁ v₃'`, `v₃ v'` span no triangle of `K`
  have hsafe : ∀ p ∈ [(0, 4), (1, 5), (2, 3)], ∀ t ∈ K, ¬ ({g p.1, g p.2} : Finset V) ⊆ t := by
    intro p hp t ht hsub
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> dsimp only at hsub <;>
      rcases cases t ht with rfl | rfl | ⟨h, h1, h2⟩
    all_goals try (simp [insert_subset_iff] at hsub; done)
    · rcases hstar t h hsub with rfl | rfl
      · exact h1 rfl
      · exact h2 rfl
    · exact h15 t h ⟨hsub (by simp), hsub (by simp)⟩
    · exact h23 t h ⟨hsub (by simp), hsub (by simp)⟩
  have hfrK : ∀ n, 6 ≤ n → g n ∉ verts2 K := by
    intro n hn h
    obtain ⟨t, ht, hnt⟩ := mem_verts2.mp h
    rcases cases t ht with rfl | rfl | ⟨h', -, -⟩
    · simp at hnt; omega
    · simp at hnt; omega
    · exact hfr n hn (mem_verts2.mpr ⟨t, h', hnt⟩)
  -- a triangle of `M` with a vertex outside the band survives the flip and the surgery
  have surv : ∀ t ∈ M, ∀ w, (∀ i < 6, w ≠ g i) → w ∈ t → t ∈ surg K g cutTube cutEnds := by
    intro t ht w hw' hwt
    refine mem_surg.mpr (Or.inl ⟨keep t ht ?_ ?_, ?_⟩)
    · exact ne_of_witness hwt (by simp [hw' 0 (by norm_num), hw' 4 (by norm_num),
        hw' 3 (by norm_num)])
    · exact ne_of_witness hwt (by simp [hw' 0 (by norm_num), hw' 4 (by norm_num),
        hw' 1 (by norm_num)])
    · intro hX'
      obtain ⟨s, hs, rfl⟩ := mem_liftK.mp hX'
      obtain ⟨i, hi, rfl⟩ := mem_map.mp hwt
      exact hw' i (cutTube_lt s hs i hi) rfl
  have hY : ∀ s ∈ cutEnds, s.map g ∈ surg K g cutTube cutEnds := fun s hs =>
    mem_surg.mpr (Or.inr (map_mem_liftK.mpr hs))
  have hσS : ({g 0, g 1, g 2} : Finset V) ∈ surg K g cutTube cutEnds := by
    simpa only [map_insert, map_singleton] using hY {0, 1, 2} (by decide)
  have hσ'S : ({g 3, g 4, g 5} : Finset V) ∈ surg K g cutTube cutEnds := by
    simpa only [map_insert, map_singleton] using hY {3, 4, 5} (by decide)
  have to0 : ∀ m ∈ verts2 cutEnds, Relation.ReflTransGen
      (fun x y => ({x, y} : Finset V) ∈ edges2 (surg K g cutTube cutEnds)) (g m) (g 0) := by
    obtain ⟨t₁, ht₁, h0₁, h4₁⟩ := e04
    obtain ⟨t₂, ht₂, h4₂, h2₂⟩ := e42
    obtain ⟨t₃, ht₃, h2₃, h3₃⟩ := e23
    have path3 : Relation.ReflTransGen
        (fun x y => ({x, y} : Finset V) ∈ edges2 (surg K g cutTube cutEnds)) (g 3) (g 0) :=
      ((Relation.ReflTransGen.single
        (pair_mem_edges2 (surv t₃ ht₃ w₂ hw₂ h2₃) h3₃ h2₃ (hw₂ 3 (by norm_num)).symm)).tail
        (pair_mem_edges2 (surv t₂ ht₂ w₂ hw₂ h2₂) h2₂ h4₂ hw)).tail
        (pair_mem_edges2 (surv t₁ ht₁ w₄ hw₄ h4₁) h4₁ h0₁ (hw₄ 0 (by norm_num)))
    intro m hm
    rw [verts2_cutEnds] at hm
    simp only [mem_insert, mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    · exact .refl
    · exact .single (pair_mem_edges2 hσS (by simp) (by simp) (gne 1 0 (by decide)))
    · exact .single (pair_mem_edges2 hσS (by simp) (by simp) (gne 2 0 (by decide)))
    · exact path3
    · exact .head (pair_mem_edges2 hσ'S (by simp) (by simp) (gne 4 3 (by decide))) path3
    · exact .head (pair_mem_edges2 hσ'S (by simp) (by simp) (gne 5 3 (by decide))) path3
  refine ⟨_, CutTo.of_surgery hLK hK hC surgOK_tube ?_
    (by rw [euler2_cutTube, euler2_cutEnds]; rfl) hfrK hsafe⟩
  intro m₁ h₁ m₂ h₂
  exact (to0 m₁ h₁).trans (rtg_pair_symm (to0 m₂ h₂))

/-- Replacing the last vertex `c` of the triangle `{a, b, c}` by `d`. -/
lemma insert_erase_last {a b c d : V} (hac : a ≠ c) (hbc : b ≠ c) :
    insert d (({a, b, c} : Finset V).erase c) = {d, a, b} := by
  rw [erase_insert_of_ne hac, erase_insert_of_ne hbc, erase_singleton, insert_empty]

/-! ## The three splits -/

/-- **The third split and the cut.** In a surface `M` related to `L` by moves, after the splits of
`v` and `v₁`, split `v₃` along its link arc from `v` through `v'` to `v₁'`, with new vertex `v₃'`.
If the arc ends with `v₁, v₁'`, the band is one-sided; otherwise it is two-sided. -/
lemma cut_final {L M : Finset (Finset V)} {g : ℕ ↪ V} {w₂ w₄ : V}
    (hL : Relation.EqvGen Move2 L M) (hM : IsSurface M)
    (h140 : ({g 1, g 4, g 0} : Finset V) ∈ M) (h142 : ({g 1, g 4, g 2} : Finset V) ∈ M)
    (h403 : ({g 4, g 0, g 3} : Finset V) ∈ M) (h032 : ({g 0, g 3, g 2} : Finset V) ∈ M)
    (h13 : ∀ t ∈ M, ¬ (g 1 ∈ t ∧ g 3 ∈ t))
    (hσ : ({g 0, g 1, g 2} : Finset V) ∉ M) (hσ' : ({g 2, g 3, g 4} : Finset V) ∉ M)
    (hw₂ : ∀ i < 6, w₂ ≠ g i) (hw₄ : ∀ i < 6, w₄ ≠ g i) (hw : w₂ ≠ w₄)
    (e04 : ∃ t ∈ M, g 0 ∈ t ∧ w₄ ∈ t) (e42 : ∃ t ∈ M, w₄ ∈ t ∧ w₂ ∈ t)
    (e23 : ∃ t ∈ M, w₂ ∈ t ∧ g 3 ∈ t)
    (hfr : ∀ n, 5 ≤ n → g n ∉ verts2 M) :
    (∃ A, CutTo L cutTube cutEnds [(0, 4), (1, 5), (2, 3)] 2 A g) ∨
      ∃ A, CutTo L cutBand cutCap [(3, 2), (3, 1)] 1 A g := by
  have gne : ∀ i j, i ≠ j → g i ≠ g j := fun i j h => g.injective.ne h
  -- the arc at `v₃` from `v` through `v'` to `v₁'`
  have hτ : ({g 2, g 0, g 3} : Finset V) ∈ M := by
    rwa [show ({g 2, g 0, g 3} : Finset V) = {g 0, g 3, g 2} by perm3]
  have hq : g 4 ∈ verts2 (lk2 M (g 2)) :=
    mem_verts2_lk2 h142 (by simp) (by simp) (gne 4 2 (by decide))
  obtain ⟨l, hnd, hul, hch, hlast⟩ := hM.exists_arc hτ hq (gne 4 0 (by decide))
  have hlast' : (g 0 :: g 3 :: l).getLast? = some (g 4) := by rwa [List.getLast?_cons_cons]
  have hg5 : g 5 ∉ verts2 M := hfr 5 le_rfl
  have hg5' : ∀ t ∈ M, g 5 ∉ t := fun t ht h => hg5 (mem_verts2.mpr ⟨t, ht, h⟩)
  have hlv : ∀ a ∈ g 0 :: g 3 :: l, a ∈ verts2 M := mem_verts2_of_chain hch
  have h5l : g 5 ∉ g 0 :: g 3 :: l := fun h => hg5 (hlv _ h)
  have hF : fanT (g 2) (g 0 :: g 3 :: l) ⊆ M := fanT_subset hch
  have hst := hM.split_steps hg5 l (g 0) (g 3) (g 4) hnd hul hch hlast
  obtain ⟨N, hN⟩ : ∃ N, N = splitV M (g 2) (g 5) (g 0) (g 4) (g 0 :: g 3 :: l) := ⟨_, rfl⟩
  rw [← hN] at hst
  have hMN := Relation.EqvGen.reflTransGen_le_eqvGen _ _ _ hst
  have hLN : Relation.EqvGen Move2 L N := hL.trans _ _ _ hMN
  have hSN : IsSurface N := (isSurface_iff_of_eqvGen hMN).mp hM
  -- the band
  have h034 : ({g 0, g 3, g 4} : Finset V) ∈ N := by
    rw [show ({g 0, g 3, g 4} : Finset V) = {g 4, g 0, g 3} by perm3, hN]
    exact mem_splitV_of_notMem h403 (by simp)
  have h035 : ({g 0, g 3, g 5} : Finset V) ∈ N := by
    rw [show ({g 0, g 3, g 5} : Finset V) = {g 5, g 0, g 3} by perm3, hN]
    exact mem_splitV_of_mem_fanT (by rw [fanT]; exact mem_insert_self _ _)
  have h140' : ({g 1, g 4, g 0} : Finset V) ∈ N := by
    rw [hN]; exact mem_splitV_of_notMem h140 (by simp)
  have h250 : ({g 2, g 5, g 0} : Finset V) ∈ N := by
    rw [hN, splitV]; exact mem_insert_self _ _
  have h254 : ({g 2, g 5, g 4} : Finset V) ∈ N := by
    rw [hN, splitV]; exact mem_insert_of_mem (mem_insert_self _ _)
  -- the two sides of the cut are not triangles
  have hσN : ({g 0, g 1, g 2} : Finset V) ∉ N := by
    intro h
    rw [hN] at h
    rcases mem_splitV_cases h with h | h
    · exact hσ h
    · simp at h
  have hσ'N : ({g 3, g 4, g 5} : Finset V) ∉ N := by
    intro h
    rw [hN] at h
    rcases mem_splitV_new h5l hg5' h (by simp) with h | h | h
    · exact ne_of_witness (x := g 3) (by simp) (by simp) h
    · exact ne_of_witness (x := g 3) (by simp) (by simp) h
    · rw [insert_erase_last (by simp) (by simp)] at h
      exact hσ' (hF h)
  -- the safe pairs
  have h23 : ∀ t ∈ N, ¬ (g 2 ∈ t ∧ g 3 ∈ t) := by
    rw [hN]
    exact notMem_splitV_interior hM.closed hnd hul hF
      (exists_interior_split (by simp) rfl hlast' (gne 3 0 (by decide)) (gne 3 4 (by decide)))
      (gne 3 0 (by decide)) (gne 3 4 (by decide)) (gne 3 5 (by decide)) (gne 2 5 (by decide))
  have h13N : ∀ t ∈ N, ¬ (g 1 ∈ t ∧ g 3 ∈ t) := by
    intro t ht h
    rw [hN] at ht
    obtain ⟨t', ht', h'⟩ := (pair_splitV_iff hul h5l hF (gne 1 3 (by decide))
      (gne 1 2 (by decide)) (gne 1 5 (by decide)) (gne 3 2 (by decide))
      (gne 3 5 (by decide))).mp ⟨t, ht, h⟩
    exact h13 t' ht' h'
  have hfrN : ∀ n, 6 ≤ n → g n ∉ verts2 N := by
    intro n hn h
    rw [hN] at h
    have hg2 : g 2 ∈ verts2 M := mem_verts2.mpr ⟨_, h142, by simp⟩
    have hg4 : g 4 ∈ verts2 M := mem_verts2.mpr ⟨_, h142, by simp⟩
    rcases mem_verts2_splitV hg2 (hlv _ (by simp)) hg4 hlv h with h | h
    · exact gne n 5 (by omega) h
    · exact hfr n (by omega) h
  by_cases hts : ({g 1, g 4, g 2} : Finset V) ∈ fanT (g 2) (g 0 :: g 3 :: l)
  · -- one-sided: the arc ends with `v₁, v₁'`, and the band is a Möbius band
    right
    have h145 : ({g 1, g 4, g 5} : Finset V) ∈ N := by
      have h := fanT_rename (g 5) hul _ hts
      rw [insert_erase_last (by simp) (by simp)] at h
      rw [show ({g 1, g 4, g 5} : Finset V) = {g 5, g 1, g 4} by perm3, hN]
      exact mem_splitV_of_mem_fanT h
    have hX : liftK g cutBand ⊆ N := by
      intro t ht
      obtain ⟨s, hs, rfl⟩ := mem_liftK.mp ht
      simp only [cutBand, mem_insert, mem_singleton] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [map_insert, map_singleton]
      · exact h034
      · exact h035
      · exact h140'
      · exact h145
      · exact h250
      · exact h254
    exact ⟨_, cut_one hLN hSN hX (fun t ht hs => h23 t ht ⟨hs (by simp), hs (by simp)⟩)
      (fun t ht hs => h13N t ht ⟨hs (by simp), hs (by simp)⟩) hfrN⟩
  · -- two-sided
    left
    have h142N : ({g 1, g 4, g 2} : Finset V) ∈ N := by
      rw [hN]; exact mem_splitV_of_notMem_fanT h142 hts
    have h15 : ∀ t ∈ N, ¬ (g 1 ∈ t ∧ g 5 ∈ t) := by
      rintro t ht ⟨h1, h5⟩
      rw [hN] at ht
      rcases mem_splitV_new h5l hg5' ht h5 with rfl | rfl | h
      · simp at h1
      · simp at h1
      · have hm : g 1 ∈ g 0 :: g 3 :: l := by
          rcases (mem_fanT h).2 (g 1)
              (mem_insert_of_mem (mem_erase.mpr ⟨gne 1 5 (by decide), h1⟩)) with h | h
          · exact absurd h (gne 1 2 (by decide))
          · exact h
        obtain ⟨l₁, a, b, l₂, hl⟩ := exists_interior_split hm rfl hlast' (gne 1 0 (by decide))
          (gne 1 4 (by decide))
        exact hts (mem_fanT_of_interior hM.closed hnd hul hF hl h142 (by simp) (by simp))
    have edge : ∀ {x y : V}, x ≠ y → x ≠ g 2 → x ≠ g 5 → y ≠ g 2 → y ≠ g 5 →
        (∃ t ∈ M, x ∈ t ∧ y ∈ t) → ∃ t ∈ N, x ∈ t ∧ y ∈ t := fun hxy h1 h2 h3 h4 h => by
      rw [hN]; exact (pair_splitV_iff hul h5l hF hxy h1 h2 h3 h4).mpr h
    exact cut_two hLN hSN h034 h035 h140' h250 h254 h142N hσN hσ'N
      (fun t ht h => h13N t ht ⟨h.2, h.1⟩) h23 h15 hw₂ hw₄ hw
      (edge (hw₄ 0 (by norm_num)).symm (gne 0 2 (by decide)) (gne 0 5 (by decide))
        (hw₄ 2 (by norm_num)) (hw₄ 5 (by norm_num)) e04)
      (edge hw.symm (hw₄ 2 (by norm_num)) (hw₄ 5 (by norm_num)) (hw₂ 2 (by norm_num))
        (hw₂ 5 (by norm_num)) e42)
      (edge (hw₂ 3 (by norm_num)) (hw₂ 2 (by norm_num)) (hw₂ 5 (by norm_num))
        (gne 3 2 (by decide)) (gne 3 5 (by decide)) e23)
      hfrN

/-- **The second split.** After the split of `v`, split `v₁` along its link arc from `v` through
`v'` to `v₃`, with new vertex `v₁'`; then continue with `cut_final`. -/
lemma cut_mid {L M : Finset (Finset V)} {g : ℕ ↪ V} {w₂ w₄ : V}
    (hL : Relation.EqvGen Move2 L M) (hM : IsSurface M)
    (h031 : ({g 0, g 3, g 1} : Finset V) ∈ M) (h032 : ({g 0, g 3, g 2} : Finset V) ∈ M)
    (e12 : ∃ t ∈ M, g 1 ∈ t ∧ g 2 ∈ t)
    (hσ : ({g 0, g 1, g 2} : Finset V) ∉ M) (hσ' : ({g 1, g 2, g 3} : Finset V) ∉ M)
    (hw₂ : ∀ i < 6, w₂ ≠ g i) (hw₄ : ∀ i < 6, w₄ ≠ g i) (hw : w₂ ≠ w₄)
    (e04 : ∃ t ∈ M, g 0 ∈ t ∧ w₄ ∈ t) (e42 : ∃ t ∈ M, w₄ ∈ t ∧ w₂ ∈ t)
    (e23 : ∃ t ∈ M, w₂ ∈ t ∧ g 3 ∈ t)
    (hfr : ∀ n, 4 ≤ n → g n ∉ verts2 M) :
    (∃ A, CutTo L cutTube cutEnds [(0, 4), (1, 5), (2, 3)] 2 A g) ∨
      ∃ A, CutTo L cutBand cutCap [(3, 2), (3, 1)] 1 A g := by
  have gne : ∀ i j, i ≠ j → g i ≠ g j := fun i j h => g.injective.ne h
  -- the arc at `v₁` from `v` through `v'` to `v₃`
  have hτ : ({g 1, g 0, g 3} : Finset V) ∈ M := by
    rwa [show ({g 1, g 0, g 3} : Finset V) = {g 0, g 3, g 1} by perm3]
  obtain ⟨t₁₂, ht₁₂, h1, h2⟩ := e12
  have hq : g 2 ∈ verts2 (lk2 M (g 1)) := mem_verts2_lk2 ht₁₂ h1 h2 (gne 2 1 (by decide))
  obtain ⟨l, hnd, hul, hch, hlast⟩ := hM.exists_arc hτ hq (gne 2 0 (by decide))
  have hlast' : (g 0 :: g 3 :: l).getLast? = some (g 2) := by rwa [List.getLast?_cons_cons]
  have hg4 : g 4 ∉ verts2 M := hfr 4 le_rfl
  have hg4' : ∀ t ∈ M, g 4 ∉ t := fun t ht h => hg4 (mem_verts2.mpr ⟨t, ht, h⟩)
  have hlv : ∀ a ∈ g 0 :: g 3 :: l, a ∈ verts2 M := mem_verts2_of_chain hch
  have h4l : g 4 ∉ g 0 :: g 3 :: l := fun h => hg4 (hlv _ h)
  have hF : fanT (g 1) (g 0 :: g 3 :: l) ⊆ M := fanT_subset hch
  have hst := hM.split_steps hg4 l (g 0) (g 3) (g 2) hnd hul hch hlast
  obtain ⟨N, hN⟩ : ∃ N, N = splitV M (g 1) (g 4) (g 0) (g 2) (g 0 :: g 3 :: l) := ⟨_, rfl⟩
  rw [← hN] at hst
  have hMN := Relation.EqvGen.reflTransGen_le_eqvGen _ _ _ hst
  have edge : ∀ {x y : V}, x ≠ y → x ≠ g 1 → x ≠ g 4 → y ≠ g 1 → y ≠ g 4 →
      (∃ t ∈ M, x ∈ t ∧ y ∈ t) → ∃ t ∈ N, x ∈ t ∧ y ∈ t := fun hxy h1 h2 h3 h4 h => by
    rw [hN]; exact (pair_splitV_iff hul h4l hF hxy h1 h2 h3 h4).mpr h
  refine cut_final (hL.trans _ _ _ hMN) ((isSurface_iff_of_eqvGen hMN).mp hM) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    hw₂ hw₄ hw ?_ ?_ ?_ ?_
  · rw [hN, splitV]; exact mem_insert_self _ _
  · rw [hN, splitV]; exact mem_insert_of_mem (mem_insert_self _ _)
  · rw [hN]; exact mem_splitV_of_mem_fanT (by rw [fanT]; exact mem_insert_self _ _)
  · rw [hN]; exact mem_splitV_of_notMem h032 (by simp)
  · rw [hN]
    exact notMem_splitV_interior hM.closed hnd hul hF
      (exists_interior_split (by simp) rfl hlast' (gne 3 0 (by decide)) (gne 3 2 (by decide)))
      (gne 3 0 (by decide)) (gne 3 2 (by decide)) (gne 3 4 (by decide)) (gne 1 4 (by decide))
  · intro h
    rw [hN] at h
    rcases mem_splitV_cases h with h | h
    · exact hσ h
    · simp at h
  · intro h
    rw [hN] at h
    rcases mem_splitV_new h4l hg4' h (by simp) with h | h | h
    · exact ne_of_witness (x := g 2) (by simp) (by simp) h
    · exact ne_of_witness (x := g 3) (by simp) (by simp) h
    · rw [insert_erase_last (by simp) (by simp)] at h
      exact hσ' (hF h)
  · exact edge (hw₄ 0 (by norm_num)).symm (gne 0 1 (by decide)) (gne 0 4 (by decide))
      (hw₄ 1 (by norm_num)) (hw₄ 4 (by norm_num)) e04
  · exact edge hw.symm (hw₄ 1 (by norm_num)) (hw₄ 4 (by norm_num)) (hw₂ 1 (by norm_num))
      (hw₂ 4 (by norm_num)) e42
  · exact edge (hw₂ 3 (by norm_num)) (hw₂ 1 (by norm_num)) (hw₂ 4 (by norm_num))
      (gne 3 1 (by decide)) (gne 3 4 (by decide)) e23
  · intro n hn h
    rw [hN] at h
    rcases mem_verts2_splitV (mem_verts2.mpr ⟨_, h031, by simp⟩) (hlv _ (by simp))
      (mem_verts2.mpr ⟨_, h032, by simp⟩) hlv h with h | h
    · exact gne n 4 (by omega) h
    · exact hfr n (by omega) h

/-- **Cutting along a non-facial 3-cycle.** Let `v₁, v₂, v₃, v₄` be consecutive vertices of the
link of `v` in a closed surface `L` (that is, `{v, v₁, v₂}`, `{v, v₂, v₃}`, `{v, v₃, v₄}` are
triangles), with `v₁ ≠ v₃`, `v₂ ≠ v₄`, `v₁ ≠ v₄`, such that `v₁v₃` and `v₂v₄` are edges. Then `L`
is related by 2D moves to a surface containing a tube (two-sided case) or a Möbius band
(one-sided case) along the 3-cycle `v v₁ v₃`, and replacing it by two triangles, respectively a fan
of four triangles, gives a closed surface whose Euler characteristic is larger by two,
respectively by one. -/
theorem IsSurface.cut [Infinite V] {L : Finset (Finset V)} (hS : IsSurface L)
    {v v₁ v₂ v₃ v₄ : V} (h₁ : ({v, v₁, v₂} : Finset V) ∈ L) (h₂ : ({v, v₂, v₃} : Finset V) ∈ L)
    (h₃ : ({v, v₃, v₄} : Finset V) ∈ L) (h13 : v₁ ≠ v₃) (h24 : v₂ ≠ v₄) (h14 : v₁ ≠ v₄)
    (e13 : ∃ τ ∈ L, v₁ ∈ τ ∧ v₃ ∈ τ) (e24 : ∃ τ ∈ L, v₂ ∈ τ ∧ v₄ ∈ τ) :
    (∃ A g, CutTo L cutTube cutEnds [(0, 4), (1, 5), (2, 3)] 2 A g) ∨
      ∃ A g, CutTo L cutBand cutCap [(3, 2), (3, 1)] 1 A g := by
  obtain ⟨hvv1, hvv2, hv1v2⟩ := tri_ne (hS.card _ h₁)
  obtain ⟨-, hvv3, hv2v3⟩ := tri_ne (hS.card _ h₂)
  obtain ⟨-, hvv4, hv3v4⟩ := tri_ne (hS.card _ h₃)
  obtain ⟨g, hgl, hgF⟩ := exists_emb [v, v₁, v₃] (by simp [hvv1, hvv3, h13]) (verts2 L)
  have g0 : g 0 = v := hgl 0 (by simp)
  have g1 : g 1 = v₁ := hgl 1 (by simp)
  have g2 : g 2 = v₃ := hgl 2 (by simp)
  subst g0 g1 g2
  have hfr : ∀ n, 3 ≤ n → g n ∉ verts2 L := fun n hn => hgF n (by simpa using hn)
  have gne : ∀ i j, i ≠ j → g i ≠ g j := fun i j h => g.injective.ne h
  -- the 3-cycle bounds no triangle
  have hσ : ({g 0, g 1, g 2} : Finset V) ∉ L := by
    intro h
    have h₂' : ({g 0, g 2, v₂} : Finset V) ∈ L := by
      rwa [show ({g 0, g 2, v₂} : Finset V) = {g 0, v₂, g 2} by perm3]
    rcases hS.tris_at_edge h₂' h₃ h24 _ h (by simp [insert_subset_iff]) with h' | h'
    · exact ne_of_witness (x := g 1) (by simp) (by simp [hv1v2]) h'
    · exact ne_of_witness (x := g 1) (by simp) (by simp [h14]) h'
  -- the first split: `v` along `v₁, v₂, v₃`, with new vertex `v'`
  have hg3 : g 3 ∉ verts2 L := hfr 3 le_rfl
  have hg3' : ∀ t ∈ L, g 3 ∉ t := fun t ht h => hg3 (mem_verts2.mpr ⟨t, ht, h⟩)
  have hnd : [g 1, v₂, g 2].Nodup := by simp [hv1v2, hv2v3]
  have hul : g 0 ∉ [g 1, v₂, g 2] := by simp [hvv2]
  have hch : [g 1, v₂, g 2].IsChain (fun a b => ({g 0, a, b} : Finset V) ∈ L) :=
    List.isChain_cons_cons.mpr ⟨h₁, List.isChain_cons_cons.mpr ⟨h₂, List.isChain_singleton _⟩⟩
  have hlv : ∀ a ∈ [g 1, v₂, g 2], a ∈ verts2 L := mem_verts2_of_chain hch
  have h3l : g 3 ∉ [g 1, v₂, g 2] := fun h => hg3 (hlv _ h)
  have hF : fanT (g 0) [g 1, v₂, g 2] ⊆ L := fanT_subset hch
  have hst := hS.split_steps hg3 [g 2] (g 1) v₂ (g 2) hnd hul hch rfl
  obtain ⟨N, hN⟩ : ∃ N, N = splitV L (g 0) (g 3) (g 1) (g 2) [g 1, v₂, g 2] := ⟨_, rfl⟩
  rw [← hN] at hst
  have hLN := Relation.EqvGen.reflTransGen_le_eqvGen _ _ _ hst
  have edge : ∀ {x y : V}, x ≠ y → x ≠ g 0 → x ≠ g 3 → y ≠ g 0 → y ≠ g 3 →
      (∃ t ∈ L, x ∈ t ∧ y ∈ t) → ∃ t ∈ N, x ∈ t ∧ y ∈ t := fun hxy h1 h2 h3 h4 h => by
    rw [hN]; exact (pair_splitV_iff hul h3l hF hxy h1 h2 h3 h4).mpr h
  have hv₂L : v₂ ∈ verts2 L := mem_verts2.mpr ⟨_, h₁, by simp⟩
  have hv₄L : v₄ ∈ verts2 L := mem_verts2.mpr ⟨_, h₃, by simp⟩
  have hw₂ : ∀ i < 6, v₂ ≠ g i := by
    intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ 3 ≤ i by omega) with rfl | rfl | rfl | hi
    · exact hvv2.symm
    · exact hv1v2.symm
    · exact hv2v3
    · exact fun h => hfr i hi (h ▸ hv₂L)
  have hw₄ : ∀ i < 6, v₄ ≠ g i := by
    intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ 3 ≤ i by omega) with rfl | rfl | rfl | hi
    · exact hvv4.symm
    · exact h14.symm
    · exact hv3v4.symm
    · exact fun h => hfr i hi (h ▸ hv₄L)
  have hcut := cut_mid (w₂ := v₂) (w₄ := v₄) hLN ((isSurface_iff_of_eqvGen hLN).mp hS)
    (by rw [hN, splitV]; exact mem_insert_self _ _)
    (by rw [hN, splitV]; exact mem_insert_of_mem (mem_insert_self _ _))
    (edge (gne 1 2 (by decide)) (gne 1 0 (by decide)) (gne 1 3 (by decide)) (gne 2 0 (by decide))
      (gne 2 3 (by decide)) e13)
    (by
      intro h
      rw [hN] at h
      rcases mem_splitV_cases h with h | h
      · exact hσ h
      · simp at h)
    (by
      intro h
      rw [hN] at h
      rcases mem_splitV_new h3l hg3' h (by simp) with h | h | h
      · exact ne_of_witness (x := g 2) (by simp) (by simp) h
      · exact ne_of_witness (x := g 1) (by simp) (by simp) h
      · rw [insert_erase_last (by simp) (by simp)] at h
        exact hσ (hF h))
    hw₂ hw₄ h24
    (by
      refine ⟨{g 0, g 2, v₄}, ?_, by simp, by simp⟩
      rw [hN]
      refine mem_splitV_of_notMem_fanT h₃ fun h => ?_
      rcases (mem_fanT h).2 v₄ (by simp) with h | h
      · exact hvv4 h.symm
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h | h
        · exact h14 h.symm
        · exact h24 h.symm
        · exact hv3v4 h.symm)
    (edge h24.symm (hw₄ 0 (by norm_num)) (hw₄ 3 (by norm_num)) (hw₂ 0 (by norm_num))
      (hw₂ 3 (by norm_num)) (by obtain ⟨t, ht, h2, h4⟩ := e24; exact ⟨t, ht, h4, h2⟩))
    (⟨{g 3, v₂, g 2}, by rw [hN]; exact mem_splitV_of_mem_fanT (by simp [fanT]), by simp,
      by simp⟩)
    (by
      intro n hn h
      rw [hN] at h
      rcases mem_verts2_splitV (mem_verts2.mpr ⟨_, h₁, by simp⟩) (hlv _ (by simp))
        (hlv _ (by simp)) hlv h with h | h
      · exact gne n 3 (by omega) h
      · exact hfr n (by omega) h)
  rcases hcut with ⟨A, h⟩ | ⟨A, h⟩
  · exact Or.inl ⟨A, g, h⟩
  · exact Or.inr ⟨A, g, h⟩

end Lightlike.Surfaces
