import Lightlike.Surfaces.Dual
import Lightlike.Surfaces.Cut

/-!
# Moving the gluing site of a connected sum

A connected sum `csum M s P {0, 1, 2} f` glues a piece `P` (a closed surface on the labels
`0, …, k − 1`) along its triangle `{0, 1, 2}` to the triangle `s` of a closed surface `M`. This file
shows that, up to 2D moves, the result depends neither on `s` nor on the labelling `f`
(`GoodPiece.homog`): any two connected sums of `M` with `P` are related by moves.

The piece has to carry certificates (`GoodPiece`): that gluing it is a checked surgery, that it
has every reordering of `{0, 1, 2}` as an automorphism, and a checked chain of moves that slides
it from the triangle `{0, 1, 2}` to the neighbouring triangle `{1, 2, k}`. The argument:

* `GoodPiece.step_ordered`, `GoodPiece.step`: the slide chain moves the piece from a triangle to a
  dual neighbour, for any labellings with fresh interiors;
* `GoodPiece.refresh`: at a fixed triangle, the labelling does not matter (slide away and back);
* `GoodPiece.homog`: induction along a dual path (`IsSurface.dconn`).

The file also contains the bookkeeping for labellings: `tabE` (an embedding given by a table),
`exists_patch` (an embedding with prescribed values on an initial segment), and the algebra of
`liftK` and `csum` under composition.
-/

open Finset Relation

namespace Lightlike.Surfaces

open Lightlike.PR

variable {V : Type*} [DecidableEq V]

/-! ## Label tables -/

/-- The label map given by a table: `n ↦ l[n]` for `n` below the length of `l`, and `n ↦ n + s`
beyond it. -/
def tabF (l : List ℕ) (s : ℕ) (n : ℕ) : ℕ := if h : n < l.length then l[n] else n + s

/-- A table without repetitions whose entries lie below `length + s` gives an injective map. -/
lemma tabF_injective {l : List ℕ} {s : ℕ} (h : l.Nodup ∧ ∀ x ∈ l, x < l.length + s) :
    Function.Injective (tabF l s) := by
  intro a b hab
  simp only [tabF] at hab
  by_cases ha : a < l.length <;> by_cases hb : b < l.length <;>
    simp only [ha, hb, ↓reduceDIte] at hab
  · exact (h.1.getElem_inj_iff).mp hab
  · have := h.2 _ (List.getElem_mem ha); omega
  · have := h.2 _ (List.getElem_mem hb); omega
  · omega

/-- The **embedding given by a table** (`tabF`). -/
def tabE (l : List ℕ) (s : ℕ) (h : l.Nodup ∧ ∀ x ∈ l, x < l.length + s) : ℕ ↪ ℕ :=
  ⟨tabF l s, tabF_injective h⟩

/-- The table `[1, 2, k]` with shift `k − 2` (the relabelling of the slide chain) is valid. -/
lemma tabOK_slide {k : ℕ} (hk : 3 ≤ k) :
    [1, 2, k].Nodup ∧ ∀ x ∈ [1, 2, k], x < [1, 2, k].length + (k - 2) := by
  refine ⟨?_, fun x hx => ?_⟩
  · refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, by simp⟩⟩
    · intro h
      rcases List.mem_cons.mp h with h | h
      · omega
      · rw [List.mem_singleton] at h; omega
    · intro h
      rw [List.mem_singleton] at h; omega
  · have hl : [1, 2, k].length = 3 := rfl
    rw [hl]
    rcases List.mem_cons.mp hx with h | h
    · omega
    · rcases List.mem_cons.mp h with h | h
      · omega
      · rw [List.mem_singleton] at h; omega

/-- With infinitely many vertices, a map injective on `0, …, m − 1` agrees there with an
embedding of `ℕ` whose other values avoid a given finite set. -/
lemma exists_patch [Infinite V] (φ : ℕ → V) (m : ℕ)
    (hφ : ∀ a < m, ∀ b < m, φ a = φ b → a = b) (F : Finset V) :
    ∃ g : ℕ ↪ V, (∀ n < m, g n = φ n) ∧ ∀ n, m ≤ n → g n ∉ F := by
  have hl : ((List.range m).map φ).Nodup :=
    List.Nodup.map_on (fun a ha b hb e => hφ a (List.mem_range.mp ha) b (List.mem_range.mp hb) e)
      List.nodup_range
  obtain ⟨g, hg1, hg2⟩ := exists_emb _ hl F
  refine ⟨g, fun n hn => ?_, fun n hn => hg2 n (by simpa using hn)⟩
  rw [hg1 n (by simpa using hn)]
  simp

/-! ## Relabelling complexes -/

/-- Placing a complex by a composite embedding is placing the placed complex. -/
lemma liftK_trans (g : ℕ ↪ ℕ) (f : ℕ ↪ V) (K : Finset (Finset ℕ)) :
    liftK (g.trans f) K = liftK f (liftK g K) := by
  simp only [liftK, image_image]
  congr 1
  funext t
  exact (Finset.map_map g f t).symm

/-- Placing a union of complexes. -/
lemma liftK_union (f : ℕ ↪ V) (K K' : Finset (Finset ℕ)) :
    liftK f (K ∪ K') = liftK f K ∪ liftK f K' := image_union _ _

/-- Placing a complex depends only on the embedding at its vertices. -/
lemma liftK_congr {f f' : ℕ ↪ V} {K : Finset (Finset ℕ)} (h : ∀ n ∈ verts2 K, f n = f' n) :
    liftK f K = liftK f' K := by
  refine image_congr fun t ht => ?_
  simp only [map_eq_image]
  exact image_congr fun n hn => h n (mem_verts2.mpr ⟨t, ht, hn⟩)

/-- **Relabelling a connected sum** relabels both parts. -/
lemma csum_map (h : ℕ ↪ V) (K : Finset (Finset ℕ)) (s : Finset ℕ) (P : Finset (Finset ℕ))
    (τ₀ : Finset ℕ) (g : ℕ ↪ ℕ) :
    liftK h (csum K s P τ₀ g) = csum (liftK h K) (s.map h) P τ₀ (g.trans h) := by
  rw [csum, csum, liftK_union, liftK_erase, liftK_trans]

/-- The gluing conditions survive relabelling. -/
lemma IsGlue.relabel {K : Finset (Finset ℕ)} {s : Finset ℕ} {P : Finset (Finset ℕ)} {τ₀ : Finset ℕ}
    {g : ℕ ↪ ℕ} (hg : IsGlue K s P τ₀ g) (h : ℕ ↪ V) :
    IsGlue (liftK h K) (s.map h) P τ₀ (g.trans h) where
  mem := map_mem_liftK.mpr hg.mem
  mem₀ := hg.mem₀
  map := by rw [← Finset.map_map, hg.map]
  fresh n hn hn0 hv := by
    rw [verts2_liftK] at hv
    obtain ⟨m, hm, e⟩ := mem_map.mp hv
    rw [Function.Embedding.trans_apply] at e
    exact hg.fresh n hn hn0 (h.injective e ▸ hm)

/-- **Two connected sums in a row**: gluing `Q` to the triangle `t` of the piece `P` (placed by
`g`) after gluing `P` to `M` is gluing the combined piece. -/
lemma csum_csum {M : Finset (Finset V)} {s : Finset V} {P Q : Finset (Finset ℕ)}
    {τ₀ τ₁ t : Finset ℕ} {f : ℕ ↪ V} {g : ℕ ↪ ℕ} (ht : t.map f ∉ M.erase s) :
    csum (csum M s P τ₀ f) (t.map f) Q τ₁ (g.trans f) =
      M.erase s ∪ liftK f ((P.erase τ₀).erase t ∪ liftK g (Q.erase τ₁)) := by
  rw [csum, csum, union_erase_of_notMem ht, liftK_union, liftK_erase, liftK_trans, union_assoc]
  simp only [liftK_erase]

/-! ## Good pieces -/

/-- The reorderings of `{0, 1, 2}`. -/
lemma tri012_of_lt {i j l : ℕ} (hi : i < 3) (hj : j < 3) (hl : l < 3) (hij : i ≠ j) (hil : i ≠ l)
    (hjl : j ≠ l) : ({i, j, l} : Finset ℕ) = {0, 1, 2} := by
  interval_cases i <;> interval_cases j <;> interval_cases l <;> first | rfl | omega | decide

/-- A **good piece** on the labels `0, …, k − 1`: a closed surface `P` with the gluing triangle
`{0, 1, 2}`, all of whose other triangles have a label `≥ 3`, with the certificates used to move
gluing sites:

* `surgOK`, `reach`: replacing a triangle by `P` minus `{0, 1, 2}` is a checked surgery
  (`IsSurface.surgery`), so connected sums with `P` are closed surfaces;
* `slide`: a checked chain of moves taking `P` minus `{0, 1, 2}`, together with the triangle
  `{1, 2, k}` beside it, to `{0, 1, 2}` together with a copy of `P` minus `{0, 1, 2}` glued along
  `{1, 2, k}` (labels `0, 1, 2 ↦ 1, 2, k` and `n ↦ n + k − 2` from `3` on);
* `aut`: every reordering of `0, 1, 2` extends to an automorphism of `P` minus `{0, 1, 2}`. -/
structure GoodPiece (P : Finset (Finset ℕ)) (k : ℕ) : Prop where
  three_le : 3 ≤ k
  closed : IsClosed2 P
  tri : IsTri2 P
  mem₀ : ({0, 1, 2} : Finset ℕ) ∈ P
  verts : verts2 (P.erase {0, 1, 2}) = range k
  inner : ∀ t ∈ P.erase {0, 1, 2}, ∃ n ∈ t, 3 ≤ n
  surgOK : SurgOK {{0, 1, 2}} (P.erase {0, 1, 2}) []
  reach : ∃ a, ∀ m ∈ verts2 (P.erase {0, 1, 2}), m ∈ reachAll (edges2 (P.erase {0, 1, 2})) a
  slide : ∃ ms, checkChain {0, 1, 2, k} [(1, 2)] (insert {1, 2, k} (P.erase {0, 1, 2})) ms =
    some (insert {0, 1, 2} (liftK (tabE [1, 2, k] (k - 2) (tabOK_slide three_le))
      (P.erase {0, 1, 2})))
  aut : ∀ i j l, i < 3 → j < 3 → l < 3 → i ≠ j → i ≠ l → j ≠ l →
    ∃ α : ℕ ↪ ℕ, α 0 = i ∧ α 1 = j ∧ α 2 = l ∧ liftK α (P.erase {0, 1, 2}) = P.erase {0, 1, 2}

section good

variable {P : Finset (Finset ℕ)} {k : ℕ} {M : Finset (Finset V)}

/-- A vertex of a good piece other than `0, 1, 2` lies in a triangle other than `{0, 1, 2}`. -/
lemma GoodPiece.lt_of_mem (hP : GoodPiece P k) {n : ℕ} (hn : n ∈ verts2 P) : n < k := by
  by_cases h : n ∈ ({0, 1, 2} : Finset ℕ)
  · simp only [mem_insert, mem_singleton] at h
    have := hP.three_le
    omega
  · obtain ⟨t, ht, hnt⟩ := mem_verts2.mp hn
    have : n ∈ verts2 (P.erase {0, 1, 2}) :=
      mem_verts2.mpr ⟨t, mem_erase.mpr ⟨fun e => h (e ▸ hnt), ht⟩, hnt⟩
    rw [hP.verts] at this
    exact mem_range.mp this

/-- A label `n < k` of a good piece is a vertex of `P` minus `{0, 1, 2}`. -/
lemma GoodPiece.mem_erase_verts (hP : GoodPiece P k) {n : ℕ} (hn : n < k) :
    n ∈ verts2 (P.erase {0, 1, 2}) := by
  rw [hP.verts]; exact mem_range.mpr hn

/-- A label `n < k` of a good piece is a vertex of `P`. -/
lemma GoodPiece.mem_verts (hP : GoodPiece P k) {n : ℕ} (hn : n < k) : n ∈ verts2 P := by
  obtain ⟨t, ht, hnt⟩ := mem_verts2.mp (hP.mem_erase_verts hn)
  exact mem_verts2.mpr ⟨t, mem_of_mem_erase ht, hnt⟩

/-- The interior labels of a glued piece go outside `M`. -/
lemma GoodPiece.fresh_of_glue (hP : GoodPiece P k) {s : Finset V} {f : ℕ ↪ V}
    (hg : IsGlue M s P {0, 1, 2} f) {n : ℕ} (h3 : 3 ≤ n) (hk : n < k) : f n ∉ verts2 M :=
  hg.fresh n (hP.mem_verts hk) (by simp only [mem_insert, mem_singleton]; omega)

/-- An embedding sending `0, 1, 2` to the vertices of a triangle of `M` and the other labels
outside `M` glues `P` to that triangle. -/
lemma isGlue_of_emb {x y z : V} (hP : GoodPiece P k) (hs : ({x, y, z} : Finset V) ∈ M)
    {g : ℕ ↪ V} (g0 : g 0 = x) (g1 : g 1 = y) (g2 : g 2 = z) (hg : ∀ n, 3 ≤ n → g n ∉ verts2 M) :
    IsGlue M {x, y, z} P {0, 1, 2} g where
  mem := hs
  mem₀ := hP.mem₀
  map := by simp [g0, g1, g2]
  fresh n _ hn := hg n (by simp only [mem_insert, mem_singleton] at hn; omega)

/-- **Gluings exist**: with infinitely many vertices, `P` can be glued to any triangle of a
complex of triangles, with its interior labels outside a given finite set. -/
lemma exists_glue [Infinite V] (hP : GoodPiece P k) (hT : IsTri2 M) {t : Finset V} (ht : t ∈ M)
    (F : Finset V) : ∃ g : ℕ ↪ V, IsGlue M t P {0, 1, 2} g ∧ ∀ n, 3 ≤ n → g n ∉ F := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := card_eq_three.mp (hT _ ht)
  obtain ⟨g, hgl, hgF⟩ := exists_emb [x, y, z] (by simp [hxy, hxz, hyz]) (F ∪ verts2 M)
  have g0 : g 0 = x := hgl 0 (by simp)
  have g1 : g 1 = y := hgl 1 (by simp)
  have g2 : g 2 = z := hgl 2 (by simp)
  have hn : ∀ n, 3 ≤ n → g n ∉ F ∪ verts2 M := fun n hn => hgF n (by simpa using hn)
  exact ⟨g, isGlue_of_emb hP ht g0 g1 g2 fun n h => fun hm => hn n h (mem_union_right _ hm),
    fun n h hm => hn n h (mem_union_left _ hm)⟩

/-- **A connected sum with a good piece is a closed surface.** -/
theorem GoodPiece.isSurface_csum (hP : GoodPiece P k) (hM : IsSurface M) {s : Finset V}
    {f : ℕ ↪ V} (hg : IsGlue M s P {0, 1, 2} f) : IsSurface (csum M s P {0, 1, 2} f) := by
  have hsub : liftK f {{0, 1, 2}} = {s} := by simp [liftK, ← hg.map]
  have hC : SurgCtx M f {{0, 1, 2}} (P.erase {0, 1, 2}) [] :=
    { sub := by rw [hsub]; exact singleton_subset_iff.mpr hg.mem
      fresh := fun n hn hnX => by
        obtain ⟨t, ht, hnt⟩ := mem_verts2.mp hn
        refine hg.fresh n (mem_verts2.mpr ⟨t, mem_of_mem_erase ht, hnt⟩) ?_
        simpa [verts2] using hnX
      safe := by simp
      new := fun t ht hm => by
        obtain ⟨n, hn, h3⟩ := hP.inner t ht
        exact hg.fresh n (mem_verts2.mpr ⟨t, mem_of_mem_erase ht, hn⟩)
          (by simp only [mem_insert, mem_singleton]; omega)
          (mem_verts2.mpr ⟨_, hm, mem_map_of_mem f hn⟩) }
  have e : surg M f {{0, 1, 2}} (P.erase {0, 1, 2}) = csum M s P {0, 1, 2} f := by
    rw [surg, hsub, sdiff_singleton_eq_erase, csum]
  obtain ⟨a, ha⟩ := hP.reach
  rw [← e]
  exact hM.surgery hC hP.surgOK (hconn_of_reach (by rw [e]; exact subset_union_right) ha)

/-! ### Reordering the gluing triangle -/

/-- Composing with an automorphism of the piece does not change the connected sum. -/
lemma csum_aut {s : Finset V} {f : ℕ ↪ V} {α : ℕ ↪ ℕ}
    (hα : liftK α (P.erase {0, 1, 2}) = P.erase {0, 1, 2}) :
    csum M s P {0, 1, 2} (α.trans f) = csum M s P {0, 1, 2} f := by
  rw [csum, csum, liftK_trans, hα]

/-- An automorphism of the piece fixing `{0, 1, 2}` as a set keeps the interior labels. -/
lemma GoodPiece.aut_interior (hP : GoodPiece P k) {α : ℕ ↪ ℕ}
    (h012 : ({0, 1, 2} : Finset ℕ).map α = {0, 1, 2})
    (hα : liftK α (P.erase {0, 1, 2}) = P.erase {0, 1, 2}) {n : ℕ} (h3 : 3 ≤ n) (hk : n < k) :
    3 ≤ α n ∧ α n < k := by
  refine ⟨?_, ?_⟩
  · by_contra hlt
    have : α n ∈ ({0, 1, 2} : Finset ℕ).map α := by
      rw [h012]; simp only [mem_insert, mem_singleton]; omega
    obtain ⟨m, hm, e⟩ := mem_map.mp this
    rw [α.injective e] at hm
    simp only [mem_insert, mem_singleton] at hm
    omega
  · have : α n ∈ verts2 (liftK α (P.erase {0, 1, 2})) := by
      rw [verts2_liftK]; exact mem_map_of_mem α (hP.mem_erase_verts hk)
    rw [hα, hP.verts] at this
    exact mem_range.mp this

/-- The gluing conditions survive composing with an automorphism of the piece. -/
lemma GoodPiece.isGlue_aut (hP : GoodPiece P k) {s : Finset V} {f : ℕ ↪ V}
    (hg : IsGlue M s P {0, 1, 2} f) {α : ℕ ↪ ℕ}
    (h012 : ({0, 1, 2} : Finset ℕ).map α = {0, 1, 2})
    (hα : liftK α (P.erase {0, 1, 2}) = P.erase {0, 1, 2}) :
    IsGlue M s P {0, 1, 2} (α.trans f) where
  mem := hg.mem
  mem₀ := hg.mem₀
  map := by rw [← Finset.map_map, h012, hg.map]
  fresh n hn hn0 := by
    have hk := hP.lt_of_mem hn
    have h3 : 3 ≤ n := by simp only [mem_insert, mem_singleton] at hn0; omega
    obtain ⟨h3', hk'⟩ := hP.aut_interior h012 hα h3 hk
    exact hP.fresh_of_glue hg h3' hk'

/-- **Reordering**: if `f` sends `{0, 1, 2}` onto `{a, b, c}`, an automorphism `α` of the piece
makes `α.trans f` send `0, 1, 2` to `a, b, c` in this order. -/
lemma GoodPiece.exists_order (hP : GoodPiece P k) {f : ℕ ↪ V} {a b c : V}
    (hmap : ({0, 1, 2} : Finset ℕ).map f = {a, b, c}) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ α : ℕ ↪ ℕ, f (α 0) = a ∧ f (α 1) = b ∧ f (α 2) = c ∧
      ({0, 1, 2} : Finset ℕ).map α = {0, 1, 2} ∧
      liftK α (P.erase {0, 1, 2}) = P.erase {0, 1, 2} := by
  have pre : ∀ v ∈ ({a, b, c} : Finset V), ∃ i, i < 3 ∧ f i = v := by
    intro v hv
    rw [← hmap] at hv
    obtain ⟨i, hi, e⟩ := mem_map.mp hv
    simp only [mem_insert, mem_singleton] at hi
    exact ⟨i, by omega, e⟩
  obtain ⟨i, hi, fi⟩ := pre a (by simp)
  obtain ⟨j, hj, fj⟩ := pre b (by simp)
  obtain ⟨l, hl, fl⟩ := pre c (by simp)
  have hij : i ≠ j := fun e => hab (by rw [← fi, ← fj, e])
  have hil : i ≠ l := fun e => hac (by rw [← fi, ← fl, e])
  have hjl : j ≠ l := fun e => hbc (by rw [← fj, ← fl, e])
  obtain ⟨α, α0, α1, α2, hα⟩ := hP.aut i j l hi hj hl hij hil hjl
  refine ⟨α, by rw [α0, fi], by rw [α1, fj], by rw [α2, fl], ?_, hα⟩
  rw [map_tri, α0, α1, α2]
  exact tri012_of_lt hi hj hl hij hil hjl

/-! ### Sliding the piece across an edge -/

/-- **One slide, in coordinates.** Let `s = {w, x, y}` and `t = {x, y, z}` be adjacent triangles
of a closed surface `M`, `f` glue `P` to `s` with `0, 1, 2 ↦ w, x, y`, and `g` send `0, 1, 2` to
`x, y, z` with interior labels outside the first connected sum. Then the two connected sums are
related by moves: the checked slide chain of the piece, placed by an embedding that agrees with
`f` on `P`, sends `k` to `z`, and continues with `g` on the copy. -/
theorem GoodPiece.step_ordered [Infinite V] (hP : GoodPiece P k) (hM : IsSurface M)
    {s t : Finset V} {w x y z : V} (hsM : s ∈ M) (htM : t ∈ M) (hs : s = {w, x, y})
    (ht : t = {x, y, z}) (hwz : w ≠ z) {f g : ℕ ↪ V} (hf : IsGlue M s P {0, 1, 2} f)
    (f0 : f 0 = w) (f1 : f 1 = x) (f2 : f 2 = y) (g0 : g 0 = x) (g1 : g 1 = y) (g2 : g 2 = z)
    (hgf : ∀ n, 3 ≤ n → n < k → g n ∉ verts2 (csum M s P {0, 1, 2} f)) :
    EqvGen Move2 (csum M s P {0, 1, 2} f) (csum M t P {0, 1, 2} g) := by
  have hk3 := hP.three_le
  obtain ⟨hwx, hwy, hxy⟩ := tri_ne (hM.card _ (hs ▸ hsM))
  obtain ⟨-, hxz, hyz⟩ := tri_ne (hM.card _ (ht ▸ htM))
  have hst : s ≠ t := by
    intro e
    have : w ∈ t := e ▸ hs ▸ mem_insert_self w _
    rw [ht] at this
    simp only [mem_insert, mem_singleton] at this
    rcases this with h | h | h
    · exact hwx h
    · exact hwy h
    · exact hwz h
  have htC : t ∈ M.erase s := mem_erase.mpr ⟨hst.symm, htM⟩
  have hsC : s ∈ M.erase t := mem_erase.mpr ⟨hst, hsM⟩
  -- the vertices of the first connected sum
  have hfC : ∀ n < k, f n ∈ verts2 (csum M s P {0, 1, 2} f) := by
    intro n hn
    rw [csum, verts2_union, mem_union, verts2_liftK]
    exact Or.inr (mem_map_of_mem f (hP.mem_erase_verts hn))
  have hzt : z ∈ t := by rw [ht]; simp
  have hzM : z ∈ verts2 M := mem_verts2.mpr ⟨t, htM, hzt⟩
  have hzC : z ∈ verts2 (csum M s P {0, 1, 2} f) := by
    rw [csum, verts2_union, mem_union]
    exact Or.inl (mem_verts2.mpr ⟨t, htC, hzt⟩)
  -- the labelling of the chain
  let φ : ℕ → V := fun n => if n < k then f n else if n = k then z else g (n + 2 - k)
  have φlt : ∀ n, n < k → φ n = f n := fun n hn => by simp [φ, hn]
  have φk : φ k = z := by simp [φ]
  have φgt : ∀ n, k < n → φ n = g (n + 2 - k) := fun n hn => by
    simp [φ, show ¬ n < k by omega, show n ≠ k by omega]
  have hzf : ∀ a < k, f a ≠ z := by
    intro a ha e
    by_cases h3 : 3 ≤ a
    · exact hP.fresh_of_glue hf h3 ha (e ▸ hzM)
    · interval_cases a
      · exact hwz (f0 ▸ e)
      · exact hxz (f1 ▸ e)
      · exact hyz (f2 ▸ e)
  have hφ : ∀ a < 2 * k - 2, ∀ b < 2 * k - 2, φ a = φ b → a = b := by
    intro a ha b hb e
    rcases lt_trichotomy a k with hak | hak | hak <;>
      rcases lt_trichotomy b k with hbk | hbk | hbk
    · rw [φlt a hak, φlt b hbk] at e; exact f.injective e
    · rw [φlt a hak, hbk, φk] at e; exact absurd e (hzf a hak)
    · rw [φlt a hak, φgt b hbk] at e
      exact absurd (show g (b + 2 - k) ∈ verts2 (csum M s P {0, 1, 2} f) by
        rw [← e]; exact hfC a hak) (hgf _ (by omega) (by omega))
    · rw [hak, φk, φlt b hbk] at e; exact absurd e.symm (hzf b hbk)
    · omega
    · rw [hak, φk, φgt b hbk] at e
      exact absurd (show g (b + 2 - k) ∈ verts2 (csum M s P {0, 1, 2} f) by
        rw [← e]; exact hzC) (hgf _ (by omega) (by omega))
    · rw [φgt a hak, φlt b hbk] at e
      exact absurd (show g (a + 2 - k) ∈ verts2 (csum M s P {0, 1, 2} f) by
        rw [e]; exact hfC b hbk) (hgf _ (by omega) (by omega))
    · rw [φgt a hak, hbk, φk] at e
      exact absurd (show g (a + 2 - k) ∈ verts2 (csum M s P {0, 1, 2} f) by
        rw [e]; exact hzC) (hgf _ (by omega) (by omega))
    · rw [φgt a hak, φgt b hbk] at e
      have := g.injective e
      omega
  obtain ⟨F, hFφ, hFout⟩ := exists_patch φ (2 * k - 2) hφ (verts2 (csum M s P {0, 1, 2} f))
  have F_lt : ∀ n < k, F n = f n := fun n hn => by rw [hFφ n (by omega), φlt n hn]
  have F0 : F 0 = w := by rw [F_lt 0 (by omega), f0]
  have F1 : F 1 = x := by rw [F_lt 1 (by omega), f1]
  have F2 : F 2 = y := by rw [F_lt 2 (by omega), f2]
  have Fk : F k = z := by rw [hFφ k (by omega), φk]
  -- the surrounding complex `A = M − s − t`
  have hAM : ∀ v ∈ verts2 ((M.erase s).erase t), v ∈ verts2 M := by
    intro v hv
    obtain ⟨τ, hτ, hvτ⟩ := mem_verts2.mp hv
    exact mem_verts2.mpr ⟨τ, mem_of_mem_erase (mem_of_mem_erase hτ), hvτ⟩
  have hAC : ∀ v ∈ verts2 ((M.erase s).erase t), v ∈ verts2 (csum M s P {0, 1, 2} f) := by
    intro v hv
    obtain ⟨τ, hτ, hvτ⟩ := mem_verts2.mp hv
    rw [csum, verts2_union]
    exact mem_union_left _ (mem_verts2.mpr ⟨τ, mem_of_mem_erase hτ, hvτ⟩)
  have hxyw : ({x, y, w} : Finset V) = s := by
    rw [hs]; ext; simp only [mem_insert, mem_singleton]; tauto
  have hctx : Ctx ((M.erase s).erase t) F {0, 1, 2, k} [(1, 2)] := by
    refine ⟨fun n hn hv => ?_, ?_⟩
    · simp only [mem_insert, mem_singleton, not_or] at hn
      rcases lt_trichotomy n k with hnk | hnk | hnk
      · rw [F_lt n hnk] at hv
        exact hP.fresh_of_glue hf (by omega) hnk (hAM _ hv)
      · exact hn.2.2.2 hnk
      · by_cases hm : n < 2 * k - 2
        · rw [hFφ n hm, φgt n hnk] at hv
          exact hgf _ (by omega) (by omega) (hAC _ hv)
        · exact hFout n (by omega) (hAC _ hv)
    · intro p hp τ hτ hsub
      rw [List.mem_singleton] at hp
      subst hp
      dsimp only at hsub
      rw [F1, F2] at hsub
      have hτM : τ ∈ M := mem_of_mem_erase (mem_of_mem_erase hτ)
      rcases hM.tris_at_edge (hxyw ▸ hsM) (ht ▸ htM) hwz τ hτM hsub with rfl | rfl
      · rw [hxyw] at hτ
        exact (mem_erase.mp (mem_of_mem_erase hτ)).1 rfl
      · rw [← ht] at hτ
        exact (mem_erase.mp hτ).1 rfl
  have hD : Disj ((M.erase s).erase t) F (insert {1, 2, k} (P.erase {0, 1, 2})) := by
    intro τ hτ hA
    rcases mem_insert.mp hτ with rfl | hτ
    · rw [map_tri, F1, F2, Fk, ← ht] at hA
      exact (mem_erase.mp hA).1 rfl
    · obtain ⟨n, hn, h3⟩ := hP.inner τ hτ
      have hnk : n < k := by
        have h : n ∈ verts2 (P.erase {0, 1, 2}) := mem_verts2.mpr ⟨τ, hτ, hn⟩
        rw [hP.verts] at h
        exact mem_range.mp h
      refine hP.fresh_of_glue hf h3 hnk (hAM _ ?_)
      rw [← F_lt n hnk]
      exact mem_verts2.mpr ⟨_, hA, mem_map_of_mem F hn⟩
  obtain ⟨ms, hms⟩ := hP.slide
  have key := checkChain_sound hctx ms hD hms
  -- identify both ends
  have hQ : liftK F (P.erase {0, 1, 2}) = liftK f (P.erase {0, 1, 2}) :=
    liftK_congr fun n hn => F_lt n (by rw [hP.verts] at hn; exact mem_range.mp hn)
  have hQ' : liftK ((tabE [1, 2, k] (k - 2) (tabOK_slide hk3)).trans F) (P.erase {0, 1, 2}) =
      liftK g (P.erase {0, 1, 2}) := by
    refine liftK_congr fun n hn => ?_
    rw [hP.verts, mem_range] at hn
    simp only [Function.Embedding.trans_apply, tabE, Function.Embedding.coeFn_mk, tabF]
    rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ 3 ≤ n) with rfl | rfl | rfl | h3
    · simp [F1, g0]
    · simp [F2, g1]
    · simp [Fk, g2]
    · have hn3 : ¬ n < [1, 2, k].length := by simp; omega
      simp only [hn3, ↓reduceDIte]
      rw [hFφ _ (by omega), φgt _ (by omega)]
      congr 1
      omega
  have hL : (M.erase s).erase t ∪ liftK F (insert {1, 2, k} (P.erase {0, 1, 2})) =
      csum M s P {0, 1, 2} f := by
    rw [liftK_insert, map_tri, F1, F2, Fk, ← ht, hQ, union_insert, ← insert_union,
      insert_erase htC, csum]
  have hR : (M.erase s).erase t ∪ liftK F (insert {0, 1, 2}
      (liftK (tabE [1, 2, k] (k - 2) (tabOK_slide hk3)) (P.erase {0, 1, 2}))) =
      csum M t P {0, 1, 2} g := by
    rw [liftK_insert, map_tri, F0, F1, F2, ← hs, ← liftK_trans, hQ', union_insert,
      ← insert_union, erase_right_comm, insert_erase hsC, csum]
  rw [← hL, ← hR]
  exact key

/-- **One slide.** If `s` and `t` are dual-adjacent triangles of a closed surface `M`, `f` glues
`P` to `s` and `g` glues `P` to `t` with interior labels outside the first connected sum, the two
connected sums are related by moves (after reordering both gluings by automorphisms of `P`). -/
theorem GoodPiece.step [Infinite V] (hP : GoodPiece P k) (hM : IsSurface M) {s t : Finset V}
    (hst : DAdj M s t) {f g : ℕ ↪ V} (hf : IsGlue M s P {0, 1, 2} f)
    (hg : IsGlue M t P {0, 1, 2} g)
    (hgf : ∀ n, 3 ≤ n → n < k → g n ∉ verts2 (csum M s P {0, 1, 2} f)) :
    EqvGen Move2 (csum M s P {0, 1, 2} f) (csum M t P {0, 1, 2} g) := by
  have hsM := hst.1
  have htM := hst.2.1
  obtain ⟨w, x, y, z, hs, ht, hwz, hxy, hwx, hwy, hzx, hzy⟩ := hst.split hM.card
  obtain ⟨α, fα0, fα1, fα2, h012, hα⟩ := hP.exists_order (hf.map.trans hs) hwx hwy hxy
  obtain ⟨β, gβ0, gβ1, gβ2, h012', hβ⟩ :=
    hP.exists_order (hg.map.trans ht) hxy hzx.symm hzy.symm
  have e1 := csum_aut (M := M) (s := s) (f := f) hα
  have e2 := csum_aut (M := M) (s := t) (f := g) hβ
  rw [← e1, ← e2]
  refine hP.step_ordered hM hsM htM hs ht hwz (hP.isGlue_aut hf h012 hα) fα0 fα1 fα2 gβ0 gβ1
    gβ2 ?_
  intro n h3 hk
  rw [e1]
  obtain ⟨h3', hk'⟩ := hP.aut_interior h012' hβ h3 hk
  exact hgf _ h3' hk'

/-- **Refreshing a gluing**: two gluings of `P` to the same triangle of a closed surface give
connected sums related by moves (slide both to a neighbouring triangle, with the same fresh
labels there). -/
theorem GoodPiece.refresh [Infinite V] (hP : GoodPiece P k) (hM : IsSurface M) {s : Finset V}
    {f f' : ℕ ↪ V} (hf : IsGlue M s P {0, 1, 2} f) (hf' : IsGlue M s P {0, 1, 2} f') :
    EqvGen Move2 (csum M s P {0, 1, 2} f) (csum M s P {0, 1, 2} f') := by
  obtain ⟨a, b, c, hab, hac, hbc, hs⟩ := card_eq_three.mp (hM.card _ hf.mem)
  obtain ⟨d, hdc, hda, hdb, hd, -⟩ := hM.other_tri (hs ▸ hf.mem)
  have hadj : DAdj M s {a, b, d} := by
    refine ⟨hf.mem, hd, ?_, a, b, hab, by simp [hs], by simp [hs], by simp, by simp⟩
    intro e
    have : c ∈ ({a, b, d} : Finset V) := e ▸ (by simp [hs])
    simp only [mem_insert, mem_singleton] at this
    rcases this with h | h | h
    · exact hac h.symm
    · exact hbc h.symm
    · exact hdc h.symm
  obtain ⟨h, hh, hhF⟩ := exists_glue hP hM.card hd
    (verts2 (csum M s P {0, 1, 2} f) ∪ verts2 (csum M s P {0, 1, 2} f'))
  have e1 := hP.step hM hadj hf hh fun n h3 _ hv => hhF n h3 (mem_union_left _ hv)
  have e2 := hP.step hM hadj hf' hh fun n h3 _ hv => hhF n h3 (mem_union_right _ hv)
  exact EqvGen.trans _ _ _ e1 (EqvGen.symm _ _ e2)

/-- Gluings to dual-adjacent triangles give connected sums related by moves. -/
theorem GoodPiece.adjacent [Infinite V] (hP : GoodPiece P k) (hM : IsSurface M)
    {s t : Finset V} (hst : DAdj M s t) {f g : ℕ ↪ V} (hf : IsGlue M s P {0, 1, 2} f)
    (hg : IsGlue M t P {0, 1, 2} g) :
    EqvGen Move2 (csum M s P {0, 1, 2} f) (csum M t P {0, 1, 2} g) := by
  obtain ⟨h, hh, hhF⟩ := exists_glue hP hM.card hst.2.1 (verts2 (csum M s P {0, 1, 2} f))
  exact EqvGen.trans _ _ _ (hP.step hM hst hf hh fun n h3 _ => hhF n h3) (hP.refresh hM hh hg)

/-- **The connected sum does not depend on the gluing.** Any two connected sums of a closed
surface `M` with a good piece `P` are related by 2D moves, whatever the triangles and the
labellings used. -/
theorem GoodPiece.homog [Infinite V] (hP : GoodPiece P k) (hM : IsSurface M) {s t : Finset V}
    {f g : ℕ ↪ V} (hf : IsGlue M s P {0, 1, 2} f) (hg : IsGlue M t P {0, 1, 2} g) :
    EqvGen Move2 (csum M s P {0, 1, 2} f) (csum M t P {0, 1, 2} g) := by
  have hpath := hM.dconn hf.mem hg.mem
  suffices h : ∀ u, ReflTransGen (DAdj M) s u → ∀ g, IsGlue M u P {0, 1, 2} g →
      EqvGen Move2 (csum M s P {0, 1, 2} f) (csum M u P {0, 1, 2} g) from h t hpath g hg
  intro u hu
  induction hu with
  | refl => exact fun g hg => hP.refresh hM hf hg
  | tail _ hbc ih =>
    intro g hg
    obtain ⟨h, hh, -⟩ := exists_glue hP hM.card hbc.1 ∅
    exact EqvGen.trans _ _ _ (ih h hh) (hP.adjacent hM hbc hh hg)

end good

end Lightlike.Surfaces
