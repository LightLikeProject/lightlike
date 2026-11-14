import Lightlike.Surfaces.Sum

/-!
# The pieces of the standard surfaces

* `P6`: the projective plane with 6 vertices (the hemi-icosahedron, Möbius–Kühnel). Its 10
  triangles form the boundary of the icosahedron with antipodal points identified.
* `T9`: the torus with 9 vertices, the `3 × 3` grid with one diagonal in each square
  (vertex `(i, j)` is `3i + j`, indices mod 3, with the labels `2` and `3` exchanged).

Both are closed (`isClosed2_P6`, `isClosed2_T9`); their Euler characteristics are `1` and `0`.
`T9` is orientable (`isOrientation_T9`, an explicit orientation), and no complex containing the
Möbius band `P6` minus a triangle as a full neighbourhood of its inner vertices is orientable
(`not_isOrientable_of_P6`), so neither is any connected sum with `P6`.
-/

open Finset

namespace Lightlike.Surfaces

open Lightlike.PR

set_option maxRecDepth 100000

/-- The **6-vertex projective plane** (hemi-icosahedron), on the labels `0, …, 5`. -/
def P6 : Finset (Finset ℕ) :=
  {{0, 1, 2}, {0, 2, 3}, {0, 3, 4}, {0, 4, 5}, {0, 1, 5}, {1, 2, 4}, {2, 3, 5}, {1, 3, 4},
    {2, 4, 5}, {1, 3, 5}}

/-- The **9-vertex torus**: the `3 × 3` grid on the labels `0, …, 8` (vertex `(i, j)` is `3i + j`,
with the labels `2` and `3` exchanged so that `{0, 1, 2}` and `{1, 3, 4}` are triangles), each
square cut by one diagonal. -/
def T9 : Finset (Finset ℕ) :=
  {{0, 1, 2}, {0, 1, 7}, {0, 2, 5}, {0, 3, 5}, {0, 3, 6}, {0, 6, 7}, {1, 2, 4}, {1, 3, 4}, {1, 3, 8}, {1, 7, 8}, {2, 4, 6}, {2, 5, 8}, {2, 6, 8}, {3, 4, 5}, {3, 6, 8}, {4, 5, 7}, {4, 6, 7}, {5, 7, 8}}

theorem isTri2_P6 : IsTri2 P6 := by unfold IsTri2; decide +kernel
theorem isClosed2_P6 : IsClosed2 P6 := by unfold IsClosed2; decide +kernel
/-- The 6-vertex projective plane has Euler characteristic `1`. -/
theorem euler2_P6 : euler2 P6 = 1 := by decide +kernel

theorem isTri2_T9 : IsTri2 T9 := by unfold IsTri2; decide +kernel
theorem isClosed2_T9 : IsClosed2 T9 := by unfold IsClosed2; decide +kernel
/-- The 9-vertex torus has Euler characteristic `0`. -/
theorem euler2_T9 : euler2 T9 = 0 := by decide +kernel

/-! ## Orientations given by lists of oriented triangles -/

/-- The sum of the oriented triangles of a list. -/
def olist (l : List (ℕ × ℕ × ℕ)) (x y z : ℕ) : ℤ :=
  (l.map fun t => otri t.1 t.2.1 t.2.2 x y z).sum

lemma olist_rot (l : List (ℕ × ℕ × ℕ)) (x y z : ℕ) : olist l y z x = olist l x y z := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    simp only [olist, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, otri_rot]

lemma olist_swap (l : List (ℕ × ℕ × ℕ)) (x y z : ℕ) : olist l y x z = - olist l x y z := by
  induction l with
  | nil => simp [olist]
  | cons t l ih =>
    simp only [olist, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, otri_swap]
    ring

lemma olist_eq_zero {l : List (ℕ × ℕ × ℕ)} {x y z : ℕ}
    (h : ∀ t ∈ l, ({x, y, z} : Finset ℕ) ≠ {t.1, t.2.1, t.2.2}) : olist l x y z = 0 := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    simp only [olist, List.map_cons, List.sum_cons] at ih ⊢
    rw [otri_eq_zero (h t (by simp)), ih fun t' ht' => h t' (by simp [ht']), zero_add]

lemma sum_olist {l : List (ℕ × ℕ × ℕ)} {S : Finset ℕ}
    (hS : ∀ t ∈ l, t.1 ∈ S ∧ t.2.1 ∈ S ∧ t.2.2 ∈ S) (u v : ℕ) :
    ∑ w ∈ S, olist l u v w =
      (l.map fun t => edir t.1 t.2.1 u v + edir t.2.1 t.2.2 u v + edir t.2.2 t.1 u v).sum := by
  induction l with
  | nil => simp [olist]
  | cons t l ih =>
    simp only [olist, List.map_cons, List.sum_cons] at ih ⊢
    obtain ⟨h1, h2, h3⟩ := hS t (by simp)
    rw [sum_add_distrib, sum_otri h1 h2 h3, ih fun t' ht' => hS t' (by simp [ht'])]

/-- **A list of oriented triangles is an orientation** of a complex `L` on the labels below `N`
once three finite checks hold: every listed triangle is in `L`, every triangle of `L` gets the
value `±1`, and every edge gets zero boundary. -/
theorem isOrientation_olist {L : Finset (Finset ℕ)} {l : List (ℕ × ℕ × ℕ)} {N : ℕ}
    (hmem : ∀ t ∈ l, ({t.1, t.2.1, t.2.2} : Finset ℕ) ∈ L) (hlt : ∀ τ ∈ L, ∀ v ∈ τ, v < N)
    (hunit : ∀ x < N, ∀ y < N, ∀ z < N, ({x, y, z} : Finset ℕ) ∈ L →
      olist l x y z = 1 ∨ olist l x y z = -1)
    (hedge : ∀ u < N, ∀ v < N,
      (l.map fun t => edir t.1 t.2.1 u v + edir t.2.1 t.2.2 u v + edir t.2.2 t.1 u v).sum = 0) :
    IsOrientation L (olist l) where
  rot := olist_rot l
  swap := olist_swap l
  supp x y z h := by
    by_contra hn
    exact h (olist_eq_zero fun t ht e => hn (e ▸ hmem t ht))
  unit x y z h :=
    hunit x (hlt _ h x (by simp)) y (hlt _ h y (by simp)) z (hlt _ h z (by simp)) h
  cycle u v := by
    have hl : ∀ t ∈ l, t.1 < N ∧ t.2.1 < N ∧ t.2.2 < N := fun t ht =>
      ⟨hlt _ (hmem t ht) _ (by simp), hlt _ (hmem t ht) _ (by simp),
        hlt _ (hmem t ht) _ (by simp)⟩
    rw [sum_olist fun t ht => ⟨mem_verts2.mpr ⟨_, hmem t ht, by simp⟩,
      mem_verts2.mpr ⟨_, hmem t ht, by simp⟩, mem_verts2.mpr ⟨_, hmem t ht, by simp⟩⟩]
    by_cases hu : u < N
    · by_cases hv : v < N
      · exact hedge u hu v hv
      · refine List.sum_eq_zero fun a ha => ?_
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
        obtain ⟨h1, h2, h3⟩ := hl t ht
        simp only [edir]
        split_ifs <;> omega
    · refine List.sum_eq_zero fun a ha => ?_
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
      obtain ⟨h1, h2, h3⟩ := hl t ht
      simp only [edir]
      split_ifs <;> omega

/-! ## The torus is orientable -/

/-- The triangles of `T9`, oriented counterclockwise in the grid. -/
def T9or : List (ℕ × ℕ × ℕ) :=
  [(0, 2, 1), (2, 4, 1), (1, 4, 3), (4, 5, 3), (3, 5, 0), (5, 2, 0), (2, 6, 4), (6, 7, 4), (4, 7, 5), (7, 8, 5), (5, 8, 2), (8, 6, 2), (6, 0, 7), (0, 1, 7), (7, 1, 8), (1, 3, 8), (8, 3, 6), (3, 0, 6)]

lemma T9or_mem : ∀ t ∈ T9or, ({t.1, t.2.1, t.2.2} : Finset ℕ) ∈ T9 := by decide +kernel

lemma T9_lt : ∀ τ ∈ T9, ∀ v ∈ τ, v < 9 := by decide +kernel

lemma T9_unit : ∀ x < 9, ∀ y < 9, ∀ z < 9, ({x, y, z} : Finset ℕ) ∈ T9 →
    olist T9or x y z = 1 ∨ olist T9or x y z = -1 := by decide +kernel

lemma T9_edges : ∀ u < 9, ∀ v < 9,
    (T9or.map fun t => edir t.1 t.2.1 u v + edir t.2.1 t.2.2 u v + edir t.2.2 t.1 u v).sum = 0 := by
  decide +kernel

/-- **The 9-vertex torus is orientable**: the counterclockwise orientation of the grid. -/
theorem isOrientation_T9 : IsOrientation T9 (olist T9or) :=
  isOrientation_olist T9or_mem T9_lt T9_unit T9_edges

/-- The 9-vertex torus `T9` is orientable. -/
theorem isOrientable_T9 : IsOrientable T9 := ⟨_, isOrientation_T9⟩

/-! ## The projective plane is not orientable -/

lemma P6_lt : ∀ t ∈ P6, ∀ x ∈ t, x < 6 := by decide +kernel

lemma P6_cover : ∀ n < 6, ∃ t ∈ P6.erase {0, 1, 2}, n ∈ t := by decide +kernel

/-- **No complex containing the Möbius band `P6` minus a triangle as the full neighbourhood of its
inner vertices `3, 4, 5` is orientable.** The two triangles at each of its twelve inner edges carry
opposite values of an orientation, and going around the Möbius band this gives `o = −o`. -/
theorem not_isOrientable_of_P6 {V : Type*} [DecidableEq V] {C : Finset (Finset V)} {f : ℕ ↪ V}
    (hsub : liftK f (P6.erase {0, 1, 2}) ⊆ C)
    (hloc : ∀ n ∈ ({3, 4, 5} : Finset ℕ), ∀ t ∈ C, f n ∈ t →
      t ∈ liftK f (P6.erase {0, 1, 2})) :
    ¬ IsOrientable C := by
  rintro ⟨o, ho⟩
  have hv : ∀ n < 6, f n ∈ verts2 C := fun n hn => by
    obtain ⟨t, ht, hnt⟩ := P6_cover n hn
    exact mem_verts2.mpr ⟨t.map f, hsub (mem_liftK.mpr ⟨t, ht, rfl⟩), mem_map_of_mem f hnt⟩
  have hap : ∀ {u v p q : ℕ}, u ∈ ({3, 4, 5} : Finset ℕ) →
      (∀ n, ({u, v, n} : Finset ℕ) ∈ P6.erase {0, 1, 2} → n = p ∨ n = q) →
      ∀ w, ({f u, f v, w} : Finset V) ∈ C → w = f p ∨ w = f q := by
    intro u v p q hu hn w hw
    obtain ⟨t, ht, he⟩ := mem_liftK.mp (hloc u hu _ hw (by simp))
    have hwt : w ∈ t.map f := he ▸ by simp
    obtain ⟨m, hm, rfl⟩ := mem_map.mp hwt
    have : t = {u, v, m} := by
      apply map_injective f
      rw [he, tri_map]
    subst this
    rcases hn m ht with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have r0 : o (f 3) (f 0) (f 2) + o (f 3) (f 0) (f 4) = 0 :=
    ho.pair (f.injective.ne (by decide)) (hv 2 (by decide)) (hv 4 (by decide))
      (hap (by decide) fun n hn => (show ∀ n < 6, ({3, 0, n} : Finset ℕ) ∈ P6.erase {0, 1, 2} →
        n = 2 ∨ n = 4 by decide +kernel) n (P6_lt _ (mem_of_mem_erase hn) n (by simp)) hn)
  have r1 : o (f 4) (f 0) (f 3) + o (f 4) (f 0) (f 5) = 0 :=
    ho.pair (f.injective.ne (by decide)) (hv 3 (by decide)) (hv 5 (by decide))
      (hap (by decide) fun n hn => (show ∀ n < 6, ({4, 0, n} : Finset ℕ) ∈ P6.erase {0, 1, 2} →
        n = 3 ∨ n = 5 by decide +kernel) n (P6_lt _ (mem_of_mem_erase hn) n (by simp)) hn)
  have r2 : o (f 5) (f 0) (f 4) + o (f 5) (f 0) (f 1) = 0 :=
    ho.pair (f.injective.ne (by decide)) (hv 4 (by decide)) (hv 1 (by decide))
      (hap (by decide) fun n hn => (show ∀ n < 6, ({5, 0, n} : Finset ℕ) ∈ P6.erase {0, 1, 2} →
        n = 4 ∨ n = 1 by decide +kernel) n (P6_lt _ (mem_of_mem_erase hn) n (by simp)) hn)
  have r3 : o (f 3) (f 1) (f 4) + o (f 3) (f 1) (f 5) = 0 :=
    ho.pair (f.injective.ne (by decide)) (hv 4 (by decide)) (hv 5 (by decide))
      (hap (by decide) fun n hn => (show ∀ n < 6, ({3, 1, n} : Finset ℕ) ∈ P6.erase {0, 1, 2} →
        n = 4 ∨ n = 5 by decide +kernel) n (P6_lt _ (mem_of_mem_erase hn) n (by simp)) hn)
  have r4 : o (f 4) (f 1) (f 2) + o (f 4) (f 1) (f 3) = 0 :=
    ho.pair (f.injective.ne (by decide)) (hv 2 (by decide)) (hv 3 (by decide))
      (hap (by decide) fun n hn => (show ∀ n < 6, ({4, 1, n} : Finset ℕ) ∈ P6.erase {0, 1, 2} →
        n = 2 ∨ n = 3 by decide +kernel) n (P6_lt _ (mem_of_mem_erase hn) n (by simp)) hn)
  have r5 : o (f 5) (f 1) (f 0) + o (f 5) (f 1) (f 3) = 0 :=
    ho.pair (f.injective.ne (by decide)) (hv 0 (by decide)) (hv 3 (by decide))
      (hap (by decide) fun n hn => (show ∀ n < 6, ({5, 1, n} : Finset ℕ) ∈ P6.erase {0, 1, 2} →
        n = 0 ∨ n = 3 by decide +kernel) n (P6_lt _ (mem_of_mem_erase hn) n (by simp)) hn)
  have r6 : o (f 3) (f 2) (f 0) + o (f 3) (f 2) (f 5) = 0 :=
    ho.pair (f.injective.ne (by decide)) (hv 0 (by decide)) (hv 5 (by decide))
      (hap (by decide) fun n hn => (show ∀ n < 6, ({3, 2, n} : Finset ℕ) ∈ P6.erase {0, 1, 2} →
        n = 0 ∨ n = 5 by decide +kernel) n (P6_lt _ (mem_of_mem_erase hn) n (by simp)) hn)
  have r7 : o (f 4) (f 2) (f 1) + o (f 4) (f 2) (f 5) = 0 :=
    ho.pair (f.injective.ne (by decide)) (hv 1 (by decide)) (hv 5 (by decide))
      (hap (by decide) fun n hn => (show ∀ n < 6, ({4, 2, n} : Finset ℕ) ∈ P6.erase {0, 1, 2} →
        n = 1 ∨ n = 5 by decide +kernel) n (P6_lt _ (mem_of_mem_erase hn) n (by simp)) hn)
  have r8 : o (f 5) (f 2) (f 3) + o (f 5) (f 2) (f 4) = 0 :=
    ho.pair (f.injective.ne (by decide)) (hv 3 (by decide)) (hv 4 (by decide))
      (hap (by decide) fun n hn => (show ∀ n < 6, ({5, 2, n} : Finset ℕ) ∈ P6.erase {0, 1, 2} →
        n = 3 ∨ n = 4 by decide +kernel) n (P6_lt _ (mem_of_mem_erase hn) n (by simp)) hn)
  have r9 : o (f 4) (f 3) (f 0) + o (f 4) (f 3) (f 1) = 0 :=
    ho.pair (f.injective.ne (by decide)) (hv 0 (by decide)) (hv 1 (by decide))
      (hap (by decide) fun n hn => (show ∀ n < 6, ({4, 3, n} : Finset ℕ) ∈ P6.erase {0, 1, 2} →
        n = 0 ∨ n = 1 by decide +kernel) n (P6_lt _ (mem_of_mem_erase hn) n (by simp)) hn)
  have r10 : o (f 5) (f 3) (f 2) + o (f 5) (f 3) (f 1) = 0 :=
    ho.pair (f.injective.ne (by decide)) (hv 2 (by decide)) (hv 1 (by decide))
      (hap (by decide) fun n hn => (show ∀ n < 6, ({5, 3, n} : Finset ℕ) ∈ P6.erase {0, 1, 2} →
        n = 2 ∨ n = 1 by decide +kernel) n (P6_lt _ (mem_of_mem_erase hn) n (by simp)) hn)
  have r11 : o (f 5) (f 4) (f 0) + o (f 5) (f 4) (f 2) = 0 :=
    ho.pair (f.injective.ne (by decide)) (hv 0 (by decide)) (hv 2 (by decide))
      (hap (by decide) fun n hn => (show ∀ n < 6, ({5, 4, n} : Finset ℕ) ∈ P6.erase {0, 1, 2} →
        n = 0 ∨ n = 2 by decide +kernel) n (P6_lt _ (mem_of_mem_erase hn) n (by simp)) hn)
  have hu := ho.unit (f 0) (f 2) (f 3)
    (hsub (mem_liftK.mpr ⟨{0, 2, 3}, by decide, tri_map f 0 2 3⟩))
  rcases hu with hu | hu <;> linarith [ho.rot (f 0) (f 2) (f 3), ho.rot (f 2) (f 3) (f 0), ho.swap (f 0) (f 2) (f 3),
      ho.swap (f 2) (f 3) (f 0), ho.swap (f 3) (f 0) (f 2),
      ho.rot (f 0) (f 3) (f 4), ho.rot (f 3) (f 4) (f 0), ho.swap (f 0) (f 3) (f 4),
      ho.swap (f 3) (f 4) (f 0), ho.swap (f 4) (f 0) (f 3),
      ho.rot (f 0) (f 4) (f 5), ho.rot (f 4) (f 5) (f 0), ho.swap (f 0) (f 4) (f 5),
      ho.swap (f 4) (f 5) (f 0), ho.swap (f 5) (f 0) (f 4),
      ho.rot (f 0) (f 1) (f 5), ho.rot (f 1) (f 5) (f 0), ho.swap (f 0) (f 1) (f 5),
      ho.swap (f 1) (f 5) (f 0), ho.swap (f 5) (f 0) (f 1),
      ho.rot (f 1) (f 2) (f 4), ho.rot (f 2) (f 4) (f 1), ho.swap (f 1) (f 2) (f 4),
      ho.swap (f 2) (f 4) (f 1), ho.swap (f 4) (f 1) (f 2),
      ho.rot (f 2) (f 3) (f 5), ho.rot (f 3) (f 5) (f 2), ho.swap (f 2) (f 3) (f 5),
      ho.swap (f 3) (f 5) (f 2), ho.swap (f 5) (f 2) (f 3),
      ho.rot (f 1) (f 3) (f 4), ho.rot (f 3) (f 4) (f 1), ho.swap (f 1) (f 3) (f 4),
      ho.swap (f 3) (f 4) (f 1), ho.swap (f 4) (f 1) (f 3),
      ho.rot (f 2) (f 4) (f 5), ho.rot (f 4) (f 5) (f 2), ho.swap (f 2) (f 4) (f 5),
      ho.swap (f 4) (f 5) (f 2), ho.swap (f 5) (f 2) (f 4),
      ho.rot (f 1) (f 3) (f 5), ho.rot (f 3) (f 5) (f 1), ho.swap (f 1) (f 3) (f 5),
      ho.swap (f 3) (f 5) (f 1), ho.swap (f 5) (f 1) (f 3)]

/-- **A connected sum with the projective plane `P6` (glued along `{0, 1, 2}`) is not
orientable.** -/
theorem not_isOrientable_csum_P6 {V : Type*} [DecidableEq V] {L : Finset (Finset V)}
    {σ : Finset V} {f : ℕ ↪ V} (hg : IsGlue L σ P6 {0, 1, 2} f) :
    ¬ IsOrientable (csum L σ P6 {0, 1, 2} f) := by
  refine not_isOrientable_of_P6 subset_union_right fun n hn t ht hnt => ?_
  rcases mem_union.mp ht with ht | ht
  · exfalso
    refine hg.fresh n ?_ ?_ (mem_verts2.mpr ⟨t, mem_of_mem_erase ht, hnt⟩)
    · simp only [mem_insert, mem_singleton] at hn
      rcases hn with rfl | rfl | rfl <;> decide
    · simp only [mem_insert, mem_singleton] at hn ⊢
      omega
  · exact ht

end Lightlike.Surfaces
