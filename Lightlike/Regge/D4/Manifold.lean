import Lightlike.Regge.D4.Complex
import Lightlike.Regge.Manifold

/-!
# The manifold condition at triangles

`Lightlike/Regge/D4/Complex.lean` classifies triangles combinatorially: a triangle is on the
boundary if it lies in a tetrahedron contained in only one 4-simplex, and interior otherwise. This
file adds the condition under which the classification has its geometric meaning, as
`Lightlike/Regge/Manifold.lean` does for edges in 3D.

In a triangulated 4-manifold the 4-simplices around an interior triangle `abc` form a ring: their
vertices other than `a, b, c` form a cycle `w 0, …, w (n-1)`, `w n = w 0`, the **link** of the
triangle, and the 4-simplices are `{a, b, c, w i, w (i+1)}`. Around a boundary triangle they form a
fan whose link is a path `w 0, …, w n`.

## Definitions

* `IsCycleLink4 K a b c n w`: the link of `{a, b, c}` is a cycle of length `n ≥ 3`.
* `IsPathLink4 K a b c n w`: the link of `{a, b, c}` is a path with `n ≥ 1` edges.
* `IsTriManifold K`: the link of every triangle is a cycle or a path. This is the part of the
  manifold condition that 4D Regge calculus uses (curvature sits on triangles).

## Main results

* `IsCycleLink4.mem_intTris4`, `IsPathLink4.mem_bdryTris4`: a triangle with a cycle link is
  interior, one with a path link is on the boundary.
* `IsTriManifold.mem_intTris4_iff`, `IsTriManifold.mem_bdryTris4_iff`: on such complexes the
  combinatorial classification is exactly cycle links versus path links.
* `IsCycleLink4.angleSum4_eq`: around a triangle with a cycle link, the angle sum runs once over
  the ring of 4-simplices.
* `isTriManifold_of_check`: a decision procedure, proven sound, with candidate link lists
  `finLinkWitness4` for vertices `Fin n`, so that the kernel can decide the condition on examples.
-/

open Finset

namespace Lightlike.Regge4

open Lightlike.FourD (Complex4)
open Lightlike.FourD.Complex4 (mem_faces mem_star mem_bdryTets)
open Lightlike.Regge (cycSucc cycSucc_lt)

variable {V : Type*} [DecidableEq V]

/-- Three distinct vertices form a 3-element set. -/
theorem card_three {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    #({a, b, c} : Finset V) = 3 := by
  rw [card_insert_of_notMem (by simp [hab, hac]), card_pair hbc]

/-- Four distinct vertices form a 4-element set. -/
theorem card_four {a b c d : V} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) : #({a, b, c, d} : Finset V) = 4 := by
  rw [card_insert_of_notMem (by simp [hab, hac, had]), card_three hbc hbd hcd]

/-- The link of the triangle `{a, b, c}` in `K` is a cycle of length `n ≥ 3`: the 4-simplices of
`K` containing `{a, b, c}` are exactly `{a, b, c, w i, w (i+1)}` for `i < n`, where
`w 0, …, w (n-1)` are distinct vertices other than `a, b, c`, and `w n = w 0`. -/
structure IsCycleLink4 (K : Complex4 V) (a b c : V) (n : ℕ) (w : ℕ → V) : Prop where
  ne_ab : a ≠ b
  ne_ac : a ≠ c
  ne_bc : b ≠ c
  three_le : 3 ≤ n
  ne_a : ∀ i < n, w i ≠ a
  ne_b : ∀ i < n, w i ≠ b
  ne_c : ∀ i < n, w i ≠ c
  inj : Set.InjOn w (range n)
  closed : w n = w 0
  star_eq : K.star {a, b, c} = (range n).image fun i => {a, b, c, w i, w (i + 1)}

/-- The link of the triangle `{a, b, c}` in `K` is a path with `n ≥ 1` edges: the 4-simplices of
`K` containing `{a, b, c}` are exactly `{a, b, c, w i, w (i+1)}` for `i < n`, where
`w 0, …, w n` are distinct vertices other than `a, b, c`. -/
structure IsPathLink4 (K : Complex4 V) (a b c : V) (n : ℕ) (w : ℕ → V) : Prop where
  ne_ab : a ≠ b
  ne_ac : a ≠ c
  ne_bc : b ≠ c
  one_le : 1 ≤ n
  ne_a : ∀ i ≤ n, w i ≠ a
  ne_b : ∀ i ≤ n, w i ≠ b
  ne_c : ∀ i ≤ n, w i ≠ c
  inj : Set.InjOn w (range (n + 1))
  star_eq : K.star {a, b, c} = (range n).image fun i => {a, b, c, w i, w (i + 1)}

/-- `K` satisfies the **manifold condition at triangles**: the link of every triangle is a cycle
(interior triangle) or a path (boundary triangle). -/
def IsTriManifold (K : Complex4 V) : Prop :=
  ∀ t ∈ K.tris, ∃ a b c n w, t = {a, b, c} ∧
    (IsCycleLink4 K a b c n w ∨ IsPathLink4 K a b c n w)

namespace IsCycleLink4

variable {K : Complex4 V} {a b c : V} {n : ℕ} {w : ℕ → V}

/-- In a cycle link, `w (i+1)` is the link vertex with index `cycSucc n i`. -/
theorem w_succ (h : IsCycleLink4 K a b c n w) {i : ℕ} (hi : i < n) :
    w (i + 1) = w (cycSucc n i) := by
  unfold cycSucc
  split_ifs with h1
  · rfl
  · rw [show i + 1 = n by omega, h.closed]

/-- The link vertices `w 0, …, w (n-1)` are distinct. -/
theorem w_inj (h : IsCycleLink4 K a b c n w) {i j : ℕ} (hi : i < n) (hj : j < n)
    (hw : w i = w j) : i = j :=
  h.inj (by simpa using hi) (by simpa using hj) hw

/-- The `n` 4-simplices around the triangle are distinct. -/
theorem injOn_simp (h : IsCycleLink4 K a b c n w) :
    Set.InjOn (fun i => ({a, b, c, w i, w (i + 1)} : Finset V)) (range n) := by
  intro i hi j hj hij
  simp only [coe_range, Set.mem_Iio] at hi hj
  have h3 := h.three_le
  have hsi : cycSucc n i < n := cycSucc_lt (by omega)
  have hsj : cycSucc n j < n := cycSucc_lt (by omega)
  have hij' : ({a, b, c, w i, w (cycSucc n i)} : Finset V) =
      {a, b, c, w j, w (cycSucc n j)} := by
    rw [← h.w_succ hi, ← h.w_succ hj]
    exact hij
  have m1 : w i ∈ ({a, b, c, w j, w (cycSucc n j)} : Finset V) := by rw [← hij']; simp
  have m2 : w (cycSucc n i) ∈ ({a, b, c, w j, w (cycSucc n j)} : Finset V) := by
    rw [← hij']; simp
  simp only [mem_insert, mem_singleton] at m1 m2
  rcases m1 with h1 | h1 | h1 | h1 | h1
  · exact absurd h1 (h.ne_a i hi)
  · exact absurd h1 (h.ne_b i hi)
  · exact absurd h1 (h.ne_c i hi)
  · exact h.w_inj hi hj h1
  · have e1 := h.w_inj hi hsj h1
    exfalso
    rcases m2 with h2 | h2 | h2 | h2 | h2
    · exact h.ne_a _ hsi h2
    · exact h.ne_b _ hsi h2
    · exact h.ne_c _ hsi h2
    · have e2 := h.w_inj hsi hj h2
      unfold cycSucc at e1 e2
      split_ifs at e1 e2 <;> omega
    · have e2 := h.w_inj hsi hsj h2
      unfold cycSucc at e1 e2
      split_ifs at e1 e2 <;> omega

/-- The 4-simplex `{a, b, c, w i, w (i+1)}`, `i < n`, belongs to `K`. -/
theorem simp_mem (h : IsCycleLink4 K a b c n w) {i : ℕ} (hi : i < n) :
    ({a, b, c, w i, w (i + 1)} : Finset V) ∈ K.simps := by
  have : ({a, b, c, w i, w (i + 1)} : Finset V) ∈ K.star {a, b, c} := by
    rw [h.star_eq]
    exact mem_image.mpr ⟨i, mem_range.mpr hi, rfl⟩
  exact (mem_star.mp this).1

/-- A triangle with a cycle link is a triangle of `K`. -/
theorem mem_tris (h : IsCycleLink4 K a b c n w) : ({a, b, c} : Finset V) ∈ K.tris :=
  mem_faces.mpr ⟨_, h.simp_mem (i := 0) (by have := h.three_le; omega),
    by intro x; simp; tauto, card_three h.ne_ab h.ne_ac h.ne_bc⟩

/-- The five vertices of each 4-simplex `{a, b, c, w i, w (i+1)}` of the ring are distinct. -/
theorem simp_distinct (h : IsCycleLink4 K a b c n w) {i : ℕ} (hi : i < n) :
    a ≠ w i ∧ a ≠ w (i + 1) ∧ b ≠ w i ∧ b ≠ w (i + 1) ∧ c ≠ w i ∧ c ≠ w (i + 1) ∧
      w i ≠ w (i + 1) := by
  have h3 := h.three_le
  have hs : cycSucc n i < n := cycSucc_lt (by omega)
  rw [h.w_succ hi]
  refine ⟨(h.ne_a i hi).symm, (h.ne_a _ hs).symm, (h.ne_b i hi).symm, (h.ne_b _ hs).symm,
    (h.ne_c i hi).symm, (h.ne_c _ hs).symm, ?_⟩
  intro he
  have := h.w_inj hi hs he
  unfold cycSucc at this
  split_ifs at this <;> omega

/-- **A triangle whose link is a cycle is interior**: each tetrahedron `{a, b, c, w k}` lies in the
two 4-simplices `{a, b, c, w (k-1), w k}` and `{a, b, c, w k, w (k+1)}`, so none is a boundary
tetrahedron. -/
theorem mem_intTris4 (h : IsCycleLink4 K a b c n w) : ({a, b, c} : Finset V) ∈ intTris4 K := by
  refine mem_filter.mpr ⟨h.mem_tris, ?_⟩
  rintro ⟨τ, hτ, hsub⟩
  have h3 := h.three_le
  obtain ⟨hτt, hτ1⟩ := mem_bdryTets.mp hτ
  obtain ⟨σ, hσ, hτσ, hτ4⟩ := mem_faces.mp hτt
  have hσstar : σ ∈ K.star {a, b, c} := mem_star.mpr ⟨hσ, hsub.trans hτσ⟩
  rw [h.star_eq, mem_image] at hσstar
  obtain ⟨i, hi, rfl⟩ := hσstar
  rw [mem_range] at hi
  -- the fourth vertex `v` of `τ`
  have hcard : #(τ \ {a, b, c}) = 1 := by
    rw [card_sdiff_of_subset hsub, hτ4, card_three h.ne_ab h.ne_ac h.ne_bc]
  obtain ⟨v, hv⟩ := card_pos.mp (show 0 < #(τ \ {a, b, c}) by omega)
  rw [mem_sdiff, mem_insert, mem_insert, mem_singleton, not_or, not_or] at hv
  have hvt := hτσ hv.1
  simp only [mem_insert, mem_singleton] at hvt
  -- `v = w k` for some `k < n`
  obtain ⟨k, hk, rfl⟩ : ∃ k < n, v = w k := by
    rcases hvt with h1 | h1 | h1 | h1 | h1
    · exact absurd h1 hv.2.1
    · exact absurd h1 hv.2.2.1
    · exact absurd h1 hv.2.2.2
    · exact ⟨i, hi, h1⟩
    · exact ⟨cycSucc n i, cycSucc_lt (by omega), h1.trans (h.w_succ hi)⟩
  have hτ_eq : τ = {a, b, c, w k} := by
    symm
    apply eq_of_subset_of_card_le
    · simp only [insert_subset_iff, singleton_subset_iff]
      exact ⟨hsub (by simp), hsub (by simp), hsub (by simp), hv.1⟩
    · rw [hτ4, card_four h.ne_ab h.ne_ac (h.ne_a k hk).symm h.ne_bc (h.ne_b k hk).symm
        (h.ne_c k hk).symm]
  -- the previous index `p`, with `w (p+1) = w k`
  set p := if k = 0 then n - 1 else k - 1 with hp_def
  have hp : p < n := by rw [hp_def]; split_ifs <;> omega
  have hpk : w (p + 1) = w k := by
    rw [hp_def]
    split_ifs with hk0
    · rw [show n - 1 + 1 = n by omega, h.closed, hk0]
    · rw [show k - 1 + 1 = k by omega]
  have hne : ({a, b, c, w k, w (k + 1)} : Finset V) ≠ {a, b, c, w p, w (p + 1)} := by
    intro he
    have := h.injOn_simp (by simpa using hk) (by simpa using hp) he
    rw [hp_def] at this
    split_ifs at this <;> omega
  have hsub2 : ({{a, b, c, w k, w (k + 1)}, {a, b, c, w p, w (p + 1)}} : Finset (Finset V)) ⊆
      K.star τ := by
    intro σ' hσ'
    simp only [mem_insert, mem_singleton] at hσ'
    rcases hσ' with rfl | rfl
    · exact mem_star.mpr ⟨h.simp_mem hk, by rw [hτ_eq]; intro x; simp; tauto⟩
    · refine mem_star.mpr ⟨h.simp_mem hp, ?_⟩
      rw [hτ_eq, hpk]
      intro x
      simp
      tauto
  have := card_le_card hsub2
  rw [card_pair hne, hτ1] at this
  omega

/-- Around a triangle with a cycle link, the angle sum runs once over the ring of 4-simplices. -/
theorem angleSum4_eq (h : IsCycleLink4 K a b c n w) (ℓ : Finset V → ℝ) :
    angleSum4 K ℓ {a, b, c} =
      ∑ i ∈ range n, dihedralAt4 ℓ {a, b, c, w i, w (i + 1)} {a, b, c} := by
  rw [angleSum4, h.star_eq, sum_image h.injOn_simp]

/-- The triangle lies in exactly `n` 4-simplices. -/
theorem card_star (h : IsCycleLink4 K a b c n w) : #(K.star {a, b, c}) = n := by
  rw [h.star_eq, card_image_of_injOn h.injOn_simp, card_range]

end IsCycleLink4

namespace IsPathLink4

variable {K : Complex4 V} {a b c : V} {n : ℕ} {w : ℕ → V}

/-- The 4-simplex `{a, b, c, w i, w (i+1)}`, `i < n`, belongs to `K`. -/
theorem simp_mem (h : IsPathLink4 K a b c n w) {i : ℕ} (hi : i < n) :
    ({a, b, c, w i, w (i + 1)} : Finset V) ∈ K.simps := by
  have : ({a, b, c, w i, w (i + 1)} : Finset V) ∈ K.star {a, b, c} := by
    rw [h.star_eq]
    exact mem_image.mpr ⟨i, mem_range.mpr hi, rfl⟩
  exact (mem_star.mp this).1

/-- **A triangle whose link is a path is on the boundary**: the tetrahedron `{a, b, c, w 0}` at
the end of the path lies only in the 4-simplex `{a, b, c, w 0, w 1}`. -/
theorem mem_bdryTris4 (h : IsPathLink4 K a b c n w) : ({a, b, c} : Finset V) ∈ bdryTris4 K := by
  have h1 := h.one_le
  have hσ := h.simp_mem (i := 0) (by omega)
  have hw0a := h.ne_a 0 (by omega)
  have hw0b := h.ne_b 0 (by omega)
  have hw0c := h.ne_c 0 (by omega)
  have hstar : K.star {a, b, c, w 0} = {{a, b, c, w 0, w (0 + 1)}} := by
    ext σ
    simp only [mem_star, mem_singleton]
    constructor
    · rintro ⟨hσK, hsub⟩
      have : σ ∈ K.star {a, b, c} :=
        mem_star.mpr ⟨hσK, (by intro x; simp; tauto : ({a, b, c} : Finset V) ⊆ {a, b, c, w 0}).trans
          hsub⟩
      rw [h.star_eq, mem_image] at this
      obtain ⟨i, hi, rfl⟩ := this
      rw [mem_range] at hi
      have hw : w 0 ∈ ({a, b, c, w i, w (i + 1)} : Finset V) := hsub (by simp)
      simp only [mem_insert, mem_singleton] at hw
      rcases hw with hw | hw | hw | hw | hw
      · exact absurd hw hw0a
      · exact absurd hw hw0b
      · exact absurd hw hw0c
      · have := h.inj (by simp only [coe_range, Set.mem_Iio]; omega)
          (by simp only [coe_range, Set.mem_Iio]; omega) hw
        subst this
        rfl
      · have := h.inj (by simp only [coe_range, Set.mem_Iio]; omega)
          (by simp only [coe_range, Set.mem_Iio]; omega) hw
        omega
    · rintro rfl
      exact ⟨hσ, by intro x; simp; tauto⟩
  have hcard4 : #({a, b, c, w 0} : Finset V) = 4 :=
    card_four h.ne_ab h.ne_ac hw0a.symm h.ne_bc hw0b.symm hw0c.symm
  refine mem_filter.mpr ⟨mem_faces.mpr ⟨_, hσ, by intro x; simp; tauto,
    card_three h.ne_ab h.ne_ac h.ne_bc⟩, ⟨{a, b, c, w 0}, ?_, by intro x; simp; tauto⟩⟩
  refine mem_bdryTets.mpr ⟨mem_faces.mpr ⟨_, hσ, by intro x; simp; tauto, hcard4⟩, ?_⟩
  rw [hstar, card_singleton]

end IsPathLink4

/-- On a complex satisfying the manifold condition at triangles, the interior triangles are exactly
those whose link is a cycle. -/
theorem IsTriManifold.mem_intTris4_iff {K : Complex4 V} (hK : IsTriManifold K) {t : Finset V} :
    t ∈ intTris4 K ↔ ∃ a b c n w, t = {a, b, c} ∧ IsCycleLink4 K a b c n w := by
  constructor
  · intro ht
    obtain ⟨a, b, c, n, w, rfl, hc | hp⟩ := hK t (mem_filter.mp ht).1
    · exact ⟨a, b, c, n, w, rfl, hc⟩
    · exact absurd hp.mem_bdryTris4 (disjoint_left.mp (disjoint_intTris4_bdryTris4 K) ht)
  · rintro ⟨a, b, c, n, w, rfl, hc⟩
    exact hc.mem_intTris4

/-- On a complex satisfying the manifold condition at triangles, the boundary triangles are exactly
those whose link is a path. -/
theorem IsTriManifold.mem_bdryTris4_iff {K : Complex4 V} (hK : IsTriManifold K) {t : Finset V} :
    t ∈ bdryTris4 K ↔ ∃ a b c n w, t = {a, b, c} ∧ IsPathLink4 K a b c n w := by
  constructor
  · intro ht
    obtain ⟨a, b, c, n, w, rfl, hc | hp⟩ := hK t (mem_filter.mp ht).1
    · exact absurd ht (disjoint_left.mp (disjoint_intTris4_bdryTris4 K) hc.mem_intTris4)
    · exact ⟨a, b, c, n, w, rfl, hp⟩
  · rintro ⟨a, b, c, n, w, rfl, hp⟩
    exact hp.mem_bdryTris4

/-! ## A decision procedure for triangle links -/

/-- Computable check that the list `L` is the link of the triangle `{a, b, c}`, as a cycle. -/
def cycleCheck4 (K : Complex4 V) (a b c : V) (L : List V) : Prop :=
  a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ 3 ≤ L.length ∧ L.Nodup ∧ a ∉ L ∧ b ∉ L ∧ c ∉ L ∧
    K.star {a, b, c} = (range L.length).image fun i =>
      ({a, b, c, L.getD i a, L.getD ((i + 1) % L.length) a} : Finset V)

/-- Computable check that the list `L` is the link of the triangle `{a, b, c}`, as a path. -/
def pathCheck4 (K : Complex4 V) (a b c : V) (L : List V) : Prop :=
  a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ 2 ≤ L.length ∧ L.Nodup ∧ a ∉ L ∧ b ∉ L ∧ c ∉ L ∧
    K.star {a, b, c} = (range (L.length - 1)).image fun i =>
      ({a, b, c, L.getD i a, L.getD (i + 1) a} : Finset V)

instance (K : Complex4 V) (a b c : V) (L : List V) : Decidable (cycleCheck4 K a b c L) := by
  unfold cycleCheck4; infer_instance

instance (K : Complex4 V) (a b c : V) (L : List V) : Decidable (pathCheck4 K a b c L) := by
  unfold pathCheck4; infer_instance

/-- A list passing `cycleCheck4` is a cycle link. -/
theorem IsCycleLink4.of_check {K : Complex4 V} {a b c : V} {L : List V}
    (h : cycleCheck4 K a b c L) : IsCycleLink4 K a b c L.length fun i => L.getD (i % L.length) a := by
  obtain ⟨hab, hac, hbc, h3, hnd, ha, hb, hc, hstar⟩ := h
  have hget : ∀ i (hi : i < L.length), L.getD (i % L.length) a = L[i]'hi := by
    intro i hi
    rw [Nat.mod_eq_of_lt hi, List.getD_eq_getElem _ _ hi]
  refine ⟨hab, hac, hbc, h3, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_,
    fun i hi j hj hij => ?_, ?_, ?_⟩
  · rw [hget i hi]
    exact fun h => ha (h ▸ List.getElem_mem hi)
  · rw [hget i hi]
    exact fun h => hb (h ▸ List.getElem_mem hi)
  · rw [hget i hi]
    exact fun h => hc (h ▸ List.getElem_mem hi)
  · simp only [coe_range, Set.mem_Iio] at hi hj
    simp only [hget i hi, hget j hj] at hij
    exact (hnd.getElem_inj_iff).mp hij
  · simp
  · rw [hstar]
    refine image_congr fun i hi => ?_
    simp only [coe_range, Set.mem_Iio] at hi
    simp only [Nat.mod_eq_of_lt hi]

/-- A list passing `pathCheck4` is a path link. -/
theorem IsPathLink4.of_check {K : Complex4 V} {a b c : V} {L : List V}
    (h : pathCheck4 K a b c L) : IsPathLink4 K a b c (L.length - 1) fun i => L.getD i a := by
  obtain ⟨hab, hac, hbc, h2, hnd, ha, hb, hc, hstar⟩ := h
  have hget : ∀ i (hi : i ≤ L.length - 1), L.getD i a = L[i]'(by omega) := fun i hi =>
    List.getD_eq_getElem _ _ (by omega)
  refine ⟨hab, hac, hbc, by omega, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_,
    fun i hi j hj hij => ?_, hstar⟩
  · rw [hget i hi]
    exact fun h => ha (h ▸ List.getElem_mem _)
  · rw [hget i hi]
    exact fun h => hb (h ▸ List.getElem_mem _)
  · rw [hget i hi]
    exact fun h => hc (h ▸ List.getElem_mem _)
  · simp only [coe_range, Set.mem_Iio] at hi hj
    simp only [hget i (by omega), hget j (by omega)] at hij
    exact (hnd.getElem_inj_iff).mp hij

/-- **A decision procedure for `IsTriManifold`**: if for every triangle some ordered labelling
`a, b, c` and the candidate list `W a b c` pass `cycleCheck4` or `pathCheck4`, the manifold
condition holds at every triangle. -/
theorem isTriManifold_of_check (K : Complex4 V) (W : V → V → V → List V)
    (h : ∀ t ∈ K.tris, ∃ a ∈ t, ∃ b ∈ t, ∃ c ∈ t,
      cycleCheck4 K a b c (W a b c) ∨ pathCheck4 K a b c (W a b c)) :
    IsTriManifold K := by
  intro t ht
  have ht3 : #t = 3 := Lightlike.FourD.Complex4.card_of_mem_faces ht
  obtain ⟨a, ha, b, hb, c, hc, hcp⟩ := h t ht
  have key : ∀ (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c), t = {a, b, c} := fun hab hac hbc =>
    (eq_of_subset_of_card_le (by simp [insert_subset_iff, ha, hb, hc])
      (by rw [ht3, card_three hab hac hbc])).symm
  rcases hcp with hcy | hpa
  · exact ⟨a, b, c, _, _, key hcy.1 hcy.2.1 hcy.2.2.1, Or.inl (IsCycleLink4.of_check hcy)⟩
  · exact ⟨a, b, c, _, _, key hpa.1 hpa.2.1 hpa.2.2.1, Or.inr (IsPathLink4.of_check hpa)⟩

/-! ### Candidate link lists for vertices `Fin n`

Computed by structural recursion only, so that the kernel can evaluate them in `decide`; their
correctness is never assumed, since `isTriManifold_of_check` verifies them. -/

/-- The vertices of the link of the triangle `{a, b, c}`, in increasing order. -/
def finLinkVerts4 {n : ℕ} (K : Complex4 (Fin n)) (a b c : Fin n) : List (Fin n) :=
  (List.finRange n).filter fun x =>
    decide (x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ ∃ σ ∈ K.simps, ({a, b, c, x} : Finset (Fin n)) ⊆ σ)

/-- The neighbours of `x` in the link of the triangle `{a, b, c}`: the `y` with `{a, b, c, x, y}`
a 4-simplex. -/
def finLinkNbrs4 {n : ℕ} (K : Complex4 (Fin n)) (a b c x : Fin n) : List (Fin n) :=
  (List.finRange n).filter fun y =>
    decide (y ≠ x ∧ y ≠ a ∧ y ≠ b ∧ y ≠ c ∧ ({a, b, c, x, y} : Finset (Fin n)) ∈ K.simps)

/-- Walk along the link of the triangle `{a, b, c}` for at most `k` steps, always to the first
neighbour not visited yet; `acc` holds the visited vertices, most recent first. -/
def finWalk4 {n : ℕ} (K : Complex4 (Fin n)) (a b c : Fin n) :
    ℕ → Fin n → List (Fin n) → List (Fin n)
  | 0, _, acc => acc.reverse
  | k + 1, x, acc =>
    match (finLinkNbrs4 K a b c x).find? (fun y => decide (y ∉ acc)) with
    | some y => finWalk4 K a b c k y (y :: acc)
    | none => acc.reverse

/-- The candidate link list of the triangle `{a, b, c}`: the walk from an end of the link if it has
one (a path), otherwise from its first vertex (a cycle). -/
def finLinkWitness4 {n : ℕ} (K : Complex4 (Fin n)) (a b c : Fin n) : List (Fin n) :=
  match (finLinkVerts4 K a b c).find? (fun x => decide ((finLinkNbrs4 K a b c x).length = 1)) with
  | some x => finWalk4 K a b c n x [x]
  | none =>
    match (finLinkVerts4 K a b c).head? with
    | some x => finWalk4 K a b c n x [x]
    | none => []

end Lightlike.Regge4
