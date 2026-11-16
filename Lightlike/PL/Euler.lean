import Lightlike.PL.Links
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Sum

/-!
# The Euler characteristic

The **Euler characteristic** `χ(K) = Σ_{s ∈ K, s ≠ ∅} (−1)^{#s − 1}` (vertices − edges + triangles
− …) is an invariant of stellar equivalence. We work with the signed count of all faces, empty face
included, `σ(K) = Σ_{s ∈ K} (−1)^{#s}`, which satisfies `σ(K) = 1 − χ(K)` when `K` has a face and
is multiplicative for joins.

## Main results

* `signedCount_join`: `σ(K * L) = σ(K) σ(L)` for disjoint vertex sets.
* `signedCount_starAt`, `StellarEquiv.euler_eq`: stellar subdivisions, and hence stellar
  equivalence, preserve `σ` and `χ`. (The faces removed, `A * lk(A)`, and the faces added,
  `a * ∂A * lk(A)`, have the same signed count `(−1)^{#A} σ(lk A)`.)
* `euler_boundary`, `euler_simplex`, `IsPLSphere.euler`, `IsPLBall.euler`: `χ(Sⁿ) = 1 + (−1)ⁿ` and
  `χ(Bⁿ) = 1`; hence `IsPLSphere.not_isPLBall`: no complex is both a PL sphere and a PL ball.
* `euler_eq_card_verts`, `IsPLSphere.card_verts_zero`: a PL 0-sphere has exactly two vertices.
-/

open Finset

namespace Lightlike.PL

namespace SComplex

variable {V : Type*} [DecidableEq V]

/-- The **signed count of faces** `σ(K) = Σ_{s ∈ K} (−1)^{#s}`, counting the empty face. -/
def signedCount (K : SComplex V) : ℤ := ∑ s ∈ K.faces, (-1 : ℤ) ^ #s

/-- The **Euler characteristic** `χ(K) = Σ_{s ∈ K, s ≠ ∅} (−1)^{#s − 1}`: vertices minus edges plus
triangles, and so on. -/
def euler (K : SComplex V) : ℤ := ∑ s ∈ K.faces.erase ∅, (-1 : ℤ) ^ (#s + 1)

/-- `χ(K) = [∅ ∈ K] − σ(K)`. -/
lemma euler_eq_signedCount (K : SComplex V) :
    K.euler = (if ∅ ∈ K then 1 else 0) - K.signedCount := by
  have hneg : ∀ t : Finset (Finset V),
      ∑ s ∈ t, (-1 : ℤ) ^ (#s + 1) = -∑ s ∈ t, (-1 : ℤ) ^ #s := fun t => by
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun s _ => by ring
  rw [euler, signedCount, hneg]
  split_ifs with h
  · rw [← add_sum_erase _ _ (mem_faces.2 h)]
    simp
  · rw [erase_eq_of_notMem (by simpa using h)]
    ring

/-- **The signed count is multiplicative for joins** of complexes with disjoint vertex sets. -/
theorem signedCount_join {K L : SComplex V} (h : Disjoint K.verts L.verts) :
    (K.join L).signedCount = K.signedCount * L.signedCount := by
  have hinj : Set.InjOn (fun p : Finset V × Finset V => p.1 ∪ p.2) ↑(K.faces ×ˢ L.faces) := by
    rintro ⟨t, u⟩ htu ⟨t', u'⟩ htu' he
    rw [mem_coe, mem_product] at htu htu'
    simp only at he
    have key : ∀ {t u : Finset V}, t ∈ K → u ∈ L → (t ∪ u) ∩ K.verts = t ∧ (t ∪ u) \ K.verts = u :=
      fun {t u} ht hu => by
        refine ⟨?_, ?_⟩
        · rw [union_inter_distrib_right, inter_eq_left.2 (subset_verts ht),
            disjoint_iff_inter_eq_empty.1 (disjoint_of_subset_left (subset_verts hu) h.symm),
            union_empty]
        · rw [union_sdiff_distrib, sdiff_eq_empty_iff_subset.2 (subset_verts ht), empty_union,
            sdiff_eq_self_of_disjoint (disjoint_of_subset_left (subset_verts hu) h.symm)]
    obtain ⟨h1, h2⟩ := key htu.1 htu.2
    obtain ⟨h1', h2'⟩ := key htu'.1 htu'.2
    rw [Prod.mk.injEq]
    exact ⟨h1.symm.trans (he ▸ h1'), h2.symm.trans (he ▸ h2')⟩
  change ∑ s ∈ (K.faces ×ˢ L.faces).image (fun p => p.1 ∪ p.2), (-1 : ℤ) ^ #s = _
  rw [sum_image hinj, signedCount, signedCount, sum_mul_sum, sum_product]
  refine sum_congr rfl fun t ht => sum_congr rfl fun u hu => ?_
  rw [card_union_of_disjoint (disjoint_of_subset_left (subset_verts ht)
    (disjoint_of_subset_right (subset_verts hu) h)), pow_add]

omit [DecidableEq V] in
/-- The simplex on a nonempty set has signed count `0`. -/
lemma signedCount_simplex {A : Finset V} (hA : A.Nonempty) : (simplex A).signedCount = 0 :=
  sum_powerset_neg_one_pow_card_of_nonempty hA

/-- The boundary of the simplex on a nonempty set `A` has signed count `−(−1)^{#A}`. -/
lemma signedCount_boundary {A : Finset V} (hA : A.Nonempty) :
    (boundary A).signedCount = -(-1 : ℤ) ^ #A := by
  change ∑ s ∈ A.powerset.erase A, (-1 : ℤ) ^ #s = _
  rw [sum_erase_eq_sub (mem_powerset_self A), sum_powerset_neg_one_pow_card_of_nonempty hA]
  ring

/-- The faces containing `A` contribute `(−1)^{#A} σ(lk A)`. -/
lemma sum_filter_superset (K : SComplex V) (A : Finset V) :
    ∑ s ∈ K.faces.filter (A ⊆ ·), (-1 : ℤ) ^ #s = (-1) ^ #A * (K.link A).signedCount := by
  have he : K.faces.filter (A ⊆ ·) = (K.link A).faces.image (A ∪ ·) := by
    ext s
    simp only [mem_filter, mem_image, mem_faces]
    constructor
    · rintro ⟨hs, hAs⟩
      exact ⟨s \ A, mem_link'.2 ⟨disjoint_sdiff, by rwa [union_sdiff_of_subset hAs]⟩,
        union_sdiff_of_subset hAs⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨(mem_link'.1 hu).2, subset_union_left⟩
  have hinj : Set.InjOn (A ∪ ·) (K.link A).faces := by
    intro u hu u' hu' h
    simp only [mem_coe, mem_faces] at hu hu'
    have e : ∀ {w : Finset V}, w ∈ K.link A → (A ∪ w) \ A = w := fun hw => by
      rw [union_sdiff_left, sdiff_eq_self_of_disjoint (mem_link'.1 hw).1.symm]
    rw [← e hu, ← e hu']
    exact congrArg (· \ A) h
  rw [he, sum_image hinj, signedCount, mul_sum]
  refine sum_congr rfl fun u hu => ?_
  rw [card_union_of_disjoint (mem_link'.1 hu).1, pow_add]

/-- **Stellar subdivision preserves the signed count.** -/
theorem signedCount_starAt {K : SComplex V} {A : Finset V} {a : V}
    (hne : A.Nonempty) (ha : a ∉ K.verts) : (K.starAt A a).signedCount = K.signedCount := by
  set X := K.faces.filter fun s => ¬ A ⊆ s ∧ A ∪ s ∈ K.faces with hX
  -- the closed star has signed count `0`
  have hstar : ∑ s ∈ K.faces.filter (A ⊆ ·), (-1 : ℤ) ^ #s + ∑ s ∈ X, (-1 : ℤ) ^ #s = 0 := by
    have h1 : (K.star A).faces = K.faces.filter (A ⊆ ·) ∪ X := by
      ext s
      simp only [mem_union, mem_filter, hX, mem_faces, mem_star]
      constructor
      · intro h
        by_cases hAs : A ⊆ s
        · exact .inl ⟨down_mem h subset_union_right, hAs⟩
        · exact .inr ⟨down_mem h subset_union_right, hAs, h⟩
      · rintro (⟨hs, hAs⟩ | ⟨-, -, h⟩)
        · rwa [union_eq_right.2 hAs]
        · exact h
    have h2 : Disjoint (K.faces.filter (A ⊆ ·)) X := by
      rw [hX, disjoint_filter]
      intro s _ h h'
      exact h'.1 h
    have h3 : (K.star A).signedCount = 0 := by
      rw [star_eq_join, signedCount_join, signedCount_simplex hne, zero_mul]
      rw [verts_simplex]
      exact disjoint_verts_link K A
    rw [← sum_union h2, ← h1]
    exact h3
  have hfaces : (K.starAt A a).faces = K.faces.filter (fun s => ¬ A ⊆ s) ∪ X.image (insert a) :=
    rfl
  have hdis : Disjoint (K.faces.filter fun s => ¬ A ⊆ s) (X.image (insert a)) := by
    rw [disjoint_left]
    intro s hs hs'
    obtain ⟨t, -, rfl⟩ := mem_image.1 hs'
    exact notMem_of_notMem_verts ha (mem_filter.1 hs).1 (mem_insert_self a t)
  have hinj : Set.InjOn (insert a) X := fun t ht t' ht' h =>
    insert_cancel (notMem_of_notMem_verts ha (mem_filter.1 ht).1)
      (notMem_of_notMem_verts ha (mem_filter.1 ht').1) h
  have hX' : ∑ s ∈ X.image (insert a), (-1 : ℤ) ^ #s = -∑ s ∈ X, (-1 : ℤ) ^ #s := by
    rw [sum_image hinj, ← sum_neg_distrib]
    refine sum_congr rfl fun s hs => ?_
    rw [card_insert_of_notMem (notMem_of_notMem_verts ha (mem_filter.1 hs).1), pow_succ]
    ring
  rw [signedCount, hfaces, sum_union hdis, hX', signedCount,
    ← sum_filter_add_sum_filter_not K.faces (A ⊆ ·)]
  linarith

omit [DecidableEq V] in
/-- Injective maps of the vertices preserve the signed count. -/
lemma signedCount_map {W : Type*} [DecidableEq W] (K : SComplex V) (f : V ↪ W) :
    (K.map f).signedCount = K.signedCount := by
  change ∑ s ∈ K.faces.image (Finset.map f), (-1 : ℤ) ^ #s = _
  rw [sum_image fun s _ t _ h => Finset.map_injective f h, signedCount]
  exact sum_congr rfl fun s _ => by rw [card_map]

omit [DecidableEq V] in
lemma empty_mem_map_iff {W : Type*} [DecidableEq W] {K : SComplex V} {f : V ↪ W} :
    ∅ ∈ K.map f ↔ ∅ ∈ K := by
  rw [← map_empty f, map_mem_map]

/-- The signed count is an invariant of stellar equivalence inside `V`. -/
lemma StellarEquivIn.signedCount_eq {K L : SComplex V} (h : StellarEquivIn K L) :
    K.signedCount = L.signedCount := by
  induction h with
  | rel K L h =>
    obtain ⟨-, hne, ha⟩ := h
    exact (signedCount_starAt hne ha).symm
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Having a face is an invariant of stellar equivalence inside `V`. -/
lemma StellarEquivIn.empty_mem_iff {K L : SComplex V} (h : StellarEquivIn K L) :
    ∅ ∈ K ↔ ∅ ∈ L := by
  induction h with
  | rel K L h =>
    obtain ⟨hA, hne, -⟩ := h
    refine ⟨fun _ => mem_starAt.2 (.inl ⟨empty_mem hA, fun h' => hne.ne_empty
      (subset_empty.1 h')⟩), fun _ => empty_mem hA⟩
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **The Euler characteristic is an invariant of stellar equivalence.** -/
theorem StellarEquiv.euler_eq {K L : SComplex V} (h : StellarEquiv K L) : K.euler = L.euler := by
  have h₁ := StellarEquivIn.signedCount_eq h
  have h₂ := StellarEquivIn.empty_mem_iff h
  simp only [lift, signedCount_map, empty_mem_map_iff] at h₁ h₂
  rw [euler_eq_signedCount, euler_eq_signedCount, h₁]
  simp only [h₂]

/-- **Complexes with different Euler characteristics are not stellar equivalent.** -/
theorem not_stellarEquiv_of_euler_ne {K L : SComplex V} (h : K.euler ≠ L.euler) :
    ¬ StellarEquiv K L := fun hs => h hs.euler_eq

/-- The Euler characteristic of the boundary of the simplex on `A`: `1 + (−1)^{#A}`, i.e.
`χ(Sⁿ) = 1 + (−1)ⁿ` for `#A = n + 2`. -/
theorem euler_boundary {A : Finset V} (hA : A.Nonempty) :
    (boundary A).euler = 1 + (-1 : ℤ) ^ #A := by
  rw [euler_eq_signedCount, signedCount_boundary hA, ite_eq_left (mem_boundary.2
    (Finset.ssubset_iff_subset_ne.2 ⟨empty_subset _, hA.ne_empty.symm⟩))]
  ring

/-- The Euler characteristic of a simplex is `1`. -/
theorem euler_simplex {A : Finset V} (hA : A.Nonempty) : (simplex A).euler = 1 := by
  rw [euler_eq_signedCount, signedCount_simplex hA, ite_eq_left (mem_simplex.2 (empty_subset _))]
  ring

/-- **`χ(Sⁿ) = 1 + (−1)ⁿ`**: the Euler characteristic of a PL `n`-sphere. -/
theorem IsPLSphere.euler {n : ℕ} {K : SComplex V} (h : IsPLSphere n K) :
    K.euler = 1 + (-1 : ℤ) ^ n := by
  obtain ⟨A, hA, hKA⟩ := h
  have hKA' := StellarEquivIn.signedCount_eq hKA
  have h0 := StellarEquivIn.empty_mem_iff hKA
  have hne : A.Nonempty := card_pos.1 (by omega)
  rw [signedCount_boundary hne, hA, lift, signedCount_map] at hKA'
  rw [lift, empty_mem_map_iff] at h0
  rw [euler_eq_signedCount, hKA', ite_eq_left (h0.2 (mem_boundary.2 (Finset.ssubset_iff_subset_ne.2
    ⟨empty_subset _, hne.ne_empty.symm⟩)))]
  rw [pow_add]
  ring

/-- **`χ(Bⁿ) = 1`**: the Euler characteristic of a PL `n`-ball. -/
theorem IsPLBall.euler {n : ℕ} {K : SComplex V} (h : IsPLBall n K) : K.euler = 1 := by
  obtain ⟨A, hA, hKA⟩ := h
  have hKA' := StellarEquivIn.signedCount_eq hKA
  have h0 := StellarEquivIn.empty_mem_iff hKA
  have hne : A.Nonempty := card_pos.1 (by omega)
  rw [signedCount_simplex hne, lift, signedCount_map] at hKA'
  rw [lift, empty_mem_map_iff] at h0
  rw [euler_eq_signedCount, hKA', ite_eq_left (h0.2 (mem_simplex.2 (empty_subset _)))]
  ring

/-- **No complex is both a PL sphere and a PL ball** (their Euler characteristics differ). -/
theorem IsPLSphere.not_isPLBall {n m : ℕ} {K : SComplex V} (h : IsPLSphere n K) :
    ¬ IsPLBall m K := fun h' => by
  have := h.euler.symm.trans h'.euler
  rcases neg_one_pow_eq_or ℤ n with h'' | h'' <;> rw [h''] at this <;> omega

/-- In a complex whose faces have at most one vertex, the Euler characteristic counts vertices. -/
lemma euler_eq_card_verts {K : SComplex V} (hK : K.maxCard ≤ 1) : K.euler = #K.verts := by
  have he : K.faces.erase ∅ = K.verts.image ({·}) := by
    ext s
    simp only [mem_erase, mem_image, mem_faces]
    constructor
    · rintro ⟨hs0, hs⟩
      have h1 : #s = 1 := by
        have := card_le_maxCard hs
        have : 0 < #s := card_pos.2 (nonempty_iff_ne_empty.2 hs0)
        omega
      obtain ⟨x, rfl⟩ := card_eq_one.1 h1
      exact ⟨x, mem_verts.2 hs, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨singleton_ne_empty x, mem_verts.1 hx⟩
  rw [euler, he, sum_image fun x _ y _ h => singleton_injective h]
  simp

/-- **A PL 0-sphere has exactly two vertices.** -/
theorem IsPLSphere.card_verts_zero {K : SComplex V} (h : IsPLSphere 0 K) : #K.verts = 2 := by
  have h1 := h.euler
  rw [euler_eq_card_verts (by rw [h.maxCard])] at h1
  norm_num at h1
  exact_mod_cast h1

end SComplex

end Lightlike.PL
