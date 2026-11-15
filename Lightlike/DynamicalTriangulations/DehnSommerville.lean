import Lightlike.PL.Euler
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Dehn–Sommerville relations for closed combinatorial manifolds

For a closed combinatorial `n`-manifold `K` write `N_m` for the number of faces with `m` vertices.
Every face with `n` vertices lies in exactly two top faces, hence `2 N_n = (n + 1) N_{n+1}`; the
link of a vertex is a PL `(n − 1)`-sphere, whose Euler characteristic is `1 + (−1)^{n−1}`, which
gives the second relation. For `n = 4` (the setting of four-dimensional dynamical triangulations,
with `N₀ … N₄` the numbers of vertices, edges, triangles, tetrahedra and 4-simplices):

* `2 N₃ = 5 N₄`,
* `2 N₁ − 3 N₂ + 6 N₃ − 10 N₄ = 0`.

Here the counts are written by number of vertices of the face (`#s = k + 1` for `N_k`).

## Main results

* `card_mul_eq_sum_cofaces`, `sum_card_link`: the two double countings.
* `IsClosedCombManifold.card_cofaces`: a face with `n` vertices lies in exactly two top faces.
* `IsClosedCombManifold.two_mul_card_eq`: `2 N_{n-1} = (n + 1) N_n` (for `n = 4`, `2N₃ = 5N₄`).
* `euler_eq_sum_card`: the Euler characteristic is the alternating sum of the face numbers.
* `IsClosedCombManifold.euler_link`: vertex links have the Euler characteristic of a sphere.
* `IsClosedCombManifold.dehnSommerville`: `2N₁ − 3N₂ + 6N₃ − 10N₄ = 0`.
* `Tasks.boundary_fin6_dehnSommerville`, `Tasks.twoSimplices_not_dehnSommerville`: the boundary of
  the 5-simplex satisfies the relations with `N = (6, 15, 20, 15, 6)`; two 4-simplices glued along
  a tetrahedron (not a manifold) violate `2N₃ = 5N₄`.
-/

open Finset

namespace Lightlike.PL

namespace SComplex

variable {V : Type*} [DecidableEq V]

/-- **Double counting.** Each face with `k + 2` vertices has `k + 2` faces with `k + 1` vertices, so
`(k + 2)` times the number of faces with `k + 2` vertices is the sum, over faces `σ` with `k + 1`
vertices, of the number of faces with `k + 2` vertices containing `σ`. -/
theorem card_mul_eq_sum_cofaces (K : SComplex V) (k : ℕ) :
    (k + 2) * #(K.faces.filter fun s => #s = k + 2) =
      ∑ σ ∈ K.faces.filter (fun s => #s = k + 1),
        #(K.faces.filter fun s => σ ⊆ s ∧ #s = k + 2) := by
  have h := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := K.faces.filter (fun s => #s = k + 1)) (t := K.faces.filter fun s => #s = k + 2)
    (fun σ s => σ ⊆ s)
  have hb : ∀ s ∈ K.faces.filter (fun s => #s = k + 2),
      #((K.faces.filter (fun s => #s = k + 1)).bipartiteBelow (fun σ s => σ ⊆ s) s) = k + 2 := by
    intro s hs
    rw [mem_filter] at hs
    have : (K.faces.filter (fun s => #s = k + 1)).bipartiteBelow (fun σ s => σ ⊆ s) s =
        s.powersetCard (k + 1) := by
      ext σ
      simp only [Finset.mem_bipartiteBelow, mem_filter, mem_powersetCard, mem_faces]
      exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨down_mem hs.1 h.1, h.2⟩, h.1⟩⟩
    rw [this, card_powersetCard, hs.2]
    simp [Nat.choose_succ_self_right]
  rw [sum_congr rfl hb] at h
  simp only [sum_const, nsmul_eq_mul, Nat.cast_id, mul_comm] at h
  rw [← h]
  refine sum_congr rfl fun σ _ => ?_
  simp only [Finset.bipartiteAbove, filter_filter]
  exact congrArg card (filter_congr fun _ _ => and_comm)

/-- A face of a closed combinatorial `n`-manifold with `n` vertices lies in exactly two faces with
`n + 1` vertices (the top faces). -/
theorem IsClosedCombManifold.card_cofaces {n : ℕ} (hn : 1 ≤ n) {K : SComplex V}
    (hK : IsClosedCombManifold n K) {σ : Finset V} (hσ : σ ∈ K) (hcard : #σ = n) :
    #(K.faces.filter fun s => σ ⊆ s ∧ #s = n + 1) = 2 := by
  have hne : σ.Nonempty := card_pos.1 (by omega)
  have hs := hK.isPLSphere_link hσ hne (by omega)
  rw [hcard, Nat.sub_self] at hs
  rw [← hs.card_verts_zero]
  symm
  refine card_bij (fun v _ => insert v σ) ?_ ?_ ?_
  · intro v hv
    have h1 : {v} ∈ K.link σ := mem_verts.1 hv
    rw [mem_link'] at h1
    have hv' : v ∉ σ := fun h => by simpa [h] using h1.1
    simp only [mem_filter, mem_faces]
    refine ⟨?_, subset_insert _ _, by rw [card_insert_of_notMem hv', hcard]⟩
    have := h1.2
    rwa [union_comm, singleton_union] at this
  · intro a ha b hb hab
    have h1 : {a} ∈ K.link σ := mem_verts.1 ha
    have h2 : {b} ∈ K.link σ := mem_verts.1 hb
    rw [mem_link'] at h1 h2
    have ha' : a ∉ σ := fun h => by simpa [h] using h1.1
    have hb' : b ∉ σ := fun h => by simpa [h] using h2.1
    have : a ∈ insert b σ := hab ▸ mem_insert_self a σ
    rcases mem_insert.1 this with h | h
    · exact h
    · exact absurd h ha'
  · intro s hs
    simp only [mem_filter, mem_faces] at hs
    obtain ⟨hsK, hσs, hcs⟩ := hs
    have h1 : #(s \ σ) = 1 := by rw [card_sdiff_of_subset hσs]; omega
    obtain ⟨v, hv⟩ := card_eq_one.1 h1
    have hvs : v ∈ s \ σ := by rw [hv]; simp
    rw [mem_sdiff] at hvs
    refine ⟨v, mem_verts.2 ?_, ?_⟩
    · rw [mem_link']
      refine ⟨by simpa using hvs.2, ?_⟩
      have : σ ∪ {v} = s := by
        ext x
        constructor
        · intro hx
          rcases mem_union.1 hx with h | h
          · exact hσs h
          · rw [mem_singleton.1 h]; exact hvs.1
        · intro hx
          by_cases hxσ : x ∈ σ
          · exact mem_union_left _ hxσ
          · have : x ∈ s \ σ := mem_sdiff.2 ⟨hx, hxσ⟩
            rw [hv] at this
            exact mem_union_right _ this
      rw [this]; exact hsK
    · have : insert v σ = s := by
        ext x
        constructor
        · intro hx
          rcases mem_insert.1 hx with h | h
          · rw [h]; exact hvs.1
          · exact hσs h
        · intro hx
          by_cases hxσ : x ∈ σ
          · exact mem_insert_of_mem hxσ
          · have : x ∈ s \ σ := mem_sdiff.2 ⟨hx, hxσ⟩
            rw [hv, mem_singleton] at this
            exact this ▸ mem_insert_self _ _
      exact this

/-- In a closed combinatorial `n`-manifold with `1 ≤ n`, twice the number of faces with `n` vertices
equals `n + 1` times the number of faces with `n + 1` vertices. For `n = 4`: `2N₃ = 5N₄`. -/
theorem IsClosedCombManifold.two_mul_card_eq {n : ℕ} (hn : 1 ≤ n) {K : SComplex V}
    (hK : IsClosedCombManifold n K) :
    2 * #(K.faces.filter fun s => #s = n) = (n + 1) * #(K.faces.filter fun s => #s = n + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [card_mul_eq_sum_cofaces K k]
  have : ∀ σ ∈ K.faces.filter (fun s => #s = k + 1),
      #(K.faces.filter fun s => σ ⊆ s ∧ #s = k + 2) = 2 := by
    intro σ hσ
    rw [mem_filter] at hσ
    exact hK.card_cofaces hn hσ.1 hσ.2
  rw [sum_congr rfl this, sum_const, nsmul_eq_mul, Nat.cast_id, mul_comm]

/-- Summed over the vertices `v`, the faces with `k + 1` vertices of the links of `{v}` count each
face of `K` with `k + 2` vertices once per vertex, that is `k + 2` times. -/
theorem sum_card_link (K : SComplex V) (k : ℕ) :
    ∑ v ∈ K.verts, #((K.link {v}).faces.filter fun u => #u = k + 1) =
      (k + 2) * #(K.faces.filter fun s => #s = k + 2) := by
  have h := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := K.verts) (t := K.faces.filter fun s => #s = k + 2) (fun v s => v ∈ s)
  have hb : ∀ s ∈ K.faces.filter (fun s => #s = k + 2),
      #(K.verts.bipartiteBelow (fun v s => v ∈ s) s) = k + 2 := by
    intro s hs
    rw [mem_filter] at hs
    have : K.verts.bipartiteBelow (fun v s => v ∈ s) s = s := by
      ext v
      simp only [Finset.mem_bipartiteBelow]
      exact ⟨fun h => h.2, fun h => ⟨subset_verts hs.1 h, h⟩⟩
    rw [this, hs.2]
  rw [sum_congr rfl hb] at h
  simp only [sum_const, nsmul_eq_mul, Nat.cast_id, mul_comm] at h
  rw [← h]
  refine sum_congr rfl fun v hv => ?_
  refine card_bij (fun u _ => insert v u) ?_ ?_ ?_
  · intro u hu
    simp only [mem_filter, mem_faces, mem_link'] at hu
    have hv' : v ∉ u := fun h => by simpa [h] using hu.1.1
    simp only [mem_bipartiteAbove, mem_filter, mem_faces]
    refine ⟨⟨?_, ?_⟩, mem_insert_self _ _⟩
    · have := hu.1.2
      rwa [singleton_union] at this
    · rw [card_insert_of_notMem hv', hu.2]
  · intro a ha b hb hab
    simp only [mem_filter, mem_faces, mem_link'] at ha hb
    have ha' : v ∉ a := fun h => by simpa [h] using ha.1.1
    have hb' : v ∉ b := fun h => by simpa [h] using hb.1.1
    have := congrArg (fun x => x.erase v) hab
    simpa [erase_insert ha', erase_insert hb'] using this
  · intro s hs
    simp only [mem_bipartiteAbove, mem_filter, mem_faces] at hs
    obtain ⟨⟨hsK, hcs⟩, hvs⟩ := hs
    refine ⟨s.erase v, ?_, insert_erase hvs⟩
    rw [mem_filter, mem_faces, mem_link']
    refine ⟨⟨disjoint_singleton_left.2 (notMem_erase _ _), ?_⟩, ?_⟩
    · rw [singleton_union, insert_erase hvs]; exact hsK
    · rw [card_erase_of_mem hvs]; omega

/-- The Euler characteristic as the alternating sum of the face numbers, over any range that
reaches the largest face. -/
theorem euler_eq_sum_range (K : SComplex V) {M : ℕ} (hM : K.maxCard ≤ M) :
    K.euler = ∑ k ∈ range M, (-1 : ℤ) ^ k * #(K.faces.filter fun s => #s = k + 1) := by
  have h1 : ∀ k ∈ range M, (-1 : ℤ) ^ k * #(K.faces.filter fun s => #s = k + 1) =
      ∑ s ∈ (K.faces.erase ∅).filter (fun s => #s - 1 = k), (-1 : ℤ) ^ (#s + 1) := by
    intro k _
    have : (K.faces.erase ∅).filter (fun s => #s - 1 = k) =
        K.faces.filter fun s => #s = k + 1 := by
      ext s
      simp only [mem_filter, mem_erase, mem_faces]
      constructor
      · rintro ⟨⟨hne, hs⟩, hk⟩
        have : 0 < #s := card_pos.2 (nonempty_iff_ne_empty.2 hne)
        exact ⟨hs, by omega⟩
      · rintro ⟨hs, hk⟩
        exact ⟨⟨fun h => by simp [h] at hk, hs⟩, by omega⟩
    rw [this, sum_congr rfl (fun s hs => by
      rw [(mem_filter.1 hs).2, show k + 1 + 1 = k + 2 from rfl]), sum_const, nsmul_eq_mul]
    rw [pow_succ, pow_succ]
    simp [mul_comm]
  rw [sum_congr rfl h1, sum_fiberwise_of_maps_to, euler]
  intro s hs
  rw [mem_erase] at hs
  have := card_le_maxCard hs.2
  have : 0 < #s := card_pos.2 (nonempty_iff_ne_empty.2 hs.1)
  rw [mem_range]; omega

/-- The Euler characteristic is the alternating sum `N₀ − N₁ + N₂ − ⋯` of the numbers `N_k` of faces
with `k + 1` vertices. -/
theorem euler_eq_sum_card (K : SComplex V) :
    K.euler = ∑ k ∈ range K.maxCard, (-1 : ℤ) ^ k * #(K.faces.filter fun s => #s = k + 1) :=
  K.euler_eq_sum_range le_rfl

/-- In a closed combinatorial `(n + 1)`-manifold the link of every vertex has Euler characteristic
`1 + (−1)ⁿ`, that of a PL `n`-sphere. -/
theorem IsClosedCombManifold.euler_link {n : ℕ} {K : SComplex V}
    (hK : IsClosedCombManifold (n + 1) K) {v : V} (hv : v ∈ K.verts) :
    (K.link {v}).euler = 1 + (-1) ^ n := by
  have hs := hK.isPLSphere_link (mem_verts.1 hv) (singleton_nonempty v) (by simp)
  simp only [card_singleton, Nat.add_sub_cancel] at hs
  exact hs.euler

/-- In a closed combinatorial 4-manifold, `2N₁ − 3N₂ + 4N₃ − 5N₄ = 0`, where `N_k` is the number of
faces with `k + 1` vertices: the vertex links are PL 3-spheres, of Euler characteristic 0. -/
theorem IsClosedCombManifold.dehnSommerville_link {K : SComplex V} (hK : IsClosedCombManifold 4 K) :
    2 * (#(K.faces.filter fun s => #s = 2) : ℤ) - 3 * #(K.faces.filter fun s => #s = 3) +
      4 * #(K.faces.filter fun s => #s = 4) - 5 * #(K.faces.filter fun s => #s = 5) = 0 := by
  have hv : ∀ v ∈ K.verts, (K.link {v}).euler = 0 := fun v hv => by
    have := hK.euler_link (n := 3) hv
    simpa using this
  have hmax : ∀ v ∈ K.verts, (K.link {v}).maxCard ≤ 4 := fun v hv => by
    have hs := hK.isPLSphere_link (mem_verts.1 hv) (singleton_nonempty v) (by simp)
    simp only [card_singleton] at hs
    exact (IsPLSphere.maxCard hs).le
  have hsum : ∑ v ∈ K.verts, (K.link {v}).euler = 0 := sum_eq_zero hv
  have h2 : ∀ v ∈ K.verts, (K.link {v}).euler =
      ∑ k ∈ range 4, (-1 : ℤ) ^ k * #((K.link {v}).faces.filter fun s => #s = k + 1) :=
    fun v hv => (K.link {v}).euler_eq_sum_range (hmax v hv)
  rw [sum_congr rfl h2] at hsum
  simp only [sum_range_succ, sum_range_zero, sum_add_distrib, ← mul_sum] at hsum
  have e := fun k => sum_card_link K k
  have e0 : ∑ v ∈ K.verts, (#((K.link {v}).faces.filter fun u => #u = 1) : ℤ) =
      2 * #(K.faces.filter fun s => #s = 2) := by exact_mod_cast e 0
  have e1 : ∑ v ∈ K.verts, (#((K.link {v}).faces.filter fun u => #u = 2) : ℤ) =
      3 * #(K.faces.filter fun s => #s = 3) := by exact_mod_cast e 1
  have e2 : ∑ v ∈ K.verts, (#((K.link {v}).faces.filter fun u => #u = 3) : ℤ) =
      4 * #(K.faces.filter fun s => #s = 4) := by exact_mod_cast e 2
  have e3 : ∑ v ∈ K.verts, (#((K.link {v}).faces.filter fun u => #u = 4) : ℤ) =
      5 * #(K.faces.filter fun s => #s = 5) := by exact_mod_cast e 3
  simp only [zero_add, pow_zero, one_mul, pow_succ, neg_mul, mul_one, mul_neg, neg_neg] at hsum
  norm_num at hsum
  linarith

/-- **Dehn–Sommerville relation** for closed combinatorial 4-manifolds:
`2N₁ − 3N₂ + 6N₃ − 10N₄ = 0`, where `N_k` is the number of faces with `k + 1` vertices. -/
theorem IsClosedCombManifold.dehnSommerville {K : SComplex V} (hK : IsClosedCombManifold 4 K) :
    2 * (#(K.faces.filter fun s => #s = 2) : ℤ) - 3 * #(K.faces.filter fun s => #s = 3) +
      6 * #(K.faces.filter fun s => #s = 4) - 10 * #(K.faces.filter fun s => #s = 5) = 0 := by
  have h1 := hK.dehnSommerville_link
  have h2 := hK.two_mul_card_eq (n := 4) (by norm_num)
  have h2' : (2 * #(K.faces.filter fun s => #s = 4) : ℤ) = 5 * #(K.faces.filter fun s => #s = 5) := by
    exact_mod_cast h2
  linarith

end SComplex

end Lightlike.PL
