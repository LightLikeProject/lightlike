import Lightlike.DynamicalTriangulations.DehnSommerville
import Lightlike.PL.Complex3

/-!
# Dehn–Sommerville relations in three dimensions

For a closed combinatorial 3-manifold `K` with `N₀, N₁, N₂, N₃` vertices, edges, triangles and
tetrahedra, the relations used in three-dimensional dynamical triangulations (Ambjørn,
Jurkiewicz and Loll, Non-perturbative 3d Lorentzian quantum gravity, 2001, Appendix 1):

* `2 N₂ = 4 N₃`, since every triangle lies in exactly two tetrahedra;
* `N₁ = N₀ + N₃`, since the vertex links are PL 2-spheres, of Euler characteristic 2.

Together they give `N₀ − N₁ + N₂ − N₃ = 0`, the Euler characteristic of a closed 3-manifold.
The relations leave `N₀` and `N₃` free.

## Main results

* `SComplex.IsClosedCombManifold.dehnSommerville3_link`: `2N₁ − 3N₂ + 4N₃ = 2N₀`.
* `SComplex.IsClosedCombManifold.dehnSommerville3`: `N₁ = N₀ + N₃`.
* `PR.IsCombManifold.card_tris`, `PR.IsCombManifold.card_edges`, `PR.IsCombManifold.euler_eq_zero`: the
  same for a closed combinatorial 3-manifold given by its tetrahedra (`Lightlike.PR.Complex3`).
-/

open Finset Lightlike.PL

namespace Lightlike.PL.SComplex

variable {V : Type*} [DecidableEq V]

/-- In a closed combinatorial 3-manifold, `2N₁ − 3N₂ + 4N₃ = 2N₀`, where `N_k` is the number of
faces with `k + 1` vertices: the vertex links are PL 2-spheres, of Euler characteristic 2. -/
theorem IsClosedCombManifold.dehnSommerville3_link {K : SComplex V} (hK : IsClosedCombManifold 3 K) :
    2 * (#(K.faces.filter fun s => #s = 2) : ℤ) - 3 * #(K.faces.filter fun s => #s = 3) +
      4 * #(K.faces.filter fun s => #s = 4) = 2 * #K.verts := by
  have hv : ∀ v ∈ K.verts, (K.link {v}).euler = 2 := fun v hv => by
    have := hK.euler_link (n := 2) hv
    simpa using this
  have hmax : ∀ v ∈ K.verts, (K.link {v}).maxCard ≤ 3 := fun v hv => by
    have hs := hK.isPLSphere_link (mem_verts.1 hv) (singleton_nonempty v) (by simp)
    simp only [card_singleton] at hs
    exact (IsPLSphere.maxCard hs).le
  have hsum : ∑ v ∈ K.verts, (K.link {v}).euler = 2 * #K.verts := by
    rw [sum_congr rfl hv]; simp [mul_comm]
  have h2 : ∀ v ∈ K.verts, (K.link {v}).euler =
      ∑ k ∈ range 3, (-1 : ℤ) ^ k * #((K.link {v}).faces.filter fun s => #s = k + 1) :=
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
  simp only [zero_add, pow_zero, one_mul, pow_succ, neg_mul, mul_one, mul_neg, neg_neg] at hsum
  norm_num at hsum
  linarith

/-- **Dehn–Sommerville relation** for closed combinatorial 3-manifolds: `N₁ = N₀ + N₃`. -/
theorem IsClosedCombManifold.dehnSommerville3 {K : SComplex V} (hK : IsClosedCombManifold 3 K) :
    (#(K.faces.filter fun s => #s = 2) : ℤ) = #K.verts + #(K.faces.filter fun s => #s = 4) := by
  have h1 := hK.dehnSommerville3_link
  have h2 := hK.two_mul_card_eq (n := 3) (by norm_num)
  have h2' : (2 * #(K.faces.filter fun s => #s = 3) : ℤ) =
      4 * #(K.faces.filter fun s => #s = 4) := by exact_mod_cast h2
  linarith

end Lightlike.PL.SComplex

namespace Lightlike.PL

open Lightlike.PR

variable {V : Type*} [DecidableEq V]

/-- The tetrahedra of `K` are the faces of `ofComplex3 K` with four vertices. -/
lemma filter_card_four_ofComplex3 (K : Complex3 V) :
    (ofComplex3 K).faces.filter (fun s => #s = 4) = K.tets := by
  ext s
  simp only [mem_filter, SComplex.mem_faces, ofComplex3, SComplex.mem_closure]
  constructor
  · rintro ⟨⟨t, ht, hst⟩, hs⟩
    have : s = t := eq_of_subset_of_card_le hst (by rw [hs, K.card_eq t ht])
    exact this ▸ ht
  · intro hs
    exact ⟨⟨s, hs, subset_rfl⟩, K.card_eq s hs⟩

/-- The triangles of `K` are the faces of `ofComplex3 K` with three vertices. -/
lemma filter_card_three_ofComplex3 (K : Complex3 V) :
    (ofComplex3 K).faces.filter (fun s => #s = 3) = K.tris := by
  ext s
  simp only [mem_filter, SComplex.mem_faces, ofComplex3, SComplex.mem_closure, Complex3.mem_tris]
  constructor
  · rintro ⟨⟨t, ht, hst⟩, hs⟩
    exact ⟨t, ht, hst, hs⟩
  · rintro ⟨t, ht, hst, hs⟩
    exact ⟨⟨t, ht, hst⟩, hs⟩

/-- The edges of `K` are the faces of `ofComplex3 K` with two vertices. -/
lemma filter_card_two_ofComplex3 (K : Complex3 V) :
    (ofComplex3 K).faces.filter (fun s => #s = 2) = K.edges := by
  ext s
  simp only [mem_filter, SComplex.mem_faces, ofComplex3, SComplex.mem_closure, Complex3.mem_edges]
  constructor
  · rintro ⟨⟨t, ht, hst⟩, hs⟩
    exact ⟨t, ht, hst, hs⟩
  · rintro ⟨t, ht, hst, hs⟩
    exact ⟨⟨t, ht, hst⟩, hs⟩

/-- **A closed combinatorial 3-manifold has twice as many triangles as tetrahedra**:
`N₂ = 2N₃`. -/
theorem _root_.Lightlike.PR.IsCombManifold.card_tris {K : Complex3 V} (hK : IsCombManifold K) :
    #K.tris = 2 * #K.tets := by
  have h := SComplex.IsClosedCombManifold.two_mul_card_eq (n := 3) (by norm_num)
    (isClosedCombManifold_ofComplex3 hK)
  rw [filter_card_three_ofComplex3, filter_card_four_ofComplex3] at h
  omega

/-- **Dehn–Sommerville relation for a closed combinatorial 3-manifold**: `N₁ = N₀ + N₃`. -/
theorem _root_.Lightlike.PR.IsCombManifold.card_edges {K : Complex3 V} (hK : IsCombManifold K) :
    (#K.edges : ℤ) = #K.verts + #K.tets := by
  have h := SComplex.IsClosedCombManifold.dehnSommerville3 (isClosedCombManifold_ofComplex3 hK)
  rw [filter_card_two_ofComplex3, filter_card_four_ofComplex3, verts_ofComplex3] at h
  exact h

/-- The Euler characteristic of a closed combinatorial 3-manifold vanishes:
`N₀ − N₁ + N₂ − N₃ = 0`. -/
theorem _root_.Lightlike.PR.IsCombManifold.euler_eq_zero {K : Complex3 V} (hK : IsCombManifold K) :
    (#K.verts : ℤ) - #K.edges + #K.tris - #K.tets = 0 := by
  have h1 := hK.card_edges
  have h2 : (#K.tris : ℤ) = 2 * #K.tets := by exact_mod_cast hK.card_tris
  linarith

end Lightlike.PL
