import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-!
# Barycentric coordinates as affine functions on the whole space

For an affinely independent finite set `s`, the barycentric coordinates of a point of its affine
span are affine functions on that span. They extend to affine functions on the whole space, which
is what the radial arguments of the sphere theorems use: a polytope in the affine span of `s`
given by inequalities on these coordinates is then described by affine functions on `E`.

## Main results

* `exists_barycentric`: affine functions `w y` on `E` with `w y (∑ z, u z • z) = u y` whenever the
  weights `u` sum to `1`.
-/

open Finset Module

namespace Lightlike.PL

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **Barycentric coordinates as affine functions on the whole space.** -/
theorem exists_barycentric (s : Finset E) (hs : AffineIndependent ℝ ((↑) : s → E)) :
    ∃ w : E → (E →ᵃ[ℝ] ℝ), ∀ u : E → ℝ, ∑ y ∈ s, u y = 1 → ∀ y ∈ s,
      w y (∑ z ∈ s, u z • z) = u y := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨y0, hy0⟩
  · exact ⟨fun _ => 0, fun u hu => by simp at hu⟩
  set i : s := ⟨y0, hy0⟩ with hi
  have hli := (affineIndependent_iff_linearIndependent_vsub ℝ ((↑) : s → E) i).1 hs
  set b : {x : s // x ≠ i} → E := fun j => ((j.1 : s) : E) -ᵥ ((i : s) : E) with hb
  have hli' : LinearIndependent ℝ b := hli
  let bs := Basis.span hli'
  have hext : ∀ j, ∃ L : E →ₗ[ℝ] ℝ, ∀ j', L (b j') = if j' = j then 1 else 0 := by
    intro j
    obtain ⟨L, hL⟩ := LinearMap.exists_extend (bs.coord j)
    refine ⟨L, fun j' => ?_⟩
    have := congrArg (fun f => f ⟨b j', Submodule.subset_span ⟨j', rfl⟩⟩) hL
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    have h2 : (⟨b j', Submodule.subset_span ⟨j', rfl⟩⟩ : Submodule.span ℝ (Set.range b)) = bs j' :=
      Subtype.ext (by simp [bs, Basis.span_apply])
    rw [h2] at this
    simpa [Basis.coord_apply, bs.repr_self, Finsupp.single_apply, eq_comm] using this
  choose L hL using hext
  let F : {x : s // x ≠ i} → (E →ᵃ[ℝ] ℝ) := fun j =>
    (L j).toAffineMap - AffineMap.const ℝ E (L j y0)
  let w : E → (E →ᵃ[ℝ] ℝ) := fun y =>
    if h : y ∈ s then
      (if hy : (⟨y, h⟩ : s) = i then AffineMap.const ℝ E 1 -
        ((∑ j, L j).toAffineMap - AffineMap.const ℝ E ((∑ j, L j) y0)) else F ⟨⟨y, h⟩, hy⟩)
    else 0
  refine ⟨w, fun u hu y hy => ?_⟩
  have hx : (∑ z ∈ s, u z • z) - y0 = ∑ j : {x : s // x ≠ i}, u ((j.1 : s) : E) • b j := by
    have h1 : (∑ z ∈ s, u z • z) - y0 = ∑ z ∈ s, u z • (z - y0) := by
      simp [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hu]
    rw [h1, ← Finset.sum_coe_sort s (fun z => u z • (z - y0)),
      Fintype.sum_eq_add_sum_subtype_ne _ i]
    simp [hb, hi]
  have hF : ∀ j : {x : s // x ≠ i}, F j (∑ z ∈ s, u z • z) = u ((j.1 : s) : E) := by
    intro j
    have : F j (∑ z ∈ s, u z • z) = L j ((∑ z ∈ s, u z • z) - y0) := by
      simp [F, map_sub]
    rw [this, hx, map_sum]
    simp only [map_smul, hL, smul_eq_mul, mul_ite, mul_one, mul_zero]
    simp
  have hsum : ∑ z : s, u (z : E) = 1 := by rw [Finset.sum_coe_sort s u]; exact hu
  have hy' : (⟨y, hy⟩ : s) = i ∨ (⟨y, hy⟩ : s) ≠ i := eq_or_ne _ _
  simp only [w, dite_eq_left hy]
  rcases hy' with h | h
  · rw [dite_eq_left h]
    have hy0 : y = y0 := congrArg Subtype.val h
    rw [hy0]
    have := Fintype.sum_eq_add_sum_subtype_ne (fun z : s => u (z : E)) i
    have h2 : ((AffineMap.const ℝ E 1 -
        ((∑ j, L j).toAffineMap - AffineMap.const ℝ E ((∑ j, L j) y0)) : E →ᵃ[ℝ] ℝ)) (∑ z ∈ s, u z • z) =
        1 - ∑ j : {x : s // x ≠ i}, L j ((∑ z ∈ s, u z • z) - y0) := by
      simp [map_sub, LinearMap.sum_apply]
    rw [h2]
    have h3 : ∀ j : {x : s // x ≠ i}, L j ((∑ z ∈ s, u z • z) - y0) = u ((j.1 : s) : E) := by
      intro j
      rw [← hF j]; simp [F, map_sub]
    simp only [h3]
    simp only [hi] at this
    linarith
  · rw [dite_eq_right h]
    exact hF ⟨⟨y, hy⟩, h⟩

end Lightlike.PL
