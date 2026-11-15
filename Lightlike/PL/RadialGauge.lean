import Lightlike.PL.SliceSubdiv
import Lightlike.PL.SubdivSphere
import Lightlike.PL.Gauge

/-!
# A subdivision of a simplex boundary on which a maximum of affine functions is affine

Slicing the boundary of a simplex by the differences of finitely many affine functions gives a
subdivision of it in which every simplex lies in a region where one of the functions is largest.
The maximum of the functions is then affine on every simplex of the subdivision.

## Main results

* `SComplex.exists_gauge_subdivision`: the subdivision.
-/

open Finset
open scoped Classical

namespace Lightlike.PL
namespace SComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E] {κ : Type*} [Fintype κ] [Nonempty κ]

/-- **A subdivision of the boundary of a simplex on whose simplices one of the functions
dominates.** -/
theorem exists_gauge_subdivision {σ : Finset E} (hσ : AffineIndependent ℝ ((↑) : σ → E))
    (hne : σ.Nonempty) (f : κ → E →ᵃ[ℝ] ℝ) :
    ∃ β : SComplex E, IsSubdivision β (boundary σ) ∧ ∅ ∈ β ∧
      ∀ s ∈ β, ∃ k, ∀ y ∈ convexHull ℝ (s : Set E), ∀ j, f j y ≤ f k y := by
  have hK := isGeom_boundary hσ
  have h₀ : ∅ ∈ boundary σ := mem_boundary.2 (Finset.empty_ssubset.2 hne)
  let H : κ × κ → E →ᵃ[ℝ] ℝ := fun p => f p.1 - f p.2
  refine ⟨(sliceStructure (boundary σ) hK H).chainComplex, isSubdivision_slice _ hK h₀ H,
    (sliceStructure (boundary σ) hK H).empty_mem_chainComplex, ?_⟩
  intro s hs
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · obtain ⟨k⟩ := ‹Nonempty κ›
    exact ⟨k, by simp⟩
  obtain ⟨c, hc, hsc⟩ := exists_sliceHull_of_mem_chainComplex _ hK H hs hsne
  obtain ⟨z, hz⟩ := (mem_cells.1 hc).2
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ (fun k => f k z) Finset.univ_nonempty
  refine ⟨k, fun y hy j => ?_⟩
  have h1 : SignType.sign (H (j, k) z) = c.2 (j, k) := hz.2 (j, k)
  have h2 : H (j, k) z ≤ 0 := by
    show (f j - f k) z ≤ 0
    rw [AffineMap.coe_sub, Pi.sub_apply]
    linarith [hk j (Finset.mem_univ j)]
  have h3 : c.2 (j, k) ≤ 0 := by
    rw [← h1]; exact sign_nonpos_iff.2 h2
  have h4 := (hsc hy).2 (j, k)
  have h5 : H (j, k) y ≤ 0 := by
    rcases h4 with h | h
    · exact (sign_eq_zero_iff.1 h).le
    · have : SignType.sign (H (j, k) y) ≤ 0 := h ▸ h3
      exact sign_nonpos_iff.1 this
  have : (f j - f k) y ≤ 0 := h5
  rw [AffineMap.coe_sub, Pi.sub_apply] at this
  linarith

end SComplex
end Lightlike.PL
