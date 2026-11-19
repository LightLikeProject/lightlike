import Lightlike.HarmonicAnalysis.PeterWeylComplete

/-!
# The Peter–Weyl theorem: a Hilbert basis of `L²(G)` from irreducible matrix coefficients

For a compact Hausdorff group `G` with a regular Haar probability measure `μ`, the functions
`√(dim π) · π_{ij}`, where `π` runs over the equivalence classes of irreducible continuous finite-dimensional
unitary representations (with a chosen representative) and `i, j` over the indices of the representative,
form a Hilbert basis of `L²(G, μ)` (`peterWeyl_hilbertBasis`). Equivalently, `L²(G)` is the Hilbert direct sum
of the isotypic components `L²(G)_π ≅ End(V_π)`, with `‖√(dim π) · π_{ij}‖ = 1` (Schur orthogonality).

## References

* T. Tao, *The Peter–Weyl theorem, and non-abelian Fourier analysis on compact groups* (blog post,
  23 January 2011), Propositions 7 and 8.
* T. Bröcker and T. tom Dieck, *Representations of compact Lie groups*, Springer (1985), Chapter III.
-/

open MeasureTheory

namespace Lightlike.HarmonicAnalysis

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  [IsProbabilityMeasure μ] [μ.Regular]

/-- **Peter–Weyl theorem (Hilbert basis form).** The normalised matrix coefficients of the irreducible
unitary representations form a Hilbert basis of `L²(G, μ)`. -/
theorem peterWeyl_hilbertBasis :
    ∃ b : HilbertBasis (CoeffIdx G) ℂ (Lp ℂ 2 μ), ∀ a, b a = coeffFamily μ a := by
  have hsp : ⊤ ≤ (Submodule.span ℂ (Set.range (coeffFamily μ))).topologicalClosure := by
    rw [top_le_iff, Submodule.topologicalClosure_eq_top_iff]
    refine (Submodule.eq_bot_iff _).2 fun χ hχ => ?_
    refine eq_zero_of_orthogonal_coeffFamily μ (fun a => ?_)
    have h1 : inner ℂ (coeffFamily μ a) χ = 0 :=
      (Submodule.mem_orthogonal _ _).1 hχ _ (Submodule.subset_span ⟨a, rfl⟩)
    rw [← inner_conj_symm, h1]; simp
  exact ⟨HilbertBasis.mk (orthonormal_coeffFamily μ) hsp, fun a => by simp⟩

end

end Lightlike.HarmonicAnalysis
