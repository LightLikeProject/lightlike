import Lightlike.Rows.G2_010.Expand
import Lightlike.HarmonicAnalysis.PeterWeylSeparation

/-!
# Spin networks, step C2b: the product coefficients span a dense subspace of `C(SU(2)^E)`

Row G2-010 (milestone OP, task T-CA2). The linear span `A` of the functions `h ↦ ∏_e g_e(h e)` with each
`g_e` in the span of matrix coefficients of `SU(2)` is a star subalgebra of `C(SU(2)^E, ℂ)` which separates
points; by Stone–Weierstrass it is dense (`dense_prodAlg`). By `prod_mem_phiSpan` it is contained in the span of
the `phi n i j`, which is therefore dense (`dense_phiSpanC`).

Supporting lemmas for the spin-network basis theorem; no catalogue entry.
-/

open MeasureTheory

namespace Lightlike.Rows.G2_010

open Lightlike Lightlike.Spin4 Lightlike.HarmonicAnalysis

noncomputable section

variable {E : Type} [Fintype E]

/-- Products `h ↦ ∏_e g_e (h e)` of matrix-coefficient combinations, one on each edge. -/
def prodSet (E : Type) [Fintype E] : Set C(E → SU2, ℂ) :=
  {F | ∃ g : E → C(SU2, ℂ), (∀ e, g e ∈ matrixCoeffSpan SU2) ∧ ∀ h, F h = ∏ e, g e (h e)}

lemma one_mem_prodSet : (1 : C(E → SU2, ℂ)) ∈ prodSet E :=
  ⟨fun _ => 1, fun _ => (matrixCoeffAlgebra SU2).one_mem, fun h => by simp⟩

lemma mul_mem_prodSet {F G : C(E → SU2, ℂ)} (hF : F ∈ prodSet E) (hG : G ∈ prodSet E) :
    F * G ∈ prodSet E := by
  obtain ⟨g, hg, hF⟩ := hF
  obtain ⟨k, hk, hG⟩ := hG
  refine ⟨fun e => g e * k e, fun e => (matrixCoeffAlgebra SU2).mul_mem (hg e) (hk e), fun h => ?_⟩
  simp [hF, hG, Finset.prod_mul_distrib]

lemma star_mem_prodSet {F : C(E → SU2, ℂ)} (hF : F ∈ prodSet E) : star F ∈ prodSet E := by
  obtain ⟨g, hg, hF⟩ := hF
  refine ⟨fun e => star (g e), fun e => (star_mem (show g e ∈ matrixCoeffAlgebra SU2 from hg e) :
      star (g e) ∈ matrixCoeffAlgebra SU2), fun h => ?_⟩
  simp [hF]

/-- The span of `prodSet` is a star subalgebra of `C(SU(2)^E, ℂ)`. -/
def prodAlg (E : Type) [Fintype E] : StarSubalgebra ℂ C(E → SU2, ℂ) where
  carrier := Submodule.span ℂ (prodSet E)
  mul_mem' := by
    intro a b ha hb
    have h1 : a * b ∈ Submodule.span ℂ (prodSet E) * Submodule.span ℂ (prodSet E) :=
      Submodule.mul_mem_mul ha hb
    rw [Submodule.span_mul_span] at h1
    refine Submodule.span_mono ?_ h1
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact mul_mem_prodSet hx hy
  one_mem' := Submodule.subset_span one_mem_prodSet
  add_mem' := fun ha hb => Submodule.add_mem _ ha hb
  zero_mem' := Submodule.zero_mem _
  algebraMap_mem' := fun c => by
    have : algebraMap ℂ C(E → SU2, ℂ) c = c • (1 : C(E → SU2, ℂ)) := by
      simp [Algebra.algebraMap_eq_smul_one]
    rw [this]
    exact Submodule.smul_mem _ c (Submodule.subset_span one_mem_prodSet)
  star_mem' := by
    intro a ha
    refine Submodule.span_induction (p := fun x _ => star x ∈ Submodule.span ℂ (prodSet E)) ?_ ?_ ?_ ?_ ha
    · intro x hx
      exact Submodule.subset_span (star_mem_prodSet hx)
    · simp
    · intro x y _ _ hx hy
      simpa using Submodule.add_mem _ hx hy
    · intro c x _ hx
      simpa using Submodule.smul_mem _ (starRingEnd ℂ c) hx

lemma prodAlg_separates : (prodAlg E).SeparatesPoints := by
  classical
  intro h h' hne
  obtain ⟨e, he⟩ := Function.ne_iff.1 hne
  obtain ⟨f, hf, hfe⟩ := exists_matrixCoeff_ne he
  let F : C(E → SU2, ℂ) := ⟨fun x => f (x e), f.continuous.comp (continuous_apply e)⟩
  have hF : F ∈ prodSet E := by
    refine ⟨Function.update (fun _ => 1) e f, fun e' => ?_, fun x => ?_⟩
    · by_cases h : e' = e
      · subst h; simpa using hf
      · rw [Function.update_of_ne h]; exact (matrixCoeffAlgebra SU2).one_mem
    · rw [Finset.prod_eq_single e]
      · simp [F]
      · intro b _ hb; simp [hb]
      · intro h; exact absurd (Finset.mem_univ e) h
  exact ⟨F, ⟨F, Submodule.subset_span hF, rfl⟩, hfe⟩

/-- **Stone–Weierstrass**: the span of products of matrix coefficients is dense in `C(SU(2)^E, ℂ)`. -/
theorem dense_prodAlg : Dense (Submodule.span ℂ (prodSet E) : Set C(E → SU2, ℂ)) := by
  have := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
    (prodAlg_separates (E := E))
  rw [dense_iff_closure_eq]
  have h2 : closure ((prodAlg E : StarSubalgebra ℂ C(E → SU2, ℂ)) : Set C(E → SU2, ℂ)) = Set.univ := by
    have := congrArg (fun A : StarSubalgebra ℂ C(E → SU2, ℂ) => (A : Set C(E → SU2, ℂ))) this
    simpa [StarSubalgebra.topologicalClosure_coe] using this
  exact h2

/-- The span of the `phiC n i j` inside `C(SU(2)^E, ℂ)`. -/
def phiSpanC (E : Type) [Fintype E] : Submodule ℂ C(E → SU2, ℂ) :=
  Submodule.span ℂ {F | ∃ (n : E → ℕ) (i j : Idx n), F = phiC n i j}

lemma mem_phiSpanC_of_mem_phiSpan {F : C(E → SU2, ℂ)} (hF : (F : (E → SU2) → ℂ) ∈ phiSpan E) :
    F ∈ phiSpanC E := by
  have hmap : phiSpan E = (phiSpanC E).map (ContinuousMap.coeFnLinearMap ℂ) := by
    unfold phiSpan phiSpanC
    rw [Submodule.map_span]
    congr 1
    ext G
    constructor
    · rintro ⟨n, i, j, rfl⟩
      exact ⟨phiC n i j, ⟨n, i, j, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨n, i, j, rfl⟩, rfl⟩
      exact ⟨n, i, j, rfl⟩
  rw [hmap] at hF
  obtain ⟨y, hy, hyF⟩ := hF
  have : y = F := DFunLike.coe_injective hyF
  rwa [← this]

lemma prodSet_subset_phiSpanC : Submodule.span ℂ (prodSet E) ≤ phiSpanC E := by
  rw [Submodule.span_le]
  rintro F ⟨g, hg, hF⟩
  apply mem_phiSpanC_of_mem_phiSpan
  have := prod_mem_phiSpan (fun e => (g e : SU2 → ℂ)) fun e => coe_mem_spinSpan_of_mem_matrixCoeffSpan (hg e)
  convert this using 1
  funext h
  exact hF h

/-- **The products of normalised spin coefficients span a dense subspace of `C(SU(2)^E, ℂ)`.** -/
theorem dense_phiSpanC : Dense (phiSpanC E : Set C(E → SU2, ℂ)) :=
  dense_prodAlg.mono prodSet_subset_phiSpanC

end

end Lightlike.Rows.G2_010
