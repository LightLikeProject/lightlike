import Lightlike.Rows.G2_010.Complete

/-!
# Spin networks, step C2c: the product coefficients are a Hilbert basis of `L²(SU(2)^E)`

Row G2-010 (milestone OP, task T-CA2). The classes `phiLp n i j` are orthonormal (`orthonormal_phiLp`) and span a
dense subspace of `L²(SU(2)^E, haarPi E)` (`dense_span_phiLp`: continuous functions are dense in `L²` of a
finite regular measure, and `dense_phiSpanC`). Hence they form a Hilbert basis (`phiHilbertBasis`).

Supporting lemmas for the spin-network basis theorem; no catalogue entry.
-/

open MeasureTheory

namespace Lightlike.Rows.G2_010

open Lightlike Lightlike.Spin4 Lightlike.HarmonicAnalysis

noncomputable section

variable {E : Type} [Fintype E]

/-- The family of the product coefficients, indexed by `Σ n, Idx n × Idx n`. -/
def phiFam (E : Type) [Fintype E] : (Σ n : E → ℕ, Idx n × Idx n) → Lp ℂ 2 (haarPi E) :=
  fun a => phiLp a.1 a.2.1 a.2.2

lemma map_phiSpanC :
    (phiSpanC E).map (ContinuousMap.toLp (E := ℂ) 2 (haarPi E) ℂ).toLinearMap =
      Submodule.span ℂ (Set.range (phiFam E)) := by
  unfold phiSpanC
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨n, i, j, rfl⟩, rfl⟩
    exact ⟨⟨n, i, j⟩, rfl⟩
  · rintro ⟨⟨n, i, j⟩, rfl⟩
    exact ⟨phiC n i j, ⟨n, i, j, rfl⟩, rfl⟩

/-- The product coefficients span a dense subspace of `L²(SU(2)^E)`. -/
theorem dense_span_phiLp :
    Dense (Submodule.span ℂ (Set.range (phiFam E)) : Set (Lp ℂ 2 (haarPi E))) := by
  have hd : DenseRange (ContinuousMap.toLp (E := ℂ) 2 (haarPi E) ℂ) :=
    ContinuousMap.toLp_denseRange (E := ℂ) (𝕜 := ℂ) (p := 2) (μ := haarPi E) (by norm_num)
  have := hd.dense_image (ContinuousMap.toLp (E := ℂ) 2 (haarPi E) ℂ).continuous dense_phiSpanC
  rw [← map_phiSpanC]
  simpa [Submodule.map_coe] using this

/-- **The product coefficients `√(∏(n_e+1)) ∏ D^{n_e}_{i_e j_e}(h_e)` form a Hilbert basis of `L²(SU(2)^E)`.** -/
def phiHilbertBasis (E : Type) [Fintype E] :
    HilbertBasis (Σ n : E → ℕ, Idx n × Idx n) ℂ (Lp ℂ 2 (haarPi E)) :=
  HilbertBasis.mk orthonormal_phiLp
    (Submodule.dense_iff_topologicalClosure_eq_top.1 (dense_span_phiLp (E := E))).ge

lemma phiHilbertBasis_apply (a : Σ n : E → ℕ, Idx n × Idx n) : phiHilbertBasis E a = phiFam E a := by
  unfold phiHilbertBasis
  exact congrFun (HilbertBasis.coe_mk _ _) a

end

end Lightlike.Rows.G2_010
