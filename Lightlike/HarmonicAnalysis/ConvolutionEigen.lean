import Lightlike.HarmonicAnalysis.ConvolutionSelfAdjoint
import Lightlike.HarmonicAnalysis.LeftTranslation

/-!
# Eigenfunctions of the convolution operator

For a nonzero eigenvalue `l` of `K_φ`, every eigenvector is the class of a continuous function, and the
eigenspace is invariant under left translations (`K_φ` commutes with them).

Supporting lemmas for the Peter–Weyl theorem; no catalogue entry.
-/

open MeasureTheory

namespace Lightlike.HarmonicAnalysis

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/-- An eigenvector of `K_φ` for a nonzero eigenvalue is the class of a continuous function. -/
lemma eigen_eq_toLp (φ : C(G, ℂ)) {l : ℂ} (hl : l ≠ 0) {v : Lp ℂ 2 μ}
    (hv : v ∈ Module.End.eigenspace (convOp μ φ : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) l) :
    v = ContinuousMap.toLp (E := ℂ) 2 μ ℂ (l⁻¹ • convToC μ φ v) := by
  have h : convOp μ φ v = l • v := Module.End.mem_eigenspace_iff.1 hv
  rw [map_smul]
  have h2 : ContinuousMap.toLp (E := ℂ) 2 μ ℂ (convToC μ φ v) = l • v := h
  rw [h2, smul_smul, inv_mul_cancel₀ hl, one_smul]

/-- The eigenspaces of `K_φ` are invariant under left translations, when `φ` is a class function for
the translated kernel, i.e. the kernel `φ(y⁻¹ x)` is invariant: here always. -/
lemma leftTr_mem_eigenspace (φ : C(G, ℂ)) (s : G) (l : ℂ) {v : Lp ℂ 2 μ}
    (hv : v ∈ Module.End.eigenspace (convOp μ φ : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) l) :
    leftTr μ s v ∈ Module.End.eigenspace (convOp μ φ : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) l := by
  have hk : shiftK s (kerPhi φ) = kerPhi φ := by
    ext ⟨x, y⟩
    simp [shiftK_apply, kerPhi_apply, mul_assoc, mul_inv_rev]
  have hc := leftTr_comp_kerOp μ s (kerPhi φ)
  rw [hk] at hc
  have h : convOp μ φ v = l • v := Module.End.mem_eigenspace_iff.1 hv
  rw [Module.End.mem_eigenspace_iff]
  have h3 := congrArg (fun T => T v) hc
  simp only [ContinuousLinearMap.comp_apply] at h3
  rw [convOp_eq_kerOp]
  show kerOp μ (kerPhi φ) (leftTr μ s v) = l • leftTr μ s v
  have h4 : kerOp μ (kerPhi φ) (leftTr μ s v) = leftTr μ s (kerOp μ (kerPhi φ) v) := h3.symm
  rw [h4, ← convOp_eq_kerOp, h, map_smul]

end

end Lightlike.HarmonicAnalysis
