import Lightlike.HarmonicAnalysis.KernelAdjoint

/-!
# Self-adjointness of the convolution operator

The convolution operator `K_φ` is the kernel operator of `k_φ(x, y) = φ(y⁻¹ x)` (`convOp_eq_kerOp`); for a
function with `φ(z⁻¹) = conj φ(z)` the kernel is its own adjoint, so `K_φ` is self-adjoint and compact.

Supporting lemma for the Peter–Weyl theorem; no catalogue entry.
-/

open MeasureTheory

namespace Lightlike.HarmonicAnalysis

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/-- The kernel `(x, y) ↦ φ(y⁻¹ x)` of the convolution operator. -/
def kerPhi (φ : C(G, ℂ)) : C(G × G, ℂ) := ⟨fun p => φ (p.2⁻¹ * p.1), by fun_prop⟩

lemma kerPhi_apply (φ : C(G, ℂ)) (x y : G) : kerPhi φ (x, y) = φ (y⁻¹ * x) := rfl

lemma kerCurry_kerPhi (φ : C(G, ℂ)) : kerCurry (kerPhi φ) = kernelMap φ := rfl

/-- The convolution operator is the integral operator with kernel `φ(y⁻¹ x)`. -/
theorem convOp_eq_kerOp (φ : C(G, ℂ)) : convOp μ φ = kerOp μ (kerPhi φ) := rfl

/-- The kernel `φ(y⁻¹ x)` is its own adjoint when `φ(z⁻¹) = conj φ(z)`. -/
lemma kerDagger_kerPhi {φ : C(G, ℂ)} (hφ : ∀ z, φ z⁻¹ = starRingEnd ℂ (φ z)) :
    kerDagger (kerPhi φ) = kerPhi φ := by
  ext ⟨x, y⟩
  rw [kerDagger_apply, kerPhi_apply, kerPhi_apply, ← hφ]
  simp [mul_inv_rev]

/-- **Self-adjointness.** For `φ(z⁻¹) = conj φ(z)` the convolution operator is self-adjoint. -/
theorem isSelfAdjoint_convOp {φ : C(G, ℂ)} (hφ : ∀ z, φ z⁻¹ = starRingEnd ℂ (φ z)) :
    IsSelfAdjoint (convOp μ φ) := by
  rw [convOp_eq_kerOp, IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint, adjoint_kerOp,
    kerDagger_kerPhi hφ]

end

end Lightlike.HarmonicAnalysis
