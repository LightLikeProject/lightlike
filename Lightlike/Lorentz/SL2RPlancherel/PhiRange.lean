import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.PhiL2
import Lightlike.Lorentz.SL2RPlancherel.SphericalL2
import Lightlike.Lorentz.SL2RPlancherel.HalfAbelInverse
import Lightlike.Lorentz.SL2RPlancherel.CoshCutoff

/-!
# `Φ g` lies in the range of the spherical Plancherel isometry

Two reductions towards the surjectivity of `sphericalL2` for `SL(2,ℝ)` (milestone HA3):

* `phiL2_abelSchwartz`: for a test function `F`, `phiL2 (𝒜F) = sphericalL2 (sphE F)`;
* `phiL2_mem_range_of_approx`: if a Schwartz function `h` is approximated in `H¹` by Schwartz
  functions `g` with `phiL2 g` in the (closed) range, then `phiL2 h` is in the range.
-/

open MeasureTheory Set Real
open scoped FourierTransform ContDiff ENNReal

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- For a test function `F`, `Φ (𝒜 F)` is the image of `F` under `sphericalL2`. -/
theorem phiL2_abelSchwartz (F : smoothCS) :
    phiL2 (abelSchwartz F F.2.1 F.2.2) = sphericalL2 (sphE F) := by
  rw [sphericalL2_apply_test]
  have h1 : sphF F = (memLp_sphL2fun F F.2.1 F.2.2).toLp (sphL2fun F) := rfl
  rw [h1]
  exact MemLp.toLp_congr (memLp_phi_Ioi _) (memLp_sphL2fun F F.2.1 F.2.2)
    (Filter.Eventually.of_forall fun ρ => by rw [phi_abelSchwartz F F.2.1 F.2.2])

/-- If a Schwartz function agrees with the Abel transform of a test function, then `phiL2` of it
is in the range of `sphericalL2`. -/
theorem phiL2_mem_range_of_eq_abel (g : SchwartzMap ℝ ℂ) (F : smoothCS)
    (hg : (g : ℝ → ℂ) = abelTransform F) : phiL2 g ∈ Set.range sphericalL2 := by
  have : g = abelSchwartz F F.2.1 F.2.2 := SchwartzMap.ext fun x => by
    rw [hg]; rfl
  rw [this, phiL2_abelSchwartz]
  exact ⟨_, rfl⟩

/-- If `g = √2 · P ∘ cosh` for a smooth compactly supported `P`, then `phiL2 g` is in the range of
`sphericalL2`. -/
theorem phiL2_mem_range_of_cosh (g : SchwartzMap ℝ ℂ) (P : ℝ → ℂ) (hP : ContDiff ℝ ∞ P)
    (hc : HasCompactSupport P) (hg : ∀ t, g t = (√2 : ℂ) * P (Real.cosh t)) :
    phiL2 g ∈ Set.range sphericalL2 := by
  obtain ⟨F, hF, hFc, hFP⟩ := exists_abelTransform_eq P hP hc
  exact phiL2_mem_range_of_eq_abel g ⟨F, hF, hFc⟩ (funext fun t => by rw [hg t, hFP t])

/-- **Closure step**: if `h` is approximated in `H¹` by Schwartz functions `g` with `phiL2 g` in the
range of `sphericalL2`, then so is `phiL2 h` (the range is closed and `phiL2` is `H¹`-continuous). -/
theorem phiL2_mem_range_of_approx (h : SchwartzMap ℝ ℂ)
    (H : ∀ δ : ℝ, 0 < δ → ∃ g : SchwartzMap ℝ ℂ, phiL2 g ∈ Set.range sphericalL2 ∧
      (∫ x, ‖(h - g) x‖ ^ 2) + ∫ x, ‖deriv (⇑(h - g)) x‖ ^ 2 ≤ δ) :
    phiL2 h ∈ Set.range sphericalL2 := by
  rw [← isClosed_range_sphericalL2.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨g, hg, hgδ⟩ := H (ε ^ 2 / 2) (by positivity)
  refine ⟨phiL2 g, hg, ?_⟩
  rw [dist_eq_norm, ← phiL2_sub]
  have h1 := norm_phiL2_sq_le (h - g)
  by_contra hcon
  rw [not_lt] at hcon
  nlinarith [norm_nonneg (phiL2 (h - g))]

end Lightlike.Lorentz.SL2RPlancherel
