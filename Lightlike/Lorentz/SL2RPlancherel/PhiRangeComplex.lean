import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.PhiRangeReal

/-!
# `Φ h` is in the range of `sphericalL2` for complex even compactly supported `h`

`phiL2` is `ℂ`-linear (`phiL2_add`, `phiL2_smul`); splitting an even compactly supported
Schwartz function into real and imaginary parts reduces to `phiL2_mem_range_of_real`
(milestone HA3, step S5c of the surjectivity programme for `sphericalL2`).
-/

open MeasureTheory Set Real
open scoped FourierTransform ContDiff ENNReal

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

theorem phi_add (g h : SchwartzMap ℝ ℂ) : phi (g + h) = phi g + phi h := by
  funext ρ
  simp only [phi, Pi.add_apply, map_add, add_apply, mul_add]

theorem phi_smul (c : ℂ) (g : SchwartzMap ℝ ℂ) : phi (c • g) = c • phi g := by
  funext ρ
  simp only [phi, Pi.smul_apply, map_smul, smul_apply, smul_eq_mul]
  ring

theorem phiL2_add (g h : SchwartzMap ℝ ℂ) : phiL2 (g + h) = phiL2 g + phiL2 h := by
  unfold phiL2
  rw [← MemLp.toLp_add (memLp_phi_Ioi g) (memLp_phi_Ioi h)]
  exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun ρ => by simp [phi_add])

theorem phiL2_smul (c : ℂ) (g : SchwartzMap ℝ ℂ) : phiL2 (c • g) = c • phiL2 g := by
  unfold phiL2
  rw [← MemLp.toLp_const_smul c (memLp_phi_Ioi g)]
  exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun ρ => by simp [phi_smul])

/-- `Φ h` lies in the range of `sphericalL2` for every even compactly supported Schwartz
function `h`. -/
theorem phiL2_mem_range_of_compact (h : SchwartzMap ℝ ℂ) (he : ∀ t, h (-t) = h t)
    (hc : HasCompactSupport h) :
    phiL2 h ∈ Set.range sphericalL2 := by
  obtain ⟨T0, hT0⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℝ)
  have hsup : ∀ t : ℝ, T0 < |t| → h t = 0 := by
    intro t ht
    by_contra hne
    have hmem : t ∈ Function.support h := hne
    have := hT0 (subset_tsupport _ hmem)
    rw [mem_closedBall_zero_iff, Real.norm_eq_abs] at this
    linarith
  have hre_s : ContDiff ℝ ∞ (fun t => (h t).re) :=
    Complex.reCLM.contDiff.comp (h.smooth (⊤ : ℕ∞))
  have him_s : ContDiff ℝ ∞ (fun t => (h t).im) :=
    Complex.imCLM.contDiff.comp (h.smooth (⊤ : ℕ∞))
  have hre_c : HasCompactSupport (fun t => (((h t).re : ℝ) : ℂ)) := by
    refine HasCompactSupport.intro hc.isCompact fun t ht => ?_
    have : h t = 0 := by simpa using (notMem_tsupport_iff_eventuallyEq.1 ht).self_of_nhds
    simp [this]
  have him_c : HasCompactSupport (fun t => (((h t).im : ℝ) : ℂ)) := by
    refine HasCompactSupport.intro hc.isCompact fun t ht => ?_
    have : h t = 0 := by simpa using (notMem_tsupport_iff_eventuallyEq.1 ht).self_of_nhds
    simp [this]
  set hr : SchwartzMap ℝ ℂ :=
    hre_c.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hre_s) with hhr
  set hi : SchwartzMap ℝ ℂ :=
    him_c.toSchwartzMap (Complex.ofRealCLM.contDiff.comp him_s) with hhi
  have hr1 : phiL2 hr ∈ Set.range sphericalL2 :=
    phiL2_mem_range_of_real hr (fun t => (h t).re) (fun t => rfl) hre_s
      (fun t => by simp [he t]) T0 (fun t ht => by simp [hsup t ht])
  have hi1 : phiL2 hi ∈ Set.range sphericalL2 :=
    phiL2_mem_range_of_real hi (fun t => (h t).im) (fun t => rfl) him_s
      (fun t => by simp [he t]) T0 (fun t ht => by simp [hsup t ht])
  have hdec : h = hr + Complex.I • hi := by
    ext t
    have e1 : hr t = (((h t).re : ℝ) : ℂ) := rfl
    have e2 : hi t = (((h t).im : ℝ) : ℂ) := rfl
    simp only [add_apply, smul_apply, e1, e2, smul_eq_mul]
    apply Complex.ext <;> simp
  obtain ⟨a, ha⟩ := hr1
  obtain ⟨b, hb⟩ := hi1
  refine ⟨a + Complex.I • b, ?_⟩
  rw [hdec, phiL2_add, phiL2_smul, map_add, map_smul, ha, hb]

end Lightlike.Lorentz.SL2RPlancherel
