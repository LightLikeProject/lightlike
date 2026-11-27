import Mathlib
import Lightlike.Dirac.SphereDirac
import Lightlike.Dirac.SpinorLichnerowicz
import Lightlike.Dirac.SphereSpectrum

/-!
# The Dirac spectrum on the spinor sections of the 2-sphere

The smooth sections of the spinor bundle of `sphereSpinStructure` (`Lightlike/Dirac/SphereSpin.lean`) and their
Dirac operator `SpinorSection.dirac` (`Lightlike/Dirac/SpinorBundle.lean`). This file relates the eigensections
`D σ = λ σ` to the chart eigenspinors of the two-chart spectrum theorem (`SphereEigenspace`,
`Lightlike/Dirac/SphereSpectrum.lean`) through the north chart (work in progress).

## This layer

* `northRep σ`: the representation of `σ` in the north frame, read in the north chart;
* `SpinorSection.eq_zero_of_north`: a smooth section vanishing on `S2 ∖ {N}` vanishes.
-/

open Bundle Manifold Filter
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike.Dirac

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {ρ : CliffordRep 2 V}

lemma stereoS_zero_pc : pc (stereoS 0) 2 = 1 := by
  rw [(pc_stereoS 0).2.2]; simp [nsq]

lemma stereoS_ne_north {y : Fin 2 → ℝ} (hy : y ≠ 0) : pc (stereoS y) 2 ≠ 1 := by
  rw [(pc_stereoS y).2.2]
  have hq : 0 < nsq y := by
    unfold nsq
    by_contra h
    push_neg at h
    have h0 : y 0 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
    have h1 : y 1 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
    exact hy (funext fun i => by fin_cases i <;> simp [h0, h1])
  intro h
  rw [div_eq_one_iff_eq (by positivity)] at h
  linarith

lemma pc_stereoS_ne_south (y : Fin 2 → ℝ) : pc (stereoS y) 2 ≠ -1 := by
  rw [(pc_stereoS y).2.2]
  have hq := nsq_nonneg y
  intro h
  rw [div_eq_iff (by positivity)] at h
  linarith

/-- **A smooth spinor section vanishing away from the north pole vanishes.** -/
theorem SpinorSection.eq_zero_of_north (σ : SpinorSection sphereSpinStructure ρ)
    (h : ∀ p : S2, pc p 2 ≠ 1 → σ p = 0) : σ = 0 := by
  ext p
  by_cases hp : pc p 2 = 1
  · -- `p` is the north pole `stereoS 0`; read `σ` in the south frame along `stereoS`
    have hS : p = stereoS 0 := by
      have hs := pc_sq_sum p
      have h01 : pc p 0 = 0 ∧ pc p 1 = 0 := by
        constructor <;> nlinarith [sq_nonneg (pc p 0), sq_nonneg (pc p 1)]
      apply Subtype.ext
      ext i
      obtain ⟨h0, h1, h2⟩ := pc_stereoS 0
      fin_cases i
      · exact h01.1.trans (by rw [show (0 : Fin (2 + 1)) = 0 from rfl] at h0; simpa [nsq] using h0.symm)
      · exact h01.2.trans (by simpa [nsq] using h1.symm)
      · exact hp.trans (by simpa [nsq] using h2.symm)
    subst hS
    set g : (Fin 2 → ℝ) → V := fun y => σ.toField.rep false (stereoS y)
    have hdom : ∀ y, stereoS y ∈ sphereSpinStructure.dom false := fun y => pc_stereoS_ne_south y
    have hg : ContinuousAt g 0 :=
      ((σ.toField_isSmooth false (stereoS 0) (hdom 0)).continuousAt).comp
        (contMDiff_stereoS 0).continuousAt
    have hg0 : ∀ y, y ≠ 0 → g y = 0 := fun y hy => by
      show σ.toField.rep false (stereoS y) = 0
      rw [show σ.toField.rep false (stereoS y) = σ.rep false (stereoS y) from rfl,
        σ.rep_of_mem (hdom y), h _ (stereoS_ne_north hy)]
      erw [map_zero]
    have hlim : Tendsto g (𝓝[≠] 0) (𝓝 0) :=
      tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun y hy => (hg0 y hy).symm)
    have hg00 : g 0 = 0 := tendsto_nhds_unique (hg.tendsto.mono_left nhdsWithin_le_nhds) hlim
    apply SpinStructure.coordChange_injective (ρ := ρ) (hdom 0)
    simp only
    rw [show ((0 : SpinorSection sphereSpinStructure ρ) (stereoS 0)) = 0 from rfl]
    erw [map_zero, ← σ.rep_of_mem (hdom 0)]
    exact hg00
  · exact h p hp

end Lightlike.Dirac
