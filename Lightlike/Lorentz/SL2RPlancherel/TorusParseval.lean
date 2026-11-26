module

public import Mathlib

/-!
# Parseval on the square `(0,1]²`

For a continuous `P : (Fin 2 → ℝ) → ℂ`, the Fourier coefficients
`c_n = ∫_{(0,1]²} e^{-2πi n·x} P(x) dx` satisfy `∑_n |c_n|² = ∫_{(0,1]²} |P|²`
(`hasSum_sq_box`).  It is Mathlib's Parseval identity on `UnitAddTorus (Fin 2)`, applied to `P`
restricted to the fundamental box.  Layer 2b of the Plancherel formula on `SL(2,ℝ)`, milestone HA3.
-/

@[expose] public section

open MeasureTheory Set Real UnitAddTorus

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure (AddCircle.haarAddCircle (T := 1)))

/-- The fundamental box `(0,1]²`. -/
def box : Set (Fin 2 → ℝ) := {x | ∀ i, x i ∈ Ioc (0 : ℝ) (0 + 1)}

/-- **Parseval on the box.** -/
theorem hasSum_sq_box {P : (Fin 2 → ℝ) → ℂ} (hP : Continuous P) :
    HasSum (fun n : Fin 2 → ℤ => ‖∫ x in box,
        Complex.exp (-(2 * π * Complex.I * ∑ i, (n i : ℂ) * (x i : ℂ))) * P x‖ ^ 2)
      (∫ x in box, ‖P x‖ ^ 2) := by
  set Ψ : UnitAddTorus (Fin 2) → ℂ := fun t => P (fun i => (AddCircle.equivIoc 1 0 (t i)).1) with hΨ
  have hΨm : Measurable Ψ := by
    refine hP.measurable.comp ?_
    refine measurable_pi_iff.2 (fun i => ?_)
    exact measurable_subtype_coe.comp ((AddCircle.measurableEquivIoc 1 0).measurable.comp
      (measurable_pi_apply i))
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : Fin 2 → ℝ)) (b := 1)).exists_bound_of_continuousOn
    hP.continuousOn
  have hΨb : ∀ t, ‖Ψ t‖ ≤ C := fun t => hC _ (by
    constructor <;> intro i
    · exact le_of_lt (by simpa using (AddCircle.equivIoc 1 0 (t i)).2.1)
    · simpa using (AddCircle.equivIoc 1 0 (t i)).2.2)
  have hmem : MemLp Ψ 2 volume :=
    MemLp.of_bound hΨm.aestronglyMeasurable C (ae_of_all _ hΨb)
  set f : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))) := MemLp.toLp Ψ hmem with hf
  have hfΨ : f =ᵐ[volume] Ψ := hmem.coeFn_toLp
  have h := hasSum_sq_mFourierCoeff f
  have hcoef : ∀ n, mFourierCoeff f n = mFourierCoeff Ψ n := fun n =>
    integral_congr_ae (hfΨ.mono fun t ht => by simp [ht])
  have hnorm : ∫ t, ‖f t‖ ^ 2 = ∫ t, ‖Ψ t‖ ^ 2 :=
    integral_congr_ae (hfΨ.mono fun t ht => by simp [ht])
  simp only [hcoef, hnorm] at h
  have hbox : MeasurableSet box := by
    have : box = Set.pi univ (fun _ : Fin 2 => Ioc (0 : ℝ) (0 + 1)) := by
      ext x; simp [box]
    rw [this]; exact MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)
  have hΨP : ∀ x ∈ box, Ψ (fun i => (x i : UnitAddCircle)) = P x := by
    intro x hx
    simp only [hΨ]
    congr 1
    funext i
    rw [AddCircle.equivIoc_coe_eq (hx i)]
  have hset : {x : Fin 2 → ℝ | ∀ i, x i ∈ Ioc ((0 : Fin 2 → ℝ) i) ((0 : Fin 2 → ℝ) i + 1)} = box := by
    ext x; simp [box]
  have hcoef2 : ∀ n : Fin 2 → ℤ, mFourierCoeff Ψ n = ∫ x in box,
      Complex.exp (-(2 * π * Complex.I * ∑ i, (n i : ℂ) * (x i : ℂ))) * P x := by
    intro n
    rw [mFourierCoeff_eq_integral Ψ n 0, hset]
    refine setIntegral_congr_fun hbox (fun x hx => ?_)
    simp only [smul_eq_mul]
    rw [hΨP x hx]
    congr 1
    simp only [mFourier, ContinuousMap.coe_mk, Pi.neg_apply]
    simp only [fourier_coe_apply]
    rw [← Complex.exp_sum]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    push_cast
    ring
  have hint : ∫ t, ‖Ψ t‖ ^ 2 = ∫ x in box, ‖P x‖ ^ 2 := by
    rw [integral_preimage (fun t => ‖Ψ t‖ ^ 2) 0, hset]
    exact setIntegral_congr_fun hbox (fun x hx => by simp only [hΨP x hx])
  simp only [hcoef2, hint] at h
  exact h

end Lightlike.Lorentz.SL2RPlancherel
