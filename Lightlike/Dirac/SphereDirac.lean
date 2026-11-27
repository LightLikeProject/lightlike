import Mathlib
import Lightlike.Dirac.SphereSpin
import Lightlike.Spacetime.LeviCivita

/-!
# The spin connection of the 2-sphere in the north frame

For the spin structure `sphereSpinStructure` of the round unit 2-sphere (`Lightlike/Dirac/SphereSpin.lean`), the
connection coefficients of the Levi-Civita connection in the north frame, read in the stereographic coordinate `y`,
are those of the conformally flat frame `stereoF` of `Lightlike/Dirac/StereoSphere.lean`:
`ω_abc = y_c δ_ab − y_b δ_ac` (`stereoOmega`). This identifies the Dirac operator of the spin structure in the north
frame with the chart operator `diracF ρ stereoF stereoOmega` (work in progress).

## This layer

* `dStereoN`: the derivative of `stereoN` is invertible (injective by conformality, `mfderiv_stereoN_injective`);
* `mpullback_frameN`: the pullback of the north frame vector `a` along `stereoN` is `((|y|²+1)/2) eₐ`;
* `lieBracket_frameFlat`: the flat bracket of these fields is `[Xₐ, X_b] = yₐ X_b − y_b Xₐ`.
-/

open Bundle Manifold VectorField
open scoped Manifold ContDiff Matrix

noncomputable section

namespace Lightlike.Dirac

lemma mfderiv_stereoN_injective (y : Fin 2 → ℝ) :
    Function.Injective (mfderiv 𝓘(ℝ, Fin 2 → ℝ) I2 stereoN y) := by
  intro v w h
  have hvw : mfderiv 𝓘(ℝ, Fin 2 → ℝ) I2 stereoN y (v - w) = 0 := by rw [map_sub, h, sub_self]
  have h0 := roundMetric_stereoN y (v - w) (v - w)
  simp only [hvw, map_zero, ContinuousLinearMap.zero_apply] at h0
  have hq := nsq_nonneg y
  have hpos : 0 < 4 * ((nsq y + 1)⁻¹) ^ 2 := by positivity
  have hs : (v - w) 0 * (v - w) 0 + (v - w) 1 * (v - w) 1 = 0 := by
    rcases mul_eq_zero.mp h0.symm with h | h
    · exact absurd h hpos.ne'
    · exact h
  have h00 : (v - w) 0 = 0 := by nlinarith [mul_self_nonneg ((v - w) 0), mul_self_nonneg ((v - w) 1)]
  have h11 : (v - w) 1 = 0 := by nlinarith [mul_self_nonneg ((v - w) 0), mul_self_nonneg ((v - w) 1)]
  funext i
  fin_cases i
  · exact sub_eq_zero.mp h00
  · exact sub_eq_zero.mp h11

/-- The derivative of `stereoN` at `y` as an endomorphism of `ℝ²`. -/
def dStereoNL (y : Fin 2 → ℝ) : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  show (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) from mfderiv 𝓘(ℝ, Fin 2 → ℝ) I2 stereoN y

/-- The derivative of `stereoN` at `y` as a linear isomorphism. -/
def dStereoN (y : Fin 2 → ℝ) : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ) :=
  (LinearEquiv.ofInjectiveEndo (dStereoNL y).toLinearMap (mfderiv_stereoN_injective y)).toContinuousLinearEquiv

lemma dStereoN_apply (y v : Fin 2 → ℝ) : dStereoN y v = mfderiv 𝓘(ℝ, Fin 2 → ℝ) I2 stereoN y v := rfl

/-- The flat field `y ↦ ((|y|²+1)/2) eₐ` on `ℝ²`. -/
def frameFlat (a : Fin 2) (y : Fin 2 → ℝ) : Fin 2 → ℝ := ((nsq y + 1) / 2) • (Pi.single a 1 : Fin 2 → ℝ)

/-- **The pullback of the north frame along `stereoN`** is the flat field `frameFlat a`. -/
lemma mpullback_frameN (a : Fin 2) (y : Fin 2 → ℝ) :
    mpullback 𝓘(ℝ, Fin 2 → ℝ) I2 stereoN (frameN a) y = frameFlat a y := by
  unfold mpullback
  have hd : mfderiv 𝓘(ℝ, Fin 2 → ℝ) I2 stereoN y = (dStereoN y : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) :=
    ContinuousLinearMap.ext fun v => (dStereoN_apply y v).symm
  rw [hd]
  erw [ContinuousLinearMap.inverse_equiv]
  change (dStereoN y).symm (fN a (invN (stereoN y))) = _
  rw [invN_stereoN]
  unfold fN frameFlat
  erw [ContinuousLinearEquiv.map_smul]
  congr 1
  rw [← dStereoN_apply]
  exact (dStereoN y).symm_apply_apply _

lemma hasFDerivAt_halfNsq (y : Fin 2 → ℝ) :
    HasFDerivAt (fun y : Fin 2 → ℝ => (nsq y + 1) / 2)
      ((y 0) • (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ) +
        (y 1) • (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ)) y := by
  have h0 := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) y).pow 2
  have h1 := (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) y).pow 2
  have h2 := ((h0.add h1).add_const 1).const_mul (1 / 2 : ℝ)
  refine (h2.congr_fderiv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
  · ext v; simp; ring
  · simp [nsq]; ring

/-- **The flat bracket**: `[Xₐ, X_b] = yₐ X_b − y_b Xₐ` for `Xₐ = frameFlat a`. -/
lemma lieBracket_frameFlat (a b : Fin 2) (y : Fin 2 → ℝ) :
    lieBracket ℝ (frameFlat a) (frameFlat b) y = y a • frameFlat b y - y b • frameFlat a y := by
  have hD : ∀ c : Fin 2, HasFDerivAt (frameFlat c)
      (((y 0) • (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ) +
        (y 1) • (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ)).smulRight (Pi.single c 1 : Fin 2 → ℝ)) y :=
    fun c => (hasFDerivAt_halfNsq y).smul_const _
  unfold lieBracket
  rw [(hD b).fderiv, (hD a).fderiv]
  ext i
  fin_cases a <;> fin_cases b <;> fin_cases i <;> simp [frameFlat, nsq] <;> ring

end Lightlike.Dirac
