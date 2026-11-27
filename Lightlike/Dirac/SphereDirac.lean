import Mathlib
import Lightlike.Dirac.SphereSpin
import Lightlike.Spacetime.LeviCivita
import Lightlike.Dirac.SpinManifold
import Lightlike.Dirac.StereoSphere
import Lightlike.Dirac.LichnerowiczGeneral

/-!
# The spin connection of the 2-sphere in the north frame

For the spin structure `sphereSpinStructure` of the round unit 2-sphere (`Lightlike/Dirac/SphereSpin.lean`), the
connection coefficients of the Levi-Civita connection in the north frame, read in the stereographic coordinate `y`,
are those of the conformally flat frame `stereoF` of `Lightlike/Dirac/StereoSphere.lean`:
`ω_abc = y_c δ_ab − y_b δ_ac` (`stereoOmega`). This identifies the Dirac operator of the spin structure in the north
frame with the chart operator `diracF ρ stereoF stereoOmega`.

## Main results

* `dStereoN`: the derivative of `stereoN` is invertible (injective by conformality, `mfderiv_stereoN_injective`);
* `mpullback_frameN`: the pullback of the north frame vector `a` along `stereoN` is `((|y|²+1)/2) eₐ`;
* `lieBracket_frameFlat`, `mlieBracket_frameN`: `[Fₐ, F_b] = yₐ F_b − y_b Fₐ`;
* `connForm_sphere_north`: `ω_abc = y_c δ_ab − y_b δ_ac` (Koszul formula);
* `dirac_sphere_north`: the Dirac operator of `sphereSpinStructure` in the north frame is
  `diracF ρ stereoF stereoOmega` in the north chart.
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

/-! ## The bracket of the north frame on the sphere -/

lemma pc_stereoN_ne (y : Fin 2 → ℝ) : pc (stereoN y) 2 ≠ 1 := by
  rw [(pc_stereoN y).2.2]
  have hq := nsq_nonneg y
  intro h
  rw [div_eq_one_iff_eq (by positivity)] at h
  linarith

lemma frameN_stereoN (a : Fin 2) (y : Fin 2 → ℝ) :
    (frameN a (stereoN y) : Fin 2 → ℝ) = dStereoN y (frameFlat a y) := by
  change fN a (invN (stereoN y)) = _
  rw [invN_stereoN]
  unfold fN frameFlat
  rw [map_smul, dStereoN_apply]
  rfl

/-- **The bracket of the north frame**: `[Fₐ, F_b] = yₐ F_b − y_b Fₐ` at `stereoN y`. -/
theorem mlieBracket_frameN (a b : Fin 2) (y : Fin 2 → ℝ) :
    (mlieBracket I2 (frameN a) (frameN b) (stereoN y) : Fin 2 → ℝ) =
      y a • (frameN b (stereoN y) : Fin 2 → ℝ) - y b • (frameN a (stereoN y) : Fin 2 → ℝ) := by
  have hV := (frameN_smooth a (pc_stereoN_ne y)).mdifferentiableAt (by simp)
  have hW := (frameN_smooth b (pc_stereoN_ne y)).mdifferentiableAt (by simp)
  have h := mpullback_mlieBracket (f := stereoN) (x₀ := y) hV hW (contMDiff_stereoN y) (by simp)
  have hpb : ∀ c, mpullback 𝓘(ℝ, Fin 2 → ℝ) I2 stereoN (frameN c) =
      fun z => (frameFlat c z : TangentSpace 𝓘(ℝ, Fin 2 → ℝ) z) := fun c => funext (mpullback_frameN c)
  have hfl : mlieBracket 𝓘(ℝ, Fin 2 → ℝ) (fun z => (frameFlat a z : TangentSpace 𝓘(ℝ, Fin 2 → ℝ) z))
      (fun z => (frameFlat b z : TangentSpace 𝓘(ℝ, Fin 2 → ℝ) z)) y =
      lieBracket ℝ (frameFlat a) (frameFlat b) y := by
    have := congrFun (mlieBracketWithin_eq_lieBracketWithin (𝕜 := ℝ)
      (V := fun z => (frameFlat a z : TangentSpace 𝓘(ℝ, Fin 2 → ℝ) z))
      (W := fun z => (frameFlat b z : TangentSpace 𝓘(ℝ, Fin 2 → ℝ) z)) (s := Set.univ)) y
    rw [← lieBracketWithin_univ]
    exact this
  rw [hpb, hpb, hfl] at h
  have hflat := lieBracket_frameFlat a b y
  have hd : mfderiv 𝓘(ℝ, Fin 2 → ℝ) I2 stereoN y = (dStereoN y : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) :=
    ContinuousLinearMap.ext fun v => (dStereoN_apply y v).symm
  unfold mpullback at h
  rw [hd] at h
  erw [ContinuousLinearMap.inverse_equiv] at h
  have h2 := congrArg (dStereoN y) h
  have h3 : (mlieBracket I2 (frameN a) (frameN b) (stereoN y) : Fin 2 → ℝ) =
      dStereoN y (lieBracket ℝ (frameFlat a) (frameFlat b) y) := by
    rw [← h2]; exact ((dStereoN y).apply_symm_apply _).symm
  rw [h3, frameN_stereoN, frameN_stereoN]
  change dStereoN y (lieBracket ℝ (frameFlat a) (frameFlat b) y) = _
  rw [hflat, map_sub, map_smul, map_smul]
  rfl

/-! ## The connection coefficients of the north frame -/

lemma gpair_frameN_eventually (b c : Fin 2) {p : S2} (hp : pc p 2 ≠ 1) :
    gpair (roundMetric2I 1 one_ne_zero) (frameN b) (frameN c) =ᶠ[nhds p]
      fun _ => if b = c then (1 : ℝ) else 0 := by
  filter_upwards [(isOpen_pc_ne 1).mem_nhds hp] with q hq using frameN_orthonormal hq b c

lemma mvfderiv_gpair_frameN (b c : Fin 2) {p : S2} (hp : pc p 2 ≠ 1) (v : TangentSpace I2 p) :
    mvfderiv I2 (gpair (roundMetric2I 1 one_ne_zero) (frameN b) (frameN c)) p v = 0 := by
  rw [mvfderiv_congr_nhds' (gpair_frameN_eventually b c hp), mvfderiv_const]
  rfl

lemma g_frameN_bracket (a b c : Fin 2) (y : Fin 2 → ℝ) :
    (roundMetric2I 1 one_ne_zero).g (stereoN y) (frameN c (stereoN y))
        (mlieBracket I2 (frameN a) (frameN b) (stereoN y)) =
      y a * (if c = b then 1 else 0) - y b * (if c = a then 1 else 0) := by
  have hp := pc_stereoN_ne y
  have hb := mlieBracket_frameN a b y
  change (roundMetric2I 1 one_ne_zero).g (stereoN y) (frameN c (stereoN y))
    ((mlieBracket I2 (frameN a) (frameN b) (stereoN y) : Fin 2 → ℝ)) = _
  rw [hb]
  change (roundMetric2I 1 one_ne_zero).g (stereoN y) (frameN c (stereoN y))
    (y a • frameN b (stereoN y) - y b • frameN a (stereoN y)) = _
  rw [map_sub, map_smul, map_smul, frameN_orthonormal hp, frameN_orthonormal hp, smul_eq_mul, smul_eq_mul]

/-- **The connection coefficients of the north frame are those of `stereoF`**: at `stereoN y`,
`ω_abc = g(∇_{Fₐ} F_b, F_c) = y_c δ_ab − y_b δ_ac` (`stereoOmega`). -/
theorem connForm_sphere_north (y : Fin 2 → ℝ) (a b c : Fin 2) :
    sphereSpinStructure.connForm true (stereoN y) a b c =
      (if a = b then y c else 0) - (if a = c then y b else 0) := by
  have hp := pc_stereoN_ne y
  have hd : ∀ d, MDifferentiableAt I2 (I2.prod 𝓘(ℝ, Fin 2 → ℝ))
      (fun q => (⟨q, frameN d q⟩ : TangentBundle I2 S2)) (stereoN y) :=
    fun d => (frameN_smooth d hp).mdifferentiableAt (by simp)
  change (roundMetric2I 1 one_ne_zero).g (stereoN y)
    (leviCivita (roundMetric2I 1 one_ne_zero) (frameN b) (stereoN y) (frameN a (stereoN y)))
    (frameN c (stereoN y)) = _
  rw [g_leviCivita (roundMetric2I 1 one_ne_zero) (hd a) (hd b) (hd c)]
  unfold koszul
  rw [mvfderiv_gpair_frameN b c hp, mvfderiv_gpair_frameN c a hp, mvfderiv_gpair_frameN a b hp,
    g_frameN_bracket, g_frameN_bracket, g_frameN_bracket]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp <;> ring

/-! ## The Dirac operator in the north frame is the chart operator `diracF ρ stereoF stereoOmega` -/

section Chart

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma connForm_sphere_north_eq (x : E 2) (a : Fin 2) :
    sphereSpinStructure.connForm true (stereoN (modelEquiv2 x)) a = stereoOmega x a := by
  ext b c
  rw [connForm_sphere_north]
  rfl

lemma stereoH_eq (x : E 2) : stereoH x = (nsq (modelEquiv2 x) + 1) / 2 := by
  unfold stereoH
  rw [← norm_sq_modelEquiv2_symm, ContinuousLinearEquiv.symm_apply_apply]; ring

lemma modelEquiv2_stereoF (x : E 2) (a : Fin 2) :
    modelEquiv2 (stereoF x a) = frameFlat a (modelEquiv2 x) := by
  unfold stereoF frameFlat
  rw [map_smul, stereoH_eq]
  congr 1

/-- The chain rule through the north chart: `d(φ ∘ σN ∘ e)ₓ(v) = dφ(dσN(e v))`. -/
lemma fderiv_comp_stereoN {φ : S2 → V} {x : E 2}
    (hφ : MDifferentiableAt I2 𝓘(ℝ, V) φ (stereoN (modelEquiv2 x))) (v : E 2) :
    fderiv ℝ (φ ∘ stereoN ∘ modelEquiv2) x v =
      mvfderiv I2 φ (stereoN (modelEquiv2 x)) (mfderiv 𝓘(ℝ, Fin 2 → ℝ) I2 stereoN (modelEquiv2 x) (modelEquiv2 v)) := by
  have hσ : MDifferentiableAt 𝓘(ℝ, Fin 2 → ℝ) I2 stereoN (modelEquiv2 x) :=
    (contMDiff_stereoN (modelEquiv2 x)).mdifferentiableAt (by simp)
  have h1 : fderiv ℝ ((φ ∘ stereoN) ∘ modelEquiv2) x =
      (fderiv ℝ (φ ∘ stereoN) (modelEquiv2 x)).comp (modelEquiv2 : E 2 →L[ℝ] Fin 2 → ℝ) :=
    modelEquiv2.comp_right_fderiv
  show fderiv ℝ ((φ ∘ stereoN) ∘ modelEquiv2) x v = _
  have h2 : fderiv ℝ (φ ∘ stereoN) (modelEquiv2 x) (modelEquiv2 v) =
      mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, V) (φ ∘ stereoN) (modelEquiv2 x) (modelEquiv2 v) := by
    rw [mfderiv_eq_fderiv]; rfl
  rw [h1, ContinuousLinearMap.comp_apply]
  erw [h2, mfderiv_comp _ hφ hσ]
  rfl

/-- **The Dirac operator of the spin structure of `S2` in the north frame** is the chart operator
`diracF ρ stereoF stereoOmega` of `Lightlike/Dirac/StereoSphere.lean`, read through the north chart. -/
theorem dirac_sphere_north (ρ : CliffordRep 2 V) {φ : S2 → V} {x : E 2}
    (hφ : MDifferentiableAt I2 𝓘(ℝ, V) φ (stereoN (modelEquiv2 x))) :
    sphereSpinStructure.dirac ρ true φ (stereoN (modelEquiv2 x)) =
      diracF ρ stereoF stereoOmega (φ ∘ stereoN ∘ modelEquiv2) x := by
  unfold SpinStructure.dirac diracF
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  unfold SpinStructure.nabla SpinStructure.nablaV nablaF
  rw [fderiv_comp_stereoN hφ, modelEquiv2_stereoF]
  have hC := connForm_sphere_north_eq x a
  unfold SpinStructure.connForm at hC
  rw [hC]
  congr 2
  rw [← dStereoN_apply]
  exact frameN_stereoN a (modelEquiv2 x)

end Chart

end Lightlike.Dirac
