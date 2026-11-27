import Mathlib
import Lightlike.Geometry.FlatTorus
import Lightlike.Spacetime.PullbackForm
import Lightlike.Spacetime.NondegMetricBase
import Lightlike.Spacetime.Curvature

/-!
# The flat metric of the torus `(ℝ/ℤ)ⁿ`

The flat metric `Σ dyᵢ²` of the torus is the pullback of the Euclidean form of `ℂⁿ = ℝ²ⁿ` by the embedding
`ι(x)ᵢ = e^{2πi xᵢ} / 2π` (`FlatTorus.torusEmb`), the product of the circles of circumference `1`: each factor is an
isometry of the circle `ℝ/ℤ` (length `1`) onto the circle of radius `1/2π` (`FlatTorus.flatMetric`). It is a smooth
nondegenerate metric (`Lightlike.NondegMetric`), and in every chart of the torus its coordinate metric is the identity
matrix (`FlatTorus.coordMetric_flatMetric`), as for the flat metric of `ℝⁿ` restricted to a fundamental domain.

This is the curvature-free compact example on which the heat-trace layer is checked: `a₀ = vol = 1`, `a₁ = 0`.
-/

open Set Manifold Topology Filter Complex
open scoped ContDiff Real ComplexConjugate

noncomputable section

namespace Lightlike

namespace FlatTorus

variable {n : ℕ}

/-- The circle `ℝ/ℤ` embedded in `ℂ` as the circle of radius `1/2π`: `y ↦ e^{2πiy} / 2π`. -/
def circleEmb (x : AddCircle (1 : ℝ)) : ℂ := (AddCircle.toCircle x : ℂ) / (2 * π)

theorem circleEmb_coe (y : ℝ) : circleEmb (y : AddCircle (1 : ℝ)) = Complex.exp (2 * π * y * I) / (2 * π) := by
  unfold circleEmb
  rw [AddCircle.toCircle_apply_mk, Circle.coe_exp]
  congr 2
  push_cast
  ring

/-- The torus embedded in `ℂⁿ`. -/
def torusEmb (x : FlatTorus n) : Fin n → ℂ := fun i => circleEmb (x i)

/-- The embedding in the coordinates of any chart: `y ↦ (e^{2πi yᵢ} / 2π)ᵢ`. -/
def torusEmbCoord (y : Fin n → ℝ) : Fin n → ℂ := fun i => Complex.exp (2 * π * y i * I) / (2 * π)

/-- The derivative of the embedding in coordinates: `v ↦ (vᵢ · i e^{2πi yᵢ})ᵢ`. -/
def torusEmbDeriv (y : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i)).smulRight
      (I * Complex.exp (2 * π * y i * I))

theorem torusEmbDeriv_apply (y v : Fin n → ℝ) (i : Fin n) :
    torusEmbDeriv y v i = (v i : ℂ) * (I * Complex.exp (2 * π * y i * I)) := by
  simp [torusEmbDeriv]

theorem hasDerivAt_circleCoord (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (2 * π * s * I) / (2 * π)) (I * Complex.exp (2 * π * t * I)) t := by
  have h1 : HasDerivAt (fun s : ℝ => (2 * π * s * I : ℂ)) (2 * π * I) t := by
    have := ((hasDerivAt_id (t : ℝ)).ofReal_comp).const_mul (2 * π : ℂ)
    have := this.mul_const I
    simpa [mul_assoc] using this
  have h2 := (h1.cexp).div_const (2 * π : ℂ)
  convert h2 using 1
  have hπ : (2 * π : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  field_simp

theorem hasFDerivAt_torusEmbCoord (y : Fin n → ℝ) : HasFDerivAt torusEmbCoord (torusEmbDeriv y) y := by
  rw [hasFDerivAt_pi']
  intro i
  have hp : HasFDerivAt (fun z : Fin n → ℝ => z i) (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ) y :=
    hasFDerivAt_apply i y
  have h := (hasDerivAt_circleCoord (y i)).hasFDerivAt.comp y hp
  refine HasFDerivAt.congr_fderiv (f := fun x => torusEmbCoord x i) h ?_
  ext v
  simp [torusEmbDeriv_apply, mul_comm]

theorem contDiff_torusEmbCoord : ContDiff ℝ ∞ (torusEmbCoord (n := n)) := by
  unfold torusEmbCoord
  rw [contDiff_pi]
  intro i
  have h1 : ContDiff ℝ ∞ (fun x : Fin n → ℝ => ((x i : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ (fun _ : Fin n => ℝ) i)
  have h2 : ContDiff ℝ ∞ (fun x : Fin n → ℝ => 2 * (π : ℂ) * ((x i : ℝ) : ℂ) * I) :=
    (contDiff_const.mul h1).mul contDiff_const
  exact ((Complex.contDiff_exp (𝕜 := ℝ)).comp h2).div_const _

/-- The inverse of every chart of the torus is the quotient map, coordinatewise. -/
theorem extChartAt_symm_apply (x : FlatTorus n) (y : Fin n → ℝ) :
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm y = fun i => (y i : AddCircle (1 : ℝ)) := by
  simp only [extChartAt, PartialEquiv.coe_trans_symm, modelWithCornersSelf_partialEquiv, PartialEquiv.refl_symm,
    PartialEquiv.refl_coe, Function.comp_id, OpenPartialHomeomorph.coe_toPartialEquiv_symm]
  rfl

theorem torusEmb_comp_extChartAt_symm (x : FlatTorus n) :
    torusEmb ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm = torusEmbCoord := by
  funext y i
  simp only [Function.comp_apply, extChartAt_symm_apply, torusEmb, torusEmbCoord, circleEmb_coe]

/-- **The embedding is smooth.** -/
theorem contMDiff_torusEmb : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℂ) ∞ (torusEmb (n := n)) := by
  rw [contMDiff_iff]
  refine ⟨continuous_pi fun i => ((AddCircle.continuous_toCircle.comp (continuous_apply i)).subtype_val.div_const _),
    fun x y => ?_⟩
  simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp, PartialEquiv.refl_source,
    preimage_univ, inter_univ]
  rw [torusEmb_comp_extChartAt_symm]
  exact contDiff_torusEmbCoord.contDiffOn

/-- The Euclidean form of `ℂⁿ` as a real bilinear form: `Σᵢ Re(conj aᵢ · bᵢ)`. -/
def euclidForm : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ :=
  ∑ i, (innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ).bilinearComp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i)
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i)

theorem euclidForm_apply (a b : Fin n → ℂ) : euclidForm a b = ∑ i, inner ℝ (a i) (b i) := by
  simp [euclidForm, ContinuousLinearMap.sum_apply]

/-- The derivative of the embedding at a point is the coordinate derivative in the chart at that point. -/
theorem dι_torusEmb (p : FlatTorus n) :
    dι (I := 𝓘(ℝ, Fin n → ℝ)) torusEmb p = torusEmbDeriv (extChartAt 𝓘(ℝ, Fin n → ℝ) p p) := by
  unfold dι
  have hmd : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℂ) torusEmb p :=
    contMDiff_torusEmb.mdifferentiableAt (by simp)
  rw [hmd.mfderiv]
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp,
    modelWithCornersSelf_coe, range_id]
  rw [torusEmb_comp_extChartAt_symm, fderivWithin_univ]
  exact (hasFDerivAt_torusEmbCoord _).fderiv

theorem norm_I_mul_exp (t : ℝ) : ‖I * Complex.exp (2 * π * t * I)‖ = 1 := by
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_exp]
  simp

/-- The pullback form in coordinates: `Σᵢ vᵢ wᵢ`. -/
theorem euclidForm_torusEmbDeriv (y v w : Fin n → ℝ) :
    euclidForm (torusEmbDeriv y v) (torusEmbDeriv y w) = ∑ i, v i * w i := by
  rw [euclidForm_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [torusEmbDeriv_apply, torusEmbDeriv_apply, Complex.inner]
  set z := I * Complex.exp (2 * π * y i * I)
  have hz : conj z * z = 1 := by rw [Complex.conj_mul', norm_I_mul_exp]; simp
  have : (w i : ℂ) * z * conj ((v i : ℂ) * z) = ((v i * w i : ℝ) : ℂ) * (conj z * z) := by
    rw [map_mul, Complex.conj_ofReal]; push_cast; ring
  rw [this, hz, mul_one, Complex.ofReal_re]

/-- **The flat metric of the torus**, the pullback of the Euclidean form of `ℂⁿ` by `torusEmb`. -/
def flatMetric (n : ℕ) : NondegMetric 𝓘(ℝ, Fin n → ℝ) (FlatTorus n) where
  g := pullbackForm (I := 𝓘(ℝ, Fin n → ℝ)) euclidForm torusEmb
  symm x v w := pullbackForm_symm (fun a b => by
    rw [euclidForm_apply, euclidForm_apply]; exact Finset.sum_congr rfl fun i _ => real_inner_comm _ _) _ x v w
  nondegenerate x v h := by
    have h0 := h v
    rw [pullbackForm_apply, dι_torusEmb] at h0
    erw [euclidForm_torusEmbDeriv] at h0
    have hv : ∀ i, v i = 0 := fun i => by
      have hs : ∑ j, v j * v j = 0 := h0
      have hnn : ∀ j ∈ Finset.univ, 0 ≤ v j * v j := fun j _ => mul_self_nonneg _
      have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hs i (Finset.mem_univ _)
      exact mul_self_eq_zero.1 this
    funext i; exact hv i
  contMDiff := contMDiff_pullbackForm _ contMDiff_torusEmb

/-- **The coordinate metric of the flat torus is the identity matrix** in every chart, on the whole chart target. -/
theorem coordMetric_flatMetric (x₀ : FlatTorus n) {y : Fin n → ℝ} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) :
    (flatMetric n).coordMetric x₀ y = 1 := by
  have hD : ∀ v : Fin n → ℝ, dι (I := 𝓘(ℝ, Fin n → ℝ)) torusEmb ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)
      (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y v) = torusEmbDeriv y v := by
    intro v
    have hι : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℂ) torusEmb
        ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) := contMDiff_torusEmb.mdifferentiableAt (by simp)
    have hs : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y :=
      (mdifferentiableWithinAt_extChartAt_symm hy).mdifferentiableAt (by simp)
    unfold dι
    exact (DFunLike.congr_fun (mfderiv_comp y hι hs) v).symm.trans (by
      rw [torusEmb_comp_extChartAt_symm, mfderiv_eq_fderiv, (hasFDerivAt_torusEmbCoord y).fderiv]; rfl)
  funext i j
  unfold NondegMetric.coordMetric
  change pullbackForm (I := 𝓘(ℝ, Fin n → ℝ)) euclidForm torusEmb _ _ _ = _
  rw [pullbackForm_apply, hD, hD, euclidForm_torusEmbDeriv]
  simp [Matrix.one_apply, Pi.single_apply, eq_comm]

end FlatTorus

end Lightlike
