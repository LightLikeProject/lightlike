module

public import Lightlike.Poincare.LightConeUnitary

/-!
# An invariant measure on the light cone

The map `π(v) = v vᴴ` from `ℂ² ∖ {0}` onto the forward light cone intertwines the linear action of `SL(2,ℂ)` on `ℂ²`
with its action `P ↦ A P Aᴴ` on Hermitian momenta (`proj_mulVec`). Lebesgue measure on `ℂ² ≅ ℝ⁴` is invariant
under `SL(2,ℂ)` (the real determinant of `v ↦ A v` is the norm of `det A = 1`), so its image under `π` is an
`SL(2,ℂ)`-invariant measure on the light cone (`coneMeasure`, `coneMeasure_map_smul`); it is finite on compact
sets (`isFiniteMeasureOnCompacts_coneMeasure`: `tr(v vᴴ) = ‖v‖²` is bounded on a compact set) and nonzero
(`coneMeasure_ne_zero`). With `lintegral_normSq_helicityAct_of_invariant` the massless helicity representations are
unitary for this measure (`lintegral_normSq_helicityAct`).

Supporting lemmas; no catalogue entry.
-/

@[expose] public section

noncomputable section

open Matrix MeasureTheory Lightlike.Lorentz
open scoped ComplexOrder

namespace Lightlike.Poincare

/-- The rank-one Hermitian matrix `v vᴴ`. -/
def proj (v : Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ := vecMulVec v (star v)

lemma proj_mulVec (A : SL2C) (v : Fin 2 → ℂ) :
    proj ((A : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v) = actP A (proj v) := by
  unfold proj actP
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec, ← Matrix.star_eq_conjTranspose]

lemma proj_mem_lightCone {v : Fin 2 → ℂ} (hv : v ≠ 0) : proj v ∈ LightConeH := by
  refine ⟨Matrix.posSemidef_vecMulVec_self_star v, ?_, fun h => hv ?_⟩
  · simp [proj, Matrix.det_fin_two, Matrix.vecMulVec_apply]; ring
  · funext i
    have h1 := congrFun (congrFun h i) i
    simp only [proj, Matrix.vecMulVec_apply, Pi.star_apply, RCLike.star_def, Complex.mul_conj,
      Matrix.zero_apply, Complex.ofReal_eq_zero, map_eq_zero] at h1
    simpa using h1

/-- The projection to the light cone, sending `0` to the base point. -/
def coneProj (v : Fin 2 → ℂ) : LightCone :=
  if hv : v = 0 then coneBase else ⟨proj v, proj_mem_lightCone hv⟩

lemma coneProj_of_ne {v : Fin 2 → ℂ} (hv : v ≠ 0) : coneProj v = ⟨proj v, proj_mem_lightCone hv⟩ := by
  simp [coneProj, hv]

lemma continuous_proj : Continuous proj := by
  unfold proj
  fun_prop

lemma measurable_coneProj : Measurable coneProj := by
  refine measurable_of_continuousOn_compl_singleton 0 ?_
  rw [continuousOn_iff_continuous_domRestrict]
  have : ({0}ᶜ : Set (Fin 2 → ℂ)).domRestrict coneProj =
      fun v : ({0}ᶜ : Set (Fin 2 → ℂ)) => (⟨proj v.1, proj_mem_lightCone v.2⟩ : LightCone) := by
    funext v
    exact coneProj_of_ne v.2
  rw [this]
  exact (continuous_proj.comp continuous_subtype_val).subtype_mk _

/-- The linear action of `A` on `ℂ²` as a real-linear map. -/
def mulVecR (A : SL2C) : (Fin 2 → ℂ) →ₗ[ℝ] (Fin 2 → ℂ) :=
  (Matrix.toLin' (A : Matrix (Fin 2) (Fin 2) ℂ)).restrictScalars ℝ

lemma det_mulVecR (A : SL2C) : LinearMap.det (mulVecR A) = 1 := by
  rw [mulVecR, LinearMap.det_restrictScalars, LinearMap.det_toLin', A.2, map_one]

/-- Lebesgue measure on `ℂ²` is invariant under `SL(2,ℂ)`. -/
lemma map_mulVec_volume (A : SL2C) :
    Measure.map (fun v : Fin 2 → ℂ => (A : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v) volume = volume := by
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (Fin 2 → ℂ)))
    (f := mulVecR A) (by rw [det_mulVecR]; exact one_ne_zero)
  rw [det_mulVecR] at h
  have hf : (fun v : Fin 2 → ℂ => (A : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v) =
      ((mulVecR A : (Fin 2 → ℂ) →ₗ[ℝ] (Fin 2 → ℂ)) : (Fin 2 → ℂ) → (Fin 2 → ℂ)) := by
    funext v; simp [mulVecR, Matrix.toLin'_apply]
  rw [hf, h]
  simp

/-- **An invariant measure on the light cone**: the image of Lebesgue measure on `ℂ²` under `v ↦ v vᴴ`. -/
def coneMeasure : Measure LightCone := Measure.map coneProj volume

lemma coneProj_mulVec_ae (A : SL2C) :
    (fun v : Fin 2 → ℂ => coneProj ((A : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v)) =ᵐ[volume]
      fun v => A • coneProj v := by
  have h0 : ∀ᵐ v : Fin 2 → ℂ ∂volume, v ≠ 0 := by
    rw [ae_iff]
    simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton]
    exact measure_singleton _
  filter_upwards [h0] with v hv
  have hAv : (A : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v ≠ 0 := by
    intro h
    apply hv
    have hu : IsUnit (A : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [Matrix.isUnit_iff_isUnit_det, A.2]; exact isUnit_one
    exact (Matrix.mulVec_injective_iff_isUnit.2 hu) (by rw [h, Matrix.mulVec_zero])
  rw [coneProj_of_ne hAv, coneProj_of_ne hv]
  apply Subtype.ext
  exact proj_mulVec A v

/-- **Invariance of the cone measure.** -/
theorem coneMeasure_map_smul (A : SL2C) :
    Measure.map (fun P : LightCone => A • P) coneMeasure = coneMeasure := by
  rw [coneMeasure, Measure.map_map (continuous_smul_lightCone A).measurable measurable_coneProj]
  show Measure.map (fun v => A • coneProj v) volume = _
  rw [← Measure.map_congr (coneProj_mulVec_ae A)]
  show Measure.map (coneProj ∘ fun v : Fin 2 → ℂ => (A : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v) volume = _
  rw [← Measure.map_map measurable_coneProj (Continuous.measurable (by fun_prop)), map_mulVec_volume]

/-- **Unitarity of the massless helicity representations** for the invariant cone measure. -/
theorem lintegral_normSq_helicityAct (n : ℤ) (A : SL2C) (ψ : LightCone → ℂ) :
    ∫⁻ P, ENNReal.ofReal (‖helicityAct n A ψ P‖ ^ 2) ∂coneMeasure =
      ∫⁻ P, ENNReal.ofReal (‖ψ P‖ ^ 2) ∂coneMeasure :=
  lintegral_normSq_helicityAct_of_invariant coneMeasure coneMeasure_map_smul n A ψ


lemma trace_proj_re (v : Fin 2 → ℂ) : ((proj v).trace).re = ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 := by
  simp only [proj, Matrix.trace_fin_two, Matrix.vecMulVec_apply, Pi.star_apply, RCLike.star_def,
    Complex.mul_conj, Complex.add_re, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- **The cone measure is finite on compact sets.** -/
instance isFiniteMeasureOnCompacts_coneMeasure : IsFiniteMeasureOnCompacts coneMeasure where
  lt_top_of_isCompact C hC := by
    rw [coneMeasure, Measure.map_apply measurable_coneProj hC.isClosed.measurableSet]
    have hcont : Continuous fun P : LightCone => ((P.1).trace).re :=
      Complex.continuous_re.comp (continuous_subtype_val.matrix_trace)
    obtain ⟨R, hR⟩ := (hC.image hcont).bddAbove
    refine lt_of_le_of_lt (measure_mono ?_) (measure_closedBall_lt_top (x := (0 : Fin 2 → ℂ))
      (r := Real.sqrt (max R 0)))
    intro v hv
    by_cases h0 : v = 0
    · simp [h0]
    · have hle := hR ⟨coneProj v, hv, rfl⟩
      rw [coneProj_of_ne h0] at hle
      simp only at hle
      rw [trace_proj_re] at hle
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
      intro i
      rw [Real.le_sqrt (norm_nonneg _) (le_max_right _ _)]
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue]
        nlinarith [sq_nonneg ‖v 1‖, le_max_left R 0]
      · simp only [Fin.mk_one, Fin.isValue]
        nlinarith [sq_nonneg ‖v 0‖, le_max_left R 0]

/-- **The cone measure is nonzero.** -/
theorem coneMeasure_ne_zero : coneMeasure ≠ 0 := by
  intro h
  have := congrArg (fun μ : Measure LightCone => μ Set.univ) h
  simp only [coneMeasure, Measure.map_apply measurable_coneProj MeasurableSet.univ, Set.preimage_univ,
    Measure.coe_zero, Pi.zero_apply] at this
  exact (isOpen_univ.measure_pos (volume : Measure (Fin 2 → ℂ)) Set.univ_nonempty).ne' this

end Lightlike.Poincare
