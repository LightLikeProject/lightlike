module

public import Mathlib
public import Lightlike.Lorentz.PoincareIrreps.Measure
public import Lightlike.Lorentz.PoincareIrreps.Massless

/-!
# The invariant measure on the light cone and unitarity of the massless induced representation

HA6 (Wigner's classification), piece after `Measure.lean`. The light cone `lightCone` is an orbit of
`SL(2,ℂ)` with non-compact stabiliser (`ISO(2)`), so the push-forward of the Haar measure would be
infinite on every set. Instead we use the spinor description `P = z z†`, `z ∈ ℂ²`:

* `spinorMap_measurePreserving`: `SL(2,ℂ)` acts on `ℂ² = ℝ⁴` preserving Lebesgue measure
  (the real determinant of `A` is `|det A|² = 1`);
* `spinProj z = z z†` is an equivariant map `ℂ² → Herm2`, `spinProj (A z) = A • spinProj z`;
* `coneMeasure`: the push-forward of Lebesgue measure under `spinProj`, restricted to `lightCone`
  (in energy-angle coordinates this is `E dE dΩ`, i.e. `d³p/|p|` up to a constant);
* `map_lightSMul_coneMeasure`: `coneMeasure` is `SL(2,ℂ)`-invariant;
* `lintegral_lightInducedRep_normSq`: **`lightInducedRep h A` preserves the
  `L²(coneMeasure)` norm** (lower integrals, measurable `ψ`), because `|χ_h| = 1`.

Reference: S. Weinberg, *The Quantum Theory of Fields I* (1995), Chapter 2, §2.5; only the statements
proved here are claimed, no equation numbers.
-/

@[expose] public section

open Matrix MeasureTheory

namespace Lightlike.Lorentz.Poincare

open Lightlike.Lorentz

/-- Two-component complex spinors. -/
abbrev Spinor : Type := Fin 2 → ℂ

/-- The real-linear map `z ↦ A z` of `ℂ² = ℝ⁴`. -/
noncomputable def spinorMap (A : SL2C) : Spinor →ₗ[ℝ] Spinor :=
  (Matrix.mulVecLin (A : Matrix (Fin 2) (Fin 2) ℂ)).restrictScalars ℝ

lemma spinorMap_apply (A : SL2C) (z : Spinor) :
    spinorMap A z = (A : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ z := rfl

/-- The real determinant of `z ↦ A z` is `1`. -/
lemma det_spinorMap (A : SL2C) : LinearMap.det (spinorMap A) = 1 := by
  unfold spinorMap
  rw [LinearMap.det_restrictScalars, ← Matrix.toLin'_apply', LinearMap.det_toLin']
  simp

lemma measurable_spinorMap (A : SL2C) : Measurable (spinorMap A) :=
  (LinearMap.continuous_of_finiteDimensional _).measurable

/-- **Lebesgue measure on `ℂ²` is `SL(2,ℂ)`-invariant.** -/
theorem map_spinorMap_volume (A : SL2C) :
    (volume : Measure Spinor).map (spinorMap A) = volume := by
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure Spinor)
    (by rw [det_spinorMap]; exact one_ne_zero), det_spinorMap]
  simp

/-- The projector `z ↦ z z†` as a Hermitian matrix. -/
def spinProj (z : Spinor) : Herm2 :=
  ⟨Matrix.of fun i j => z i * star (z j), by
    ext i j
    simp [Matrix.conjTranspose_apply, mul_comm]⟩

lemma spinProj_apply (z : Spinor) (i j : Fin 2) :
    (spinProj z).1 i j = z i * star (z j) := rfl

/-- **Equivariance**: `(A z)(A z)† = A (z z†) A†`. -/
lemma spinProj_mulVec (A : SL2C) (z : Spinor) :
    spinProj ((A : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ z) = A • spinProj z := by
  apply Subtype.ext
  rw [coe_smul]
  ext i j
  fin_cases i <;> fin_cases j <;>
  · simp [spinProj_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
    ring

lemma continuous_spinProj : Continuous spinProj := by
  refine Continuous.subtype_mk ?_ _
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (continuous_apply i).mul (continuous_star.comp (continuous_apply j))

/-- The measure `z z†`-pushed Lebesgue measure on Hermitian matrices. -/
noncomputable def spinMeasure : Measure Herm2 := (volume : Measure Spinor).map spinProj

theorem map_smul_spinMeasure (A : SL2C) :
    (spinMeasure).map (fun P : Herm2 => A • P) = spinMeasure := by
  have hc : Continuous fun P : Herm2 => A • P := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const
  unfold spinMeasure
  rw [Measure.map_map hc.measurable continuous_spinProj.measurable]
  have h : (fun P : Herm2 => A • P) ∘ spinProj = spinProj ∘ spinorMap A := by
    funext z; exact (spinProj_mulVec A z).symm
  rw [h, ← Measure.map_map continuous_spinProj.measurable (measurable_spinorMap A),
    map_spinorMap_volume]

lemma measurableSet_lightCone : MeasurableSet lightCone := by
  have h1 : Continuous fun P : Herm2 => P.1.det :=
    Continuous.matrix_det continuous_subtype_val
  have h2 : Continuous fun P : Herm2 => P.1.trace.re :=
    Complex.continuous_re.comp (Continuous.matrix_trace continuous_subtype_val)
  exact (measurableSet_eq_fun h1.measurable measurable_const).inter
    (measurableSet_lt measurable_const h2.measurable)

lemma measurableEmbedding_lightCone_val :
    MeasurableEmbedding (Subtype.val : lightCone → Herm2) :=
  MeasurableEmbedding.subtype_coe measurableSet_lightCone

/-- **The invariant measure on the light cone**: the Lebesgue measure of `ℂ²` pushed forward by
`z ↦ z z†` and restricted to the cone. -/
noncomputable def coneMeasure : Measure lightCone :=
  Measure.comap Subtype.val spinMeasure

lemma spinProj_mem_lightCone {z : Spinor} (hz : z ≠ 0) : (spinProj z) ∈ lightCone := by
  refine ⟨?_, ?_⟩
  · simp [Matrix.det_fin_two, spinProj_apply]
    ring
  · have : (spinProj z).1.trace.re = Complex.normSq (z 0) + Complex.normSq (z 1) := by
      simp [Matrix.trace_fin_two, spinProj_apply, Complex.normSq_apply]
    rw [this]
    by_contra hneg
    have h0 : Complex.normSq (z 0) = 0 := by
      have := Complex.normSq_nonneg (z 0); have := Complex.normSq_nonneg (z 1); linarith
    have h1 : Complex.normSq (z 1) = 0 := by
      have := Complex.normSq_nonneg (z 0); have := Complex.normSq_nonneg (z 1); linarith
    apply hz
    funext i
    fin_cases i
    · exact Complex.normSq_eq_zero.mp h0
    · exact Complex.normSq_eq_zero.mp h1

/-- **The light-cone measure is nonzero.** -/
theorem coneMeasure_ne_zero : coneMeasure ≠ 0 := by
  intro h
  have h1 : coneMeasure Set.univ = 0 := by rw [h]; rfl
  unfold coneMeasure at h1
  rw [measurableEmbedding_lightCone_val.comap_apply, Set.image_univ, Subtype.range_coe] at h1
  unfold spinMeasure at h1
  rw [Measure.map_apply continuous_spinProj.measurable measurableSet_lightCone] at h1
  have hpos : 0 < (volume : Measure Spinor) ({0}ᶜ : Set Spinor) :=
    isOpen_compl_singleton.measure_pos _ ⟨1, by simp⟩
  have hle : (volume : Measure Spinor) ({0}ᶜ : Set Spinor) ≤
      (volume : Measure Spinor) (spinProj ⁻¹' lightCone) :=
    measure_mono fun z hz => spinProj_mem_lightCone hz
  rw [h1] at hle
  exact hpos.not_ge hle

lemma measurable_lightSMul (A : SL2C) : Measurable (lightSMul A) := by
  refine Measurable.subtype_mk ?_
  have hc : Continuous fun P : lightCone => A • P.1 := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.matrix_mul (continuous_subtype_val.comp continuous_subtype_val)).matrix_mul
      continuous_const
  exact hc.measurable

/-- **Invariance of the light-cone measure** under `SL(2,ℂ)`. -/
theorem map_lightSMul_coneMeasure (A : SL2C) :
    (coneMeasure).map (lightSMul A) = coneMeasure := by
  have hc : Continuous fun P : Herm2 => A • P := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const
  ext s hs
  rw [Measure.map_apply (measurable_lightSMul A) hs]
  unfold coneMeasure
  rw [measurableEmbedding_lightCone_val.comap_apply, measurableEmbedding_lightCone_val.comap_apply]
  have hs' : MeasurableSet (Subtype.val '' s) := measurableEmbedding_lightCone_val.measurableSet_image.mpr hs
  have hset : Subtype.val '' (lightSMul A ⁻¹' s) = (fun P : Herm2 => A • P) ⁻¹' (Subtype.val '' s) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨lightSMul A y, hy, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have hxc : x ∈ lightCone := by
        have := smul_mem_lightCone A⁻¹ y.2
        rw [hyx, inv_smul_smul] at this
        exact this
      refine ⟨⟨x, hxc⟩, ?_, rfl⟩
      have : lightSMul A ⟨x, hxc⟩ = y := Subtype.ext hyx.symm
      rw [Set.mem_preimage, this]; exact hy
  rw [hset, ← Measure.map_apply hc.measurable hs', map_smul_spinMeasure]

/-- Invariance of the lower integral over the light cone. -/
theorem lintegral_lightSMul (A : SL2C) {g : lightCone → ENNReal} (hg : Measurable g) :
    ∫⁻ P, g (lightSMul A P) ∂coneMeasure = ∫⁻ P, g P ∂coneMeasure := by
  conv_rhs => rw [← map_lightSMul_coneMeasure A]
  rw [lintegral_map hg (measurable_lightSMul A)]

lemma norm_helChar (h : ℤ) (g : MulAction.stabilizer SL2C (lightMom 1)) :
    ‖((helChar h g : Circle) : ℂ)‖ = 1 := by simp

/-- **The massless induced representation preserves the `L²(coneMeasure)` norm**:
`∫ ‖(U(A) ψ)(P)‖² dμ(P) = ∫ ‖ψ(P)‖² dμ(P)` (lower integrals, measurable `ψ`). -/
theorem lintegral_lightInducedRep_normSq (h : ℤ) (A : SL2C) (ψ : lightCone → ℂ)
    (hψ : Measurable fun P => ENNReal.ofReal (‖ψ P‖ ^ 2)) :
    ∫⁻ P, ENNReal.ofReal (‖lightInducedRep h A ψ P‖ ^ 2) ∂coneMeasure =
      ∫⁻ P, ENNReal.ofReal (‖ψ P‖ ^ 2) ∂coneMeasure := by
  simp only [lightInducedRep_apply, norm_mul, norm_helChar, one_mul]
  exact lintegral_lightSMul A⁻¹ hψ

end Lightlike.Lorentz.Poincare
