import Mathlib
import Lightlike.Spacetime.GreenOperators.Support

/-!
# Integral form of the retarded solution on 1+1 Minkowski space

Supporting file for G1-021 (SC6; Bär–Ginoux–Pfäffle 2007, source key `bgp-2007`).
The change of variables `(a, b) ↦ nullPt a b = ((a + b)/2, (b - a)/2)` has Jacobian determinant `1/2`,
so for `f` continuous with compact support (indeed any integrable `f`)
`retardedSol f p = -(1/2) ∫_{J⁻(p)} f dt dx` (`retardedSol_eq_integral`),
where `J⁻(p) = {q | causalLE2 q p}` is the causal past of `p`.  That is: the retarded fundamental
solution of `-∂ₜ² + ∂ₓ²` on `1+1` Minkowski space is `-½` times the indicator of the causal past.

This is a supporting result; no catalogue entry.
-/

open Set MeasureTheory

namespace Lightlike.GreenOperators

/-- `nullPt` as a linear map of `ℝ × ℝ`. -/
noncomputable def nullLin : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ :=
  Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
    !![(1 / 2 : ℝ), 1 / 2; -1 / 2, 1 / 2]

lemma nullLin_apply (q : ℝ × ℝ) : nullLin q = nullPt q.1 q.2 := by
  unfold nullLin
  rw [Matrix.toLin_finTwoProd_apply]
  ext <;> simp only [nullPt] <;> ring

lemma det_nullLin : LinearMap.det nullLin = 1 / 2 := by
  unfold nullLin
  rw [LinearMap.det_toLin, Matrix.det_fin_two_of]
  norm_num

lemma map_nullLin_volume :
    Measure.map nullLin (volume : Measure (ℝ × ℝ)) = ENNReal.ofReal 2 • volume := by
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [det_nullLin]; norm_num),
    det_nullLin]
  congr 2
  norm_num

lemma toNull_nullLin (q : ℝ × ℝ) : toNull (nullLin q) = q := by
  rw [nullLin_apply]
  ext <;> simp [toNull_apply, nullPt] <;> ring

/-- The causal past `{q | causalLE2 q p}` is the preimage of a lower-left quadrant under `toNull`. -/
lemma causalPast_eq (p : ℝ × ℝ) :
    {q : ℝ × ℝ | causalLE2 q p} = toNull ⁻¹' Iic (toNull p) := by
  ext q
  simp only [mem_ofPred_eq, mem_preimage, mem_Iic, Prod.le_def, toNull_apply]
  exact causalLE2_iff q p

/-- **Integral form of the retarded solution**: for `f` continuous with compact support (on `1+1`
Minkowski space), `retardedSol f p = -(1/2) ∫_{J⁻(p)} f`, i.e. the retarded fundamental solution of
`-∂ₜ² + ∂ₓ²` is `-½` times the indicator of the causal past. -/
theorem retardedSol_eq_integral {f : ℝ × ℝ → ℝ} (hf : Continuous f) (p : ℝ × ℝ) :
    retardedSol f p = -(1 / 2 : ℝ) * ∫ q in {q : ℝ × ℝ | causalLE2 q p}, f q := by
  have hs : MeasurableSet (toNull ⁻¹' Iic (toNull p)) :=
    measurableSet_Iic.preimage toNull.continuous.measurable
  have hN : Continuous nullLin := LinearMap.continuous_of_finiteDimensional _
  have h1 : retardedSol f p = -(1 / 4 : ℝ) * ∫ q in Iic (toNull p), f (nullLin q) := by
    unfold retardedSol quadPrim
    simp only [Pi.smul_apply, smul_eq_mul, nullSource]
    rw [integral_const_mul]
    simp only [nullLin_apply]
  have h2 : ∫ q in Iic (toNull p), f (nullLin q)
      = ∫ y in toNull ⁻¹' Iic (toNull p), f y ∂(Measure.map nullLin volume) := by
    rw [setIntegral_map hs hf.aestronglyMeasurable hN.measurable.aemeasurable]
    have : nullLin ⁻¹' (toNull ⁻¹' Iic (toNull p)) = Iic (toNull p) := by
      ext q
      simp [toNull_nullLin]
    rw [this]
  rw [h1, h2, map_nullLin_volume, causalPast_eq, Measure.restrict_smul, integral_smul_measure, ENNReal.toReal_ofReal
    (by norm_num)]
  simp only [smul_eq_mul]
  ring

lemma timeRev_measurePreserving :
    MeasurePreserving timeRevHomeo (volume : Measure (ℝ × ℝ)) volume := by
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
    (MeasurePreserving.id (volume : Measure ℝ))
  exact h

/-- **Integral form of the advanced solution**: `advancedSol f p = -(1/2) ∫_{J⁺(p)} f`. -/
theorem advancedSol_eq_integral {f : ℝ × ℝ → ℝ} (hf : Continuous f) (p : ℝ × ℝ) :
    advancedSol f p = -(1 / 2 : ℝ) * ∫ q in {q : ℝ × ℝ | causalLE2 p q}, f q := by
  have hc : Continuous fun q => f (timeRevL q) := hf.comp timeRevL.continuous
  unfold advancedSol
  rw [retardedSol_eq_integral hc]
  congr 1
  have hset : {q : ℝ × ℝ | causalLE2 q (timeRevL p)} = timeRevHomeo ⁻¹' {q : ℝ × ℝ | causalLE2 p q} := by
    ext q
    simp only [mem_ofPred_eq, mem_preimage, timeRevHomeo_apply, causalLE2, timeRevL_apply]
    rw [abs_sub_comm]
    constructor <;> intro h <;> linarith
  rw [hset]
  exact timeRev_measurePreserving.setIntegral_preimage_emb timeRevHomeo.measurableEmbedding f _

/-- The **Pauli–Jordan function** of the massless field on `1+1` Minkowski space, as a function of
the difference `d = p - q = (Δt, Δx)`: `-½ sign(Δt)` inside the closed light cone `|Δx| ≤ |Δt|`
(value `0` for `d = 0` and `0` outside), i.e. `½` on the past cone, `-½` on the future cone,
`0` at spacelike separation. -/
noncomputable def pauliJordan (d : ℝ × ℝ) : ℝ :=
  (if |d.2| ≤ -d.1 then (1 / 2 : ℝ) else 0) - (if |d.2| ≤ d.1 then (1 / 2 : ℝ) else 0)

lemma pauliJordan_of_future {d : ℝ × ℝ} (h : |d.2| < d.1) : pauliJordan d = -(1 / 2 : ℝ) := by
  have h1 : ¬ |d.2| ≤ -d.1 := by
    have := abs_nonneg d.2
    intro h'; linarith
  have h2 : |d.2| ≤ d.1 := h.le
  simp [pauliJordan, h1, h2]

lemma pauliJordan_of_past {d : ℝ × ℝ} (h : |d.2| < -d.1) : pauliJordan d = (1 / 2 : ℝ) := by
  have h2 : ¬ |d.2| ≤ d.1 := by
    have := abs_nonneg d.2
    intro h'; linarith
  have h1 : |d.2| ≤ -d.1 := h.le
  simp [pauliJordan, h1, h2]

lemma pauliJordan_of_spacelike {d : ℝ × ℝ} (h : |d.1| < |d.2|) : pauliJordan d = 0 := by
  have h1 : ¬ |d.2| ≤ -d.1 := by
    intro h'
    have : |(-d.1)| ≥ |d.2| := by simpa using (le_trans h' (le_abs_self _))
    rw [abs_neg] at this
    linarith
  have h2 : ¬ |d.2| ≤ d.1 := by
    intro h'
    have := le_trans h' (le_abs_self _)
    linarith
  simp [pauliJordan, h1, h2]

/-- **Pauli–Jordan function of Minkowski space** (massless, `1+1`): the difference of the retarded
and advanced solutions is the convolution with the Pauli–Jordan function,
`G⁺ f - G⁻ f = ∫ pauliJordan (p - q) f(q) dq`, for `f` continuous with compact support. -/
theorem retarded_sub_advanced_eq_integral {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) (p : ℝ × ℝ) :
    retardedSol f p - advancedSol f p = ∫ q, pauliJordan (p - q) * f q := by
  have hi : Integrable f := hf.integrable_of_hasCompactSupport hc
  rw [retardedSol_eq_integral hf, advancedSol_eq_integral hf]
  have hm1 : MeasurableSet {q : ℝ × ℝ | causalLE2 q p} := by
    have : {q : ℝ × ℝ | causalLE2 q p} = toNull ⁻¹' Iic (toNull p) := causalPast_eq p
    rw [this]; exact measurableSet_Iic.preimage toNull.continuous.measurable
  have hm2 : MeasurableSet {q : ℝ × ℝ | causalLE2 p q} := by
    have : {q : ℝ × ℝ | causalLE2 p q} = toNull ⁻¹' Ici (toNull p) := by
      ext q
      simp only [mem_ofPred_eq, mem_preimage, mem_Ici, Prod.le_def, toNull_apply]
      rw [causalLE2_iff]
    rw [this]; exact measurableSet_Ici.preimage toNull.continuous.measurable
  have hk : ∀ q, pauliJordan (p - q) * f q
      = (1 / 2 : ℝ) * {q : ℝ × ℝ | causalLE2 p q}.indicator f q
        - (1 / 2 : ℝ) * {q : ℝ × ℝ | causalLE2 q p}.indicator f q := by
    intro q
    have e1 : (|(p - q).2| ≤ -(p - q).1) ↔ causalLE2 p q := by
      simp only [causalLE2, Prod.snd_sub, Prod.fst_sub]
      rw [abs_sub_comm]
      constructor <;> intro h <;> linarith
    have e2 : (|(p - q).2| ≤ (p - q).1) ↔ causalLE2 q p := by
      simp only [causalLE2, Prod.snd_sub, Prod.fst_sub]
    classical
    have e3 : pauliJordan (p - q) = (if causalLE2 p q then (1 / 2 : ℝ) else 0)
        - (if causalLE2 q p then (1 / 2 : ℝ) else 0) := by
      unfold pauliJordan
      rw [if_congr e1 rfl rfl, if_congr e2 rfl rfl]
    rw [e3]
    by_cases h1 : causalLE2 p q <;> by_cases h2 : causalLE2 q p <;>
      simp [h1, h2, indicator, mem_ofPred_eq]
  simp_rw [hk]
  rw [integral_sub ((hi.indicator hm2).const_mul _) ((hi.indicator hm1).const_mul _),
    integral_const_mul, integral_const_mul, integral_indicator hm2, integral_indicator hm1]
  ring

end Lightlike.GreenOperators
