import Mathlib
import Lightlike.Spacetime.GreenOperators.Primitive

/-!
# The double primitive of a continuous function vanishing near the lower edges

Supporting file for G1-021 (SC6; Bär–Ginoux–Pfäffle 2007, source key `bgp-2007`).
`Primitive.lean` treats compactly supported `C²` functions.  For the massive Klein–Gordon
equation the integrand is `w = h + c u`, which is only known to be continuous and to vanish when
`a ≤ -R` or `b ≤ -R`, while `quadPrim w = u` is known to be `C²`.  Here the three results
`quadPrim_eq_iterated'`, `fderiv_quadPrim_fst'`, `fderiv_fderiv_quadPrim'` are proved under the
hypotheses `Continuous w`, `hz`, and `ContDiff ℝ 2 (quadPrim w)`.

This is a supporting result; no catalogue entry.
-/

open Set MeasureTheory

namespace Lightlike.GreenOperators

/-- Iterated-integral form of `quadPrim w`, for `w` continuous vanishing when a coordinate is `≤ -R`. -/
lemma quadPrim_eq_iterated' {w : ℝ × ℝ → ℝ} (hw : Continuous w) {R : ℝ}
    (hz : ∀ q : ℝ × ℝ, (q.1 ≤ -R ∨ q.2 ≤ -R) → w q = 0) (p : ℝ × ℝ) :
    quadPrim w p = ∫ a in (-R)..p.1, ∫ b in (-R)..p.2, w (a, b) := by
  have hset : Iic p = Iic p.1 ×ˢ Iic p.2 := by
    ext q; simp [Prod.le_def]
  have hint0 : IntegrableOn w (Icc ((-R, -R) : ℝ × ℝ) p) (volume : Measure (ℝ × ℝ)) :=
    hw.continuousOn.integrableOn_compact isCompact_Icc
  have hint1 : IntegrableOn w (Iic p) (volume : Measure (ℝ × ℝ)) := by
    refine hint0.of_forall_sdiff_eq_zero measurableSet_Iic (fun q hq => ?_)
    refine hz q ?_
    by_contra hc
    simp only [not_or, not_le] at hc
    exact hq.2 ⟨⟨hc.1.le, hc.2.le⟩, hq.1⟩
  rw [hset] at hint1
  have hint := hint1
  rw [Measure.volume_eq_prod] at hint
  unfold quadPrim
  rw [hset, Measure.volume_eq_prod, setIntegral_prod _ hint]
  have h1 : ∀ a, ∫ b in Iic p.2, w (a, b) = ∫ b in (-R)..p.2, w (a, b) := fun a =>
    integral_Iic_eq_intervalIntegral (fun b hb => hz (a, b) (Or.inr hb)) p.2
  simp_rw [h1]
  refine integral_Iic_eq_intervalIntegral (fun a ha => ?_) p.1
  have h0 : ∀ b, w (a, b) = 0 := fun b => hz (a, b) (Or.inl ha)
  simp [h0]

/-- `∂ₐ` of the double primitive is the single primitive `∫_{b' ≤ b} w(a, b') db'`. -/
theorem fderiv_quadPrim_fst' {w : ℝ × ℝ → ℝ} (hc : Continuous w) {R : ℝ}
    (hz : ∀ q : ℝ × ℝ, (q.1 ≤ -R ∨ q.2 ≤ -R) → w q = 0) (hu : ContDiff ℝ 2 (quadPrim w))
    (p : ℝ × ℝ) :
    fderiv ℝ (quadPrim w) p ((1 : ℝ), (0 : ℝ)) = ∫ b in (-R)..p.2, w (p.1, b) := by
  have hd : Differentiable ℝ (quadPrim w) := hu.differentiable (by norm_num)
  have h1 : HasDerivAt (fun a => quadPrim w (a, p.2)) (fderiv ℝ (quadPrim w) p ((1 : ℝ), (0 : ℝ)))
      p.1 := by
    have hl : HasFDerivAt (quadPrim w) (fderiv ℝ (quadPrim w) p) (p.1, p.2) := (hd p).hasFDerivAt
    have hf : HasDerivAt (fun a : ℝ => (a, p.2)) ((1 : ℝ), (0 : ℝ)) p.1 :=
      (hasDerivAt_id p.1).prodMk (hasDerivAt_const _ _)
    exact hl.comp_hasDerivAt p.1 hf
  have hV : Continuous (fun a : ℝ => ∫ b in (-R)..p.2, w (a, b)) :=
    (intervalIntegral.continuous_parametric_primitive_of_continuous (a₀ := -R)
      (f := fun a b => w (a, b)) (hc.comp (by fun_prop))).comp
      (by fun_prop : Continuous fun a : ℝ => (a, p.2))
  have h2 : HasDerivAt (fun a => ∫ a' in (-R)..a, ∫ b in (-R)..p.2, w (a', b))
      (∫ b in (-R)..p.2, w (p.1, b)) p.1 :=
    (hV.integral_hasStrictDerivAt (-R) p.1).hasDerivAt
  have h3 : (fun a => quadPrim w (a, p.2))
      = fun a => ∫ a' in (-R)..a, ∫ b in (-R)..p.2, w (a', b) :=
    funext fun a => quadPrim_eq_iterated' hc hz (a, p.2)
  rw [h3] at h1
  exact h1.unique h2

/-- `∂_b ∂ₐ` of the double primitive is `w`: `D²u (0,1) (1,0) = w`. -/
theorem fderiv_fderiv_quadPrim' {w : ℝ × ℝ → ℝ} (hc : Continuous w) {R : ℝ}
    (hz : ∀ q : ℝ × ℝ, (q.1 ≤ -R ∨ q.2 ≤ -R) → w q = 0) (hu : ContDiff ℝ 2 (quadPrim w))
    (p : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ (quadPrim w)) p ((0 : ℝ), (1 : ℝ)) ((1 : ℝ), (0 : ℝ)) = w p := by
  have hG : Differentiable ℝ (fderiv ℝ (quadPrim w)) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hl : HasFDerivAt (fderiv ℝ (quadPrim w)) (fderiv ℝ (fderiv ℝ (quadPrim w)) p) (p.1, p.2) :=
    (hG p).hasFDerivAt
  have hf : HasDerivAt (fun b : ℝ => (p.1, b)) ((0 : ℝ), (1 : ℝ)) p.2 :=
    (hasDerivAt_const _ _).prodMk (hasDerivAt_id p.2)
  have h3 := hl.comp_hasDerivAt p.2 hf
  have h4 := (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : ℝ))
    : ((ℝ × ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt p.2 h3
  have h5 : HasDerivAt (fun b => ∫ b' in (-R)..b, w (p.1, b')) (w p) p.2 := by
    have := (Continuous.integral_hasStrictDerivAt (hc.comp (by fun_prop : Continuous
      fun b : ℝ => (p.1, b))) (-R) p.2).hasDerivAt
    simpa using this
  have h6 : (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : ℝ)) : ((ℝ × ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ)
      ∘ (fderiv ℝ (quadPrim w)) ∘ (fun b : ℝ => (p.1, b))
      = fun b => ∫ b' in (-R)..b, w (p.1, b') := by
    funext b
    simp only [Function.comp, ContinuousLinearMap.apply_apply]
    exact fderiv_quadPrim_fst' hc hz hu (p.1, b)
  rw [h6] at h4
  exact h4.unique h5

end Lightlike.GreenOperators
