module

public import Mathlib
public import Lightlike.Lorentz.SL2RPlancherel.Cayley
public import Lightlike.Lorentz.SL2RPlancherel.UpperHalfPlaneIntegral

/-!
# Hyperbolic polar coordinates on the upper half-plane

For measurable `G : ℍ → [0,∞]`, with `c(w) = i(1+w)/(1-w)` the inverse Cayley transform,
`∫_ℍ G dμ_ℍ = ∫_{-π}^{π} ∫_0^∞ G(c(tanh(ξ/2) e^{iφ})) sinh ξ dξ dφ`
(`lintegral_upperHalfPlane_polar`).  The proof moves the integral to the unit disc by the Cayley
transform (`lintegral_upperHalf_eq_disc`), where the weight `1/Im²` becomes `1/(1-|w|²)²`, then
uses Mathlib's plane polar coordinates and the substitution `r = tanh(ξ/2)`
(`lintegral_tanh_half`).  Layer 2a of the Plancherel formula on `SL(2,ℝ)`, milestone HA3.
-/

@[expose] public section

open MeasureTheory Set Real UpperHalfPlane Lightlike.Lorentz.SL2RPlancherel

noncomputable section

namespace Lightlike.Lorentz.SL2R

lemma hasDerivAt_tanh_half (ξ : ℝ) :
    HasDerivAt (fun x : ℝ => Real.tanh (x / 2)) ((1 / 2) * (1 - Real.tanh (ξ / 2) ^ 2)) ξ := by
  have hc : Real.cosh (ξ / 2) ≠ 0 := (Real.cosh_pos _).ne'
  have h1 : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) ξ := by
    simpa using (hasDerivAt_id ξ).div_const 2
  have h2 := (Real.hasDerivAt_sinh (ξ / 2)).comp ξ h1
  have h3 := (Real.hasDerivAt_cosh (ξ / 2)).comp ξ h1
  have e : (fun x : ℝ => Real.tanh (x / 2)) = fun x => Real.sinh (x / 2) / Real.cosh (x / 2) := by
    ext x; exact Real.tanh_eq_sinh_div_cosh _
  rw [e]
  refine HasDerivAt.congr_deriv (h2.div h3 hc) ?_
  simp only [Function.comp, Real.tanh_eq_sinh_div_cosh]
  have := Real.cosh_sq (ξ / 2)
  field_simp

/-- The substitution `r = tanh(ξ/2)`: `4 r/(1-r²)² dr = sinh ξ dξ`. -/
lemma lintegral_tanh_half (K : ℝ → ENNReal) :
    ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (4 * r / (1 - r ^ 2) ^ 2) * K r =
      ∫⁻ ξ in Ioi (0 : ℝ), ENNReal.ofReal (Real.sinh ξ) * K (Real.tanh (ξ / 2)) := by
  have himg : (fun x : ℝ => Real.tanh (x / 2)) '' Ioi 0 = Ioo 0 1 := by
    ext r
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, Real.tanh_lt_one _⟩
      show 0 < Real.tanh (x / 2)
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_pos (Real.sinh_pos_iff.2 (by simpa using hx)) (Real.cosh_pos _)
    · intro hr
      refine ⟨2 * Real.artanh r, ?_, ?_⟩
      · have := Real.artanh_pos hr
        simpa using this
      · simp only [mul_div_cancel_left₀ _ (two_ne_zero' ℝ)]
        exact Real.tanh_artanh ⟨by linarith [hr.1], hr.2⟩
  have key := lintegral_image_eq_lintegral_abs_deriv_mul (f := fun x : ℝ => Real.tanh (x / 2))
    (f' := fun ξ => (1 / 2) * (1 - Real.tanh (ξ / 2) ^ 2)) (s := Ioi 0) measurableSet_Ioi
    (fun x _ => (hasDerivAt_tanh_half x).hasDerivWithinAt)
    (fun x _ y _ h => by
      have := Real.tanh_injective h
      linarith)
    (fun r => ENNReal.ofReal (4 * r / (1 - r ^ 2) ^ 2) * K r)
  rw [himg] at key
  rw [key]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun ξ hξ => ?_)
  have hc := Real.cosh_pos (ξ / 2)
  have ht : Real.tanh (ξ / 2) = Real.sinh (ξ / 2) / Real.cosh (ξ / 2) := Real.tanh_eq_sinh_div_cosh _
  have h1 : 1 - Real.tanh (ξ / 2) ^ 2 = 1 / Real.cosh (ξ / 2) ^ 2 := by
    rw [ht]; field_simp; nlinarith [Real.cosh_sq (ξ / 2)]
  have hpos : 0 ≤ (1 / 2) * (1 - Real.tanh (ξ / 2) ^ 2) := by rw [h1]; positivity
  have hs : Real.sinh ξ = 2 * Real.sinh (ξ / 2) * Real.cosh (ξ / 2) := by
    rw [← Real.sinh_two_mul]; ring_nf
  have key2 : (1 / 2) * (1 - Real.tanh (ξ / 2) ^ 2) * (4 * Real.tanh (ξ / 2) /
      (1 - Real.tanh (ξ / 2) ^ 2) ^ 2) = Real.sinh ξ := by
    rw [hs, h1, ht]; field_simp; ring
  rw [abs_of_nonneg hpos, ← mul_assoc, ← ENNReal.ofReal_mul hpos, key2]

lemma disc_weight (G : UpperHalfPlane → ENNReal) {w : ℂ} (hw : w ∈ Metric.ball (0 : ℂ) 1) :
    ENNReal.ofReal (4 / ‖1 - w‖ ^ 4) *
        (G (UpperHalfPlane.ofComplex (cayleyInv w)) *
          ENNReal.ofReal (1 / (cayleyInv w).im ^ 2)) =
      ENNReal.ofReal (4 / (1 - ‖w‖ ^ 2) ^ 2) * G (UpperHalfPlane.ofComplex (cayleyInv w)) := by
  have h1 := one_sub_ne_zero hw
  have hn : 0 < ‖1 - w‖ := norm_pos_iff.2 h1
  have hw1 : ‖w‖ < 1 := by simpa using hw
  have hpos : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  rw [mul_comm (G _), ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [im_cayleyInv hw, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  field_simp

lemma ofComplex_eq_of_not_pos (w v : ℂ) (hw : ¬ 0 < w.im) (hv : ¬ 0 < v.im) :
    (UpperHalfPlane.ofComplex w : ℍ) = UpperHalfPlane.ofComplex v := by
  have e : ∀ u : ℂ, (UpperHalfPlane.ofComplex u : ℍ) = Function.invFunOn UpperHalfPlane.coe Set.univ u := by
    intro u
    unfold UpperHalfPlane.ofComplex
    simp [Topology.IsOpenEmbedding.toOpenPartialHomeomorph]
  rw [e, e, Function.invFunOn_neg, Function.invFunOn_neg]
  · rintro ⟨z, -, rfl⟩; exact hv z.im_pos
  · rintro ⟨z, -, rfl⟩; exact hw z.im_pos

lemma measurable_ofComplex : Measurable (fun w : ℂ => (UpperHalfPlane.ofComplex w : ℍ)) := by
  have hs : MeasurableSet {w : ℂ | 0 < w.im} := measurableSet_lt measurable_const Complex.measurable_im
  have hso : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hc : ContinuousOn (fun w : ℂ => (UpperHalfPlane.ofComplex w : ℍ)) {w : ℂ | 0 < w.im} := by
    intro w hw
    exact (UpperHalfPlane.ofComplex.continuousAt (by simpa [UpperHalfPlane.ofComplex, Topology.IsOpenEmbedding.toOpenPartialHomeomorph] using hw)).continuousWithinAt
  refine measurable_of_isOpen (fun U hU => ?_)
  have h1 : IsOpen ({w : ℂ | 0 < w.im} ∩ (fun w : ℂ => (UpperHalfPlane.ofComplex w : ℍ)) ⁻¹' U) :=
    hc.isOpen_inter_preimage hso hU
  have h2 : MeasurableSet ({w : ℂ | 0 < w.im}ᶜ ∩ (fun w : ℂ => (UpperHalfPlane.ofComplex w : ℍ)) ⁻¹' U) := by
    by_cases h : ∃ w0 : ℂ, ¬ 0 < w0.im ∧ (UpperHalfPlane.ofComplex w0 : ℍ) ∈ U
    · obtain ⟨w0, hw0, hU0⟩ := h
      have : {w : ℂ | 0 < w.im}ᶜ ∩ (fun w : ℂ => (UpperHalfPlane.ofComplex w : ℍ)) ⁻¹' U = {w : ℂ | 0 < w.im}ᶜ := by
        ext w
        simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_preimage, and_iff_left_iff_imp]
        intro hw; rw [ofComplex_eq_of_not_pos w w0 hw hw0]; exact hU0
      rw [this]; exact hs.compl
    · have : {w : ℂ | 0 < w.im}ᶜ ∩ (fun w : ℂ => (UpperHalfPlane.ofComplex w : ℍ)) ⁻¹' U = ∅ := by
        ext w
        simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_empty_iff_false, iff_false, not_and]
        intro hw hwU; exact h ⟨w, hw, hwU⟩
      rw [this]; exact MeasurableSet.empty
  have : (fun w : ℂ => (UpperHalfPlane.ofComplex w : ℍ)) ⁻¹' U =
      ({w : ℂ | 0 < w.im} ∩ (fun w : ℂ => (UpperHalfPlane.ofComplex w : ℍ)) ⁻¹' U) ∪
      ({w : ℂ | 0 < w.im}ᶜ ∩ (fun w : ℂ => (UpperHalfPlane.ofComplex w : ℍ)) ⁻¹' U) := by
    rw [← Set.union_inter_distrib_right, Set.union_compl_self, Set.univ_inter]
  rw [this]
  exact h1.measurableSet.union h2

lemma measurable_cayleyInv : Measurable cayleyInv := by
  unfold cayleyInv; fun_prop

/-- **Hyperbolic polar coordinates on `ℍ`**: for measurable `G : ℍ → [0,∞]`,
`∫_ℍ G dμ_ℍ = ∫_{-π}^{π} ∫_0^∞ G(c(tanh(ξ/2) e^{iφ})) sinh ξ dξ dφ`, `c` the inverse Cayley
transform. -/
theorem lintegral_upperHalfPlane_polar {G : UpperHalfPlane → ENNReal} (hG : Measurable G) :
    ∫⁻ z, G z = ∫⁻ φ in Ioo (-π) π, ∫⁻ ξ in Ioi (0 : ℝ),
      ENNReal.ofReal (Real.sinh ξ) * G (UpperHalfPlane.ofComplex (cayleyInv
        ((Real.tanh (ξ / 2) : ℝ) * (Real.cos φ + Real.sin φ * Complex.I)))) := by
  set f : ℂ → ENNReal := (Metric.ball (0 : ℂ) 1).indicator (fun w =>
    ENNReal.ofReal (4 / (1 - ‖w‖ ^ 2) ^ 2) * G (UpperHalfPlane.ofComplex (cayleyInv w))) with hf
  have hfm : Measurable f := by
    refine Measurable.indicator ?_ Metric.isOpen_ball.measurableSet
    have h2 : Measurable fun w : ℂ => G (UpperHalfPlane.ofComplex (cayleyInv w)) :=
      hG.comp (measurable_ofComplex.comp measurable_cayleyInv)
    have h3 : Measurable fun w : ℂ => ENNReal.ofReal (4 / (1 - ‖w‖ ^ 2) ^ 2) := by fun_prop
    exact h3.mul h2
  have h1 : ∫⁻ z, G z = ∫⁻ w, f w := by
    rw [lintegral_upperHalfPlane hG]
    have := lintegral_upperHalf_eq_disc (fun w => G (UpperHalfPlane.ofComplex w) *
      ENNReal.ofReal (1 / w.im ^ 2))
    have e : {w : ℂ | 0 < w.im} = {w : ℂ | 0 < w.im} := rfl
    rw [this, hf, lintegral_indicator Metric.isOpen_ball.measurableSet]
    exact setLIntegral_congr_fun Metric.isOpen_ball.measurableSet (fun w hw => disc_weight G hw)
  rw [h1, ← Complex.lintegral_comp_polarCoord_symm, polarCoord_target,
    Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [lintegral_prod_symm]
  · refine setLIntegral_congr_fun measurableSet_Ioo (fun φ hφ => ?_)
    rw [← lintegral_tanh_half (fun r => G (UpperHalfPlane.ofComplex (cayleyInv
      ((r : ℝ) * (Real.cos φ + Real.sin φ * Complex.I)))))]
    set K : ℝ → ENNReal := fun r => G (UpperHalfPlane.ofComplex (cayleyInv
      ((r : ℝ) * (Real.cos φ + Real.sin φ * Complex.I)))) with hK
    have hind : ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (4 * r / (1 - r ^ 2) ^ 2) * K r =
        ∫⁻ r in Ioi (0 : ℝ), (Ioo (0 : ℝ) 1).indicator
          (fun r => ENNReal.ofReal (4 * r / (1 - r ^ 2) ^ 2) * K r) r := by
      rw [lintegral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
        inter_eq_left.2 Ioo_subset_Ioi_self]
    rw [hind]
    refine setLIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
    have hr0 : 0 < r := hr
    have hsymm : Complex.polarCoord.symm (r, φ) = (r : ℝ) * (Real.cos φ + Real.sin φ * Complex.I) := by
      rw [Complex.polarCoord_symm_apply]
    have hnorm : ‖(r : ℂ) * (Real.cos φ + Real.sin φ * Complex.I)‖ = r := by
      rw [← hsymm, Complex.norm_polarCoord_symm]; exact abs_of_pos hr0
    simp only [smul_eq_mul, hsymm, hf, indicator, Metric.mem_ball, dist_zero_right, hnorm,
      mem_Ioo, hr0, true_and]
    by_cases h1 : r < 1
    · simp only [h1, ite_true]
      rw [← mul_assoc, ← ENNReal.ofReal_mul hr0.le]
      congr 2
      have : (1 - r ^ 2) ≠ 0 := by nlinarith
      field_simp
    · simp [h1]
  · have hs : Measurable fun p : ℝ × ℝ => (Complex.polarCoord.symm p : ℂ) := by
      have : (fun p : ℝ × ℝ => (Complex.polarCoord.symm p : ℂ)) =
          fun p => (p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * Complex.I) := by
        funext p; exact Complex.polarCoord_symm_apply p
      rw [this]; fun_prop
    exact ((ENNReal.measurable_ofReal.comp measurable_fst).smul (hfm.comp hs)).aemeasurable

end Lightlike.Lorentz.SL2R
