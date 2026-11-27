import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.PrincipalPairing
import Lightlike.Lorentz.SL2RPlancherel.HaarTorusIntegral
import Lightlike.Lorentz.SL2RPlancherel.KKParseval

/-!
# Matrix coefficients of the principal series as functions on `SL(2,ℝ)`

For every `v ∈ L²(ℝ)` the matrix coefficient `g ↦ ⟪v, π_ν(g) e_n⟫` is continuous on `SL(2,ℝ)`
(`continuous_inner_principalSeries_kVecL2`): it is `∫ conj(v(x)) Q(num g x, den g x) dx` with `Q`
continuous where `num² + den² > 0`, dominated near each `g₀` by
`(Σ g₀ij² + 1)^{1/2} |v(x)| (1 + x²)^{-1/2}`, which is integrable by Cauchy–Schwarz.
For `f` integrable on `SL(2,ℝ)` the coefficient `∫ f(g) ⟪e_m, π_ν(g) e_n⟫ dg` (`piCoeff`) is, in polar
coordinates, `∫_{ξ>0} sinh ξ Φ^ν_{m,n}(ξ) ∫∫ e^{-2i(mα + nθ)} f(k_α a_ξ k_θ) dθ dα dξ`
(`piCoeff_eq_polar`), and for continuous compactly supported `f` the angle integral is the
`K × K` component, `piCoeff ν f m n = (2π)² ∫_{ξ>0} sinh ξ Φ^ν_{m,n}(ξ) kkCoeff f (2m, 2n) ξ dξ`
(`piCoeff_eq_kkCoeff`).
Layer 2c-v of the Plancherel formula on `SL(2,ℝ)` (matrix coefficients of `π_ν(f)`), milestone HA3.
-/

open MeasureTheory Set Complex Filter Topology Lightlike.Lorentz.SL2R
open scoped Real

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

lemma continuous_entry (i j : Fin 2) : Continuous fun g : SL2R => g i j :=
  (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)

lemma continuousAt_qForm_comp (ν : ℝ) (n : ℤ) (x : ℝ) (g₀ : SL2R) :
    ContinuousAt (fun g : SL2R => qForm ν n (num g x) (den g x)) g₀ := by
  have hN : Continuous fun g : SL2R => num g x :=
    ((continuous_entry 0 0).mul continuous_const).add (continuous_entry 1 0)
  have hD : Continuous fun g : SL2R => den g x :=
    ((continuous_entry 0 1).mul continuous_const).add (continuous_entry 1 1)
  have hpos := num_sq_add_den_sq_pos g₀ x
  have hA : ContinuousAt (fun g : SL2R => (((num g x) ^ 2 + (den g x) ^ 2 : ℝ) : ℂ) ^ (wP ν)) g₀ :=
    ((Complex.continuous_ofReal.comp ((hN.pow 2).add (hD.pow 2))).continuousAt).cpow
      continuousAt_const (Complex.ofReal_mem_slitPlane.2 hpos)
  have hden : ((num g₀ x : ℝ) : ℂ) + I * (den g₀ x : ℂ) ≠ 0 := by
    intro h0
    have hr := congrArg Complex.re h0
    have hi := congrArg Complex.im h0
    simp at hr hi
    simp [hr, hi] at hpos
  have hnum : ((num g₀ x : ℝ) : ℂ) - I * (den g₀ x : ℂ) ≠ 0 := by
    intro h0
    have hr := congrArg Complex.re h0
    have hi := congrArg Complex.im h0
    simp at hr hi
    simp [hr, hi] at hpos
  have hB : ContinuousAt (fun g : SL2R => ((((num g x : ℝ) : ℂ) - I * (den g x : ℂ)) /
      (((num g x : ℝ) : ℂ) + I * (den g x : ℂ))) ^ n) g₀ := by
    refine ContinuousAt.zpow₀ ?_ n (Or.inl (div_ne_zero hnum hden))
    exact ((Complex.continuous_ofReal.comp hN).sub
      (continuous_const.mul (Complex.continuous_ofReal.comp hD))).continuousAt.div
      ((Complex.continuous_ofReal.comp hN).add
        (continuous_const.mul (Complex.continuous_ofReal.comp hD))).continuousAt hden
  exact hA.mul hB

/-- **Continuity of the matrix coefficients**: `g ↦ ⟪v, π_ν(g) e_n⟫` is continuous. -/
theorem continuous_inner_principalSeries_kVecL2 (ν : ℝ) (n : ℤ) (v : L2R) :
    Continuous fun g : SL2R => inner ℂ v (principalSeries 0 ν g (kVecL2 ν n)) := by
  have e : (fun g : SL2R => inner ℂ v (principalSeries 0 ν g (kVecL2 ν n))) =
      fun g => ∫ x, (starRingEnd ℂ) (v x) * qForm ν n (num g x) (den g x) :=
    funext fun g => inner_principalSeries_kVecL2 ν n v g
  rw [e, continuous_iff_continuousAt]
  intro g₀
  set S : SL2R → ℝ := fun g => g 0 0 ^ 2 + g 0 1 ^ 2 + g 1 0 ^ 2 + g 1 1 ^ 2 with hSdef
  have hS : Continuous S :=
    ((((continuous_entry 0 0).pow 2).add ((continuous_entry 0 1).pow 2)).add
      ((continuous_entry 1 0).pow 2)).add ((continuous_entry 1 1).pow 2)
  have hev : ∀ᶠ g in 𝓝 g₀, S g < S g₀ + 1 :=
    hS.continuousAt.eventually_lt continuousAt_const (by linarith)
  set r : L2R := memLp_rpow_neg_half.toLp _ with hr
  have hrae : (r : ℝ → ℂ) =ᵐ[volume] fun x => (((1 + x ^ 2) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) :=
    MemLp.coeFn_toLp _
  refine continuousAt_of_dominated
    (bound := fun x => (S g₀ + 1) ^ ((1 : ℝ) / 2) * ‖(starRingEnd ℂ) (v x) * r x‖) ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun g => ?_
    exact ((Complex.continuous_conj.comp_aestronglyMeasurable (Lp.aestronglyMeasurable v)).mul
      ((Lp.aestronglyMeasurable (principalSeries 0 ν g (kVecL2 ν n))).congr
        (coeFn_principalSeries_kVecL2 ν n g)))
  · filter_upwards [hev] with g hg
    filter_upwards [hrae] with x hx
    have hq := norm_qForm_le ν n g x
    have hS0 : 0 ≤ S g := by simp only [hSdef]; positivity
    have hmono : S g ^ ((1 : ℝ) / 2) ≤ (S g₀ + 1) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow hS0 hg.le (by norm_num)
    have hrx : ‖r x‖ = (1 + x ^ 2) ^ (-(1 : ℝ) / 2) := by
      rw [hx, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [norm_mul, norm_mul, Complex.norm_conj, hrx]
    calc ‖v x‖ * ‖qForm ν n (num g x) (den g x)‖
        ≤ ‖v x‖ * ((S g₀ + 1) ^ ((1 : ℝ) / 2) * (1 + x ^ 2) ^ (-(1 : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left (hq.trans (mul_le_mul_of_nonneg_right hmono (by positivity)))
            (norm_nonneg _)
      _ = (S g₀ + 1) ^ ((1 : ℝ) / 2) * (‖v x‖ * (1 + x ^ 2) ^ (-(1 : ℝ) / 2)) := by ring
  · exact (integrable_conj_mul v r).norm.const_mul _
  · exact Eventually.of_forall fun x => continuousAt_const.mul (continuousAt_qForm_comp ν n x g₀)

lemma norm_inner_principalSeries_le (ν : ℝ) (m n : ℤ) (g : SL2R) :
    ‖inner ℂ (kVecL2 ν m) (principalSeries 0 ν g (kVecL2 ν n))‖ ≤ ‖kVecL2 ν m‖ * ‖kVecL2 ν n‖ :=
  calc _ ≤ ‖kVecL2 ν m‖ * ‖principalSeries 0 ν g (kVecL2 ν n)‖ := norm_inner_le_norm _ _
    _ = _ := by rw [principalSeries_apply, (piIso 0 ν g).norm_map]

/-- The `(m, n)` matrix coefficient of `π_ν(f) = ∫ f(g) π_ν(g) dg`:
`∫ f(g) ⟪e_m, π_ν(g) e_n⟫ dg`. -/
def piCoeff (ν : ℝ) (f : SL2R → ℂ) (m n : ℤ) : ℂ :=
  ∫ g, f g * inner ℂ (kVecL2 ν m) (principalSeries 0 ν g (kVecL2 ν n)) ∂haarR

lemma integrable_mul_inner_principalSeries (ν : ℝ) {f : SL2R → ℂ} (hf : Integrable f haarR)
    (m n : ℤ) :
    Integrable (fun g => f g * inner ℂ (kVecL2 ν m) (principalSeries 0 ν g (kVecL2 ν n))) haarR :=
  hf.mul_bdd (continuous_inner_principalSeries_kVecL2 ν n _).aestronglyMeasurable
    (Eventually.of_forall (norm_inner_principalSeries_le ν m n))

/-- **The matrix coefficients of `π_ν(f)` in polar coordinates**:
`∫ f(g) ⟪e_m, π_ν(g) e_n⟫ dg
= ∫_{ξ>0} sinh ξ Φ^ν_{m,n}(ξ) ∫_0^{2π} ∫_0^{2π} e^{-2i(mα + nθ)} f(k_α a_ξ k_θ) dθ dα dξ`. -/
theorem piCoeff_eq_polar (ν : ℝ) {f : SL2R → ℂ} (hf : Integrable f haarR) (m n : ℤ) :
    piCoeff ν f m n = ∫ ξ in Ioi (0 : ℝ), (Real.sinh ξ : ℂ) * (mcoefP ν m n ξ *
      ∫ α in Ioc 0 (2 * π), ∫ θ in Ioc 0 (2 * π),
        Complex.exp (-(2 * (m * α + n * θ) * I)) * f (rot α * aR ξ * rot θ)) := by
  rw [piCoeff, integral_haarR_torus (integrable_mul_inner_principalSeries ν hf m n)]
  refine setIntegral_congr_fun measurableSet_Ioi fun ξ _ => ?_
  congr 1
  simp only [inner_kVecL2_kak]
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun α => ?_)
  simp only
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
  simp only
  ring

/-- Iterated form of the Bochner integral over the box `(0,1]²`, for continuous `h`. -/
lemma integral_box_eq {h : (Fin 2 → ℝ) → ℂ} (hh : Continuous h) :
    ∫ x in box, h x = ∫ a in Ioc (0 : ℝ) 1, ∫ b in Ioc (0 : ℝ) 1, h ![a, b] := by
  have hmp := volume_preserving_finTwoArrow ℝ
  have hbox : box = (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ) ⁻¹'
      (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) := by
    ext x
    simp [box, Fin.forall_fin_two, MeasurableEquiv.finTwoArrow]
  have key := hmp.setIntegral_preimage_emb (MeasurableEquiv.finTwoArrow.measurableEmbedding)
    (fun p => h (MeasurableEquiv.finTwoArrow.symm p)) (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1)
  simp only [MeasurableEquiv.symm_apply_apply] at key
  have hv : Continuous fun p : ℝ × ℝ => (![p.1, p.2] : Fin 2 → ℝ) :=
    continuous_pi fun i => by fin_cases i <;> simp <;> fun_prop
  have hc : Continuous fun p : ℝ × ℝ => h (MeasurableEquiv.finTwoArrow.symm p) := hh.comp hv
  have hint : IntegrableOn (fun p : ℝ × ℝ => h (MeasurableEquiv.finTwoArrow.symm p))
      (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  rw [IntegrableOn, ← Measure.prod_restrict] at hint
  rw [hbox, key, Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod _ hint]
  rfl

/-- Scaling the angle: `∫_0^{2π} φ = 2π ∫_0^1 φ(2π x) dx`. -/
lemma integral_Ioc_two_pi_eq (φ : ℝ → ℂ) :
    ∫ α in Ioc 0 (2 * π), φ α = (2 * π : ℝ) * ∫ x in Ioc (0 : ℝ) 1, φ (2 * π * x) := by
  have h2 : (2 * π : ℝ) ≠ 0 := by positivity
  rw [← intervalIntegral.integral_of_le (by positivity), ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_comp_mul_left φ h2, mul_zero, mul_one, Complex.real_smul,
    ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ h2, Complex.ofReal_one, one_mul]

/-- **The angle integral is a `K × K` component**: for continuous `f`,
`∫_0^{2π} ∫_0^{2π} e^{-2i(mα + nθ)} f(k_α a_ξ k_θ) dθ dα = (2π)² kkCoeff f (2m, 2n) ξ`. -/
theorem integral_angles_eq_kkCoeff {f : SL2R → ℂ} (hf : Continuous f) (ξ : ℝ) (m n : ℤ) :
    ∫ α in Ioc 0 (2 * π), ∫ θ in Ioc 0 (2 * π),
        Complex.exp (-(2 * (m * α + n * θ) * I)) * f (rot α * aR ξ * rot θ) =
      ((2 * π : ℝ) : ℂ) ^ 2 * kkCoeff f ![2 * m, 2 * n] ξ := by
  simp only [integral_Ioc_two_pi_eq (fun θ => Complex.exp (-(2 * (m * _ + n * θ) * I)) *
    f (rot _ * aR ξ * rot θ))]
  rw [integral_Ioc_two_pi_eq, integral_const_mul, kkCoeff,
    integral_box_eq (by
      have := continuous_kkProfile hf ξ
      fun_prop)]
  rw [sq, mul_assoc]
  congr 2
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  refine integral_congr_ae (Eventually.of_forall fun b => ?_)
  simp only [kkProfile, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  congr 1
  congr 1
  push_cast
  ring

/-- **The matrix coefficients of `π_ν(f)` through the `K × K` components**: for continuous compactly
supported `f`,
`∫ f(g) ⟪e_m, π_ν(g) e_n⟫ dg = (2π)² ∫_{ξ>0} sinh ξ Φ^ν_{m,n}(ξ) kkCoeff f (2m, 2n) ξ dξ`. -/
theorem piCoeff_eq_kkCoeff (ν : ℝ) {f : SL2R → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    (m n : ℤ) :
    piCoeff ν f m n = ((2 * π : ℝ) : ℂ) ^ 2 * ∫ ξ in Ioi (0 : ℝ), (Real.sinh ξ : ℂ) *
      (mcoefP ν m n ξ * kkCoeff f ![2 * m, 2 * n] ξ) := by
  rw [piCoeff_eq_polar ν (hf.integrable_of_hasCompactSupport hc), ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun ξ _ => ?_
  rw [integral_angles_eq_kkCoeff hf ξ m n]
  ring

end Lightlike.Lorentz.SL2RPlancherel
