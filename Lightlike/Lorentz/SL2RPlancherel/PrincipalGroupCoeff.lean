import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.PrincipalPairing
import Lightlike.Lorentz.SL2RPlancherel.HaarTorusIntegral

/-!
# Matrix coefficients of the principal series as functions on `SL(2,ℝ)`

For every `v ∈ L²(ℝ)` the matrix coefficient `g ↦ ⟪v, π_ν(g) e_n⟫` is continuous on `SL(2,ℝ)`
(`continuous_inner_principalSeries_kVecL2`): it is `∫ conj(v(x)) Q(num g x, den g x) dx` with `Q`
continuous where `num² + den² > 0`, dominated near each `g₀` by
`(Σ g₀ij² + 1)^{1/2} |v(x)| (1 + x²)^{-1/2}`, which is integrable by Cauchy–Schwarz.
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

end Lightlike.Lorentz.SL2RPlancherel
