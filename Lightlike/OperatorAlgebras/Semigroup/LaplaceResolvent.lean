import Lightlike.OperatorAlgebras.Semigroup.Continuity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The resolvent of a contraction semigroup as a Laplace transform

For `λ > 0` the Bochner integral `R_λ y = ∫₀^∞ e^{-λ t} S t y dt` exists (`integrable_resolventIntegrand`),
lies in the domain of the generator and satisfies `λ R_λ y - A R_λ y = y`: this proves that `λ - A` is
surjective for the generator `A` of a contraction semigroup.
-/

open Filter Topology NNReal MeasureTheory Set intervalIntegral

noncomputable section

namespace Lightlike.OperatorAlgebras

namespace ContractionSemigroup

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  (S : ContractionSemigroup 𝕜 X) [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] [CompleteSpace X]

/-- The integrand `e^{-λ t} S t y` of the resolvent integral. -/
def resolventIntegrand (l : ℝ) (y : X) (t : ℝ) : X := Real.exp (-l * t) • S.orbit y t

/-- The resolvent `R_λ y = ∫₀^∞ e^{-λ t} S t y dt`. -/
def resolvent (l : ℝ) (y : X) : X := ∫ t in Ioi (0 : ℝ), S.resolventIntegrand l y t

lemma continuous_resolventIntegrand (l : ℝ) (y : X) : Continuous (S.resolventIntegrand l y) := by
  unfold resolventIntegrand
  exact (Real.continuous_exp.comp (by fun_prop)).smul (S.continuous_orbit y)

lemma integrableOn_resolventIntegrand {l : ℝ} (hl : 0 < l) (y : X) :
    IntegrableOn (S.resolventIntegrand l y) (Ioi 0) := by
  have hb : IntegrableOn (fun t : ℝ => ‖y‖ * Real.exp (-l * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul _
  refine hb.mono' (S.continuous_resolventIntegrand l y).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
  unfold resolventIntegrand
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm]
  have : ‖S.orbit y t‖ ≤ ‖y‖ := by
    unfold orbit; exact S.norm_apply_le _ _
  exact mul_le_mul_of_nonneg_left this (Real.exp_pos _).le |>.trans_eq (mul_comm _ _) |> fun h => by
    simpa [mul_comm] using h

/-- Translation of a half-line integral. -/
lemma integral_Ioi_comp_add_right (g : ℝ → X) (h : ℝ) :
    ∫ t in Ioi (0 : ℝ), g (t + h) = ∫ t in Ioi h, g t := by
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi, ← MeasureTheory.integral_indicator measurableSet_Ioi,
    ← integral_add_right_eq_self (fun t => (Ioi h).indicator g t) h]
  congr 1
  ext t
  by_cases ht : 0 < t
  · rw [Set.indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht),
      Set.indicator_of_mem (show t + h ∈ Ioi h from by simpa using ht)]
  · rw [Set.indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht),
      Set.indicator_of_notMem (show t + h ∉ Ioi h from by simpa using ht)]

/-- `S h R_λ y = e^{λ h} ∫_h^∞ e^{-λ t} S t y dt`. -/
lemma apply_resolvent {l : ℝ} (hl : 0 < l) (y : X) {h : ℝ} (hh : 0 ≤ h) :
    S (Real.toNNReal h) (S.resolvent l y) =
      Real.exp (l * h) • ∫ t in Ioi h, S.resolventIntegrand l y t := by
  unfold resolvent
  have hc := ((S (Real.toNNReal h)).restrictScalars ℝ).integral_comp_comm
    (S.integrableOn_resolventIntegrand hl y)
  simp only [ContinuousLinearMap.coe_restrictScalars'] at hc
  rw [← hc]
  have h1 : ∀ t ∈ Ioi (0 : ℝ), S (Real.toNNReal h) (S.resolventIntegrand l y t) =
      Real.exp (l * h) • S.resolventIntegrand l y (t + h) := by
    intro t ht
    have ht' : (0 : ℝ) ≤ t := le_of_lt ht
    unfold resolventIntegrand
    have : S (Real.toNNReal h) (Real.exp (-l * t) • S.orbit y t) =
        Real.exp (-l * t) • S.orbit y (t + h) := by
      have hsm : S (Real.toNNReal h) (Real.exp (-l * t) • S.orbit y t) =
          Real.exp (-l * t) • S (Real.toNNReal h) (S.orbit y t) := by
        simpa using ((S (Real.toNNReal h)).restrictScalars ℝ).map_smul (Real.exp (-l * t)) (S.orbit y t)
      rw [hsm, S.orbit_add y ht' hh]
    rw [this, smul_smul, ← Real.exp_add]
    congr 2
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi h1, MeasureTheory.integral_smul,
    integral_Ioi_comp_add_right (S.resolventIntegrand l y) h]

lemma resolvent_eq_add {l : ℝ} (hl : 0 < l) (y : X) {h : ℝ} (hh : 0 ≤ h) :
    S.resolvent l y = (∫ t in (0 : ℝ)..h, S.resolventIntegrand l y t) +
      ∫ t in Ioi h, S.resolventIntegrand l y t := by
  unfold resolvent
  rw [intervalIntegral.integral_of_le hh, ← Set.Ioc_union_Ioi_eq_Ioi hh]
  refine setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi ?_ ?_
  · exact (S.integrableOn_resolventIntegrand hl y).mono_set (Set.Ioc_subset_Ioi_self)
  · exact (S.integrableOn_resolventIntegrand hl y).mono_set (Set.Ioi_subset_Ioi hh)

/-- The difference quotient of `R_λ y` converges to `λ R_λ y - y`. -/
lemma tendsto_quot_resolvent {l : ℝ} (hl : 0 < l) (y : X) :
    Tendsto (fun h : ℝ≥0 => S.quot h (S.resolvent l y)) (𝓝[>] 0)
      (𝓝 (l • S.resolvent l y - y)) := by
  set f := S.resolventIntegrand l y with hf
  set K : ℝ → X := fun h => ∫ t in (0 : ℝ)..h, f t with hK
  have hfc : Continuous f := S.continuous_resolventIntegrand l y
  have hKd : HasDerivAt K (f 0) 0 := (hfc.integral_hasStrictDerivAt 0 0).hasDerivAt
  have hf0 : f 0 = y := by
    simp [hf, resolventIntegrand, S.orbit_of_nonpos y le_rfl]
  have hK0 : K 0 = 0 := intervalIntegral.integral_same
  have hKlim : Tendsto (fun h : ℝ => h⁻¹ • K h) (𝓝[>] 0) (𝓝 y) := by
    have := hasDerivAt_iff_tendsto_slope_zero.1 hKd
    have h' : Tendsto (fun h : ℝ => h⁻¹ • (K (0 + h) - K 0)) (𝓝[>] 0) (𝓝 (f 0)) :=
      this.mono_left (nhdsWithin_mono _ fun a ha => ne_of_gt ha)
    rw [hf0] at h'
    simpa [hK0] using h'
  have hexp : Tendsto (fun h : ℝ => (Real.exp (l * h) - 1) / h) (𝓝[>] 0) (𝓝 l) := by
    have hd : HasDerivAt (fun h : ℝ => Real.exp (l * h)) l 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul l).exp
    have := hasDerivAt_iff_tendsto_slope_zero.1 hd
    have h' := this.mono_left (nhdsWithin_mono _ fun a ha => ne_of_gt ha)
    refine h'.congr' ?_
    filter_upwards with h
    simp [div_eq_inv_mul]
  have hexp1 : Tendsto (fun h : ℝ => Real.exp (l * h)) (𝓝[>] 0) (𝓝 1) := by
    have : Tendsto (fun h : ℝ => Real.exp (l * h)) (𝓝 0) (𝓝 (Real.exp (l * 0))) :=
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).tendsto 0)
    simpa using this.mono_left nhdsWithin_le_nhds
  have hlim := ((hexp.smul_const (S.resolvent l y)).sub (hexp1.smul hKlim))
  have hlim' := hlim.comp tendsto_coe_nnreal_gt
  rw [one_smul] at hlim'
  refine hlim'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : (0 : ℝ) < (h : ℝ) := by exact_mod_cast (show (0 : ℝ≥0) < h from hh)
  simp only [Function.comp, quot]
  have hS := S.apply_resolvent hl y hh'.le
  rw [Real.toNNReal_coe] at hS
  have hsplit := S.resolvent_eq_add hl y hh'.le
  have key : ∀ (r : ℝ) (v : X), ((r : 𝕜) • v) = r • v := fun r v =>
    (RCLike.real_smul_eq_coe_smul (K := 𝕜) r v).symm
  rw [hS, key]
  set R := S.resolvent l y
  set Kh := K h with hKh
  have hJ : ∫ t in Ioi (h : ℝ), f t = R - Kh := by
    exact eq_sub_of_add_eq' hsplit.symm
  rw [hJ]
  simp only [smul_sub, smul_smul]
  have hne : (h : ℝ) ≠ 0 := hh'.ne'
  have e1 : ((Real.exp (l * h) - 1) / h) • R = (h : ℝ)⁻¹ • (Real.exp (l * h) • R - R) := by
    rw [div_eq_inv_mul, mul_smul, sub_smul, one_smul]
  have e2 : Real.exp (l * h) • (h : ℝ)⁻¹ • Kh = (h : ℝ)⁻¹ • (Real.exp (l * h) • Kh) := by
    rw [smul_comm]
  rw [e1]
  simp only [smul_sub, smul_smul, mul_comm (Real.exp (l * (h : ℝ))) ((h : ℝ)⁻¹)]
  abel

end ContractionSemigroup

end Lightlike.OperatorAlgebras
