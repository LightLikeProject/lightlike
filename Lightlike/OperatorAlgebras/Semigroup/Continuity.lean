import Lightlike.OperatorAlgebras.Semigroup.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Continuity of the orbits of a contraction semigroup

Strong continuity at `0` gives continuity of `t ↦ S t x` on `[0, ∞)`: on the right,
`S (t + h) x = S h (S t x) → S t x`; on the left,
`‖S (t - h) x - S t x‖ = ‖S (t - h) (x - S h x)‖ ≤ ‖x - S h x‖ → 0`. The orbit is extended by `x` to
negative times (`orbit`), which is then continuous on `ℝ` (`continuous_orbit`).
-/

open Filter Topology NNReal MeasureTheory intervalIntegral

noncomputable section

namespace Lightlike.OperatorAlgebras

namespace ContractionSemigroup

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  (S : ContractionSemigroup 𝕜 X)

/-- The orbit `s ↦ S s x` for `s ≥ 0`, extended by `x` for `s < 0`. -/
def orbit (x : X) (s : ℝ) : X := S (Real.toNNReal s) x

lemma norm_apply_le (t : ℝ≥0) (x : X) : ‖S t x‖ ≤ ‖x‖ :=
  ((S t).le_opNorm x).trans (by simpa using mul_le_mul_of_nonneg_right (S.norm_le t) (norm_nonneg x))

lemma orbit_of_nonpos (x : X) {s : ℝ} (hs : s ≤ 0) : S.orbit x s = x := by
  simp [orbit, Real.toNNReal_of_nonpos hs, S.zero]

lemma tendsto_toNNReal_sub (s : ℝ) :
    Tendsto (fun s' : ℝ => Real.toNNReal (s' - s)) (𝓝 s) (𝓝 0) := by
  have h : Continuous fun s' : ℝ => Real.toNNReal (s' - s) := continuous_real_toNNReal.comp (by fun_prop)
  simpa using h.continuousAt.tendsto (x := s)

lemma tendsto_toNNReal_sub' (s : ℝ) :
    Tendsto (fun s' : ℝ => Real.toNNReal (s - s')) (𝓝 s) (𝓝 0) := by
  have h : Continuous fun s' : ℝ => Real.toNNReal (s - s') := continuous_real_toNNReal.comp (by fun_prop)
  simpa using h.continuousAt.tendsto (x := s)

lemma orbit_add (x : X) {s h : ℝ} (hs : 0 ≤ s) (hh : 0 ≤ h) :
    S.orbit x (s + h) = S (Real.toNNReal h) (S.orbit x s) := by
  unfold orbit
  rw [Real.toNNReal_add hs hh, add_comm, S.add]
  rfl

lemma continuousWithinAt_orbit_Ici (x : X) (s : ℝ) : ContinuousWithinAt (S.orbit x) (Set.Ici s) s := by
  rcases lt_or_ge s 0 with hs | hs
  · have : S.orbit x =ᶠ[𝓝 s] fun _ => x := by
      filter_upwards [Iio_mem_nhds hs] with y hy
      exact S.orbit_of_nonpos x (le_of_lt hy)
    exact (continuousAt_const.congr this.symm).continuousWithinAt
  · have hlim : Tendsto (fun s' : ℝ => S (Real.toNNReal (s' - s)) (S.orbit x s)) (𝓝 s)
        (𝓝 (S.orbit x s)) :=
      (S.tendsto_zero (S.orbit x s)).comp (tendsto_toNNReal_sub s)
    refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy' : s ≤ y := hy
    have := S.orbit_add x hs (sub_nonneg.2 hy')
    rw [add_sub_cancel] at this
    exact this.symm

lemma continuousWithinAt_orbit_Iic (x : X) (s : ℝ) : ContinuousWithinAt (S.orbit x) (Set.Iic s) s := by
  rcases le_or_gt s 0 with hs | hs
  · have : ∀ y ∈ Set.Iic s, S.orbit x y = x := fun y hy => S.orbit_of_nonpos x (hy.trans hs)
    have h0 : S.orbit x s = x := S.orbit_of_nonpos x hs
    refine (continuousWithinAt_const (b := x)).congr this h0
  · -- `0 < s`: `‖orbit s - orbit s'‖ ≤ ‖S (s - s') x - x‖`
    have hlim : Tendsto (fun s' : ℝ => S (Real.toNNReal (s - s')) x) (𝓝 s) (𝓝 x) :=
      (S.tendsto_zero x).comp (tendsto_toNNReal_sub' s)
    rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_
      ((tendsto_iff_dist_tendsto_zero.1 (hlim.mono_left nhdsWithin_le_nhds)))
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds hs)] with y hy hy0
    have hy' : y ≤ s := hy
    have hy0' : 0 < y := hy0
    have h1 : S.orbit x s = S (Real.toNNReal y) (S (Real.toNNReal (s - y)) x) := by
      unfold orbit
      have := Real.toNNReal_add hy0'.le (sub_nonneg.2 hy')
      rw [add_sub_cancel] at this
      rw [this, S.add]; rfl
    have h2 : S.orbit x y = S (Real.toNNReal y) x := rfl
    rw [dist_comm, dist_eq_norm, dist_eq_norm, h1, h2, ← map_sub]
    exact S.norm_apply_le _ _

/-- **The orbits are continuous.** -/
theorem continuous_orbit (x : X) : Continuous (S.orbit x) := by
  refine continuous_iff_continuousAt.2 fun s => ?_
  exact continuousAt_iff_continuous_left_right.2 ⟨S.continuousWithinAt_orbit_Iic x s,
    S.continuousWithinAt_orbit_Ici x s⟩

variable [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] [CompleteSpace X]

/-- The integral of the orbit, `F t = ∫₀ᵗ S s x ds`. -/
def intOrbit (x : X) (t : ℝ) : X := ∫ s in (0 : ℝ)..t, S.orbit x s

lemma intervalIntegrable_orbit (x : X) (a b : ℝ) :
    IntervalIntegrable (S.orbit x) MeasureTheory.volume a b :=
  (S.continuous_orbit x).intervalIntegrable a b

/-- `S h (∫₀ᵗ S s x ds) = ∫₀^{t+h} - ∫₀^h` (the shift of the integral). -/
lemma apply_intOrbit (x : X) {t h : ℝ} (ht : 0 ≤ t) (hh : 0 ≤ h) :
    S (Real.toNNReal h) (S.intOrbit x t) = S.intOrbit x (t + h) - S.intOrbit x h := by
  unfold intOrbit
  have hc := ((S (Real.toNNReal h)).restrictScalars ℝ).intervalIntegral_comp_comm (S.intervalIntegrable_orbit x 0 t)
  simp only [ContinuousLinearMap.coe_restrictScalars'] at hc
  rw [← hc]
  have h1 : ∫ s in (0 : ℝ)..t, S (Real.toNNReal h) (S.orbit x s) = ∫ s in (0 : ℝ)..t, S.orbit x (s + h) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    have hs' : s ∈ Set.Icc 0 t := by rwa [Set.uIcc_of_le ht] at hs
    rw [S.orbit_add x hs'.1 hh]
  rw [h1, intervalIntegral.integral_comp_add_right, zero_add]
  exact (intervalIntegral.integral_interval_sub_left (S.intervalIntegrable_orbit x 0 (t + h))
      (S.intervalIntegrable_orbit x 0 h)).symm

lemma tendsto_coe_nnreal_gt : Tendsto (fun h : ℝ≥0 => (h : ℝ)) (𝓝[>] 0) (𝓝[>] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · exact (NNReal.continuous_coe.tendsto 0).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact_mod_cast (show (0 : ℝ≥0) < h from hh)

lemma hasDerivAt_intOrbit (x : X) (t : ℝ) : HasDerivAt (S.intOrbit x) (S.orbit x t) t :=
  ((S.continuous_orbit x).integral_hasStrictDerivAt 0 t).hasDerivAt

/-- The difference quotient of `∫₀ᵗ S s x ds` converges: `∫₀ᵗ S s x ds` is in the domain of the
generator, with `A ∫₀ᵗ S s x ds = S t x - x`. -/
lemma tendsto_quot_intOrbit (x : X) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun h : ℝ≥0 => S.quot h (S.intOrbit x t)) (𝓝[>] 0) (𝓝 (S.orbit x t - x)) := by
  have h1 := (hasDerivAt_iff_tendsto_slope_zero.1 (S.hasDerivAt_intOrbit x t))
  have h2 := (hasDerivAt_iff_tendsto_slope_zero.1 (S.hasDerivAt_intOrbit x 0))
  have h1' : Tendsto (fun h : ℝ => h⁻¹ • (S.intOrbit x (t + h) - S.intOrbit x t)) (𝓝[>] 0)
      (𝓝 (S.orbit x t)) := h1.mono_left (nhdsWithin_mono _ fun y hy => ne_of_gt hy)
  have h2' : Tendsto (fun h : ℝ => h⁻¹ • (S.intOrbit x (0 + h) - S.intOrbit x 0)) (𝓝[>] 0)
      (𝓝 (S.orbit x 0)) := h2.mono_left (nhdsWithin_mono _ fun y hy => ne_of_gt hy)
  have h3 := (h1'.sub h2').comp tendsto_coe_nnreal_gt
  have hx0 : S.orbit x 0 = x := S.orbit_of_nonpos x le_rfl
  rw [hx0] at h3
  refine h3.congr' ?_
  filter_upwards with h
  simp only [Function.comp, quot]
  have hS := S.apply_intOrbit x ht.le (NNReal.coe_nonneg h)
  rw [Real.toNNReal_coe] at hS
  have key : ∀ (r : ℝ) (y : X), ((r : 𝕜) • y) = r • y := fun r y =>
    (RCLike.real_smul_eq_coe_smul (K := 𝕜) r y).symm
  rw [hS]
  simp only [key]
  rw [← smul_sub]
  congr 1
  have h0 : S.intOrbit x 0 = 0 := intervalIntegral.integral_same
  simp only [zero_add, h0, sub_zero]
  abel

lemma intOrbit_mem_generatorDomain (x : X) {t : ℝ} (ht : 0 < t) :
    S.intOrbit x t ∈ S.generatorDomain :=
  ⟨_, S.tendsto_quot_intOrbit x ht⟩

variable [T2Space X]

/-- **The domain of the generator is dense**: `t⁻¹ ∫₀ᵗ S s x ds` is in the domain and tends to `x`. -/
theorem dense_generatorDomain : Dense (S.generatorDomain : Set X) := by
  intro x
  have h2 := (hasDerivAt_iff_tendsto_slope_zero.1 (S.hasDerivAt_intOrbit x 0))
  have h2' : Tendsto (fun h : ℝ => h⁻¹ • (S.intOrbit x (0 + h) - S.intOrbit x 0)) (𝓝[>] 0)
      (𝓝 x) := by
    have := h2.mono_left (nhdsWithin_mono _ fun y hy => ne_of_gt hy)
    rwa [S.orbit_of_nonpos x le_rfl] at this
  have h0 : S.intOrbit x 0 = 0 := intervalIntegral.integral_same
  simp only [zero_add, h0, sub_zero] at h2'
  refine mem_closure_of_tendsto h2' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : 0 < h := hh
  exact S.generatorDomain.smul_mem' _ (S.intOrbit_mem_generatorDomain x hh') |> fun hm => by
    simpa [RCLike.real_smul_eq_coe_smul (K := 𝕜)] using hm

end ContractionSemigroup

end Lightlike.OperatorAlgebras
