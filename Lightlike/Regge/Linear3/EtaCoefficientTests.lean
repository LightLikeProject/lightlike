import Lightlike.Regge.Linear3.EtaCoefficient
import Lightlike.Regge.Linear3.SaintVenantCore

/-!
# Trust checks for the `η²` coefficient: a non-zero field and the density without volume weights

For the test field `h(y) = cos (2π y₀) · E₁₂` (`E₁₂` the symmetric matrix with `1` at `(1, 2)` and `(2, 1)`: smooth, symmetric,
`ℤ³`-periodic) the cube integral of the Fierz–Pauli density is `-π²` (`integral_fpDens_hTest`), so the `η²` coefficient of
`eh_eta_sq_coeff` (half of it) is non-zero for it. The hinge density of the linearized Regge coefficient with the weights `1 / |w|²` of the
hinge vectors replaced by `1`, the density without volume weights (`wrongDens`), is `-14/3 π² cos² (2π y₀)` for this field and
integrates to `-7π²/3` (`integral_wrongDens_hTest`), different from `-π²` (`wrong_weights_ne`); with the weights the same field
gives `-π²` (`rightDens_integral_hTest`).

## Main results

* `hTest`, `wrongDens`: the test field and the density without volume weights.
* `integral_fpDens_hTest`, `integral_wrongDens_hTest`, `rightDens_integral_hTest`: the three cube integrals.
* `wrong_weights_ne`: the wrong weights do not reproduce the Fierz–Pauli integral, the second `η`-derivative (twice the `η²` coefficient).

**Limits.** One test field and one wrong model (the weights `1 / |w|²` dropped); the cube integrals are those of the
densities, not of the Regge action of a triangulation. Exact-arithmetic evidence for the pointwise densities:
`scripts/regge/eh_wrong_model_check.py`. It does not address the relation between geodesic and interpolated edge lengths.
-/

open Real Finset MeasureTheory
open scoped ContDiff
namespace Lightlike.Regge.Linear3
open Lightlike.Regge Lightlike.Regge.Conv3

/-- The partial derivative of a function of the first coordinate only. -/
theorem pd1_comp0 (g : ℝ → ℝ) (hg : Differentiable ℝ g) (y : Fin 3 → ℝ) (k : Fin 3) :
    pd1 (fun z => g (z 0)) y k = if k = 0 then deriv g (y 0) else 0 := by
  have h := HasFDerivAt.comp (g := g) (f := fun z : Fin 3 → ℝ => z 0) y ((hg (y 0)).hasDerivAt.hasFDerivAt)
    (hasFDerivAt_apply (0 : Fin 3) y)
  unfold pd1
  have h2 : fderiv ℝ (fun z : Fin 3 → ℝ => g (z 0)) y =
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv g (y 0))).comp
        (ContinuousLinearMap.proj (0 : Fin 3)) := h.fderiv
  rw [h2]
  by_cases hk : k = 0
  · subst hk; simp
  · simp [hk]


/-- The test field `cos (2π y₀) · E₁₂`, with `E₁₂` the symmetric matrix with entries `1` at `(1, 2)` and `(2, 1)`. -/
noncomputable def hTest (y : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then Real.cos (2 * π * y 0) else 0

/-- The mask of the entries `(1, 2)` and `(2, 1)`. -/
def mk12 (i j : Fin 3) : Prop := (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)

instance (i j : Fin 3) : Decidable (mk12 i j) := by unfold mk12; infer_instance

theorem hTest_entry (y : Fin 3 → ℝ) (i j : Fin 3) :
    hTest y i j = if mk12 i j then Real.cos (2 * π * y 0) else 0 := rfl

theorem hTest_smooth (i j : Fin 3) : ContDiff ℝ ∞ (fun y => hTest y i j) := by
  simp only [hTest_entry]
  split_ifs
  · exact Real.contDiff_cos.comp (contDiff_const.mul ((contDiff_pi.1 contDiff_id) (0 : Fin 3)))
  · exact contDiff_const

theorem hTest_symm (y : Fin 3 → ℝ) (i j : Fin 3) : hTest y i j = hTest y j i := by
  simp only [hTest_entry, mk12]
  have : ((i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)) ↔ ((j = 1 ∧ i = 2) ∨ (j = 2 ∧ i = 1)) := by tauto
  simp only [this]

theorem hTest_periodic (p : Fin 3 → ℝ) (e : Fin 3 → ℤ) :
    hTest (p + fun i => (e i : ℝ)) = hTest p := by
  ext i j
  simp only [hTest_entry, Pi.add_apply]
  split_ifs
  · rw [show 2 * π * (p 0 + (e 0 : ℝ)) = 2 * π * p 0 + (e 0 : ℝ) * (2 * π) by ring, Real.cos_add_int_mul_two_pi]
  · rfl


theorem deriv_gcos (t : ℝ) : deriv (fun t : ℝ => Real.cos (2 * π * t)) t = -(2 * π) * Real.sin (2 * π * t) := by
  have := ((Real.hasDerivAt_cos (2 * π * t)).comp t ((hasDerivAt_id t).const_mul (2 * π)))
  simp [mul_comm, mul_assoc, mul_left_comm]

theorem deriv_gsin (t : ℝ) : deriv (fun t : ℝ => -(2 * π) * Real.sin (2 * π * t)) t =
    -(2 * π) ^ 2 * Real.cos (2 * π * t) := by
  have := ((Real.hasDerivAt_sin (2 * π * t)).comp t ((hasDerivAt_id t).const_mul (2 * π))).const_mul (-(2 * π))
  have h2 : HasDerivAt (fun t : ℝ => -(2 * π) * Real.sin (2 * π * t))
      (-(2 * π) * (Real.cos (2 * π * t) * (2 * π * 1))) t := this
  rw [h2.deriv]; ring

theorem dh1_hTest (y : Fin 3 → ℝ) (k i j : Fin 3) :
    dh1 hTest y k i j = if mk12 i j ∧ k = 0 then -(2 * π) * Real.sin (2 * π * y 0) else 0 := by
  unfold dh1
  by_cases h : mk12 i j
  · have e : (fun z => hTest z i j) = fun z => (fun t : ℝ => Real.cos (2 * π * t)) (z 0) := by
      funext z; simp [hTest_entry, h]
    rw [e, pd1_comp0 (fun t : ℝ => Real.cos (2 * π * t)) (by fun_prop) y k, deriv_gcos]
    simp [h]
  · have e : (fun z => hTest z i j) = fun _ => (0 : ℝ) := by funext z; simp [hTest_entry, h]
    rw [e]; simp [pd1, h]

theorem dd2_hTest (y : Fin 3 → ℝ) (k l i j : Fin 3) :
    dd2 hTest y k l i j = if mk12 i j ∧ k = 0 ∧ l = 0 then -(2 * π) ^ 2 * Real.cos (2 * π * y 0) else 0 := by
  have hs : ContDiff ℝ 2 (fun z => hTest z i j) := (hTest_smooth i j).of_le (by simp)
  unfold dd2
  rw [← pd1_pd1 hs y k l]
  by_cases h : mk12 i j
  · have e : (fun z => pd1 (fun w => hTest w i j) z k) = fun z => (fun t : ℝ => if k = 0 then -(2 * π) * Real.sin (2 * π * t) else 0) (z 0) := by
      funext z
      have := dh1_hTest z k i j
      simp only [dh1] at this
      rw [this]; by_cases hk : k = 0 <;> simp [h, hk]
    rw [e]
    by_cases hk : k = 0
    · subst hk
      simp only [ite_true]
      rw [pd1_comp0 (fun t : ℝ => -(2 * π) * Real.sin (2 * π * t)) (by fun_prop) y l]
      simp only [deriv_gsin]
      by_cases hl : l = 0 <;> simp [h, hl]
    · simp [hk, pd1]
  · have e : (fun z => pd1 (fun w => hTest w i j) z k) = fun _ => (0 : ℝ) := by
      funext z
      have := dh1_hTest z k i j
      simp only [dh1] at this
      rw [this]; simp [h]
    rw [e]; simp [pd1, h]


/-- The cube integral of a function of the first coordinate is the interval integral. -/
theorem integral_cube_comp0 (f : ℝ → ℝ) (hf : Continuous f) :
    ∫ y in unitCube, f (y 0) = ∫ x in (0 : ℝ)..1, f x := by
  have hbox : unitCube = Set.pi Set.univ fun _ : Fin 3 => Set.Icc (0 : ℝ) 1 := rfl
  have : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    ⟨by simp [Measure.restrict_apply MeasurableSet.univ]⟩
  have h1 : (volume : Measure (Fin 3 → ℝ)).restrict unitCube =
      Measure.pi fun _ : Fin 3 => volume.restrict (Set.Icc (0 : ℝ) 1) := by
    rw [hbox, volume_pi, Measure.restrict_pi_pi]
  rw [h1, integral_comp_eval (μ := fun _ : Fin 3 => volume.restrict (Set.Icc (0 : ℝ) 1)) (i := 0) (f := f) hf.aestronglyMeasurable]
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]

theorem integral_sin_sq_two_pi : ∫ x in (0 : ℝ)..1, Real.sin (2 * π * x) ^ 2 = 1 / 2 := by
  have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) (fun t : ℝ => Real.sin t ^ 2)
    (c := 2 * π) (by positivity)
  rw [h, integral_sin_sq]
  simp
  field_simp

theorem integral_cos_sq_two_pi : ∫ x in (0 : ℝ)..1, Real.cos (2 * π * x) ^ 2 = 1 / 2 := by
  have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) (fun t : ℝ => Real.cos t ^ 2)
    (c := 2 * π) (by positivity)
  rw [h, integral_cos_sq]
  simp
  field_simp

theorem fpDens_hTest (y : Fin 3 → ℝ) : fpDens (dh1 hTest y) = -(2 * π ^ 2) * Real.sin (2 * π * y 0) ^ 2 := by
  simp only [fpDens, dh1_hTest, mk12, Fin.sum_univ_three]
  simp
  ring

/-- Non-vacuity: for the test field the cube integral of the Fierz–Pauli density is `-π²`. -/
theorem integral_fpDens_hTest : ∫ y in unitCube, fpDens (dh1 hTest y) = -π ^ 2 := by
  simp only [fpDens_hTest]
  rw [integral_const_mul, integral_cube_comp0 (fun t => Real.sin (2 * π * t) ^ 2) (by fun_prop), integral_sin_sq_two_pi]
  ring


/-- The hinge density of the linearized Regge coefficient with the weight `1 / |w|²` of each hinge replaced by `1`: the
density without the volume weights. -/
noncomputable def wrongDens (H : Fin 3 → Fin 3 → ℝ) (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : ℝ :=
  ∑ σ : Fin 6, ∑ h : Fin 6, (-(qf H (hvec σ h)) / 2) * dth h (lenR dd σ h)

/-- The squared hinge lengths are positive. -/
theorem hbase_pos (h : Fin 6) : 0 < hbase h 0 := by
  fin_cases h <;> simp [hbase]

/-- The matrix with `c` at `(1, 2)` and `(2, 1)`. -/
def Htest (c : ℝ) (i j : Fin 3) : ℝ := if mk12 i j then c else 0

/-- The second derivatives with `d` at the entry `∂₀∂₀ h₁₂`. -/
def ddtest (d : ℝ) (k l i j : Fin 3) : ℝ := if mk12 i j ∧ k = 0 ∧ l = 0 then d else 0

theorem Htest_symm (c : ℝ) (i j : Fin 3) : Htest c i j = Htest c j i := by
  unfold Htest mk12
  have : ((i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)) ↔ ((j = 1 ∧ i = 2) ∨ (j = 2 ∧ i = 1)) := by tauto
  simp only [this]

theorem ddtest_symm1 (d : ℝ) (k l i j : Fin 3) : ddtest d k l i j = ddtest d l k i j := by
  unfold ddtest; by_cases h : mk12 i j ∧ k = 0 ∧ l = 0
  · have : mk12 i j ∧ l = 0 ∧ k = 0 := ⟨h.1, h.2.2, h.2.1⟩
    simp [h]
  · have : ¬ (mk12 i j ∧ l = 0 ∧ k = 0) := fun h' => h ⟨h'.1, h'.2.2, h'.2.1⟩
    simp [h, this]

theorem ddtest_symm2 (d : ℝ) (k l i j : Fin 3) : ddtest d k l i j = ddtest d k l j i := by
  unfold ddtest mk12
  have : ((i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)) ↔ ((j = 1 ∧ i = 2) ∨ (j = 2 ∧ i = 1)) := by tauto
  simp only [this]

theorem wrongDens_test (c d : ℝ) : wrongDens (Htest c) (ddtest d) = 7 / 6 * c * d := by
  set H := Htest c with hHdef
  set dd := ddtest d with hdddef
  have hH : ∀ i j, H i j = H j i := Htest_symm c
  have hd1 : ∀ k l i j, dd k l i j = dd l k i j := ddtest_symm1 d
  have hd2 : ∀ k l i j, dd k l i j = dd k l j i := ddtest_symm2 d
  have key : ∀ σ h : Fin 6, (-(qf H (hvec σ h)) / 2) * dth h (lenR dd σ h) =
      hbase h 0 * ((-(qf H (hvec σ h)) / (2 * hbase h 0)) * dth h (lenR dd σ h)) := fun σ h => by
    have := (hbase_pos h).ne'
    field_simp
  unfold wrongDens
  simp only [key, Fin.sum_univ_six]
  rw [sv_inc_0_0 H dd hH hd1 hd2, sv_inc_0_1 H dd hH hd1 hd2, sv_inc_0_2 H dd hH hd1 hd2, sv_inc_0_3 H dd hH hd1 hd2, sv_inc_0_4 H dd hH hd1 hd2, sv_inc_0_5 H dd hH hd1 hd2, sv_inc_1_0 H dd hH hd1 hd2, sv_inc_1_1 H dd hH hd1 hd2, sv_inc_1_2 H dd hH hd1 hd2, sv_inc_1_3 H dd hH hd1 hd2, sv_inc_1_4 H dd hH hd1 hd2, sv_inc_1_5 H dd hH hd1 hd2, sv_inc_2_0 H dd hH hd1 hd2, sv_inc_2_1 H dd hH hd1 hd2, sv_inc_2_2 H dd hH hd1 hd2, sv_inc_2_3 H dd hH hd1 hd2, sv_inc_2_4 H dd hH hd1 hd2, sv_inc_2_5 H dd hH hd1 hd2, sv_inc_3_0 H dd hH hd1 hd2, sv_inc_3_1 H dd hH hd1 hd2, sv_inc_3_2 H dd hH hd1 hd2, sv_inc_3_3 H dd hH hd1 hd2, sv_inc_3_4 H dd hH hd1 hd2, sv_inc_3_5 H dd hH hd1 hd2, sv_inc_4_0 H dd hH hd1 hd2, sv_inc_4_1 H dd hH hd1 hd2, sv_inc_4_2 H dd hH hd1 hd2, sv_inc_4_3 H dd hH hd1 hd2, sv_inc_4_4 H dd hH hd1 hd2, sv_inc_4_5 H dd hH hd1 hd2, sv_inc_5_0 H dd hH hd1 hd2, sv_inc_5_1 H dd hH hd1 hd2, sv_inc_5_2 H dd hH hd1 hd2, sv_inc_5_3 H dd hH hd1 hd2, sv_inc_5_4 H dd hH hd1 hd2, sv_inc_5_5 H dd hH hd1 hd2]
  simp [hbase, hHdef, hdddef, Htest, ddtest, mk12]
  ring

theorem rightDens_test (c d : ℝ) :
    ∑ σ : Fin 6, ∑ h : Fin 6, (-(qf (Htest c) (hvec σ h)) / (2 * hbase h 0)) * dth h (lenR (ddtest d) σ h) =
      1 / 2 * c * d := by
  rw [sv_pointwise (Htest c) (ddtest d) (Htest_symm c) (ddtest_symm1 d) (ddtest_symm2 d)]
  simp [svPair, eps3, Fin.sum_univ_three, Htest, ddtest, mk12]
  ring


theorem Hm_hTest (y : Fin 3 → ℝ) : Hm hTest y = Htest (Real.cos (2 * π * y 0)) := rfl

theorem dd2_hTest' (y : Fin 3 → ℝ) : dd2 hTest y = ddtest (-(2 * π) ^ 2 * Real.cos (2 * π * y 0)) := by
  funext k l i j
  rw [dd2_hTest]
  unfold ddtest
  rfl

/-- **The density without the volume weights has the wrong cube integral.** For the test field the cube integral of
`wrongDens` is `-7 π² / 3`, while the Fierz–Pauli density (the correct limit) integrates to `-π²`. -/
theorem integral_wrongDens_hTest :
    ∫ y in unitCube, wrongDens (Hm hTest y) (dd2 hTest y) = -(7 / 3) * π ^ 2 := by
  have hpt : ∀ y : Fin 3 → ℝ, wrongDens (Hm hTest y) (dd2 hTest y) =
      -(14 / 3 * π ^ 2) * Real.cos (2 * π * y 0) ^ 2 := fun y => by
    rw [Hm_hTest, dd2_hTest', wrongDens_test]; ring
  simp only [hpt]
  rw [integral_const_mul, integral_cube_comp0 (fun t => Real.cos (2 * π * t) ^ 2) (by fun_prop),
    integral_cos_sq_two_pi]
  ring

/-- **The wrong weights do not reproduce the Fierz–Pauli integral.** The cube integral of the density without volume weights
differs from the cube integral of the Fierz–Pauli density (twice the `η²` coefficient of `eh_eta_sq_coeff`) for the test field. -/
theorem wrong_weights_ne :
    ∫ y in unitCube, wrongDens (Hm hTest y) (dd2 hTest y) ≠ ∫ y in unitCube, fpDens (dh1 hTest y) := by
  rw [integral_wrongDens_hTest, integral_fpDens_hTest]
  have : 0 < π ^ 2 := by positivity
  intro h
  nlinarith

/-- Trust check: the same field gives the correct density `1/2 · c · d` with the volume weights, whose cube integral is
`-π²`, the integral of the Fierz–Pauli density. -/
theorem rightDens_integral_hTest :
    ∫ y in unitCube, (∑ σ : Fin 6, ∑ h : Fin 6,
      (-(qf (Hm hTest y) (hvec σ h)) / (2 * hbase h 0)) * dth h (lenR (dd2 hTest y) σ h)) = -π ^ 2 := by
  have hpt : ∀ y : Fin 3 → ℝ, (∑ σ : Fin 6, ∑ h : Fin 6,
      (-(qf (Hm hTest y) (hvec σ h)) / (2 * hbase h 0)) * dth h (lenR (dd2 hTest y) σ h)) =
      -(2 * π ^ 2) * Real.cos (2 * π * y 0) ^ 2 := fun y => by
    rw [Hm_hTest, dd2_hTest', rightDens_test]; ring
  simp only [hpt]
  rw [integral_const_mul, integral_cube_comp0 (fun t => Real.cos (2 * π * t) ^ 2) (by fun_prop),
    integral_cos_sq_two_pi]
  ring

end Lightlike.Regge.Linear3
