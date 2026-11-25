module

public import Lightlike.Cosmology.EffectiveLQCFriedmann.LQC

/-!
# Numerical value of the critical density of loop quantum cosmology

Trust check of `G2-018`: at the Barbero–Immirzi value `γ = γ_M ≈ 0.2375` fixed by the black-hole
entropy count, `ρ_c = √3/(32π²γ³) ρ_Pl ≈ 0.41 ρ_Pl` (Ashtekar–Pawlowski–Singh 2006, `aps-2006`).

`γ_M` is the root of a transcendental equation and is not defined in the repository, so the result
is stated for any `γ` in the interval `(0.2374, 0.2376)`.

* `critDensity_coeff_bounds` : `0.40 < √3/(32π²γ³) < 0.42` there.
* `critDensity_areaGap_bounds` : the same for `ρ_c = critDensity G γ (areaGap G γ)` in units of
  `ρ_Pl = G⁻²`.
-/

@[expose] public section

noncomputable section

namespace Lightlike

namespace Cosmology

namespace LQC

/-- **`ρ_c ≈ 0.41 ρ_Pl`**: for `0.2374 < γ < 0.2376` (a neighbourhood of `γ_M ≈ 0.2375`),
`√3/(32π²γ³)` lies in `(0.40, 0.42)`. -/
theorem critDensity_coeff_bounds {γ : ℝ} (h1 : 0.2374 < γ) (h2 : γ < 0.2376) :
    0.40 < Real.sqrt 3 / (32 * Real.pi ^ 2 * γ ^ 3) ∧
      Real.sqrt 3 / (32 * Real.pi ^ 2 * γ ^ 3) < 0.42 := by
  have hγ : 0 < γ := by linarith
  have hπ1 : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hπ2 : Real.pi < (3.15 : ℝ) := Real.pi_lt_d2
  have hpp : 0 < Real.pi := Real.pi_pos
  have hπsq1 : (3.14 : ℝ) ^ 2 < Real.pi ^ 2 := pow_lt_pow_left₀ hπ1 (by norm_num) (by norm_num)
  have hπsq2 : Real.pi ^ 2 < (3.15 : ℝ) ^ 2 := pow_lt_pow_left₀ hπ2 hpp.le (by norm_num)
  have hγ1 : (0.2374 : ℝ) ^ 3 < γ ^ 3 := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
  have hγ2 : γ ^ 3 < (0.2376 : ℝ) ^ 3 := pow_lt_pow_left₀ h2 hγ.le (by norm_num)
  have hs1 : (1.73 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs2 : Real.sqrt 3 < (1.74 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hD : 0 < 32 * Real.pi ^ 2 * γ ^ 3 := by positivity
  have hP : 0 < Real.pi ^ 2 := by positivity
  have hG : 0 < γ ^ 3 := by positivity
  constructor
  · rw [lt_div_iff₀ hD]
    have : 32 * Real.pi ^ 2 * γ ^ 3 < 32 * (3.15 : ℝ) ^ 2 * (0.2376 : ℝ) ^ 3 := by
      have := mul_lt_mul'' hπsq2 hγ2 hP.le hG.le
      nlinarith
    nlinarith
  · rw [div_lt_iff₀ hD]
    have : 32 * (3.14 : ℝ) ^ 2 * (0.2374 : ℝ) ^ 3 < 32 * Real.pi ^ 2 * γ ^ 3 := by
      have := mul_lt_mul'' hπsq1 hγ1 (by norm_num) (by norm_num)
      nlinarith
    nlinarith

/-- **`ρ_c ≈ 0.41 ρ_Pl`** in the form of the critical density: for `G > 0` and
`0.2374 < γ < 0.2376`, `0.40 G⁻² < ρ_c < 0.42 G⁻²` for `ρ_c` with the area gap
`Δ = 4√3 π γ ℓ_P²`. -/
theorem critDensity_areaGap_bounds {Gn γ : ℝ} (hG : 0 < Gn) (h1 : 0.2374 < γ) (h2 : γ < 0.2376) :
    0.40 * (Gn ^ 2)⁻¹ < critDensity Gn γ (areaGap Gn γ) ∧
      critDensity Gn γ (areaGap Gn γ) < 0.42 * (Gn ^ 2)⁻¹ := by
  rw [critDensity_areaGap hG.ne' (by linarith)]
  obtain ⟨hl, hu⟩ := critDensity_coeff_bounds h1 h2
  have hi : 0 < (Gn ^ 2)⁻¹ := by positivity
  exact ⟨mul_lt_mul_of_pos_right hl hi, mul_lt_mul_of_pos_right hu hi⟩

end LQC

end Cosmology

end Lightlike
