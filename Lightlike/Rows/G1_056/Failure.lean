import Lightlike.Rows.G1_056.KMS
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Failure of the KMS boundary identity at other boost parameters (G1-056)

Trust check for the Bisognano-Wichmann model of `KMS.lean`: the flow `e^{-iκtx}` at a parameter
`κ ∉ {0, 2π}` does **not** satisfy the KMS boundary identity for the Gaussian vector
`ξ₀(x) = exp(-x²/2 + πx/2) ∈ H` (`InH_gauss`).  Candidate analytic continuation of
`t ↦ ⟨ξ₀, e^{-iκt·}ξ₀⟩ = ∫ conj ξ₀ ξ₀ e^{-iκtx}` is `z ↦ ∫ conj ξ₀ ξ₀ e^{-iκzx}`, whose value at
`z = -i` is `∫ conj ξ₀ ξ₀ e^{-κx}`; we show it differs from `conj ⟨ξ₀, ξ₀⟩` (`boundary_fails`).
For `κ = 2π` the two sides agree by `strip_kms`.

Scope: this is a check on the explicit continuation (not a uniqueness theorem for strip functions),
and no "rotation flow" is modelled, since the rapidity model has no spatial rotations.

Supporting lemmas; no catalogue entry.
-/

open MeasureTheory Complex Set Filter
open scoped Real ComplexConjugate

noncomputable section

namespace Lightlike.BisognanoWichmann

/-- The Gaussian `exp(-x²/2 + c x)`. -/
def gauss (c x : ℝ) : ℂ := cexp (-(x : ℂ) ^ 2 / 2 + (c : ℂ) * x)

lemma gauss_conj (c x : ℝ) : conj (gauss c x) = gauss c x := by
  rw [gauss, ← Complex.exp_conj]
  simp only [map_add, map_div₀, map_neg, map_pow, Complex.conj_ofReal, map_mul, map_ofNat]

lemma continuous_gauss (c : ℝ) : Continuous (gauss c) := by
  unfold gauss; fun_prop

lemma memLp_gauss (c : ℝ) : MemLp (gauss c) 2 volume := by
  rw [memLp_two_iff_integrable_sq_norm (continuous_gauss c).aestronglyMeasurable]
  have hi := (integrable_cexp_quadratic' (b := (-1 : ℂ)) (by simp) ((2 * c : ℝ) : ℂ) 0).norm
  refine hi.congr (Eventually.of_forall fun x => ?_)
  simp only [gauss, Complex.norm_exp]
  rw [← Real.exp_nat_mul]
  congr 1
  simp
  ring

/-- The Gaussian vector `ξ₀` lies in the standard subspace `H`. -/
lemma InH_gauss : InH (gauss (π / 2)) := by
  refine ⟨memLp_gauss _, ?_, ?_⟩
  · have : (fun x : ℝ => ((Real.exp (-(π * x)) : ℝ) : ℂ) * gauss (π / 2) x) = gauss (-(π / 2)) := by
      funext x
      simp only [gauss]
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1; push_cast; ring
    rw [this]; exact memLp_gauss _
  · refine Eventually.of_forall fun x => ?_
    rw [gauss_conj]
    simp only [gauss]
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; push_cast; ring

/-- Value at `z = -i` of the candidate continuation for the flow with parameter `s`:
`∫ conj ξ₀ ξ₀ e^{-s x}`. -/
lemma boundary_gauss (s : ℝ) :
    ∫ x : ℝ, corr (gauss (π / 2)) (gauss (π / 2)) x * cexp (-((s : ℂ) * x)) =
      ((π : ℂ) / -(-1 : ℂ)) ^ (1 / 2 : ℂ) * cexp (((π - s) ^ 2 / 4 : ℝ) : ℂ) := by
  have h : ∀ x : ℝ, corr (gauss (π / 2)) (gauss (π / 2)) x * cexp (-((s : ℂ) * x)) =
      cexp (-1 * (x : ℂ) ^ 2 + ((π - s : ℝ) : ℂ) * x + 0) := by
    intro x
    rw [corr, gauss_conj]
    simp only [gauss]
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1; push_cast; ring
  simp_rw [h]
  rw [integral_cexp_quadratic (by simp)]
  congr 2
  push_cast; ring

/-- **Failure of the boundary identity** off the boost parameter `2π`: for `κ ∉ {0, 2π}` the
continuation of `t ↦ ⟨ξ₀, e^{-iκt·}ξ₀⟩` evaluated at `t - i`, `t = 0`, is not
`conj ⟨ξ₀, ξ₀⟩`. -/
theorem boundary_fails (κ : ℝ) (h0 : κ ≠ 0) (h2 : κ ≠ 2 * π) :
    InH (gauss (π / 2)) ∧
      ∫ x : ℝ, corr (gauss (π / 2)) (gauss (π / 2)) x * cexp (-((κ : ℂ) * x)) ≠
        conj (∫ x : ℝ, corr (gauss (π / 2)) (gauss (π / 2)) x) := by
  refine ⟨InH_gauss, ?_⟩
  have hc : conj (∫ x : ℝ, corr (gauss (π / 2)) (gauss (π / 2)) x) =
      ∫ x : ℝ, corr (gauss (π / 2)) (gauss (π / 2)) x * cexp (-(((0 : ℝ) : ℂ) * x)) := by
    rw [← integral_conj]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [corr, gauss_conj]
  rw [hc, boundary_gauss, boundary_gauss]
  intro h
  have hA : ((π : ℂ) / -(-1 : ℂ)) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    simp [Real.pi_ne_zero]
  have h' := mul_left_cancel₀ hA h
  rw [← Complex.ofReal_exp, ← Complex.ofReal_exp] at h'
  have h'' := Real.exp_injective (Complex.ofReal_injective h')
  have hk : κ * (κ - 2 * π) = 0 := by linear_combination 4 * h''
  rcases mul_eq_zero.1 hk with h | h
  · exact h0 h
  · exact h2 (by linarith)

end Lightlike.BisognanoWichmann
