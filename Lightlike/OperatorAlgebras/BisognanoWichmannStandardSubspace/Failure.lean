import Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.Model

/-!
# A wrong-rate flow fails the KMS relation (Gaussian witness)

Row G1-054 (Bisognano–Wichmann in the standard-subspace form of Brunetti–Guido–Longo).

In the momentum model of `Model.lean` (`Δ = e^{-2π k}`), the flow `Δ^{i c t} = e^{-2π i c t k}`
with rate `c` has matrix elements `laplace φ (-2π i c z)`. The boundary relation of `kms_model`
at rate `c` would read `laplace φ (-2π i c t - 2π c) = conj (laplace φ (-2π i c t))`.

For the Gaussian vector `ξ(k) = e^{π k/2 - k²}` (an `L²` vector satisfying `BWRel`, hence an
instance of `kms_model`) and `φ = conj ξ · ξ = e^{π k - 2k²}`, we compute
`laplace φ s = √(π/2) · exp((π+s)²/8)` for real `s`, and show that the rate-`c` relation at
`t = 0` fails for every real `c ∉ {0, 1}`.

There is no rotation flow in `1+1` dimensions; the trust check "a rotation flow fails KMS" is
realised here as "the flow `Δ^{i c t}` with `c ∉ {0,1}` fails KMS at the same inverse temperature".

## Main results

* `gaussXi_memLp`, `gaussXi_bwRel` — the Gaussian is an instance of `kms_model`.
* `laplace_gauss_real` — closed form of the Laplace transform on the real axis.
* `gauss_not_kms_rate` — the failure for the wrong rate.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real

namespace Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace

/-- The Gaussian vector `ξ(k) = e^{π k/2 - k²}`. -/
noncomputable def gaussXi (k : ℝ) : ℂ := ((Real.exp (π * k / 2 - k ^ 2) : ℝ) : ℂ)

lemma matrixDensity_gauss (k : ℝ) :
    matrixDensity gaussXi gaussXi k = cexp (-2 * (k : ℂ) ^ 2 + (π : ℂ) * k + 0) := by
  unfold matrixDensity gaussXi
  rw [Complex.conj_ofReal, ← Complex.ofReal_mul, ← Real.exp_add, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- The Gaussian is in `L²`. -/
lemma gaussXi_memLp : MemLp gaussXi 2 := by
  have hc : Continuous gaussXi := by unfold gaussXi; fun_prop
  rw [memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable]
  have h := (integrable_cexp_quadratic (b := (2 : ℂ)) (by simp) (π : ℂ) 0).norm
  refine h.congr (Filter.Eventually.of_forall fun k => ?_)
  have e : ‖gaussXi k‖ ^ 2 = ‖matrixDensity gaussXi gaussXi k‖ := by
    simp [matrixDensity, sq]
  show ‖cexp (-(2 : ℂ) * (k : ℂ) ^ 2 + (π : ℂ) * k + 0)‖ = ‖gaussXi k‖ ^ 2
  rw [e, matrixDensity_gauss]

/-- The Gaussian satisfies the Bisognano–Wichmann relation. -/
lemma gaussXi_bwRel : BWRel gaussXi := by
  refine Filter.Eventually.of_forall fun k => ?_
  unfold gaussXi
  rw [Complex.conj_ofReal, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

lemma laplace_gauss_eq (w : ℂ) :
    laplace (matrixDensity gaussXi gaussXi) w
      = ∫ k : ℝ, cexp ((-2 : ℂ) * (k : ℂ) ^ 2 + ((π : ℂ) + w) * k + 0) := by
  unfold laplace
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only
  rw [matrixDensity_gauss, ← Complex.exp_add]
  congr 1
  ring

/-- Closed form of the Laplace transform of `φ = e^{π k - 2k²}` on the real axis. -/
lemma laplace_gauss_real (s : ℝ) :
    laplace (matrixDensity gaussXi gaussXi) (s : ℂ)
      = ((Real.sqrt (π / 2) * Real.exp ((π + s) ^ 2 / 8) : ℝ) : ℂ) := by
  rw [laplace_gauss_eq, integral_cexp_quadratic (by simp)]
  have hK : ((π : ℂ) / -(-2 : ℂ)) ^ (1 / 2 : ℂ) = ((Real.sqrt (π / 2) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    congr 1
    · push_cast; ring
    · push_cast; ring
  have hE : cexp (0 - ((π : ℂ) + s) ^ 2 / (4 * (-2))) = ((Real.exp ((π + s) ^ 2 / 8) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hK, hE, Complex.ofReal_mul]

/-- **A wrong-rate flow fails KMS.** For the Gaussian instance of `kms_model`, the boundary relation
of the flow `Δ^{i c t}` at rate `c ∉ {0,1}` fails (already at `t = 0`). -/
theorem gauss_not_kms_rate (c : ℝ) (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    ¬ ∀ t : ℝ, laplace (matrixDensity gaussXi gaussXi) (-(2 * π * Complex.I * t) - 2 * π * c)
        = (starRingEnd ℂ) (laplace (matrixDensity gaussXi gaussXi) (-(2 * π * Complex.I * t))) := by
  intro h
  have h0 := h 0
  have e1 : (-(2 * (π : ℂ) * Complex.I * ((0 : ℝ) : ℂ)) - 2 * π * c : ℂ)
      = ((-(2 * π * c) : ℝ) : ℂ) := by push_cast; ring
  have e2 : (-(2 * (π : ℂ) * Complex.I * ((0 : ℝ) : ℂ)) : ℂ) = ((0 : ℝ) : ℂ) := by simp
  rw [e1, e2, laplace_gauss_real, laplace_gauss_real, Complex.conj_ofReal] at h0
  have h1 := Complex.ofReal_injective h0
  have hs : 0 < Real.sqrt (π / 2) := Real.sqrt_pos.mpr (by positivity)
  have h2 := Real.exp_injective (mul_left_cancel₀ hs.ne' h1)
  have hp := Real.pi_pos
  have h3 : π ^ 2 * (c * (c - 1)) = 0 := by nlinarith
  have h4 : c * (c - 1) = 0 := by
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h (by positivity)
    · exact h
  rcases mul_eq_zero.mp h4 with h | h
  · exact hc0 h
  · exact hc1 (by linarith)

end Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.gaussXi := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.gaussXi
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.gaussXi_bwRel := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.gaussXi_bwRel
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.gaussXi_memLp := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.gaussXi_memLp
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.gauss_not_kms_rate := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.gauss_not_kms_rate
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.laplace_gauss_eq := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.laplace_gauss_eq
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.laplace_gauss_real := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.laplace_gauss_real
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.matrixDensity_gauss := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.matrixDensity_gauss
