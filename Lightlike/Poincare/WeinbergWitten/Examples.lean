import Mathlib
import Lightlike.Poincare.WeinbergWitten.WeinbergWitten
import Lightlike.Poincare.WeinbergWitten.Graviton

/-!
# Weinberg–Witten: helicity `±1` and `±2` examples, massive evasion

Row G3-253 (target T-PG3). Trust checks for `ww_vanishing`:

* helicity `±1` (`k = ±2`) admits a nonzero covariant tensor (`photon_allows`),
* helicity `±2` (`k = ±4`) does not (`ww_graviton`, `ww_helicity`),
* a massive particle evades the argument: the diagonal rest-frame matrix element has `k = 0`
  and a nonzero solution exists (`massive_evades`).

## Limits

The Breit-frame reduction (`k = 2h`) and the limit `p' → p` are only described in docstrings, not formalised;
neither is Weinberg's soft theorem. The "massive evasion" is the algebraic statement that `k = 0`, which is what a
diagonal massive matrix element has, is compatible with a nonzero tensor such as `e_t e_tᵀ` (the energy density at rest).
-/

namespace Lightlike.Poincare.WeinbergWitten

open Matrix

noncomputable section

/-- `R(θ)ᵀ = R(-θ)`. -/
theorem zRot_transpose (θ : ℝ) : (zRot θ)ᵀ = zRot (-θ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [zRot]

/-- `R(θ)` multiplies the weight vector of weight `w` by `e^{-iwθ}`. -/
theorem zRot_wBasis (θ : ℝ) (i : Fin 4) :
    zRot θ *ᵥ wBasis i = Complex.exp (((-(wWeight i : ℂ)) * θ) * Complex.I) • wBasis i := by
  have h := zRot_transpose_wBasis (-θ) i
  rw [zRot_transpose, neg_neg] at h
  rw [h]
  push_cast
  ring_nf

/-- Rank-one tensors `e_i e_jᵀ` on the weight basis are covariant with `k = -(wᵢ + wⱼ)`. -/
theorem zRot_vecMulVec_wBasis (θ : ℝ) (i j : Fin 4) :
    zRot θ * vecMulVec (wBasis i) (wBasis j) * (zRot θ)ᵀ =
      Complex.exp ((((-(wWeight i + wWeight j) : ℤ) : ℂ) * θ) * Complex.I) • vecMulVec (wBasis i) (wBasis j) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose, zRot_wBasis, zRot_wBasis]
  ext a b
  simp only [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]
  rw [show ((((-(wWeight i + wWeight j) : ℤ) : ℂ) * θ) * Complex.I) =
      (((-(wWeight i : ℂ)) * θ) * Complex.I) + (((-(wWeight j : ℂ)) * θ) * Complex.I) by push_cast; ring,
    Complex.exp_add]
  ring

/-- **Helicity `±1` is allowed**: for `k = 2` and `k = -2` there is a nonzero covariant tensor. -/
theorem photon_allows :
    (∃ M : Matrix (Fin 4) (Fin 4) ℂ, M ≠ 0 ∧
      ∀ θ : ℝ, zRot θ * M * (zRot θ)ᵀ = Complex.exp (((2 : ℤ) : ℂ) * θ * Complex.I) • M) ∧
    (∃ M : Matrix (Fin 4) (Fin 4) ℂ, M ≠ 0 ∧
      ∀ θ : ℝ, zRot θ * M * (zRot θ)ᵀ = Complex.exp (((-2 : ℤ) : ℂ) * θ * Complex.I) • M) := by
  refine ⟨⟨vecMulVec (wBasis 2) (wBasis 2), ?_, fun θ => ?_⟩, ⟨vecMulVec (wBasis 1) (wBasis 1), ?_, fun θ => ?_⟩⟩
  · intro h
    have := congrFun (congrFun h 1) 1
    simp [wBasis] at this
  · have := zRot_vecMulVec_wBasis θ 2 2
    simpa [wWeight] using this
  · intro h
    have := congrFun (congrFun h 1) 1
    simp [wBasis] at this
  · have := zRot_vecMulVec_wBasis θ 1 1
    simpa [wWeight] using this

/-- **Helicity `h` with `|h| > 1` is excluded** (Weinberg–Witten): with `k = 2h`, a covariant tensor vanishes. -/
theorem ww_helicity (h : ℤ) (hh : 1 < |h|) (M : Matrix (Fin 4) (Fin 4) ℂ)
    (H : ∀ θ : ℝ, zRot θ * M * (zRot θ)ᵀ = Complex.exp (((2 * h : ℤ) : ℂ) * θ * Complex.I) • M) : M = 0 := by
  refine ww_vanishing M (2 * h) ?_ H
  rw [abs_mul]
  simp only [abs_two]
  omega

/-- **Gravitons are excluded**: for helicity `±2` (`k = ±4`), including the helicity `2 * ε` of `gravitonRep ε`,
the covariant tensor vanishes. -/
theorem ww_graviton (ε : ℤˣ) (M : Matrix (Fin 4) (Fin 4) ℂ)
    (H : ∀ θ : ℝ, zRot θ * M * (zRot θ)ᵀ = Complex.exp (((2 * (2 * (ε : ℤ)) : ℤ) : ℂ) * θ * Complex.I) • M) :
    M = 0 := by
  refine ww_helicity (2 * (ε : ℤ)) ?_ M H
  rcases Int.units_eq_one_or ε with h | h <;> simp [h]

/-- **A massive particle evades the argument**: the diagonal rest-frame matrix element has `k = 0`, and the energy
density `e_t e_tᵀ` is a nonzero solution. -/
theorem massive_evades :
    ∃ M : Matrix (Fin 4) (Fin 4) ℂ, M ≠ 0 ∧
      ∀ θ : ℝ, zRot θ * M * (zRot θ)ᵀ = Complex.exp (((0 : ℤ) : ℂ) * θ * Complex.I) • M := by
  refine ⟨vecMulVec (wBasis 0) (wBasis 0), ?_, fun θ => ?_⟩
  · intro h
    have := congrFun (congrFun h 0) 0
    simp [wBasis] at this
  · have := zRot_vecMulVec_wBasis θ 0 0
    simpa [wWeight] using this

end

end Lightlike.Poincare.WeinbergWitten

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G3_253.massive_evades := _root_.Lightlike.Poincare.WeinbergWitten.massive_evades
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G3_253.photon_allows := _root_.Lightlike.Poincare.WeinbergWitten.photon_allows
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G3_253.ww_graviton := _root_.Lightlike.Poincare.WeinbergWitten.ww_graviton
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G3_253.ww_helicity := _root_.Lightlike.Poincare.WeinbergWitten.ww_helicity
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G3_253.zRot_transpose := _root_.Lightlike.Poincare.WeinbergWitten.zRot_transpose
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G3_253.zRot_vecMulVec_wBasis := _root_.Lightlike.Poincare.WeinbergWitten.zRot_vecMulVec_wBasis
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G3_253.zRot_wBasis := _root_.Lightlike.Poincare.WeinbergWitten.zRot_wBasis
