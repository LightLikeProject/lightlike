import Lightlike.SpinFoam.VertexAsymptoticsHyp.HessianKernel

/-!
# Converse of the kernel criterion for complex symmetric matrices (SF10 P2, Tier 1)

`det_ne_zero_of_re_psd_ker` shows that a complex symmetric `B` with `Re B ≥ 0` is invertible once
`ker Re B ∩ ker Im B = 0` (over `ℝ`).  Here we prove the converse, which needs no hypothesis on `B`:
an invertible `B` has trivial common real kernel.  Together they give an *equivalence*, so the kernel
statement `hker` of route 1 of T-SF10-P2 is not only sufficient but necessary for `det(-H) ≠ 0`.
-/

open Matrix

namespace Lightlike.Asymptotics.Lorentzian

/-- **Necessity of the kernel criterion.** If `B` is invertible, no nonzero real vector lies in
`ker Re B ∩ ker Im B`. -/
theorem ker_re_im_trivial_of_det_ne_zero {n : ℕ} {B : Matrix (Fin n) (Fin n) ℂ} (hdet : B.det ≠ 0)
    (v : Fin n → ℝ) (hre : (B.map Complex.re) *ᵥ v = 0) (him : (B.map Complex.im) *ᵥ v = 0) :
    v = 0 := by
  have hw : B *ᵥ (fun i => (v i : ℂ)) = 0 := by
    ext i
    apply Complex.ext
    · have := congrFun hre i
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at this
      simp only [Matrix.mulVec, dotProduct, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero, Pi.zero_apply, Complex.zero_re]
      exact this
    · have := congrFun him i
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at this
      simp only [Matrix.mulVec, dotProduct, Complex.im_sum, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, zero_add, Pi.zero_apply, Complex.zero_im]
      exact this
  have h0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hw
  ext i
  have := congrFun h0 i
  simpa using congrArg Complex.re this

/-- **Equivalence for complex symmetric matrices with positive semidefinite real part**:
`B` is invertible iff `ker Re B ∩ ker Im B = 0`. -/
theorem det_ne_zero_iff_ker_of_re_psd {n : ℕ} {B : Matrix (Fin n) (Fin n) ℂ}
    (hB : B.transpose = B) (hpsd : ∀ u : Fin n → ℝ, 0 ≤ u ⬝ᵥ ((B.map Complex.re) *ᵥ u)) :
    B.det ≠ 0 ↔ ∀ v : Fin n → ℝ, (B.map Complex.re) *ᵥ v = 0 → (B.map Complex.im) *ᵥ v = 0 →
      v = 0 :=
  ⟨fun h v h1 h2 => ker_re_im_trivial_of_det_ne_zero h v h1 h2,
    fun h => det_ne_zero_of_re_psd_ker hB hpsd h⟩

end Lightlike.Asymptotics.Lorentzian
