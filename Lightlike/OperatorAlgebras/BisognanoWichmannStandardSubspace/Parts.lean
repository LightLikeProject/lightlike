import Mathlib.Analysis.InnerProductSpace.StandardSubspace

/-!
# Complex-linear and antilinear parts of a real-linear operator (row G1-054)

A real-linear map `T` of a complex vector space splits uniquely as `T = linPart T + antiPart T`
with `linPart T` complex linear and `antiPart T` antilinear:
`linPart T x = (T x - i T (i x)) / 2` and `antiPart T x = (T x + i T (i x)) / 2`.
This is the first step of the bounded route to the modular objects `Δ`, `J` of a standard
subspace `K`: for the real reflection `R = 2 P_K - 1` in `K`, `linPart R` and `antiPart R` are
the bounded operators `C` and `D` with `C² + D² = 1` and `C D + D C = 0`
(`Δ = (1 - C)(1 + C)⁻¹`, `D = J (1 - C²)^{1/2}`).
-/

namespace Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace

open Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A complex scalar acts on `x` through its real and imaginary parts. -/
lemma smul_eq_re_im (c : ℂ) (x : H) :
    c • x = c.re • x + c.im • (I • x) := by
  calc c • x = ((c.re : ℂ) + (c.im : ℂ) * I) • x := by rw [Complex.re_add_im]
    _ = c.re • x + c.im • (I • x) := by
      rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]

/-- The complex-linear part `x ↦ (T x - i T (i x)) / 2` of a real-linear operator. -/
noncomputable def linPart (T : H →L[ℝ] H) : H →L[ℂ] H where
  toFun x := (1 / 2 : ℂ) • (T x - I • T (I • x))
  map_add' x y := by
    simp only [smul_add, map_add]
    module
  map_smul' c x := by
    have h1 : I • (c • x) = (c.re : ℝ) • (I • x) - (c.im : ℝ) • x := by
      rw [smul_comm, smul_eq_re_im c (I • x), smul_smul, I_mul_I]
      simp [sub_eq_add_neg]
    have h2 : T (c • x) = (c.re : ℝ) • T x + (c.im : ℝ) • T (I • x) := by
      rw [smul_eq_re_im c x]
      simp
    have h3 : T (I • (c • x)) = (c.re : ℝ) • T (I • x) - (c.im : ℝ) • T x := by
      rw [h1]
      simp
    simp only [RingHom.id_apply]
    rw [h2, h3]
    simp only [← Complex.coe_smul, smul_sub, smul_add, smul_smul]
    have hc : c = (c.re : ℂ) + (c.im : ℂ) * I := (Complex.re_add_im c).symm
    conv_rhs => rw [hc]
    match_scalars <;> (ring_nf; try (simp only [Complex.I_sq]; ring))
  cont := by fun_prop

/-- The antilinear part `x ↦ (T x + i T (i x)) / 2` of a real-linear operator. -/
noncomputable def antiPart (T : H →L[ℝ] H) : H →SL[starRingEnd ℂ] H where
  toFun x := (1 / 2 : ℂ) • (T x + I • T (I • x))
  map_add' x y := by
    simp only [smul_add, map_add]
    module
  map_smul' c x := by
    have h1 : I • (c • x) = (c.re : ℝ) • (I • x) - (c.im : ℝ) • x := by
      rw [smul_comm, smul_eq_re_im c (I • x), smul_smul, I_mul_I]
      simp [sub_eq_add_neg]
    have h2 : T (c • x) = (c.re : ℝ) • T x + (c.im : ℝ) • T (I • x) := by
      rw [smul_eq_re_im c x]
      simp
    have h3 : T (I • (c • x)) = (c.re : ℝ) • T (I • x) - (c.im : ℝ) • T x := by
      rw [h1]
      simp
    rw [h2, h3]
    simp only [← Complex.coe_smul, smul_sub, smul_add, smul_smul]
    have hc : starRingEnd ℂ c = (c.re : ℂ) - (c.im : ℂ) * I := by
      apply Complex.ext <;> simp
    rw [hc]
    match_scalars <;> (ring_nf; try (simp only [Complex.I_sq]; ring))
  cont := by fun_prop

lemma linPart_apply (T : H →L[ℝ] H) (x : H) :
    linPart T x = (1 / 2 : ℂ) • (T x - I • T (I • x)) := rfl

lemma antiPart_apply (T : H →L[ℝ] H) (x : H) :
    antiPart T x = (1 / 2 : ℂ) • (T x + I • T (I • x)) := rfl

/-- A real-linear operator is the sum of its complex-linear and antilinear parts. -/
theorem linPart_add_antiPart (T : H →L[ℝ] H) (x : H) :
    linPart T x + antiPart T x = T x := by
  rw [linPart_apply, antiPart_apply, ← smul_add]
  have : T x - I • T (I • x) + (T x + I • T (I • x)) = (2 : ℂ) • T x := by module
  rw [this, smul_smul]
  norm_num

/-- A complex-linear real operator is its own linear part. -/
theorem linPart_of_commute (T : H →L[ℝ] H) (h : ∀ x, T (I • x) = I • T x) (x : H) :
    linPart T x = T x := by
  rw [linPart_apply, h, smul_smul, I_mul_I]
  module

end Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.antiPart := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.antiPart
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.antiPart_apply := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.antiPart_apply
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.linPart := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.linPart
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.linPart_add_antiPart := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.linPart_add_antiPart
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.linPart_apply := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.linPart_apply
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.linPart_of_commute := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.linPart_of_commute
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.smul_eq_re_im := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.smul_eq_re_im
