import Mathlib

/-!
# The variation of the volume density (GE15, stage S1, first part)

`hasDerivAt_det_add_smul` is Jacobi's formula `d/dt det (G + t H) = det G · tr (G⁻¹ H)` at `t = 0` for an invertible `G`; `hasDerivAt_sqrt_abs_det_add_smul`
is `d/dt √|det (G + t H)| = ½ √|det G| tr (G⁻¹ H)`, the variation `δ√|g| = ½ √|g| gᵘᵛ δg_{uv}` of the volume density. Neither is in Mathlib.

**Limits.** Stage S1 of the first variation of the Einstein-Hilbert action: the variation of the Christoffel symbols, the Palatini identity
and the integral statement are not in this file.
-/

open Matrix Polynomial

namespace Lightlike

variable {n : ℕ}

/-- The derivative of `det (1 + t A)` at `t = 0` is `tr A`. -/
theorem hasDerivAt_det_one_add_smul (A : Matrix (Fin n) (Fin n) ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t • A).det) A.trace 0 := by
  set Q : ℝ[X] := (det (1 + (X : ℝ[X]) • A.map C)).divX.divX with hQ
  have h : (fun t : ℝ => (1 + t • A).det) = fun t => 1 + A.trace * t + Q.eval t * t ^ 2 := by
    funext t
    exact Matrix.det_one_add_smul t A
  rw [h]
  have h1 : HasDerivAt (fun t : ℝ => 1 + A.trace * t) A.trace 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul A.trace).const_add 1
  have h2 : HasDerivAt (fun t : ℝ => Q.eval t * t ^ 2) 0 0 := by
    have := (Q.hasDerivAt (0 : ℝ)).mul ((hasDerivAt_pow 2 (0 : ℝ)))
    convert this using 1
    simp
  have := h1.add h2
  convert this using 1
  simp

/-- **Jacobi's formula** along a line: `d/dt det (G + t H) = det G · tr (G⁻¹ H)` at `t = 0`. -/
theorem hasDerivAt_det_add_smul (G H : Matrix (Fin n) (Fin n) ℝ) (hG : IsUnit G.det) :
    HasDerivAt (fun t : ℝ => (G + t • H).det) (G.det * (G⁻¹ * H).trace) 0 := by
  have e : ∀ t : ℝ, (G + t • H).det = G.det * (1 + t • (G⁻¹ * H)).det := by
    intro t
    have : G + t • H = G * (1 + t • (G⁻¹ * H)) := by
      rw [mul_add, mul_one, Matrix.mul_smul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG, Matrix.one_mul]
    rw [this, Matrix.det_mul]
  simp_rw [e]
  exact (hasDerivAt_det_one_add_smul (G⁻¹ * H)).const_mul G.det

/-- **The variation of the volume density**: `d/dt √|det (G + t H)| = ½ √|det G| tr (G⁻¹ H)` at `t = 0`. -/
theorem hasDerivAt_sqrt_abs_det_add_smul (G H : Matrix (Fin n) (Fin n) ℝ) (hG : G.det ≠ 0) :
    HasDerivAt (fun t : ℝ => √|(G + t • H).det|) ((1 / 2) * √|G.det| * (G⁻¹ * H).trace) 0 := by
  have hd := hasDerivAt_det_add_smul G H (IsUnit.mk0 _ hG)
  set s : ℝ := (SignType.sign G.det : ℝ) with hs
  have hs2 : s * G.det = |G.det| := by
    rcases lt_or_gt_of_ne hG with h | h
    · simp [hs, abs_of_neg h, sign_neg h]
    · simp [hs, abs_of_pos h, sign_pos h]
  have hpos : 0 < |G.det| := abs_pos.2 hG
  have hs1 : s * s = 1 := by
    rcases lt_or_gt_of_ne hG with h | h
    · simp [hs, sign_neg h]
    · simp [hs, sign_pos h]
  have hev : (fun t : ℝ => √|(G + t • H).det|) =ᶠ[nhds 0] fun t => √(s * (G + t • H).det) := by
    have hc : ContinuousAt (fun t : ℝ => (G + t • H).det) 0 := hd.continuousAt
    have : ∀ᶠ t in nhds (0 : ℝ), s * (G + t • H).det > 0 := by
      have := hc.tendsto.const_mul s
      refine this.eventually (lt_mem_nhds ?_)
      simpa [hs2] using hpos
    filter_upwards [this] with t ht
    congr 1
    have : |(G + t • H).det| = s * (G + t • H).det := by
      rcases lt_or_gt_of_ne hG with h | h
      · have hsn : s = -1 := by simp [hs, sign_neg h]
        rw [hsn] at ht ⊢
        rw [abs_of_neg (by linarith)]; ring
      · have hsn : s = 1 := by simp [hs, sign_pos h]
        rw [hsn] at ht ⊢
        rw [abs_of_pos (by linarith)]; ring
    exact this
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  have h1 : HasDerivAt (fun t : ℝ => s * (G + t • H).det) (s * (G.det * (G⁻¹ * H).trace)) 0 := hd.const_mul s
  have h2 := h1.sqrt (by simpa [hs2] using hpos.ne')
  convert h2 using 1
  simp only [zero_smul, add_zero, hs2]
  have : s * (G.det * (G⁻¹ * H).trace) = |G.det| * (G⁻¹ * H).trace := by rw [← mul_assoc, hs2]
  rw [this]
  have hsq : √|G.det| * √|G.det| = |G.det| := Real.mul_self_sqrt hpos.le
  have hq : 0 < √|G.det| := Real.sqrt_pos.2 hpos
  field_simp
  rw [Real.sq_sqrt hpos.le]
  ring

end Lightlike
