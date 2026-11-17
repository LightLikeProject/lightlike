import Mathlib
import Lightlike.Gauge.MatrixInverse

/-!
# The derivative of the inverse of a matrix-valued function at one point

The pointwise version of `Lightlike.Gauge.fderiv_inv_entry`: the matrix is invertible at `x` only (invertibility
near `x` follows by continuity).
-/

open Matrix

namespace Lightlike.Gauge
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

/-- The derivative of the inverse of a matrix-valued function: `d (M⁻¹) = - M⁻¹ (dM) M⁻¹`, entrywise. -/
theorem fderiv_inv_entry_at (M : E → Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i j, Differentiable ℝ (fun y => M y i j)) (x v : E) (hdetx : (M x).det ≠ 0) (a e : Fin n) :
    fderiv ℝ (fun y => (M y)⁻¹ a e) x v =
      -∑ b, ∑ c, (M x)⁻¹ a c * fderiv ℝ (fun y => M y c b) x v * (M x)⁻¹ b e := by
  have hCi : ∀ i j, DifferentiableAt ℝ (fun y => (M y)⁻¹ i j) x := fun i j =>
    differentiableAt_inv_entry M (fun i j => hM i j x) hdetx i j
  have hev : ∀ᶠ y in nhds x, (M y).det ≠ 0 :=
    (differentiableAt_det M (fun i j => hM i j x)).continuousAt.eventually_ne hdetx
  have hid : ∀ b, (fun y => ∑ c, (M y)⁻¹ a c * M y c b) =ᶠ[nhds x] fun _ => if a = b then (1 : ℝ) else 0 := by
    intro b
    filter_upwards [hev] with y hy
    have := congrFun (congrFun (Matrix.nonsing_inv_mul (M y) (isUnit_iff_ne_zero.mpr hy)) a) b
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    exact this
  have hd : ∀ b, ∑ c, (fderiv ℝ (fun y => (M y)⁻¹ a c) x v * M x c b +
      (M x)⁻¹ a c * fderiv ℝ (fun y => M y c b) x v) = 0 := by
    intro b
    have h1 : fderiv ℝ (fun y => ∑ c, (M y)⁻¹ a c * M y c b) x v = 0 := by
      rw [(hid b).fderiv_eq]; simp
    have hs : HasFDerivAt (fun y => ∑ c, (M y)⁻¹ a c * M y c b) _ x := HasFDerivAt.fun_sum (u := Finset.univ)
      (fun c _ => (hCi a c).hasFDerivAt.mul ((hM c b x).hasFDerivAt))
    rw [hs.fderiv] at h1
    simp only [_root_.sum_apply, _root_.add_apply,
      _root_.smul_apply, smul_eq_mul] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  have hMC : ∀ c, ∑ b, M x c b * (M x)⁻¹ b e = if c = e then (1 : ℝ) else 0 := by
    intro c
    have := congrFun (congrFun (Matrix.mul_nonsing_inv (M x) (isUnit_iff_ne_zero.mpr hdetx)) c) e
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    exact this
  have hu : ∀ b, ∑ c, fderiv ℝ (fun y => (M y)⁻¹ a c) x v * M x c b =
      -∑ c, (M x)⁻¹ a c * fderiv ℝ (fun y => M y c b) x v := by
    intro b
    have := hd b
    rw [Finset.sum_add_distrib] at this
    linarith
  calc fderiv ℝ (fun y => (M y)⁻¹ a e) x v
      = ∑ c, fderiv ℝ (fun y => (M y)⁻¹ a c) x v * (if c = e then (1 : ℝ) else 0) := by simp
    _ = ∑ c, fderiv ℝ (fun y => (M y)⁻¹ a c) x v * ∑ b, M x c b * (M x)⁻¹ b e := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [hMC c]
    _ = ∑ b, (∑ c, fderiv ℝ (fun y => (M y)⁻¹ a c) x v * M x c b) * (M x)⁻¹ b e := by
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring
    _ = -∑ b, ∑ c, (M x)⁻¹ a c * fderiv ℝ (fun y => M y c b) x v * (M x)⁻¹ b e := by
        simp_rw [hu, neg_mul, Finset.sum_mul]
        rw [Finset.sum_neg_distrib]
end Lightlike.Gauge
