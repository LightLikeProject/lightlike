import Mathlib

/-!
# Differentiating the inverse of a matrix-valued function

If every entry of `M : E → Matrix (Fin n) (Fin n) ℝ` is differentiable and `M y` is invertible for every `y`,
then the entries of `M⁻¹` are differentiable and
`d (M⁻¹)_{ae} (v) = - ∑_{b,c} (M⁻¹)_{ac} d M_{cb} (v) (M⁻¹)_{be}`, i.e. `d (M⁻¹) = - M⁻¹ (dM) M⁻¹`.
The statements are entrywise, so no norm on matrices is used. They are used for the Jacobi identity of the
Dirac bracket (`Tasks/GC/T_GC4_P1.lean`).
-/

open Matrix

namespace Lightlike.Gauge
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

/-- The determinant of a matrix-valued function with differentiable entries is differentiable. -/
theorem differentiableAt_det (M : E → Matrix (Fin n) (Fin n) ℝ) {x : E}
    (hM : ∀ i j, DifferentiableAt ℝ (fun y => M y i j) x) :
    DifferentiableAt ℝ (fun y => (M y).det) x := by
  simp only [Matrix.det_apply']
  refine DifferentiableAt.fun_sum fun σ _ => ?_
  refine DifferentiableAt.const_mul ?_ _
  have h := fun i : Fin n => hM (σ i) i
  fun_prop

/-- The entries of the inverse of a matrix-valued function with differentiable entries and nonzero
determinant are differentiable (Cramer's rule). -/
theorem differentiableAt_inv_entry (M : E → Matrix (Fin n) (Fin n) ℝ) {x : E}
    (hM : ∀ i j, DifferentiableAt ℝ (fun y => M y i j) x) (hdet : (M x).det ≠ 0) (a b : Fin n) :
    DifferentiableAt ℝ (fun y => (M y)⁻¹ a b) x := by
  have hadj : ∀ i j, DifferentiableAt ℝ (fun y => (M y).adjugate i j) x := by
    intro i j
    simp only [Matrix.adjugate_apply]
    refine differentiableAt_det (fun y => (M y).updateRow j (Pi.single i 1)) ?_
    intro k l
    simp only [Matrix.updateRow_apply]
    by_cases h : k = j
    · simp [h]
    · simpa [h] using hM k l
  have hd := differentiableAt_det M hM
  simp only [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  exact (hd.inv hdet).mul (hadj a b)
/-- The derivative of the inverse of a matrix-valued function: `d (M⁻¹) = - M⁻¹ (dM) M⁻¹`, entrywise. -/
theorem fderiv_inv_entry (M : E → Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i j, Differentiable ℝ (fun y => M y i j)) (hdet : ∀ y, (M y).det ≠ 0) (x v : E) (a e : Fin n) :
    fderiv ℝ (fun y => (M y)⁻¹ a e) x v =
      -∑ b, ∑ c, (M x)⁻¹ a c * fderiv ℝ (fun y => M y c b) x v * (M x)⁻¹ b e := by
  have hCi : ∀ i j, DifferentiableAt ℝ (fun y => (M y)⁻¹ i j) x := fun i j =>
    differentiableAt_inv_entry M (fun i j => hM i j x) (hdet x) i j
  have hid : ∀ b, (fun y => ∑ c, (M y)⁻¹ a c * M y c b) = fun _ => if a = b then (1 : ℝ) else 0 := by
    intro b
    funext y
    have := congrFun (congrFun (Matrix.nonsing_inv_mul (M y) (isUnit_iff_ne_zero.mpr (hdet y))) a) b
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    exact this
  have hd : ∀ b, ∑ c, (fderiv ℝ (fun y => (M y)⁻¹ a c) x v * M x c b +
      (M x)⁻¹ a c * fderiv ℝ (fun y => M y c b) x v) = 0 := by
    intro b
    have h1 : fderiv ℝ (fun y => ∑ c, (M y)⁻¹ a c * M y c b) x v = 0 := by
      rw [hid b]; simp
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
    have := congrFun (congrFun (Matrix.mul_nonsing_inv (M x) (isUnit_iff_ne_zero.mpr (hdet x))) c) e
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
